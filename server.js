'use strict';

require('dotenv').config();

const dns = require('dns');
try {
  dns.setServers(['8.8.8.8', '8.8.4.4', '1.1.1.1', '1.0.0.1']);
  dns.setDefaultResultOrder('ipv4first');
  console.log('[dns] using 8.8.8.8 / 1.1.1.1, ipv4first');
} catch (e) {
  console.warn('[dns] could not override servers:', e.message);
}

const fs = require('fs');
const os = require('os');
const path = require('path');
const http = require('http');
const net = require('net');
const crypto = require('crypto');
const { spawn } = require('child_process');
const { pipeline } = require('stream/promises');
const { pack: tarPack, extract: tarExtract } = require('tar');

const express = require('express');
const cookieParser = require('cookie-parser');
const bcrypt = require('bcryptjs');
const jwt = require('jsonwebtoken');
const httpProxy = require('http-proxy');
const mongoose = require('mongoose');
const {
  S3Client,
  GetObjectCommand,
  DeleteObjectCommand,
  HeadObjectCommand,
} = require('@aws-sdk/client-s3');
const { Upload } = require('@aws-sdk/lib-storage');

/* ============================================================
 * Config
 * ============================================================ */

const PORT = Number(process.env.PORT || 3000);
const BASE_DOMAIN = (process.env.BASE_DOMAIN || 'localhost').toLowerCase();
const JWT_SECRET = process.env.SESSION_SECRET || process.env.JWT_SECRET || '';
const APP_PORT_START = Number(process.env.APP_PORT_START || 4000);
const APP_PORT_END = Number(process.env.APP_PORT_END || 4999);
const IS_PROD = process.env.NODE_ENV === 'production';
const MONGO_URI = process.env.MONGO_URI;
const B2_ENDPOINT = process.env.B2_ENDPOINT;
const B2_ACCESS_KEY_ID = process.env.B2_ACCESS_KEY_ID;
const B2_SECRET_ACCESS_KEY = process.env.B2_SECRET_ACCESS_KEY;
const B2_BUCKET_NAME = process.env.B2_BUCKET_NAME;
const B2_REGION = process.env.B2_REGION || 'us-east-005';
const B2_FOLDER = process.env.B2_FOLDER || 'bdeploy';

// New production settings
const ALLOWED_EMAILS = (process.env.ALLOWED_EMAILS || '')
  .split(',').map((s) => s.trim().toLowerCase()).filter(Boolean);
const INVITE_ONLY = ALLOWED_EMAILS.length > 0;
const MAX_PROJECTS_PER_USER = Number(process.env.MAX_PROJECTS_PER_USER || 5);
const BUILD_TIMEOUT_MS = Number(process.env.BUILD_TIMEOUT_MS || 5 * 60 * 1000);

// Validate required secrets at startup
if (!JWT_SECRET || JWT_SECRET.length < 32) {
  console.error('FATAL: SESSION_SECRET must be set and at least 32 characters.');
  process.exit(1);
}
if (!MONGO_URI) {
  console.error('FATAL: MONGO_URI is required.');
  process.exit(1);
}
if (!B2_ENDPOINT || !B2_ACCESS_KEY_ID || !B2_SECRET_ACCESS_KEY || !B2_BUCKET_NAME) {
  console.error('FATAL: B2_* environment variables are required.');
  process.exit(1);
}

const TEMP_ROOT = path.join(os.tmpdir(), 'minideploy-work');
fs.mkdirSync(TEMP_ROOT, { recursive: true });

const RESERVED = new Set([
  'www', 'api', 'admin', 'app', 'mail', 'ftp', 'cdn', 'static', 'assets',
  'blog', 'docs', 'status', 'support', 'dashboard', 'test', 'dev', 'staging',
  'root', 'localhost', 'ns', 'ns1', 'ns2', 'smtp', 'imap', 'pop', 'vpn', 'preview',
]);

/* ============================================================
 * Child process env — strict whitelist
 *
 * Deployed apps MUST NOT see MONGO_URI, B2_*, SESSION_SECRET.
 * ============================================================ */

const CHILD_ENV_SAFE_KEYS = [
  'PATH', 'LANG', 'LC_ALL', 'LC_CTYPE', 'TZ', 'SHELL', 'TERM',
  'TEMP', 'TMP', 'TMPDIR',
  'USER', 'USERNAME', 'LOGNAME',
  'SystemRoot', 'windir', 'PATHEXT', 'ComSpec', 'OS',
  'PROCESSOR_ARCHITECTURE', 'NUMBER_OF_PROCESSORS',
  'APPDATA', 'LOCALAPPDATA', 'PROGRAMFILES', 'PROGRAMFILES(X86)', 'PROGRAMDATA',
  'HOMEDRIVE', 'HOMEPATH',
];

const BLOCKED_USER_ENV = new Set([
  'PATH', 'HOME', 'USERPROFILE', 'HOMEDRIVE', 'HOMEPATH',
  'NODE_OPTIONS', 'NODE_PATH', 'NODE_ENV', 'PORT', 'HOST',
  'LD_PRELOAD', 'LD_LIBRARY_PATH', 'DYLD_INSERT_LIBRARIES', 'DYLD_LIBRARY_PATH',
]);

function sanitizeUserEnv(obj) {
  const out = {};
  for (const [k, v] of Object.entries(obj || {})) {
    if (BLOCKED_USER_ENV.has(k)) continue;
    if (!/^[A-Za-z_][A-Za-z0-9_]*$/.test(k)) continue;
    out[k] = String(v);
  }
  return out;
}

function homeDirFor(projectId) {
  const dir = path.join(TEMP_ROOT, 'home-' + projectId);
  fs.mkdirSync(dir, { recursive: true });
  return dir;
}

function buildChildEnv(projectId, userEnv, port) {
  const homeDir = homeDirFor(projectId);
  const env = {};

  for (const k of CHILD_ENV_SAFE_KEYS) {
    if (process.env[k] != null) env[k] = process.env[k];
  }

  // Override always
  env.HOME = homeDir;
  env.USERPROFILE = homeDir;
  env.HOMEDRIVE = path.parse(homeDir).root;
  env.HOMEPATH = homeDir.slice(path.parse(homeDir).root.length);
  env.NODE_ENV = 'production';
  if (port != null) {
    env.PORT = String(port);
    env.HOST = '0.0.0.0';
  }

  // Quiet npm
  env.npm_config_update_notifier = 'false';
  env.npm_config_fund = 'false';
  env.npm_config_audit = 'false';
  env.npm_config_cache = path.join(homeDir, '.npm');

  Object.assign(env, sanitizeUserEnv(userEnv));
  return env;
}

/* ============================================================
 * Backblaze B2 — streamed
 * ============================================================ */

const s3 = new S3Client({
  endpoint: 'https://' + B2_ENDPOINT,
  region: B2_REGION,
  credentials: { accessKeyId: B2_ACCESS_KEY_ID, secretAccessKey: B2_SECRET_ACCESS_KEY },
  forcePathStyle: true,
});

const b2Key = (projectId) => B2_FOLDER + '/' + projectId + '.tar.gz';

async function uploadToB2(projectId, sourceDir) {
  const tarPath = path.join(TEMP_ROOT, projectId + '.tar.gz');
  try {
    await tarPack({ gzip: true, file: tarPath, cwd: sourceDir }, ['.']);
    const stat = fs.statSync(tarPath);
    const upload = new Upload({
      client: s3,
      params: {
        Bucket: B2_BUCKET_NAME,
        Key: b2Key(projectId),
        Body: fs.createReadStream(tarPath),
        ContentType: 'application/gzip',
        ContentLength: stat.size,
      },
    });
    await upload.done();
    console.log('[b2] uploaded', b2Key(projectId), '(' + (stat.size / 1024).toFixed(1) + ' KB)');
  } finally {
    try { fs.unlinkSync(tarPath); } catch (e) {}
  }
}

async function downloadFromB2(projectId, destDir) {
  const tarPath = path.join(TEMP_ROOT, projectId + '-dl.tar.gz');
  try {
    const resp = await s3.send(new GetObjectCommand({
      Bucket: B2_BUCKET_NAME,
      Key: b2Key(projectId),
    }));
    await pipeline(resp.Body, fs.createWriteStream(tarPath));
    fs.mkdirSync(destDir, { recursive: true });
    await tarExtract({ file: tarPath, cwd: destDir });
    console.log('[b2] downloaded', b2Key(projectId));
    return true;
  } catch (err) {
    if (err.name === 'NoSuchKey' || err.$metadata?.httpStatusCode === 404) {
      console.log('[b2] no archive for', projectId);
      return false;
    }
    throw err;
  } finally {
    try { fs.unlinkSync(tarPath); } catch (e) {}
  }
}

async function deleteFromB2(projectId) {
  try {
    await s3.send(new DeleteObjectCommand({
      Bucket: B2_BUCKET_NAME,
      Key: b2Key(projectId),
    }));
    console.log('[b2] deleted', b2Key(projectId));
  } catch (err) {
    console.warn('[b2] delete failed:', err.message);
  }
}

/* ============================================================
 * MongoDB models
 * ============================================================ */

const userSchema = new mongoose.Schema({
  email: { type: String, required: true, unique: true, lowercase: true, trim: true },
  password_hash: { type: String, required: true },
}, { timestamps: true });

const projectSchema = new mongoose.Schema({
  user_id: { type: String, required: true, index: true },
  name: { type: String, required: true, unique: true, lowercase: true, trim: true },
  repo_url: { type: String, default: null },
  install_command: { type: String, default: 'npm install' },
  start_command: { type: String, default: 'npm start' },
  env_vars: { type: String, default: '{}' },
  port: { type: Number, default: null },
  pid: { type: Number, default: null },
  status: { type: String, default: 'created' },
  last_deploy: { type: Date, default: null },
  has_b2_archive: { type: Boolean, default: false },
}, { timestamps: true });

const logSchema = new mongoose.Schema({
  project_id: { type: String, required: true, unique: true },
  content: { type: String, default: '' },
}, { timestamps: true });

const User = mongoose.model('User', userSchema);
const Project = mongoose.model('Project', projectSchema);
const LogEntry = mongoose.model('LogEntry', logSchema);

/* ============================================================
 * Helpers
 * ============================================================ */

const safeJson = (val, fallback = {}) => {
  if (val == null) return fallback;
  if (typeof val === 'object') return val;
  try { return JSON.parse(val) ?? fallback; } catch { return fallback; }
};

const NAME_RE = /^[a-z0-9](?:[a-z0-9-]{0,30}[a-z0-9])?$/;

function allocatePort() {
  const used = new Set([...running.values()].map((r) => r.port).filter(Boolean));
  for (let p = APP_PORT_START; p <= APP_PORT_END; p++) if (!used.has(p)) return p;
  throw new Error('No free app ports');
}

const sourceDir = (projectId) => path.join(TEMP_ROOT, 'src-' + projectId);

function parseEnvText(text) {
  const out = {};
  if (!text) return out;
  for (const raw of String(text).split(/\r?\n/)) {
    const line = raw.trim();
    if (!line || line.startsWith('#')) continue;
    const eq = line.indexOf('=');
    if (eq === -1) continue;
    const key = line.slice(0, eq).trim();
    if (!/^[A-Za-z_][A-Za-z0-9_]*$/.test(key)) continue;
    let val = line.slice(eq + 1).trim();
    if ((val.startsWith('"') && val.endsWith('"')) ||
        (val.startsWith("'") && val.endsWith("'"))) val = val.slice(1, -1);
    out[key] = val;
  }
  return out;
}

const envToText = (obj) => {
  const e = Object.entries(obj || {});
  return e.length ? e.map(([k, v]) => k + '=' + v).join('\n') : '';
};

function serializeProject(p) {
  if (!p) return p;
  const obj = typeof p.toObject === 'function' ? p.toObject() : { ...p };
  obj.id = obj._id ? String(obj._id) : obj.id;
  const { env_vars, _id, __v, ...rest } = obj;
  return { ...rest, env: envToText(safeJson(env_vars)) };
}

/* ============================================================
 * Rate limiter — in-memory, IP-based
 * ============================================================ */

function createRateLimiter(opts) {
  const windowMs = opts.windowMs || 15 * 60 * 1000;
  const max = opts.max || 30;
  const buckets = new Map();

  // Cleanup every minute
  setInterval(() => {
    const now = Date.now();
    for (const [k, arr] of buckets) {
      const fresh = arr.filter((t) => now - t < windowMs);
      if (fresh.length) buckets.set(k, fresh);
      else buckets.delete(k);
    }
  }, 60_000).unref();

  return function (req, res, next) {
    const key = req.ip || (req.socket && req.socket.remoteAddress) || 'unknown';
    const now = Date.now();
    const arr = (buckets.get(key) || []).filter((t) => now - t < windowMs);

    if (arr.length >= max) {
      const retryAfter = Math.ceil((windowMs - (now - arr[0])) / 1000);
      res.setHeader('Retry-After', String(retryAfter));
      return res.status(429).json({ error: 'Too many requests. Try again in ' + retryAfter + 's.' });
    }

    arr.push(now);
    buckets.set(key, arr);
    next();
  };
}

/* ============================================================
 * Logs
 * ============================================================ */

const MAX_LOG_CHARS = 400_000;
const logBuffers = new Map();
const logSubscribers = new Map();
const logSaveTimers = new Map();

function appendLog(projectId, chunk) {
  if (!chunk) return;
  let buf = logBuffers.get(projectId) || '';
  buf += chunk;
  if (buf.length > MAX_LOG_CHARS) buf = buf.slice(buf.length - MAX_LOG_CHARS);
  logBuffers.set(projectId, buf);

  const subs = logSubscribers.get(projectId);
  if (subs) for (const fn of subs) { try { fn(chunk); } catch (e) {} }

  if (!logSaveTimers.has(projectId)) {
    logSaveTimers.set(projectId, setTimeout(async () => {
      logSaveTimers.delete(projectId);
      try {
        await LogEntry.findOneAndUpdate(
          { project_id: projectId },
          { content: logBuffers.get(projectId) || '' },
          { upsert: true }
        );
      } catch (e) {}
    }, 2000));
  }
}

const readLogs = (projectId) => logBuffers.get(projectId) || '';

function subscribeLogs(projectId, fn) {
  if (!logSubscribers.has(projectId)) logSubscribers.set(projectId, new Set());
  logSubscribers.get(projectId).add(fn);
  return () => {
    const s = logSubscribers.get(projectId);
    if (!s) return;
    s.delete(fn);
    if (!s.size) logSubscribers.delete(projectId);
  };
}

async function loadLogs(projectId) {
  try {
    const entry = await LogEntry.findOne({ project_id: projectId });
    if (entry && entry.content) logBuffers.set(projectId, entry.content);
  } catch (e) {}
}

/* ============================================================
 * Process manager
 * ============================================================ */

const running = new Map();

function killTree(child) {
  if (!child || child.killed) return;
  if (process.platform === 'win32') {
    try { spawn('taskkill', ['/pid', String(child.pid), '/T', '/F'], { stdio: 'ignore' }); }
    catch (e) {}
  } else {
    try { process.kill(-child.pid, 'SIGTERM'); }
    catch (e) { try { child.kill('SIGTERM'); } catch (e2) {} }
  }
}

function runCommand(command, cwd, projectId, opts) {
  opts = opts || {};
  const args = opts.args || [];
  const timeoutMs = opts.timeoutMs || BUILD_TIMEOUT_MS;

  return new Promise((resolve, reject) => {
    const useShell = args.length === 0;
    const env = buildChildEnv(projectId, {}, null);

    const child = useShell
      ? spawn(command, { cwd, shell: true, env, detached: process.platform !== 'win32' })
      : spawn(command, args, { cwd, env, detached: process.platform !== 'win32' });

    let settled = false;
    const finish = (err) => {
      if (settled) return;
      settled = true;
      clearTimeout(timer);
      if (err) reject(err); else resolve();
    };

    const timer = setTimeout(() => {
      appendLog(projectId, '\n[bdeploy] command timed out after ' + Math.round(timeoutMs / 1000) + 's — killing\n');
      killTree(child);
      finish(new Error('`' + command + '` timed out after ' + Math.round(timeoutMs / 1000) + 's'));
    }, timeoutMs);

    child.stdout.on('data', (d) => appendLog(projectId, d.toString()));
    child.stderr.on('data', (d) => appendLog(projectId, d.toString()));
    child.on('error', (err) => finish(new Error('spawn ' + command + ': ' + err.message)));
    child.on('close', (code) => {
      if (code === 0) return finish();
      finish(new Error('`' + command + (args.length ? ' ' + args.join(' ') : '') + '` exited ' + code));
    });
  });
}

function waitForPort(port, timeoutMs) {
  timeoutMs = timeoutMs || 25000;
  return new Promise((resolve, reject) => {
    const start = Date.now();
    const tick = () => {
      const sock = net.createConnection(port, '127.0.0.1');
      sock.once('connect', () => { sock.destroy(); resolve(); });
      sock.once('error', () => {
        sock.destroy();
        if (Date.now() - start > timeoutMs) return reject(new Error('timeout port ' + port));
        setTimeout(tick, 300);
      });
    };
    tick();
  });
}

function writePlaceholderApp(dir, name) {
  const indexJs =
    "const http = require('http');\n" +
    "const PORT = process.env.PORT || 3000;\n" +
    "const NAME = " + JSON.stringify(name) + ";\n" +
    "http.createServer(function (req, res) {\n" +
    "  res.writeHead(200, { 'Content-Type': 'text/html; charset=utf-8' });\n" +
    "  res.end('<!doctype html><meta charset=\"utf-8\"><title>' + NAME + '</title>'\n" +
    "    + '<body style=\"font-family:system-ui;background:#09090b;color:#e4e4e7;padding:60px;text-align:center;\">'\n" +
    "    + '<h1 style=\"color:#fafafa;font-size:36px;\">' + NAME + '</h1>'\n" +
    "    + '<p style=\"color:#a1a1aa;\">Your app is live. Deploy your own code by adding a Git repo URL.</p>');\n" +
    "}).listen(PORT, function () { console.log('listening on port ' + PORT); });\n";
  const pkg = JSON.stringify({
    name, version: '1.0.0', private: true,
    scripts: { start: 'node index.js' },
  }, null, 2);
  fs.writeFileSync(path.join(dir, 'index.js'), indexJs, 'utf8');
  fs.writeFileSync(path.join(dir, 'package.json'), pkg, 'utf8');
}

async function startProject(projectId) {
  stopProject(projectId, { silent: true });

  const project = await Project.findById(projectId);
  if (!project) return;
  const src = sourceDir(projectId);

  if (!fs.existsSync(path.join(src, 'package.json'))) {
    appendLog(projectId, '[bdeploy] source not on disk, downloading from B2...\n');
    const ok = await downloadFromB2(projectId, src);
    if (!ok) {
      appendLog(projectId, '[bdeploy] no B2 archive found — triggering full deploy\n');
      await deployProject(projectId);
      return;
    }
    if (project.install_command && project.install_command.trim()) {
      appendLog(projectId, '$ ' + project.install_command + '\n');
      try {
        await runCommand(project.install_command, src, projectId);
      } catch (err) {
        appendLog(projectId, '[bdeploy] install failed: ' + err.message + '\n');
      }
    }
  }

  const port = allocatePort();
  appendLog(projectId, '\n[bdeploy] starting "' + project.name + '" on port ' + port + '\n');

  const childEnv = buildChildEnv(projectId, safeJson(project.env_vars), port);

  const child = spawn(project.start_command, {
    cwd: src,
    shell: true,
    detached: process.platform !== 'win32',
    env: childEnv,
  });

  running.set(projectId, { child, port });

  child.stdout.on('data', (d) => appendLog(projectId, d.toString()));
  child.stderr.on('data', (d) => appendLog(projectId, d.toString()));

  child.on('error', async (err) => {
    appendLog(projectId, '\n[bdeploy] start failed: ' + err.message + '\n');
    await Project.findByIdAndUpdate(projectId, { status: 'failed', pid: null });
    running.delete(projectId);
  });

  child.on('close', async (code) => {
    appendLog(projectId, '\n[bdeploy] process exited (' + code + ')\n');
    running.delete(projectId);
    const cur = await Project.findById(projectId);
    if (cur && (cur.status === 'running' || cur.status === 'starting')) {
      await Project.findByIdAndUpdate(projectId, { status: 'stopped', pid: null });
    }
  });

  await Project.findByIdAndUpdate(projectId, { status: 'starting', port, pid: child.pid });

  const suffix = PORT === 80 ? '' : ':' + PORT;
  waitForPort(port, 25000).then(async () => {
    await Project.findByIdAndUpdate(projectId, { status: 'running' });
    appendLog(projectId, '[bdeploy] live → http://' + project.name + '.' + BASE_DOMAIN + suffix + '\n');
    appendLog(projectId, '[bdeploy] preview → http://' + BASE_DOMAIN + suffix + '/preview/' + project.name + '/\n');
  }).catch(async () => {
    appendLog(projectId, '[bdeploy] warning: port ' + port + ' not ready within 25s\n');
    await Project.findByIdAndUpdate(projectId, { status: 'running' });
  });
}

function stopProject(projectId, opts) {
  opts = opts || {};
  const rt = running.get(projectId);
  if (rt) {
    if (!opts.silent) appendLog(projectId, '[bdeploy] stopping\n');
    killTree(rt.child);
    running.delete(projectId);
  }
}

async function deployProject(projectId) {
  const project = await Project.findById(projectId);
  if (!project) return;

  await Project.findByIdAndUpdate(projectId, { status: 'building' });
  logBuffers.set(projectId, '');
  appendLog(projectId, '[bdeploy] deploy started ' + new Date().toISOString() + '\n');

  const src = sourceDir(projectId);

  try {
    if (project.repo_url) {
      if (!/^https?:\/\/|^git@/i.test(project.repo_url)) {
        throw new Error('Invalid repository URL — must start with http(s):// or git@');
      }

      const hasGit = fs.existsSync(path.join(src, '.git'));
      if (hasGit) {
        appendLog(projectId, '$ git fetch --all && git reset --hard HEAD\n');
        await runCommand('git', src, projectId, { args: ['fetch', '--all'] });
        await runCommand('git', src, projectId, { args: ['reset', '--hard', 'HEAD'] });
        await runCommand('git', src, projectId, { args: ['pull', '--force'] });
      } else {
        fs.rmSync(src, { recursive: true, force: true });
        appendLog(projectId, '$ git clone --depth 1 ' + project.repo_url + '\n');
        await runCommand('git', TEMP_ROOT, projectId, {
          args: ['clone', '--depth', '1', project.repo_url, src],
        });
      }
    } else {
      fs.mkdirSync(src, { recursive: true });
      if (!fs.existsSync(path.join(src, 'package.json'))) {
        appendLog(projectId, '[bdeploy] no repo URL → placeholder app\n');
        writePlaceholderApp(src, project.name);
      }
    }

    if (project.install_command && project.install_command.trim()) {
      appendLog(projectId, '$ ' + project.install_command + '\n');
      await runCommand(project.install_command, src, projectId);
    }

    appendLog(projectId, '[bdeploy] archiving to B2...\n');
    try {
      await uploadToB2(projectId, src);
      await Project.findByIdAndUpdate(projectId, { has_b2_archive: true, last_deploy: new Date() });
      appendLog(projectId, '[bdeploy] archived to B2 ✓\n');
    } catch (err) {
      appendLog(projectId, '[bdeploy] B2 upload warning: ' + err.message + '\n');
    }

    await startProject(projectId);
  } catch (err) {
    appendLog(projectId, '\n[bdeploy] DEPLOY FAILED: ' + err.message + '\n');
    await Project.findByIdAndUpdate(projectId, { status: 'failed' });
  }
}

async function autoStartProjects() {
  try {
    const all = await Project.find({
      status: { $in: ['running', 'starting', 'stopped', 'building'] },
      $or: [{ has_b2_archive: true }, { repo_url: { $ne: null } }],
    }).limit(50);

    if (!all.length) { console.log('[boot] no projects to auto-start'); return; }
    console.log('[boot] auto-starting ' + all.length + ' project(s)...');

    for (const p of all) {
      const pid = String(p._id);
      await loadLogs(pid);
      setTimeout(() => {
        startProject(pid).catch((err) =>
          console.error('[boot] start', p.name, err.message));
      }, 800);
    }
  } catch (err) {
    console.error('[boot] autostart failed:', err.message);
  }
}

/* ============================================================
 * Auth
 * ============================================================ */

const signToken = (userId) => jwt.sign({ sub: userId }, JWT_SECRET, { expiresIn: '7d' });

function setAuthCookie(res, userId) {
  res.cookie('token', signToken(userId), {
    httpOnly: true,
    sameSite: 'lax',
    secure: IS_PROD,
    maxAge: 7 * 24 * 60 * 60 * 1000,
    path: '/',
  });
}

function currentUser(req) {
  const token = (req.cookies && req.cookies.token) ||
    (req.headers.authorization || '').replace(/^Bearer\s+/i, '');
  if (!token) return null;
  try { return { id: jwt.verify(token, JWT_SECRET).sub }; }
  catch (e) { return null; }
}

async function requireAuth(req, res, next) {
  const cu = currentUser(req);
  if (!cu) return res.status(401).json({ error: 'Not authenticated' });
  const user = await User.findById(cu.id).lean();
  if (!user) return res.status(401).json({ error: 'Not authenticated' });
  req.user = { id: String(user._id), email: user.email };
  next();
}

/* ============================================================
 * Express app
 * ============================================================ */

const app = express();
app.disable('x-powered-by');
app.set('trust proxy', 1); // Render sits in front of us

// Security headers
app.use((req, res, next) => {
  res.setHeader('X-Content-Type-Options', 'nosniff');
  res.setHeader('X-Frame-Options', 'DENY');
  res.setHeader('Referrer-Policy', 'strict-origin-when-cross-origin');
  res.setHeader('Permissions-Policy', 'geolocation=(), microphone=(), camera=()');
  if (IS_PROD) {
    res.setHeader('Strict-Transport-Security', 'max-age=31536000; includeSubDomains');
  }
  next();
});

app.use(express.json({ limit: '1mb' }));
app.use(cookieParser());

/* ---------- Rate limiters ---------- */

const authLimiter = createRateLimiter({ windowMs: 15 * 60 * 1000, max: 20 });
const signupLimiter = createRateLimiter({ windowMs: 60 * 60 * 1000, max: 5 });
const createProjectLimiter = createRateLimiter({ windowMs: 60 * 60 * 1000, max: 20 });

/* ---------- Health ---------- */

app.get('/health', (req, res) => {
  const mongoOk = mongoose.connection.readyState === 1;
  res.status(200).json({
    ok: true,
    mongo: mongoOk ? 'connected' : 'disconnected',
    uptime: Math.floor(process.uptime()),
    running: running.size,
    version: '1.0.0',
  });
});

/* ---------- Auth routes ---------- */

app.post('/api/auth/signup', signupLimiter, async (req, res) => {
  try {
    const email = String((req.body && req.body.email) || '').trim().toLowerCase();
    const password = String((req.body && req.body.password) || '');

    if (!/^[^@\s]+@[^@\s]+\.[^@\s]+$/.test(email))
      return res.status(400).json({ error: 'Invalid email' });
    if (password.length < 8)
      return res.status(400).json({ error: 'Password must be at least 8 characters' });
    if (password.length > 200)
      return res.status(400).json({ error: 'Password too long' });

    if (INVITE_ONLY && !ALLOWED_EMAILS.includes(email)) {
      return res.status(403).json({ error: 'This email is not on the invite list' });
    }

    if (await User.findOne({ email }))
      return res.status(409).json({ error: 'Email already registered' });

    const password_hash = await bcrypt.hash(password, 12);
    const user = await User.create({ email, password_hash });
    setAuthCookie(res, String(user._id));
    res.status(201).json({ user: { id: String(user._id), email } });
  } catch (err) {
    console.error('[signup]', err);
    res.status(500).json({ error: 'Signup failed' });
  }
});

app.post('/api/auth/login', authLimiter, async (req, res) => {
  try {
    const email = String((req.body && req.body.email) || '').trim().toLowerCase();
    const password = String((req.body && req.body.password) || '');

    const user = await User.findOne({ email });
    if (!user || !(await bcrypt.compare(password, user.password_hash)))
      return res.status(401).json({ error: 'Invalid credentials' });

    setAuthCookie(res, String(user._id));
    res.json({ user: { id: String(user._id), email: user.email } });
  } catch (err) {
    console.error('[login]', err);
    res.status(500).json({ error: 'Login failed' });
  }
});

app.post('/api/auth/logout', (req, res) => {
  res.clearCookie('token', { path: '/' });
  res.json({ ok: true });
});

app.get('/api/auth/me', async (req, res) => {
  const cu = currentUser(req);
  if (!cu) return res.json({ user: null });
  const user = await User.findById(cu.id).lean();
  if (!user) return res.json({ user: null });
  res.json({ user: { id: String(user._id), email: user.email } });
});

/* ---------- Projects ---------- */

app.get('/api/projects', requireAuth, async (req, res) => {
  const list = await Project.find({ user_id: req.user.id }).sort({ createdAt: -1 }).lean();
  const out = list.map((p) => {
    const s = serializeProject(p);
    if (running.has(String(p._id))) s.status = 'running';
    return s;
  });
  res.json({ projects: out });
});

app.post('/api/projects', requireAuth, createProjectLimiter, async (req, res) => {
  try {
    const body = req.body || {};
    const name = String(body.name || '').trim().toLowerCase();
    const repoUrl = String(body.repoUrl || '').trim() || null;
    const installCommand = String(body.installCommand != null ? body.installCommand : 'npm install').trim();
    const startCommand = String(body.startCommand != null ? body.startCommand : 'npm start').trim();
    const envObj = typeof body.env === 'string'
      ? parseEnvText(body.env)
      : (body.env && typeof body.env === 'object' && !Array.isArray(body.env) ? body.env : {});

    if (!NAME_RE.test(name))
      return res.status(400).json({ error: 'Name: 1-32 chars, lowercase, alphanumeric + dash' });
    if (RESERVED.has(name))
      return res.status(400).json({ error: '"' + name + '" is reserved' });
    if (await Project.findOne({ name }))
      return res.status(409).json({ error: '"' + name + '" is taken' });
    if (!startCommand)
      return res.status(400).json({ error: 'Start command required' });
    if (installCommand.length > 500 || startCommand.length > 500)
      return res.status(400).json({ error: 'Commands too long (max 500 chars)' });

    const count = await Project.countDocuments({ user_id: req.user.id });
    if (count >= MAX_PROJECTS_PER_USER)
      return res.status(403).json({ error: 'Project limit reached (' + MAX_PROJECTS_PER_USER + ')' });

    const project = await Project.create({
      user_id: req.user.id, name, repo_url: repoUrl,
      install_command: installCommand, start_command: startCommand,
      env_vars: JSON.stringify(envObj), status: 'created',
    });

    const pid = String(project._id);
    fs.mkdirSync(sourceDir(pid), { recursive: true });

    res.status(201).json({ project: serializeProject(project) });
    deployProject(pid).catch((err) => console.error('[deploy]', err));
  } catch (err) {
    console.error('[create-project]', err);
    res.status(500).json({ error: 'Failed to create project' });
  }
});

async function ownProject(req, res) {
  const p = await Project.findById(req.params.id);
  if (!p) { res.status(404).json({ error: 'Not found' }); return null; }
  if (p.user_id !== req.user.id) { res.status(403).json({ error: 'Forbidden' }); return null; }
  return p;
}

app.post('/api/projects/:id/deploy', requireAuth, async (req, res) => {
  const p = await ownProject(req, res); if (!p) return;
  if (p.status === 'building') return res.status(409).json({ error: 'Deploy in progress' });
  stopProject(String(p._id));
  res.status(202).json({ ok: true });
  deployProject(String(p._id)).catch((err) => console.error('[deploy]', err));
});

app.post('/api/projects/:id/restart', requireAuth, async (req, res) => {
  const p = await ownProject(req, res); if (!p) return;
  startProject(String(p._id)).catch((err) => console.error(err));
  res.json({ ok: true });
});

app.post('/api/projects/:id/stop', requireAuth, async (req, res) => {
  const p = await ownProject(req, res); if (!p) return;
  stopProject(String(p._id));
  await Project.findByIdAndUpdate(p._id, { status: 'stopped', pid: null });
  res.json({ ok: true });
});

app.get('/api/projects/:id/logs', requireAuth, async (req, res) => {
  const p = await ownProject(req, res); if (!p) return;
  const pid = String(p._id);
  if (!logBuffers.has(pid)) await loadLogs(pid);
  res.json({ logs: readLogs(pid), status: p.status });
});

app.get('/api/projects/:id/logs/stream', requireAuth, async (req, res) => {
  const p = await ownProject(req, res); if (!p) return;
  const pid = String(p._id);
  if (!logBuffers.has(pid)) await loadLogs(pid);

  res.setHeader('Content-Type', 'text/event-stream; charset=utf-8');
  res.setHeader('Cache-Control', 'no-cache, no-transform');
  res.setHeader('Connection', 'keep-alive');
  res.setHeader('X-Accel-Buffering', 'no');
  if (res.flushHeaders) res.flushHeaders();

  const send = (obj) => { try { res.write('data: ' + JSON.stringify(obj) + '\n\n'); } catch (e) {} };
  send({ reset: true, chunk: readLogs(pid) });
  const unsub = subscribeLogs(pid, (chunk) => send({ chunk }));
  const hb = setInterval(() => { try { res.write(': ping\n\n'); } catch (e) {} }, 25000);
  req.on('close', () => { clearInterval(hb); unsub(); });
});

app.patch('/api/projects/:id', requireAuth, async (req, res) => {
  const p = await ownProject(req, res); if (!p) return;
  const body = req.body || {};
  const patch = {};
  if (typeof body.startCommand === 'string') patch.start_command = body.startCommand.trim().slice(0, 500);
  if (typeof body.installCommand === 'string') patch.install_command = body.installCommand.trim().slice(0, 500);
  if (typeof body.repoUrl === 'string') patch.repo_url = body.repoUrl.trim() || null;
  if (typeof body.env === 'string') patch.env_vars = JSON.stringify(parseEnvText(body.env));
  if (!Object.keys(patch).length) return res.status(400).json({ error: 'Nothing to update' });
  const updated = await Project.findByIdAndUpdate(p._id, patch, { new: true }).lean();
  res.json({ project: serializeProject(updated) });
});

app.delete('/api/projects/:id', requireAuth, async (req, res) => {
  const p = await ownProject(req, res); if (!p) return;
  const pid = String(p._id);
  stopProject(pid);
  try { fs.rmSync(sourceDir(pid), { recursive: true, force: true }); } catch (e) {}
  await Project.findByIdAndDelete(p._id);
  await LogEntry.deleteOne({ project_id: pid });
  deleteFromB2(pid).catch(() => {});
  logBuffers.delete(pid);
  logSubscribers.delete(pid);
  res.json({ ok: true });
});

app.use('/api', (req, res) => res.status(404).json({ error: 'Not found' }));

/* ============================================================
 * DASHBOARD — premium zinc UI (unchanged)
 * ============================================================ */

const DASHBOARD_HTML = String.raw`<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>MiniDeploy — Deploy Node.js Apps</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link href="https://fonts.googleapis.com/css2?family=Manrope:wght@400;500;600;700;800&family=Inter:wght@300;400;500;600;700&family=JetBrains+Mono:wght@400;500;600&display=swap" rel="stylesheet">
<link rel="stylesheet" href="https://cdnjs.cloudflare.com/ajax/libs/font-awesome/6.5.1/css/all.min.css">
<style>
:root{
  --z50:#fafafa;  --z100:#f4f4f5; --z200:#e4e4e7; --z300:#d4d4d8;
  --z400:#a1a1aa; --z500:#71717a; --z600:#52525b; --z700:#3f3f46;
  --z800:#27272a; --z900:#18181b; --z950:#09090b;
  --bg:#0a0a0c; --surface:#111114; --raised:#17171b; --overlay:#1c1c21;
  --bd:rgba(255,255,255,.055); --bd-soft:rgba(255,255,255,.035); --bd-strong:rgba(255,255,255,.09);
  --tx:#fafafa; --tx-soft:#d4d4d8; --tx-mut:#8a8a93; --tx-dim:#5c5c66;
  --ok:#10b981; --ok-bg:rgba(16,185,129,.10); --ok-bd:rgba(16,185,129,.22);
  --wn:#f59e0b; --wn-bg:rgba(245,158,11,.10); --wn-bd:rgba(245,158,11,.22);
  --er:#ef4444; --er-bg:rgba(239,68,68,.10); --er-bd:rgba(239,68,68,.22);
  --in:#3b82f6; --in-bg:rgba(59,130,246,.10); --in-bd:rgba(59,130,246,.22);
  --display:'Manrope','Inter',system-ui,sans-serif;
  --body:'Inter',system-ui,sans-serif;
  --mono:'JetBrains Mono',ui-monospace,Menlo,Consolas,monospace;
  --sh-sm:0 1px 3px rgba(0,0,0,.4),0 1px 2px rgba(0,0,0,.3);
  --sh-md:0 4px 12px -2px rgba(0,0,0,.5),0 2px 4px -2px rgba(0,0,0,.4);
  --sh-lg:0 12px 24px -6px rgba(0,0,0,.55),0 4px 8px -4px rgba(0,0,0,.4);
  --sh-xl:0 24px 48px -12px rgba(0,0,0,.7),0 8px 16px -8px rgba(0,0,0,.5);
  --sh-2xl:0 48px 96px -24px rgba(0,0,0,.85);
  --sh-inset:inset 0 1px 0 rgba(255,255,255,.04);
  --r:10px; --r-sm:7px; --r-lg:14px;
}
*{box-sizing:border-box;margin:0;padding:0;}
html,body{background:var(--bg);color:var(--tx-soft);font-family:var(--body);
  font-size:14px;line-height:1.55;-webkit-font-smoothing:antialiased;min-height:100vh;}
body{background:
  radial-gradient(ellipse 80% 60% at 50% -20%, rgba(255,255,255,.035), transparent 60%),
  radial-gradient(ellipse 60% 40% at 100% 100%, rgba(59,130,246,.025), transparent 70%),
  var(--bg);background-attachment:fixed;}
a{color:var(--tx-soft);text-decoration:none;transition:color .15s;}
a:hover{color:var(--tx);}
button{font:inherit;cursor:pointer;border:0;background:none;color:inherit;}
input,textarea{font:inherit;}
.hidden{display:none!important;}
::selection{background:rgba(255,255,255,.15);color:var(--tx);}
::-webkit-scrollbar{width:8px;height:8px;}
::-webkit-scrollbar-track{background:transparent;}
::-webkit-scrollbar-thumb{background:var(--z800);border-radius:4px;border:2px solid var(--bg);}
::-webkit-scrollbar-thumb:hover{background:var(--z700);}
.topbar{position:sticky;top:0;z-index:50;height:64px;
  background:rgba(10,10,12,.72);backdrop-filter:saturate(180%) blur(20px);
  -webkit-backdrop-filter:saturate(180%) blur(20px);border-bottom:1px solid var(--bd);}
.topbar-in{max-width:1240px;margin:0 auto;height:100%;padding:0 32px;
  display:flex;align-items:center;justify-content:space-between;}
.logo{display:inline-flex;align-items:center;gap:11px;
  font-family:var(--display);font-weight:800;font-size:16px;
  letter-spacing:-.028em;color:var(--tx);}
.logo-mark{width:32px;height:32px;border-radius:9px;
  background:linear-gradient(145deg,#27272a 0%,#18181b 100%);
  border:1px solid var(--bd-strong);box-shadow:var(--sh-inset),var(--sh-sm);
  display:flex;align-items:center;justify-content:center;
  color:var(--tx);font-size:14px;position:relative;overflow:hidden;}
.logo-mark::after{content:'';position:absolute;inset:0;
  background:radial-gradient(circle at 30% 20%, rgba(255,255,255,.10), transparent 60%);
  pointer-events:none;}
.topbar-right{display:flex;align-items:center;gap:12px;font-size:13px;}
.user-chip{display:inline-flex;align-items:center;gap:9px;padding:5px 12px 5px 5px;
  background:var(--surface);border:1px solid var(--bd);border-radius:999px;
  color:var(--tx-mut);box-shadow:var(--sh-inset);transition:border-color .15s;}
.user-chip:hover{border-color:var(--bd-strong);}
.avatar{width:24px;height:24px;border-radius:50%;
  background:linear-gradient(135deg,#52525b,#27272a);color:var(--tx);
  display:flex;align-items:center;justify-content:center;
  font-size:10px;font-weight:700;letter-spacing:.02em;
  box-shadow:inset 0 0 0 1px rgba(255,255,255,.08);}
.btn{display:inline-flex;align-items:center;justify-content:center;gap:8px;
  height:36px;padding:0 16px;border-radius:var(--r-sm);
  font-family:var(--body);font-size:13px;font-weight:500;letter-spacing:-.005em;
  transition:all .15s cubic-bezier(.4,0,.2,1);white-space:nowrap;border:1px solid transparent;}
.btn i{font-size:12px;}
.btn-primary{background:linear-gradient(180deg,#ffffff 0%,#e4e4e7 100%);
  color:#09090b;border-color:rgba(255,255,255,.6);
  box-shadow:var(--sh-sm),var(--sh-inset);font-weight:600;}
.btn-primary:hover{background:linear-gradient(180deg,#ffffff 0%,#f4f4f5 100%);
  box-shadow:var(--sh-md),var(--sh-inset);transform:translateY(-1px);}
.btn-primary:active{transform:translateY(0);}
.btn-primary:disabled{opacity:.4;cursor:not-allowed;transform:none;box-shadow:var(--sh-sm);}
.btn-secondary{background:var(--surface);color:var(--tx-soft);
  border-color:var(--bd);box-shadow:var(--sh-inset);}
.btn-secondary:hover{background:var(--raised);border-color:var(--bd-strong);
  color:var(--tx);transform:translateY(-1px);box-shadow:var(--sh-sm),var(--sh-inset);}
.btn-ghost{background:transparent;color:var(--tx-mut);border-color:var(--bd);}
.btn-ghost:hover{background:var(--surface);color:var(--tx-soft);border-color:var(--bd-strong);}
.btn-danger{background:transparent;color:var(--er);border-color:var(--er-bd);}
.btn-danger:hover{background:var(--er-bg);border-color:var(--er);}
.btn.sm{height:30px;padding:0 11px;font-size:11.5px;border-radius:6px;}
.btn.sm i{font-size:10.5px;}
.btn.block{width:100%;height:42px;}
.container{max-width:1240px;margin:0 auto;padding:0 32px;}
.auth-wrap{min-height:100vh;display:flex;align-items:center;justify-content:center;padding:48px 24px;}
.auth-shell{width:100%;max-width:420px;}
.auth-brand{display:flex;align-items:center;justify-content:center;gap:14px;margin-bottom:28px;}
.auth-brand-icon{width:52px;height:52px;border-radius:14px;
  background:linear-gradient(145deg,#1f1f23 0%,#0f0f12 100%);
  border:1px solid var(--bd-strong);box-shadow:var(--sh-inset),var(--sh-lg);
  display:flex;align-items:center;justify-content:center;
  color:var(--tx);font-size:22px;position:relative;overflow:hidden;}
.auth-brand-icon::after{content:'';position:absolute;inset:0;
  background:radial-gradient(circle at 30% 20%, rgba(255,255,255,.14), transparent 55%);}
.auth-brand-text h1{font-family:var(--display);font-size:26px;font-weight:800;
  letter-spacing:-.032em;color:var(--tx);line-height:1;}
.auth-brand-text p{font-size:12.5px;color:var(--tx-mut);margin-top:5px;letter-spacing:-.005em;}
.auth-card{background:linear-gradient(180deg,var(--surface) 0%,#0e0e11 100%);
  border:1px solid var(--bd);border-radius:var(--r-lg);padding:8px;
  box-shadow:var(--sh-2xl),var(--sh-inset);}
.auth-tabs{display:grid;grid-template-columns:1fr 1fr;gap:4px;padding:4px;
  background:var(--bg);border:1px solid var(--bd);border-radius:var(--r);margin-bottom:20px;}
.auth-tabs button{height:34px;border-radius:6px;font-size:12.5px;font-weight:500;
  color:var(--tx-mut);transition:all .18s;}
.auth-tabs button:hover{color:var(--tx-soft);}
.auth-tabs button.active{background:var(--raised);color:var(--tx);box-shadow:var(--sh-sm),var(--sh-inset);}
.auth-form{padding:6px 20px 22px;}
.field{margin-bottom:16px;}
.field:last-of-type{margin-bottom:0;}
.field label{display:flex;align-items:center;gap:7px;font-size:11px;font-weight:600;
  letter-spacing:.06em;text-transform:uppercase;color:var(--tx-mut);margin-bottom:8px;}
.field label i{font-size:10px;color:var(--tx-dim);}
.input{width:100%;height:42px;padding:0 14px;background:var(--bg);color:var(--tx);
  border:1px solid var(--bd);border-radius:var(--r-sm);font-family:var(--body);
  font-size:13.5px;outline:none;transition:all .15s;box-shadow:inset 0 1px 2px rgba(0,0,0,.25);}
.input:focus{border-color:var(--z600);
  box-shadow:inset 0 1px 2px rgba(0,0,0,.25),0 0 0 3px rgba(255,255,255,.05);}
.input::placeholder{color:var(--tx-dim);}
textarea.input{height:auto;min-height:104px;padding:11px 14px;
  font-family:var(--mono);font-size:12.5px;line-height:1.7;resize:vertical;}
.fhint{display:flex;align-items:flex-start;gap:6px;font-size:11.5px;
  color:var(--tx-dim);margin-top:7px;letter-spacing:-.005em;line-height:1.5;}
.fhint i{font-size:10px;margin-top:3px;flex-shrink:0;}
.err{color:var(--er);font-size:12.5px;min-height:20px;margin-top:14px;
  display:flex;align-items:center;gap:7px;}
.err:empty{display:none;}
main{padding:52px 0 120px;}
.page-head{display:flex;align-items:flex-end;justify-content:space-between;gap:24px;margin-bottom:36px;}
.page-title{font-family:var(--display);font-size:34px;font-weight:800;
  letter-spacing:-.038em;line-height:1;color:var(--tx);margin-bottom:10px;}
.page-sub{font-size:13.5px;color:var(--tx-mut);letter-spacing:-.005em;}
.stats{display:grid;grid-template-columns:repeat(auto-fit,minmax(180px,1fr));
  gap:12px;margin-bottom:32px;}
.stat{padding:18px 20px;background:linear-gradient(180deg,var(--surface) 0%,#0e0e11 100%);
  border:1px solid var(--bd);border-radius:var(--r);display:flex;align-items:center;gap:14px;
  box-shadow:var(--sh-inset);transition:all .2s;}
.stat:hover{border-color:var(--bd-strong);box-shadow:var(--sh-md),var(--sh-inset);transform:translateY(-1px);}
.stat-icon{width:40px;height:40px;border-radius:9px;background:var(--raised);
  border:1px solid var(--bd);display:flex;align-items:center;justify-content:center;
  font-size:15px;color:var(--tx-mut);flex-shrink:0;box-shadow:var(--sh-inset);}
.stat-icon.ok{background:var(--ok-bg);border-color:var(--ok-bd);color:var(--ok);}
.stat-icon.wn{background:var(--wn-bg);border-color:var(--wn-bd);color:var(--wn);}
.stat-icon.er{background:var(--er-bg);border-color:var(--er-bd);color:var(--er);}
.stat-val{font-family:var(--display);font-size:22px;font-weight:800;
  letter-spacing:-.028em;line-height:1;color:var(--tx);}
.stat-lbl{font-size:10.5px;font-weight:600;letter-spacing:.09em;
  text-transform:uppercase;color:var(--tx-dim);margin-top:5px;}
.empty{padding:96px 32px;border:1px dashed var(--bd-strong);border-radius:var(--r-lg);
  background:linear-gradient(180deg,var(--surface) 0%,#0e0e11 100%);
  text-align:center;box-shadow:var(--sh-inset);}
.empty-icon{width:56px;height:56px;border-radius:14px;background:var(--raised);
  border:1px solid var(--bd);display:inline-flex;align-items:center;justify-content:center;
  font-size:22px;color:var(--tx-dim);margin-bottom:18px;box-shadow:var(--sh-inset);}
.empty h3{font-family:var(--display);font-size:17px;font-weight:700;
  letter-spacing:-.022em;color:var(--tx);margin-bottom:6px;}
.empty p{font-size:13px;color:var(--tx-mut);}
.grid{display:grid;grid-template-columns:repeat(auto-fill,minmax(360px,1fr));gap:16px;}
.card{padding:22px;background:linear-gradient(180deg,var(--surface) 0%,#0e0e11 100%);
  border:1px solid var(--bd);border-radius:var(--r);display:flex;flex-direction:column;gap:16px;
  transition:all .22s cubic-bezier(.4,0,.2,1);box-shadow:var(--sh-inset);
  position:relative;overflow:hidden;}
.card::before{content:'';position:absolute;top:0;left:0;right:0;height:1px;
  background:linear-gradient(90deg,transparent,rgba(255,255,255,.10),transparent);
  opacity:0;transition:opacity .3s;}
.card:hover{border-color:var(--bd-strong);transform:translateY(-2px);
  box-shadow:var(--sh-xl),var(--sh-inset);}
.card:hover::before{opacity:1;}
.card-head{display:flex;align-items:flex-start;justify-content:space-between;gap:12px;}
.card-title{display:flex;align-items:center;gap:11px;min-width:0;}
.card-title-icon{width:38px;height:38px;border-radius:9px;background:var(--raised);
  border:1px solid var(--bd);display:flex;align-items:center;justify-content:center;
  color:var(--tx-mut);font-size:14px;flex-shrink:0;box-shadow:var(--sh-inset);}
.card h3{font-family:var(--display);font-size:16px;font-weight:700;
  letter-spacing:-.02em;color:var(--tx);word-break:break-all;line-height:1.25;}
.urls{display:flex;flex-direction:column;gap:5px;}
.url{font-family:var(--mono);font-size:11px;color:var(--tx-dim);
  display:flex;align-items:center;gap:7px;word-break:break-all;padding:5px 0;
  border-bottom:1px solid var(--bd-soft);}
.url:last-child{border-bottom:0;}
.url i{font-size:9.5px;color:var(--tx-dim);flex-shrink:0;width:12px;text-align:center;}
.url a{color:var(--tx-mut);}
.url a:hover{color:var(--tx);}
.badge{display:inline-flex;align-items:center;gap:6px;padding:4px 10px;border-radius:100px;
  font-size:10px;font-weight:700;letter-spacing:.09em;text-transform:uppercase;
  border:1px solid;white-space:nowrap;flex-shrink:0;font-family:var(--body);}
.badge-dot{width:5px;height:5px;border-radius:50% !important;background:currentColor;
  box-shadow:0 0 6px currentColor;}
.badge.running{color:var(--ok);border-color:var(--ok-bd);background:var(--ok-bg);}
.badge.running .badge-dot{animation:pulse 1.6s ease-in-out infinite;}
.badge.stopped{color:var(--tx-mut);border-color:var(--bd);background:var(--surface);}
.badge.stopped .badge-dot{box-shadow:none;}
.badge.starting,.badge.building{color:var(--wn);border-color:var(--wn-bd);background:var(--wn-bg);}
.badge.starting .badge-dot,.badge.building .badge-dot{animation:pulse 1.1s ease-in-out infinite;}
.badge.failed{color:var(--er);border-color:var(--er-bd);background:var(--er-bg);}
.badge.failed .badge-dot{box-shadow:none;}
.badge.created{color:var(--in);border-color:var(--in-bd);background:var(--in-bg);}
.badge.created .badge-dot{box-shadow:none;}
@keyframes pulse{0%,100%{opacity:1}50%{opacity:.4}}
.card-actions{display:flex;flex-wrap:wrap;gap:6px;margin-top:auto;padding-top:2px;}
.card-actions .btn{flex:1;min-width:0;}
dialog{border:1px solid var(--bd-strong);border-radius:var(--r-lg);
  background:linear-gradient(180deg,var(--surface) 0%,#0d0d10 100%);
  color:var(--tx-soft);padding:0;max-width:560px;width:calc(100% - 40px);
  box-shadow:var(--sh-2xl),var(--sh-inset);overflow:hidden;}
dialog::backdrop{background:rgba(5,5,7,.75);backdrop-filter:blur(6px);
  -webkit-backdrop-filter:blur(6px);}
.dlg-head{padding:24px 28px 20px;border-bottom:1px solid var(--bd);
  display:flex;align-items:center;gap:14px;}
.dlg-icon{width:42px;height:42px;border-radius:11px;
  background:linear-gradient(145deg,#27272a,#0f0f12);
  border:1px solid var(--bd-strong);display:flex;align-items:center;justify-content:center;
  color:var(--tx);font-size:16px;flex-shrink:0;box-shadow:var(--sh-inset);}
.dlg-title{font-family:var(--display);font-size:19px;font-weight:800;
  letter-spacing:-.026em;line-height:1.15;color:var(--tx);}
.dlg-sub{font-size:12.5px;color:var(--tx-mut);margin-top:3px;}
.dlg-sub code{font-family:var(--mono);font-size:11.5px;padding:2px 6px;border-radius:4px;
  background:var(--raised);border:1px solid var(--bd);color:var(--tx-soft);}
.dlg-body{padding:22px 28px;max-height:60vh;overflow-y:auto;}
.dlg-foot{padding:16px 28px;border-top:1px solid var(--bd);background:var(--bg);
  display:flex;align-items:center;justify-content:space-between;gap:12px;}
.dlg-foot .err{flex:1;margin:0;}
.dlg-foot .actions{display:flex;gap:8px;}
.toast{position:fixed;bottom:24px;right:24px;padding:14px 18px 14px 14px;
  background:linear-gradient(180deg,var(--overlay) 0%,var(--surface) 100%);
  border:1px solid var(--bd-strong);border-radius:var(--r);
  box-shadow:var(--sh-2xl),var(--sh-inset);color:var(--tx-soft);font-size:13px;
  display:flex;align-items:center;gap:12px;z-index:400;max-width:400px;
  animation:slideUp .25s cubic-bezier(.4,0,.2,1);}
@keyframes slideUp{from{opacity:0;transform:translateY(12px)}to{opacity:1;transform:translateY(0)}}
.toast-icon{width:32px;height:32px;border-radius:8px;display:flex;
  align-items:center;justify-content:center;flex-shrink:0;font-size:13px;}
.toast-icon.ok{background:var(--ok-bg);color:var(--ok);border:1px solid var(--ok-bd);}
.toast-icon.err{background:var(--er-bg);color:var(--er);border:1px solid var(--er-bd);}
.terminal{position:fixed;left:0;right:0;bottom:0;height:60vh;background:#050507;
  border-top:1px solid var(--bd-strong);display:flex;flex-direction:column;
  transform:translateY(110%);transition:transform .32s cubic-bezier(.4,0,.2,1);
  z-index:200;box-shadow:0 -32px 64px -20px rgba(0,0,0,.85);}
.terminal.open{transform:translateY(0);}
.term-head{display:flex;align-items:center;gap:14px;padding:12px 18px;
  background:linear-gradient(180deg,#0b0b0e 0%,#08080a 100%);
  border-bottom:1px solid var(--bd);font-family:var(--mono);font-size:12px;}
.term-dots{display:flex;gap:8px;}
.term-dots span{width:12px;height:12px;border-radius:50%;display:inline-block;}
.term-dots .d1{background:#ff5f57;box-shadow:inset 0 0 0 1px rgba(0,0,0,.3);}
.term-dots .d2{background:#febc2e;box-shadow:inset 0 0 0 1px rgba(0,0,0,.3);}
.term-dots .d3{background:#28c840;box-shadow:inset 0 0 0 1px rgba(0,0,0,.3);}
.term-title{flex:1;display:flex;align-items:center;justify-content:center;gap:8px;
  color:var(--tx-mut);font-family:var(--mono);font-size:11.5px;
  overflow:hidden;text-overflow:ellipsis;white-space:nowrap;}
.term-title i{color:var(--tx-dim);font-size:10px;}
.term-actions{display:flex;align-items:center;gap:14px;font-size:11.5px;color:var(--tx-mut);}
.term-live{display:inline-flex;align-items:center;gap:6px;
  font-family:var(--mono);font-size:9.5px;font-weight:600;
  letter-spacing:.11em;text-transform:uppercase;color:var(--ok);}
.term-live-dot{width:6px;height:6px;border-radius:50%;background:currentColor;
  box-shadow:0 0 8px currentColor;animation:pulse 1.5s ease-in-out infinite;}
.term-live.paused{color:var(--tx-dim);}
.term-live.paused .term-live-dot{box-shadow:none;animation:none;}
.term-follow{display:inline-flex;align-items:center;gap:6px;cursor:pointer;
  user-select:none;color:var(--tx-mut);font-family:var(--mono);font-size:11px;}
.term-follow input{width:auto;accent-color:var(--z500);cursor:pointer;transform:scale(.9);}
.term-close{display:inline-flex;align-items:center;gap:5px;padding:4px 11px;
  background:var(--surface);border:1px solid var(--bd);border-radius:6px;
  color:var(--tx-mut);font-family:var(--mono);font-size:10.5px;
  letter-spacing:.05em;text-transform:uppercase;transition:all .15s;}
.term-close:hover{color:var(--tx);border-color:var(--bd-strong);background:var(--raised);}
.term-body{flex:1;margin:0;padding:18px 22px 32px;overflow-y:auto;
  font-family:var(--mono);font-size:12.5px;line-height:1.65;
  white-space:pre-wrap;word-break:break-word;background:#050507;color:var(--tx-soft);}
.term-body::-webkit-scrollbar-thumb{background:#1c1c21;border-color:#050507;}
.log-line{display:block;min-height:1em;}
.log-line.partial::after{content:'▋';margin-left:2px;color:var(--tx-dim);
  animation:blink 1s steps(2,start) infinite;}
@keyframes blink{to{opacity:0}}
.log-cmd{color:#86efac;}
.log-err{color:#fca5a5;}
.log-sys{color:var(--tx-mut);}
.log-ok{color:#93c5fd;}
.log-info{color:#fde68a;}
.log-out{color:var(--tx-soft);}
@media(max-width:640px){
  .topbar-in,.container{padding:0 20px;}
  .page-head{flex-direction:column;align-items:stretch;gap:16px;}
  .page-title{font-size:26px;}
  .grid{grid-template-columns:1fr;}
  .stats{grid-template-columns:1fr 1fr;}
  .card-actions .btn{flex:0 1 auto;min-width:auto;}
  .auth-wrap{padding:24px 16px;}
  .toast{left:16px;right:16px;bottom:16px;max-width:none;}
}
</style>
</head>
<body>

<header class="topbar hidden" id="topbar">
  <div class="topbar-in">
    <div class="logo">
      <span class="logo-mark"><i class="fa-solid fa-rocket"></i></span>
      <span>MiniDeploy</span>
    </div>
    <div class="topbar-right">
      <div class="user-chip">
        <div class="avatar" id="userAv">U</div>
        <span id="userEmail">user@example.com</span>
      </div>
      <button class="btn btn-ghost sm" id="logoutBtn" type="button">
        <i class="fa-solid fa-arrow-right-from-bracket"></i>Log out
      </button>
    </div>
  </div>
</header>

<section id="authView" class="auth-wrap">
  <div class="auth-shell">
    <div class="auth-brand">
      <div class="auth-brand-icon"><i class="fa-solid fa-rocket"></i></div>
      <div class="auth-brand-text">
        <h1>MiniDeploy</h1>
        <p>Ship Node.js apps to their own subdomain</p>
      </div>
    </div>
    <div class="auth-card">
      <div class="auth-tabs">
        <button id="tabLogin" class="active" type="button">Log in</button>
        <button id="tabSignup" type="button">Sign up</button>
      </div>
      <form id="authForm" class="auth-form">
        <div class="field">
          <label for="email"><i class="fa-solid fa-envelope"></i>Email address</label>
          <input id="email" class="input" type="email" autocomplete="email" required placeholder="you@example.com">
        </div>
        <div class="field">
          <label for="password"><i class="fa-solid fa-lock"></i>Password</label>
          <input id="password" class="input" type="password" autocomplete="current-password" required placeholder="At least 8 characters" minlength="8">
        </div>
        <button type="submit" id="authSubmit" class="btn btn-primary block" style="margin-top:22px;">
          <i class="fa-solid fa-arrow-right-to-bracket"></i><span id="authSubmitText">Log in</span>
        </button>
        <div class="err" id="authErr"></div>
      </form>
    </div>
  </div>
</section>

<main class="container hidden" id="dashView">
  <div class="page-head">
    <div>
      <h1 class="page-title">Projects</h1>
      <p class="page-sub">Deploy, manage, and monitor your applications.</p>
    </div>
    <button id="newProjectBtn" class="btn btn-primary" type="button">
      <i class="fa-solid fa-plus"></i>New project
    </button>
  </div>
  <div class="stats" id="statsRow"></div>
  <div id="projects"></div>
</main>

<dialog id="newDialog">
  <div class="dlg-head">
    <div class="dlg-icon"><i class="fa-solid fa-cube"></i></div>
    <div>
      <div class="dlg-title">New project</div>
      <div class="dlg-sub">Preview at <code id="newHint">/preview/myapp/</code></div>
    </div>
  </div>
  <form id="newForm">
    <div class="dlg-body">
      <div class="field">
        <label for="pName"><i class="fa-solid fa-tag"></i>Project name</label>
        <input id="pName" class="input" required placeholder="myapp" pattern="[a-z0-9](?:[a-z0-9-]{0,30}[a-z0-9])?">
        <div class="fhint"><i class="fa-solid fa-circle-info"></i>Lowercase, numbers, dashes. Becomes the subdomain.</div>
      </div>
      <div class="field">
        <label for="pRepo"><i class="fa-brands fa-github"></i>Git repository URL</label>
        <input id="pRepo" class="input" placeholder="https://github.com/user/repo.git">
        <div class="fhint"><i class="fa-solid fa-circle-info"></i>Leave blank to deploy a placeholder app.</div>
      </div>
      <div class="field">
        <label for="pInstall"><i class="fa-solid fa-download"></i>Install command</label>
        <input id="pInstall" class="input" value="npm install">
      </div>
      <div class="field">
        <label for="pStart"><i class="fa-solid fa-play"></i>Start command</label>
        <input id="pStart" class="input" value="npm start" required>
      </div>
      <div class="field">
        <label for="pEnv"><i class="fa-solid fa-sliders"></i>Environment variables</label>
        <textarea id="pEnv" class="input" rows="5" spellcheck="false" placeholder="NODE_ENV=production&#10;DATABASE_URL=postgres://localhost/db"></textarea>
        <div class="fhint"><i class="fa-solid fa-circle-info"></i>KEY=value, one per line.</div>
      </div>
    </div>
    <div class="dlg-foot">
      <div class="err" id="newErr"></div>
      <div class="actions">
        <button type="button" class="btn btn-ghost" id="newCancel">Cancel</button>
        <button type="submit" class="btn btn-primary" id="newSubmit">
          <i class="fa-solid fa-rocket"></i>Create &amp; deploy
        </button>
      </div>
    </div>
  </form>
</dialog>

<div class="terminal" id="terminal">
  <div class="term-head">
    <div class="term-dots"><span class="d1"></span><span class="d2"></span><span class="d3"></span></div>
    <div class="term-title"><i class="fa-solid fa-terminal"></i><span id="termTitle">logs</span></div>
    <div class="term-actions">
      <span class="term-live" id="termLive"><span class="term-live-dot"></span>Live</span>
      <label class="term-follow" title="Follow output">
        <input type="checkbox" id="autoScroll" checked><span>Follow</span>
      </label>
      <button class="term-close" id="termClose" type="button"><i class="fa-solid fa-xmark"></i>Close</button>
    </div>
  </div>
  <pre class="term-body" id="termBody"></pre>
</div>

<script>
(function(){
'use strict';

var HOST=location.hostname+(location.port?':'+location.port:'');
var BD=location.hostname;
function $(id){return document.getElementById(id);}
function show(el,on){if(el)el.classList.toggle('hidden',!on);}
function esc(s){return String(s==null?'':s).replace(/[&<>"']/g,function(c){
  return{'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c];});}

var toastTimer=null;
function toast(msg,isErr){
  var old=document.querySelector('.toast');
  if(old&&old.parentNode)old.parentNode.removeChild(old);
  var el=document.createElement('div');
  el.className='toast';
  el.innerHTML=
    '<div class="toast-icon '+(isErr?'err':'ok')+'">'+
      '<i class="fa-solid '+(isErr?'fa-circle-exclamation':'fa-circle-check')+'"></i>'+
    '</div>'+
    '<div>'+esc(msg)+'</div>';
  document.body.appendChild(el);
  clearTimeout(toastTimer);
  toastTimer=setTimeout(function(){if(el.parentNode)el.parentNode.removeChild(el);},3800);
}

function api(url,opts){
  opts=opts||{};
  opts.headers=Object.assign({'Content-Type':'application/json'},opts.headers||{});
  opts.credentials='same-origin';
  if(opts.body&&typeof opts.body!=='string')opts.body=JSON.stringify(opts.body);
  return fetch(url,opts).then(function(res){
    return res.json().catch(function(){return null;}).then(function(data){
      if(!res.ok)throw new Error((data&&data.error)||('Error '+res.status));
      return data;
    });
  });
}

var user=null,authMode='login',projects=[],pollTimer=null;
var currentProjectId=null,eventSource=null,partialLine='';
var terminalEl=$('terminal'),termBody=$('termBody'),termTitle=$('termTitle');
var termLive=$('termLive'),autoScroll=$('autoScroll');

function setAuthMode(mode){
  authMode=mode;var isL=mode==='login';
  $('tabLogin').classList.toggle('active',isL);
  $('tabSignup').classList.toggle('active',!isL);
  $('authSubmitText').textContent=isL?'Log in':'Create account';
  $('password').autocomplete=isL?'current-password':'new-password';
  $('authErr').textContent='';
}
$('tabLogin').onclick=function(){setAuthMode('login');};
$('tabSignup').onclick=function(){setAuthMode('signup');};

$('authForm').onsubmit=function(e){
  e.preventDefault();
  var errEl=$('authErr');errEl.textContent='';
  var btn=$('authSubmit');btn.disabled=true;
  var path=authMode==='login'?'/api/auth/login':'/api/auth/signup';
  api(path,{method:'POST',body:{email:$('email').value,password:$('password').value}})
  .then(function(data){
    user=data.user;$('email').value='';$('password').value='';
    renderAuth();return loadProjects();
  }).catch(function(err){errEl.textContent=err.message;})
  .then(function(){btn.disabled=false;});
};

$('logoutBtn').onclick=function(){
  api('/api/auth/logout',{method:'POST'}).catch(function(){}).then(function(){
    user=null;projects=[];closeTerminal();renderAuth();
  });
};

function renderAuth(){
  show($('topbar'),!!user);show($('dashView'),!!user);show($('authView'),!user);
  if(user){$('userEmail').textContent=user.email;$('userAv').textContent=user.email.charAt(0).toUpperCase();}
}

function loadProjects(){
  if(!user)return Promise.resolve();
  return api('/api/projects').then(function(data){
    projects=data.projects||[];renderStats();renderProjects();
  }).catch(function(err){
    if(/not authenticated/i.test(err.message)){user=null;renderAuth();}
    else console.error(err);
  });
}

function pUrl(n){return location.protocol+'//'+HOST+'/preview/'+n+'/';}
function sUrl(n){return location.protocol+'//'+n+'.'+BD+(location.port?':'+location.port:'');}

function renderStats(){
  var t=projects.length,r=0,b=0,f=0;
  for(var i=0;i<projects.length;i++){
    if(projects[i].status==='running')r++;
    if(projects[i].status==='building'||projects[i].status==='starting')b++;
    if(projects[i].status==='failed')f++;
  }
  var root=$('statsRow');
  if(!t){root.innerHTML='';return;}
  root.innerHTML=
    '<div class="stat">'+
      '<div class="stat-icon"><i class="fa-solid fa-cubes"></i></div>'+
      '<div><div class="stat-val">'+t+'</div><div class="stat-lbl">Total</div></div>'+
    '</div>'+
    '<div class="stat">'+
      '<div class="stat-icon ok"><i class="fa-solid fa-circle-play"></i></div>'+
      '<div><div class="stat-val">'+r+'</div><div class="stat-lbl">Running</div></div>'+
    '</div>'+
    '<div class="stat">'+
      '<div class="stat-icon wn"><i class="fa-solid fa-spinner"></i></div>'+
      '<div><div class="stat-val">'+b+'</div><div class="stat-lbl">Building</div></div>'+
    '</div>'+
    '<div class="stat">'+
      '<div class="stat-icon er"><i class="fa-solid fa-triangle-exclamation"></i></div>'+
      '<div><div class="stat-val">'+f+'</div><div class="stat-lbl">Failed</div></div>'+
    '</div>';
}

function renderProjects(){
  var root=$('projects');
  if(!projects.length){
    root.className='';
    root.innerHTML=
      '<div class="empty">'+
        '<div class="empty-icon"><i class="fa-solid fa-inbox"></i></div>'+
        '<h3>No projects yet</h3>'+
        '<p>Click <strong style="color:var(--tx-soft);font-weight:600;">New project</strong> to deploy your first app.</p>'+
      '</div>';
    return;
  }
  root.className='grid';
  var html='';
  for(var i=0;i<projects.length;i++){
    var p=projects[i],isR=p.status==='running';
    html+=
      '<div class="card" data-id="'+esc(p.id)+'">'+
        '<div class="card-head">'+
          '<div class="card-title">'+
            '<div class="card-title-icon"><i class="fa-solid fa-cube"></i></div>'+
            '<h3>'+esc(p.name)+'</h3>'+
          '</div>'+
          '<span class="badge '+esc(p.status)+'"><span class="badge-dot"></span>'+esc(p.status)+'</span>'+
        '</div>'+
        '<div class="urls">'+
          '<div class="url"><i class="fa-solid fa-link"></i><a href="'+esc(pUrl(p.name))+'" target="_blank">'+esc(pUrl(p.name))+'</a></div>'+
          '<div class="url"><i class="fa-solid fa-globe"></i><a href="'+esc(sUrl(p.name))+'" target="_blank">'+esc(sUrl(p.name))+'</a></div>'+
        '</div>'+
        '<div class="card-actions">'+
          '<button class="btn btn-secondary sm" data-act="deploy"><i class="fa-solid fa-rocket"></i>Deploy</button>'+
          (isR
            ?'<button class="btn btn-ghost sm" data-act="stop"><i class="fa-solid fa-stop"></i>Stop</button>'
            :'<button class="btn btn-ghost sm" data-act="restart"><i class="fa-solid fa-play"></i>Start</button>')+
          '<button class="btn btn-ghost sm" data-act="logs"><i class="fa-solid fa-terminal"></i>Logs</button>'+
          '<button class="btn btn-danger sm" data-act="delete"><i class="fa-solid fa-trash"></i></button>'+
        '</div>'+
      '</div>';
  }
  root.innerHTML=html;
}

$('projects').addEventListener('click',function(e){
  var btn=e.target.closest('button[data-act]');
  if(!btn)return;
  var card=btn.closest('.card'),id=card.getAttribute('data-id');
  var act=btn.getAttribute('data-act'),proj=null;
  for(var i=0;i<projects.length;i++){if(projects[i].id===id){proj=projects[i];break;}}
  if(!proj)return;

  if(act==='deploy'){
    api('/api/projects/'+id+'/deploy',{method:'POST'})
    .then(function(){toast('Deploy started');openTerminal(id,proj.name);loadProjects();})
    .catch(function(err){toast(err.message,true);});
  } else if(act==='restart'){
    api('/api/projects/'+id+'/restart',{method:'POST'})
    .then(function(){toast('Starting');openTerminal(id,proj.name);loadProjects();})
    .catch(function(err){toast(err.message,true);});
  } else if(act==='stop'){
    api('/api/projects/'+id+'/stop',{method:'POST'})
    .then(function(){toast('Stopped');loadProjects();})
    .catch(function(err){toast(err.message,true);});
  } else if(act==='delete'){
    if(!confirm('Delete this project permanently?'))return;
    if(currentProjectId===id)closeTerminal();
    api('/api/projects/'+id,{method:'DELETE'})
    .then(function(){toast('Deleted');loadProjects();})
    .catch(function(err){toast(err.message,true);});
  } else if(act==='logs'){
    if(currentProjectId===id&&terminalEl.classList.contains('open'))closeTerminal();
    else openTerminal(id,proj.name);
  }
});

function stripAnsi(s){return s.replace(/\x1b\[[0-9;]*m/g,'');}
function classLine(l){
  var t=l.replace(/^\s+/,'');
  if(t.charAt(0)==='$')return'log-cmd';
  if(t.indexOf('[bdeploy]')===0)return'log-sys';
  if(/^error|^ERR!|failed|exception|throw /i.test(t))return'log-err';
  if(/listening|ready on|live|started on|server running/i.test(t))return'log-ok';
  if(/^warn|deprecated/i.test(t))return'log-info';
  return'log-out';
}

function feedTerm(raw){
  var chunk=stripAnsi(raw);
  partialLine+=chunk;
  var lines=partialLine.split('\n');
  partialLine=lines.pop();
  var old=termBody.querySelector('.log-line.partial');
  if(old&&old.parentNode)old.parentNode.removeChild(old);
  var frag=document.createDocumentFragment();
  for(var i=0;i<lines.length;i++){
    var div=document.createElement('div');
    div.className='log-line '+classLine(lines[i]);
    div.textContent=lines[i]||'\u00a0';
    frag.appendChild(div);
  }
  if(partialLine){
    var d2=document.createElement('div');
    d2.className='log-line partial '+classLine(partialLine);
    d2.textContent=partialLine;
    frag.appendChild(d2);
  }
  termBody.appendChild(frag);
  while(termBody.childNodes.length>4000)termBody.removeChild(termBody.firstChild);
  if(autoScroll.checked)termBody.scrollTop=termBody.scrollHeight;
}

function openTerminal(pid,pname){
  closeTerminal();
  currentProjectId=pid;partialLine='';termBody.innerHTML='';
  termTitle.textContent=pname+' \u2014 logs';
  terminalEl.classList.add('open');
  termLive.classList.remove('paused');
  termLive.innerHTML='<span class="term-live-dot"></span>Live';
  eventSource=new EventSource('/api/projects/'+pid+'/logs/stream',{withCredentials:true});
  eventSource.onmessage=function(e){
    if(currentProjectId!==pid)return;
    var d;try{d=JSON.parse(e.data);}catch(err){return;}
    if(d.reset){termBody.innerHTML='';partialLine='';if(d.chunk)feedTerm(d.chunk);}
    else if(d.chunk)feedTerm(d.chunk);
  };
  eventSource.onopen=function(){termLive.classList.remove('paused');termLive.innerHTML='<span class="term-live-dot"></span>Live';};
  eventSource.onerror=function(){termLive.classList.add('paused');termLive.innerHTML='<span class="term-live-dot"></span>Reconnecting';};
}

function closeTerminal(){
  terminalEl.classList.remove('open');
  if(eventSource){eventSource.close();eventSource=null;}
  currentProjectId=null;
}
$('termClose').onclick=closeTerminal;
termBody.addEventListener('scroll',function(){
  autoScroll.checked=termBody.scrollHeight-termBody.scrollTop-termBody.clientHeight<40;
});
document.addEventListener('keydown',function(e){
  if(e.key==='Escape'&&terminalEl.classList.contains('open'))closeTerminal();
});

$('newProjectBtn').onclick=function(){
  $('newHint').textContent='/preview/myapp/';$('newErr').textContent='';$('newDialog').showModal();
};
$('newCancel').onclick=function(){$('newDialog').close();};
$('newDialog').addEventListener('click',function(e){if(e.target===$('newDialog'))$('newDialog').close();});
$('pName').addEventListener('input',function(){
  $('newHint').textContent='/preview/'+(($('pName').value.trim().toLowerCase())||'myapp')+'/';
});

$('newForm').onsubmit=function(e){
  e.preventDefault();
  var errEl=$('newErr');errEl.textContent='';
  var btn=$('newSubmit');btn.disabled=true;
  api('/api/projects',{method:'POST',body:{
    name:$('pName').value.trim().toLowerCase(),
    repoUrl:$('pRepo').value.trim(),
    installCommand:$('pInstall').value.trim(),
    startCommand:$('pStart').value.trim(),
    env:$('pEnv').value
  }}).then(function(c){
    $('newDialog').close();
    var nm=c&&c.project?c.project.name:'project';
    var id=c&&c.project?c.project.id:null;
    $('newForm').reset();$('pInstall').value='npm install';$('pStart').value='npm start';
    toast('Project created — deploying');
    return loadProjects().then(function(){if(id)openTerminal(id,nm);});
  }).catch(function(err){errEl.textContent=err.message;})
  .then(function(){btn.disabled=false;});
};

setAuthMode('login');
api('/api/auth/me').then(function(d){user=d.user;}).catch(function(){}).then(function(){
  renderAuth();if(user)return loadProjects();
}).then(function(){
  pollTimer=setInterval(function(){
    if(user&&document.visibilityState==='visible')loadProjects();
  },5000);
});
})();
</script>
</body>
</html>`;

app.get('/', (req, res) => res.type('html').send(DASHBOARD_HTML));

/* ============================================================
 * Proxy
 * ============================================================ */

const proxy = httpProxy.createProxyServer({ xfwd: true, ws: true });
proxy.on('error', (err, req, res) => {
  console.error('[proxy]', err.message);
  if (!res) return;
  if (typeof res.writeHead === 'function' && !res.headersSent)
    res.writeHead(502, { 'Content-Type': 'text/plain; charset=utf-8' });
  if (typeof res.end === 'function') res.end('502 Bad Gateway');
});

app.use('/preview/:name', async (req, res) => {
  const name = String(req.params.name || '').toLowerCase();
  const project = await Project.findOne({ name });
  if (!project) return res.status(404).send('No project "' + name + '"');
  const rt = running.get(String(project._id));
  if (!rt) return res.status(503).send('"' + name + '" not running (' + project.status + ')');
  req.url = req.originalUrl.replace(/^\/preview\/[^/]+/, '') || '/';
  proxy.web(req, res, { target: 'http://127.0.0.1:' + rt.port });
});

app.use((req, res) => {
  res.status(404).type('html').send(
    '<!doctype html><meta charset="utf-8"><title>404</title>' +
    '<body style="font-family:system-ui;background:#09090b;color:#a1a1aa;padding:60px;text-align:center;">' +
    '<h1 style="font-size:64px;color:#e4e4e7;margin:0;">404</h1>' +
    '<p>Nothing here.</p>' +
    '<p><a href="/" style="color:#d4d4d8;">Back to dashboard</a></p></body>'
  );
});

// Central error handler — must be last
app.use((err, req, res, next) => {
  console.error('[express]', err);
  if (res.headersSent) return next(err);
  res.status(500).json({ error: 'Internal server error' });
});

function getSubdomain(hostHeader) {
  if (!hostHeader) return null;
  const host = hostHeader.split(':')[0].toLowerCase();
  if (host === BASE_DOMAIN || host === 'www.' + BASE_DOMAIN) return null;
  if (host.endsWith('.' + BASE_DOMAIN)) return host.slice(0, -(BASE_DOMAIN.length + 1));
  return null;
}

function sendPlain(res, status, msg) {
  res.writeHead(status, { 'Content-Type': 'text/plain; charset=utf-8' });
  res.end(msg);
}

const server = http.createServer(async (req, res) => {
  try {
    const sub = getSubdomain(req.headers.host);
    if (!sub) return app(req, res);
    const project = await Project.findOne({ name: sub });
    if (!project) return sendPlain(res, 404, '404 - no app "' + sub + '"');
    const rt = running.get(String(project._id));
    if (!rt) return sendPlain(res, 503, '503 - "' + sub + '" not running (' + project.status + ')');
    proxy.web(req, res, { target: 'http://127.0.0.1:' + rt.port });
  } catch (err) {
    console.error('[server]', err);
    sendPlain(res, 500, '500 - internal error');
  }
});

server.on('upgrade', async (req, socket, head) => {
  try {
    const sub = getSubdomain(req.headers.host);
    if (!sub) return socket.destroy();
    const project = await Project.findOne({ name: sub });
    const rt = project && running.get(String(project._id));
    if (!rt) return socket.destroy();
    proxy.ws(req, socket, head, { target: 'ws://127.0.0.1:' + rt.port });
  } catch (e) { socket.destroy(); }
});

/* ============================================================
 * Boot
 * ============================================================ */

async function connectMongo(retries) {
  retries = retries == null ? 5 : retries;
  for (let attempt = 1; attempt <= retries; attempt++) {
    try {
      console.log('  MongoDB    …  connecting (attempt ' + attempt + '/' + retries + ')');
      await mongoose.connect(MONGO_URI, {
        serverSelectionTimeoutMS: 30000,
        socketTimeoutMS: 45000,
        connectTimeoutMS: 30000,
        family: 4,
        maxPoolSize: 5,
      });
      console.log('  MongoDB    ✓  connected');
      return;
    } catch (err) {
      console.error('  MongoDB    ✗  attempt ' + attempt + ' failed:', err.message);
      if (attempt === retries) throw err;
      const wait = 3000 * attempt;
      console.log('  retrying in ' + (wait / 1000) + 's…');
      await new Promise((r) => setTimeout(r, wait));
    }
  }
}

async function boot() {
  console.log('');
  console.log('  MiniDeploy — booting');
  console.log('  ──────────────────────────────────────────');

  // Security posture checks
  if (INVITE_ONLY) {
    console.log('  Invite     ✓  ' + ALLOWED_EMAILS.length + ' email(s) allowed');
  } else {
    console.log('  Invite     ⚠  OPEN SIGNUP — anyone can register');
    console.log('             Set ALLOWED_EMAILS to restrict');
  }

  if (process.platform !== 'win32' && process.getuid && process.getuid() === 0) {
    console.warn('  Runtime    ⚠  running as root — deployed apps will too');
  }

  try {
    const host = MONGO_URI.replace(/^mongodb(\+srv)?:\/\//, '').split('@').pop().split('/')[0].split('?')[0];
    console.log('  resolving  ' + host + ' …');
    const addrs = await dns.promises.resolveSrv('_mongodb._tcp.' + host).catch(() => null);
    if (addrs && addrs.length) console.log('  SRV        ✓  ' + addrs.length + ' target(s) resolved');
    else console.log('  SRV        ·  no SRV records (will try direct host)');
  } catch (e) { console.log('  DNS probe skipped:', e.message); }

  await connectMongo(5);

  try {
    await s3.send(new HeadObjectCommand({ Bucket: B2_BUCKET_NAME, Key: B2_FOLDER + '/.keep' }));
  } catch (e) {
    if (e.$metadata?.httpStatusCode === 404) {}
    else if (e.name === 'NotFound' || e.Code === 'NotFound') {}
    else console.warn('  B2         ⚠  ' + e.message);
  }
  console.log('  B2 bucket  ✓  ' + B2_BUCKET_NAME);

  server.listen(PORT, () => {
    console.log('');
    console.log('  MiniDeploy running');
    console.log('  ──────────────────────────────────────────');
    console.log('  Dashboard :  http://' + BASE_DOMAIN + (PORT === 80 ? '' : ':' + PORT));
    console.log('  Health    :  http://' + BASE_DOMAIN + (PORT === 80 ? '' : ':' + PORT) + '/health');
    console.log('  Preview   :  http://' + BASE_DOMAIN + (PORT === 80 ? '' : ':' + PORT) + '/preview/<name>/');
    console.log('  Subdomain :  http://<name>.' + BASE_DOMAIN + (PORT === 80 ? '' : ':' + PORT));
    console.log('  App ports :  ' + APP_PORT_START + ' – ' + APP_PORT_END);
    console.log('  Temp dir  :  ' + TEMP_ROOT);
    console.log('');

    setTimeout(() => autoStartProjects().catch((err) => console.error('[boot]', err)), 2000);
  });
}

boot().catch((err) => {
  console.error('');
  console.error('  FATAL: boot failed');
  console.error('  ' + err.message);
  console.error('');
  console.error('  Common causes:');
  console.error('    1. MongoDB Atlas IP allowlist — add 0.0.0.0/0 (or Render IPs)');
  console.error('    2. Wrong password in MONGO_URI');
  console.error('    3. Database user has no access to the "node" database');
  console.error('');
  process.exit(1);
});

/* ============================================================
 * Shutdown
 * ============================================================ */

let shuttingDown = false;
function shutdown(signal) {
  if (shuttingDown) return;
  shuttingDown = true;
  console.log('\n' + signal + ': shutting down gracefully…');

  for (const [id] of running) {
    try { stopProject(id, { silent: true }); } catch (e) {}
  }

  for (const [pid, buf] of logBuffers) {
    LogEntry.findOneAndUpdate(
      { project_id: pid },
      { content: buf },
      { upsert: true }
    ).catch(() => {});
  }

  mongoose.disconnect().catch(() => {});
  server.close(() => process.exit(0));
  setTimeout(() => process.exit(0), 8000).unref();
}

process.on('SIGINT', () => shutdown('SIGINT'));
process.on('SIGTERM', () => shutdown('SIGTERM'));
process.on('unhandledRejection', (err) => console.error('[unhandled]', err));
process.on('uncaughtException', (err) => {
  console.error('[uncaught]', err);
  shutdown('uncaughtException');
});