// server.js (FULL — MULTI PRODUCT IMAGES + SELECT DISPLAY/DETAIL + FEATURED + PRICING + ORDERS + REVIEWS + SECURITY)
// Backend on Render: https://kikelara1.onrender.com
//
// ENV (Render):
//   DATABASE_URL
//   NODE_ENV=production
//   ADMIN_SECRET
//   ADMIN_PASSWORD_HASH          (bcrypt hash)
//   PAYSTACK_SECRET_KEY          (optional if you use Paystack verify/webhook)
//   SUPABASE_URL
//   SUPABASE_SERVICE_ROLE_KEY
//   SUPABASE_BUCKET=kikelara     (or your bucket)
//   SIGNED_URL_TTL_SECONDS=604800 (7d) optional
//   FRONTEND_ORIGINS=https://yourdomain.com,https://another.com  (optional extra)
//   HCAPTCHA_SECRET_KEY          (optional)
//   CAPTCHA_REQUIRED=true/false  (default true)
//   GMAIL_USER + GMAIL_APP_PASS  (optional for emails)
//
// Required DB tables (you already have most):
//  - products (id, name, price, description, image_url, is_active, payload jsonb, created_at, updated_at)
//  - orders (id, reference UNIQUE, status, payload jsonb, created_at)
//  - messages (id, name, email, message, created_at)
//  - newsletter_subscribers (id, email UNIQUE, subscribed_at)
//  - delivery_pricing (id=1, default_fee, updated_at, data jsonb)
//  - homepage_featured (id, title, link_url, image_key, sort_order, is_active, created_at, updated_at, payload jsonb)
//  - paystack_events (for webhook replay protection) (recommended)
//
// Reviews (optional):
//  - product_reviews (id, product_id text, name, title, text, rating int, verified bool, device_id text, created_at)
//    RECOMMENDED UNIQUE: (product_id, device_id) for ON CONFLICT to work
//  - review_votes (id, review_id bigint, device_id text, vote_type text, created_at)
//    RECOMMENDED UNIQUE: (review_id, device_id) for ON CONFLICT to work
//
// NOTE: Node 18+ recommended (built-in fetch). If older: install node-fetch.

"use strict";

const express = require("express");
const cors = require("cors");
const path = require("path");
const crypto = require("crypto");
const nodemailer = require("nodemailer");
const helmet = require("helmet");
const compression = require("compression");
const multer = require("multer");
const { Pool } = require("pg");
const sharp = require("sharp");
const { z, ZodError } = require("zod");
const cookieParser = require("cookie-parser");
const bcrypt = require("bcryptjs");
const { createClient } = require("@supabase/supabase-js");

// Optional security middlewares (only used if installed)
let rateLimit, slowDown, xssClean, mongoSanitize, hpp;
try { rateLimit = require("express-rate-limit"); } catch {}
try { slowDown = require("express-slow-down"); } catch {}
try { xssClean = require("xss-clean"); } catch {}
try { mongoSanitize = require("express-mongo-sanitize"); } catch {}
try { hpp = require("hpp"); } catch {}
try { require("dotenv").config(); } catch {}

const app = express();
const PORT = process.env.PORT || 4000;

/* ===================== BASE CONFIG ===================== */
app.disable("x-powered-by");
app.disable("etag");
app.set("trust proxy", 1);

const SERVICE_NAME = process.env.SERVICE_NAME || "kikelara-api";
const ENV = process.env.NODE_ENV || "development";
const IS_PROD = ENV === "production";

/* ===================== ADMIN AUTH CONFIG ===================== */
const ADMIN_SECRET = process.env.ADMIN_SECRET || "CHANGE_ME_SUPER_SECRET";
const ADMIN_PASSWORD_HASH = process.env.ADMIN_PASSWORD_HASH || "";
const ADMIN_TOTP_SECRET = process.env.ADMIN_TOTP_SECRET || ""; // optional (not implemented)

/* ===================== PAYSTACK ===================== */
const PAYSTACK_SECRET_KEY = process.env.PAYSTACK_SECRET_KEY || "";

/* ===================== COOKIES + CSRF ===================== */
const COOKIE_NAME = "admin_session";
const CSRF_COOKIE = "admin_csrf";

const COOKIE_OPTS = {
  httpOnly: true,
  secure: IS_PROD,
  sameSite: IS_PROD ? "none" : "lax",
  path: "/",
};

const CSRF_COOKIE_OPTS = {
  httpOnly: false, // must be readable by browser JS
  secure: IS_PROD,
  sameSite: IS_PROD ? "none" : "lax",
  path: "/",
};

/* ===================== FETCH HELPER ===================== */
let fetchFn = global.fetch;
async function ensureFetch() {
  if (fetchFn) return fetchFn;
  try {
    const mod = await import("node-fetch");
    fetchFn = mod.default;
  } catch {
    fetchFn = null;
  }
  return fetchFn;
}

/* ===================== SAFE LOGGING ===================== */
function nowIso() { return new Date().toISOString(); }

function log(level, event, payload = {}) {
  const line = { ts: nowIso(), level, service: SERVICE_NAME, env: ENV, event, ...payload };
  console.log(JSON.stringify(line));
}
const logInfo = (e, p) => log("info", e, p);
const logWarn = (e, p) => log("warn", e, p);
const logError = (e, p) => log("error", e, p);

function makeRid() {
  return `${Date.now().toString(36)}-${Math.random().toString(36).slice(2, 10)}`;
}

function getClientIp(req) {
  const xf = (req.headers["x-forwarded-for"] || "").toString().split(",")[0].trim();
  return xf || req.socket?.remoteAddress || "unknown";
}

const SENSITIVE_KEYWORDS = [
  "authorization", "cookie", "set-cookie",
  "token", "access_token", "refresh_token",
  "password", "pass", "secret", "api_key", "apikey", "key",
  "pin", "code", "otp",
  "paystack", "card", "cvv",
];

function isSensitiveKey(k) {
  const key = String(k || "").toLowerCase();
  return SENSITIVE_KEYWORDS.some((s) => key.includes(s));
}

function safeHeaders(req) {
  const keep = {};
  const hdrs = req.headers || {};
  for (const [k, v] of Object.entries(hdrs)) {
    const lk = k.toLowerCase();
    if (lk === "authorization" || lk === "cookie" || lk === "set-cookie") { keep[lk] = "[REDACTED]"; continue; }
    if (["origin","referer","user-agent","content-type","accept","x-forwarded-proto","x-paystack-signature","x-csrf-token"].includes(lk)) {
      keep[lk] = typeof v === "string" ? (v.length > 300 ? v.slice(0, 300) + "…" : v) : v;
      continue;
    }
    if (isSensitiveKey(lk)) keep[lk] = "[REDACTED]";
  }
  return keep;
}

function safeQuery(req) {
  const q = req.query || {};
  const out = {};
  for (const [k, v] of Object.entries(q)) {
    out[k] = isSensitiveKey(k)
      ? "[REDACTED]"
      : (typeof v === "string" ? (v.length > 300 ? v.slice(0, 300) + "…" : v) : v);
  }
  return out;
}

/* ===================== REQUEST ID (MUST BE EARLY) ===================== */
app.use((req, res, next) => {
  const rid = makeRid();
  req.rid = rid;
  res.setHeader("X-Request-Id", rid);
  next();
});

/* ===================== CORS (MOVED EARLY — IMPORTANT FOR CREDENTIALS) ===================== */
const FRONTEND_ORIGINS = (process.env.FRONTEND_ORIGINS || "")
  .split(",")
  .map((s) => s.trim())
  .filter(Boolean);

const ALLOW_ORIGINS = [
  "http://localhost:3000",
  "http://localhost:5173",
  "http://127.0.0.1:5500",
  "http://localhost:5500",

  // your vercel(s)
  "https://kikelara1.vercel.app",
  "https://www.kikelara1.vercel.app",

  // (extra) common variant — does not break anything if unused
  "https://kikelara.vercel.app",
  "https://www.kikelara.vercel.app",

  ...FRONTEND_ORIGINS,
];

function originAllowed(origin) {
  if (!origin) return true; // server-to-server, curl
  return ALLOW_ORIGINS.includes(origin);
}

const corsOptions = {
  origin: function (origin, cb) {
    if (originAllowed(origin)) return cb(null, true);
    return cb(new Error("Not allowed by CORS: " + origin));
  },
  methods: ["GET", "POST", "PUT", "PATCH", "DELETE", "OPTIONS"],
  allowedHeaders: [
    "Content-Type",
    "Accept",
    "X-CSRF-Token",
    "x-csrf-token",
    "x-paystack-signature",
    "Authorization",
  ],
  exposedHeaders: ["X-Request-Id"],
  credentials: true,
  optionsSuccessStatus: 204,
  maxAge: 86400,
};

app.use(cors(corsOptions));
app.options(/.*/, cors(corsOptions));

/* ===================== TEMP BAN (LIGHT) ===================== */
const banMap = new Map();
function isBanned(ip) {
  const v = banMap.get(ip);
  if (!v) return false;
  if (Date.now() > v.until) { banMap.delete(ip); return false; }
  return true;
}
function banIp(ip, minutes, reason) {
  const until = Date.now() + minutes * 60 * 1000;
  const prev = banMap.get(ip);
  const hits = (prev?.hits || 0) + 1;
  banMap.set(ip, { until, reason, hits });
  logWarn("security.temp_ban", { ip, minutes, reason, until: new Date(until).toISOString(), hits });
}

/* ===================== REQUEST LOGGER (AFTER CORS NOW) ===================== */
app.use((req, res, next) => {
  const ip = getClientIp(req);

  if (isBanned(ip)) {
    logWarn("security.banned_request", { rid: req.rid || "-", ip, method: req.method, path: req.originalUrl });
    return res.status(403).json({ success: false, message: "Access blocked. Try later." });
  }

  const start = process.hrtime.bigint();

  logInfo("http.req", {
    rid: req.rid,
    ip,
    method: req.method,
    path: req.originalUrl,
    headers: safeHeaders(req),
    query: safeQuery(req),
  });

  res.on("finish", () => {
    const end = process.hrtime.bigint();
    const ms = Number(end - start) / 1e6;
    const payload = { rid: req.rid, ip, method: req.method, path: req.originalUrl, status: res.statusCode, ms: Math.round(ms) };
    if (res.statusCode >= 500) logError("http.res", payload);
    else if (res.statusCode >= 400) logWarn("http.res", payload);
    else logInfo("http.res", payload);
  });

  next();
});

/* ===================== DB ===================== */
const pool = process.env.DATABASE_URL
  ? new Pool({
      connectionString: process.env.DATABASE_URL,
      ssl: IS_PROD ? { rejectUnauthorized: false } : false,
    })
  : null;

async function dbQuery(text, params) {
  if (!pool) throw new Error("DATABASE_URL not set");
  return pool.query(text, params);
}
async function withDbClient(fn) {
  if (!pool) throw new Error("DATABASE_URL not set");
  const client = await pool.connect();
  try { return await fn(client); } finally { client.release(); }
}

/* ===================== DB CAPS (SCHEMA FLEX) ===================== */
const DB_CAPS = {
  products: { columns: new Set(), idType: "", idHasDefault: true },
  messages: { columns: new Set(), idType: "", idHasDefault: true },
  newsletter_subscribers: { columns: new Set(), idType: "", idHasDefault: true },
  product_reviews: { exists: true },
  review_votes: { exists: true },
};

async function tableExists(tableName) {
  const r = await dbQuery(
    `SELECT 1 FROM information_schema.tables WHERE table_schema='public' AND table_name=$1 LIMIT 1`,
    [tableName]
  );
  return r.rows.length > 0;
}

async function loadTableCaps(tableName) {
  const r = await dbQuery(
    `SELECT column_name, data_type, column_default
     FROM information_schema.columns
     WHERE table_schema='public' AND table_name=$1`,
    [tableName]
  );

  const cols = new Set(r.rows.map((x) => x.column_name));
  let idType = "";
  let idHasDefault = true;

  for (const row of r.rows) {
    if (row.column_name === "id") {
      idType = String(row.data_type || "");
      idHasDefault = String(row.column_default || "").includes("nextval");
    }
  }
  return { columns: cols, idType, idHasDefault };
}

async function ensureCapsLoaded(tableName) {
  if (!pool) return;
  const caps = DB_CAPS[tableName];
  if (!caps) return;
  if (caps.columns && caps.columns.size > 0) return;

  try {
    if (await tableExists(tableName)) {
      DB_CAPS[tableName] = await loadTableCaps(tableName);
    }
  } catch {}
}

async function initDbCaps() {
  if (!pool) return;
  await ensureCapsLoaded("products");
  await ensureCapsLoaded("messages");
  await ensureCapsLoaded("newsletter_subscribers");
  try { DB_CAPS.product_reviews.exists = await tableExists("product_reviews"); } catch { DB_CAPS.product_reviews.exists = false; }
  try { DB_CAPS.review_votes.exists = await tableExists("review_votes"); } catch { DB_CAPS.review_votes.exists = false; }
}

/* ===================== SECURITY HEADERS + HTTPS ===================== */
app.use((req, res, next) => {
  if (IS_PROD) {
    const proto = req.headers["x-forwarded-proto"];
    // NOTE: Do NOT redirect OPTIONS; keep preflight clean
    if (proto && proto !== "https" && req.method !== "OPTIONS") {
      return res.redirect(301, "https://" + req.headers.host + req.originalUrl);
    }
  }
  next();
});

app.use(
  helmet({
    crossOriginResourcePolicy: false,
    contentSecurityPolicy: false, // keep off for cross-origin frontends
  })
);

app.use((req, res, next) => {
  res.setHeader("X-Content-Type-Options", "nosniff");
  res.setHeader("X-Frame-Options", "DENY");
  res.setHeader("Referrer-Policy", "strict-origin-when-cross-origin");
  res.setHeader("Permissions-Policy", "geolocation=(), microphone=(), camera=()");
  next();
});

app.use(compression());

/* ===================== RATE LIMIT / SLOW DOWN ===================== */
function rateLimitWithSecurityLog(name, opts) {
  if (!rateLimit) return (req, res, next) => next();

  return rateLimit({
    ...opts,
    standardHeaders: true,
    legacyHeaders: false,

    // ✅ IMPORTANT: don't rate-limit OPTIONS preflight (prevents random CORS failures)
    skip: (req) => String(req.method || "").toUpperCase() === "OPTIONS",

    handler: (req, res) => {
      const ip = getClientIp(req);
      logWarn("security.rate_limit_429", { rid: req.rid || "-", limiter: name, ip, method: req.method, path: req.originalUrl });
      banIp(ip, 10, `rate_limit:${name}`);
      res.status(429).json({ success: false, message: "Too many requests. Please try again later." });
    },
  });
}

const globalLimiter = rateLimitWithSecurityLog("global", { windowMs: 15 * 60 * 1000, max: 500 });
const authLimiter = rateLimitWithSecurityLog("auth", { windowMs: 10 * 60 * 1000, max: 25 });
const writeLimiter = rateLimitWithSecurityLog("write", { windowMs: 5 * 60 * 1000, max: 80 });

const speedLimiter = slowDown
  ? slowDown({
      windowMs: 15 * 60 * 1000,
      delayAfter: 120,
      delayMs: () => 250,
      skip: (req) => String(req.method || "").toUpperCase() === "OPTIONS",
    })
  : (req, res, next) => next();

app.use(globalLimiter);
app.use(speedLimiter);

/* ===================== COOKIE PARSER ===================== */
app.use(cookieParser(ADMIN_SECRET));

/* ===================== PAYSTACK WEBHOOK (RAW BEFORE JSON) ===================== */
function timingSafeEqualStr(a, b) {
  try {
    const aa = Buffer.from(String(a || ""), "utf8");
    const bb = Buffer.from(String(b || ""), "utf8");
    if (aa.length !== bb.length) return false;
    return crypto.timingSafeEqual(aa, bb);
  } catch { return false; }
}

function paystackSignatureValid(rawBodyBuffer, signature) {
  if (!PAYSTACK_SECRET_KEY) return false;
  if (!rawBodyBuffer || !Buffer.isBuffer(rawBodyBuffer)) return false;
  if (!signature) return false;

  const hash = crypto.createHmac("sha512", PAYSTACK_SECRET_KEY).update(rawBodyBuffer).digest("hex");
  return timingSafeEqualStr(hash, signature);
}

async function verifyPaystack(reference) {
  if (!PAYSTACK_SECRET_KEY) throw new Error("PAYSTACK_SECRET_KEY missing");
  const f = await ensureFetch();
  if (!f) throw new Error("fetch not available (Node 18+ recommended)");

  const url = `https://api.paystack.co/transaction/verify/${encodeURIComponent(reference)}`;
  const r = await f(url, { method: "GET", headers: { Authorization: `Bearer ${PAYSTACK_SECRET_KEY}`, "Content-Type": "application/json" } });
  const data = await r.json().catch(() => null);
  if (!r.ok) throw new Error(data?.message || `Paystack verify failed (${r.status})`);
  return data;
}

async function recordPaystackEventOnce({ eventId, reference, eventType, payload, signature }) {
  const r = await dbQuery(
    `insert into paystack_events (event_id, reference, event_type, payload, signature)
     values ($1,$2,$3,$4,$5)
     on conflict do nothing
     returning id`,
    [String(eventId), String(reference), String(eventType), payload || {}, signature ? String(signature) : null]
  );
  return r.rows.length > 0;
}

app.post("/payments/paystack/webhook", express.raw({ type: "application/json", limit: "300kb" }), async (req, res) => {
  const ip = getClientIp(req);
  try {
    const sig = String(req.headers["x-paystack-signature"] || "");
    if (!paystackSignatureValid(req.body, sig)) {
      logWarn("security.paystack_webhook_bad_sig", { rid: req.rid || "-", ip });
      return res.status(200).json({ received: true, ignored: true });
    }

    const bodyString = req.body.toString("utf8");
    let event = null;
    try { event = JSON.parse(bodyString); } catch {
      logWarn("paystack.webhook_bad_json", { rid: req.rid || "-", ip });
      return res.status(200).json({ received: true, ignored: true });
    }

    const evtType = String(event?.event || "");
    const data = event?.data || {};
    if (evtType !== "charge.success") return res.status(200).json({ received: true, ignored: true });

    const reference = String(data?.reference || "").trim();
    if (!reference) return res.status(200).json({ received: true, ignored: true });

    const eventId = String(event?.id || data?.id || data?.transaction || "").trim() || `no_event_id:${reference}:${evtType}`;

    let firstTime = true;
    try {
      firstTime = await recordPaystackEventOnce({ eventId, reference, eventType: evtType, payload: event, signature: sig });
    } catch {
      firstTime = true;
    }
    if (!firstTime) return res.status(200).json({ received: true, ignored: true, replay: true });

    const verify = await verifyPaystack(reference);
    const ok = Boolean(verify?.status) && verify?.data?.status === "success";
    if (!ok) return res.status(200).json({ received: true, ignored: true });

    const paidKobo = Number(verify?.data?.amount || 0);
    const paidNaira = Math.round(paidKobo / 100);

    const existing = await dbQuery(`SELECT * FROM orders WHERE reference=$1 LIMIT 1`, [reference]);
    if (!existing.rows.length) {
      const payload = {
        reference,
        status: "Paid",
        paystackRef: reference,
        createdAt: new Date().toISOString(),
        paidAt: new Date().toISOString(),
        amountPaid: paidNaira,
        paystackTransactionId: verify?.data?.id ?? null,
        note: "Created via webhook",
      };

      await dbQuery(
        `INSERT INTO orders (reference, status, payload)
         VALUES ($1,$2,$3)
         ON CONFLICT (reference) DO NOTHING`,
        [reference, "Paid", payload]
      );
      return res.status(200).json({ ok: true });
    }

    const order = existing.rows[0];
    const payload = order.payload && typeof order.payload === "object" ? order.payload : {};
    payload.status = "Paid";
    payload.paystackRef = reference;
    payload.paidAt = payload.paidAt || new Date().toISOString();
    payload.amountPaid = payload.amountPaid || paidNaira;
    payload.paystackTransactionId = payload.paystackTransactionId || (verify?.data?.id ?? null);

    await dbQuery(`UPDATE orders SET status='Paid', payload=$2 WHERE reference=$1`, [reference, payload]);
    return res.status(200).json({ ok: true });
  } catch (e) {
    logError("paystack.webhook_error", { rid: req.rid || "-", message: String(e?.message || e).slice(0, 600) });
    return res.status(200).json({ received: true, ignored: true });
  }
});

/* ===================== JSON PARSERS ===================== */
app.use(express.json({ limit: "400kb" }));
app.use(express.urlencoded({ extended: true, limit: "400kb" }));

/* ===================== OPTIONAL SANITIZERS ===================== */
if (mongoSanitize) app.use(mongoSanitize());
if (xssClean) app.use(xssClean());
if (hpp) app.use(hpp());

/* ===================== ZOD VALIDATOR ===================== */
function validate(schema, where = "body") {
  return (req, res, next) => {
    try {
      const parsed = schema.parse(req[where]);
      req[where] = parsed;
      next();
    } catch (err) {
      if (err instanceof ZodError) {
        return res.status(400).json({
          success: false,
          message: "Validation failed",
          details: err.issues.map((i) => ({ field: i.path.join("."), message: i.message })),
        });
      }
      next(err);
    }
  };
}

const zEmail = z.string().trim().toLowerCase().email("Invalid email");
const zNonEmpty = (msg) => z.string().trim().min(1, msg);
const zISODateStr = z.string().refine((v) => !Number.isNaN(new Date(v).getTime()), "Invalid date");

/* ===================== HEALTH ===================== */
app.get("/health", (req, res) => res.json({ ok: true, uptime: process.uptime() }));
app.get("/db-test", async (req, res) => {
  try {
    const r = await dbQuery("SELECT NOW() as now");
    res.json({ ok: true, now: r.rows[0].now });
  } catch (e) {
    res.status(500).json({ ok: false, error: String(e.message || e) });
  }
});

/* ===================== SUPABASE STORAGE ===================== */
const SUPABASE_URL = process.env.SUPABASE_URL || "";
const SUPABASE_SERVICE_ROLE_KEY = process.env.SUPABASE_SERVICE_ROLE_KEY || "";
const SUPABASE_BUCKET = process.env.SUPABASE_BUCKET || "kikelara";
const SIGNED_URL_TTL_SECONDS = Math.max(60, Number(process.env.SIGNED_URL_TTL_SECONDS || 604800));

const supabaseAdmin =
  SUPABASE_URL && SUPABASE_SERVICE_ROLE_KEY
    ? createClient(SUPABASE_URL, SUPABASE_SERVICE_ROLE_KEY, { auth: { persistSession: false } })
    : null;

function ensureSupabaseReady() {
  if (!supabaseAdmin) throw new Error("Supabase Storage not configured (missing SUPABASE_URL or SUPABASE_SERVICE_ROLE_KEY)");
  if (!SUPABASE_BUCKET) throw new Error("SUPABASE_BUCKET missing");
}

function safeKeyPart(str, max = 40) {
  return (
    String(str || "")
      .toLowerCase()
      .replace(/\.[^.]+$/, "")
      .replace(/[^a-z0-9_-]/g, "_")
      .replace(/_+/g, "_")
      .slice(0, max) || "image"
  );
}

async function toWebpSquareBuffer(buf) {
  return sharp(buf).rotate().resize(1080, 1080, { fit: "cover" }).webp({ quality: 82 }).toBuffer();
}
async function toWebpWideBuffer(buf) {
  return sharp(buf).rotate().resize(2000, 1125, { fit: "cover" }).webp({ quality: 82 }).toBuffer();
}

async function uploadKeyToSupabase({ buffer, key, contentType = "image/webp" }) {
  ensureSupabaseReady();
  const { error } = await supabaseAdmin.storage.from(SUPABASE_BUCKET).upload(key, buffer, {
    contentType,
    cacheControl: "31536000",
    upsert: false,
  });
  if (error) throw new Error(error.message || "Supabase upload failed");
  return { key };
}

async function uploadProductImageToSupabase({ buffer, originalName, productId }) {
  ensureSupabaseReady();
  const base = safeKeyPart(originalName);
  const key = `products/${productId}/${Date.now()}_${base}.webp`;
  const webpBuf = await toWebpSquareBuffer(buffer);
  return uploadKeyToSupabase({ buffer: webpBuf, key });
}

async function uploadFeaturedImageToSupabase({ buffer, originalName, featuredId }) {
  ensureSupabaseReady();
  const base = safeKeyPart(originalName);
  const key = `featured/${featuredId}/${Date.now()}_${base}.webp`;
  const webpBuf = await toWebpWideBuffer(buffer);
  return uploadKeyToSupabase({ buffer: webpBuf, key });
}
async function toWebpHeroBuffer(buf) {
  // 16:9 hero (crisp on desktop + mobile)
  return sharp(buf).rotate().resize(2400, 1350, { fit: "cover" }).webp({ quality: 82 }).toBuffer();
}

async function uploadHeroImageToSupabase({ buffer, originalName, heroId }) {
  ensureSupabaseReady();
  const base = safeKeyPart(originalName);
  const key = `hero/${heroId}/${Date.now()}_${base}.webp`;
  const webpBuf = await toWebpHeroBuffer(buffer);
  return uploadKeyToSupabase({ buffer: webpBuf, key });
}

async function withSignedHero(row, { includeKeys = false } = {}) {
  const r = { ...row };
  const key = String(row?.image_key || "").trim();
  r.image_url = "";
  if (key) {
    try { r.image_url = await signKey(key); } catch { r.image_url = ""; }
  }
  if (includeKeys) r.image_key = key;
  return r;
}


async function signKey(key) {
  ensureSupabaseReady();
  const k = String(key || "").trim();
  if (!k) return "";
  const { data, error } = await supabaseAdmin.storage.from(SUPABASE_BUCKET).createSignedUrl(k, SIGNED_URL_TTL_SECONDS);
  if (error) throw new Error(error.message || "Signing failed");
  return data?.signedUrl || "";
}

async function deleteSupabaseKey(key) {
  try {
    ensureSupabaseReady();
    const k = String(key || "").trim();
    if (!k) return;
    await supabaseAdmin.storage.from(SUPABASE_BUCKET).remove([k]);
  } catch {}
}

/* ===================== MULTER (MEMORY) ===================== */
function imageOnly(req, file, cb) {
  const okMime = /^image\//.test(file.mimetype || "");
  const ext = path.extname(file.originalname || "").toLowerCase();
  const okExt = [".png", ".jpg", ".jpeg", ".webp"].includes(ext);
  cb(okMime && okExt ? null : new Error("Only PNG/JPG/JPEG/WEBP images allowed"), okMime && okExt);
}

const upload = multer({
  storage: multer.memoryStorage(),
  fileFilter: imageOnly,
  limits: { fileSize: 8 * 1024 * 1024 },
});

// one main image + multiple gallery images
const uploadProductMedia = upload.fields([
  { name: "image", maxCount: 1 },   // display image
  { name: "images", maxCount: 12 }, // gallery images
]);

/* ===================== ADMIN SESSION (SIGNED COOKIE TOKEN) ===================== */
function base64url(input) {
  return Buffer.from(input).toString("base64").replace(/=/g, "").replace(/\+/g, "-").replace(/\//g, "_");
}
function unbase64url(input) {
  const b64 = input.replace(/-/g, "+").replace(/_/g, "/");
  return Buffer.from(b64, "base64").toString("utf-8");
}
function sign(payloadB64) {
  return crypto.createHmac("sha256", ADMIN_SECRET).update(payloadB64).digest("base64").replace(/=/g, "").replace(/\+/g, "-").replace(/\//g, "_");
}
function safeEq(a, b) {
  try {
    const aa = Buffer.from(String(a || ""), "utf8");
    const bb = Buffer.from(String(b || ""), "utf8");
    if (aa.length !== bb.length) return false;
    return crypto.timingSafeEqual(aa, bb);
  } catch { return false; }
}
function createToken(payloadObj) {
  const payloadB64 = base64url(JSON.stringify(payloadObj));
  return `${payloadB64}.${sign(payloadB64)}`;
}
function verifyToken(token) {
  if (!token || typeof token !== "string") return null;
  const parts = token.split(".");
  if (parts.length !== 2) return null;
  const [payloadB64, sig] = parts;
  const expected = sign(payloadB64);
  if (!safeEq(sig, expected)) return null;
  try {
    const payload = JSON.parse(unbase64url(payloadB64));
    if (payload?.exp && Date.now() > payload.exp) return null;
    return payload;
  } catch { return null; }
}

// allowlist (restart => logout)
const adminJtiMap = new Map(); // jti -> expMs
function cleanupJti() {
  const now = Date.now();
  for (const [jti, exp] of adminJtiMap.entries()) {
    if (!exp || now > exp) adminJtiMap.delete(jti);
  }
}
setInterval(cleanupJti, 60 * 1000).unref?.();

function getAdminTokenFromCookie(req) {
  return String(req.cookies?.[COOKIE_NAME] || "");
}

function isAdminAuthed(req) {
  const token = getAdminTokenFromCookie(req);
  const payload = verifyToken(token);
  if (!payload || payload.role !== "admin") return false;
  if (!payload.jti) return false;
  const exp = adminJtiMap.get(payload.jti);
  if (!exp || Date.now() > exp) return false;
  return true;
}

function requireAdmin(req, res, next) {
  const token = getAdminTokenFromCookie(req);
  const payload = verifyToken(token);

  if (!payload || payload.role !== "admin") {
    logWarn("security.admin_unauthorized", { rid: req.rid || "-", ip: getClientIp(req), path: req.originalUrl });
    return res.status(401).json({ success: false, message: "Unauthorized" });
  }
  if (!payload.jti) return res.status(401).json({ success: false, message: "Session expired" });

  const exp = adminJtiMap.get(payload.jti);
  if (!exp || Date.now() > exp) return res.status(401).json({ success: false, message: "Session expired" });

  req.admin = payload;
  next();
}

function requireCsrf(req, res, next) {
  const method = String(req.method || "").toUpperCase();
  if (["GET", "HEAD", "OPTIONS"].includes(method)) return next();

  const cookieVal = String(req.cookies?.[CSRF_COOKIE] || "");
  const headerVal = String(req.headers["x-csrf-token"] || "");

  if (!cookieVal || !headerVal || cookieVal !== headerVal) {
    logWarn("security.csrf_block", { rid: req.rid || "-", ip: getClientIp(req), path: req.originalUrl });
    return res.status(403).json({ success: false, message: "CSRF blocked" });
  }
  next();
}

function randomToken(bytes = 32) { return crypto.randomBytes(bytes).toString("hex"); }

/* ===================== AUTH ROUTES ===================== */
const AdminLoginSchema = z.object({
  password: zNonEmpty("Missing password"),
  otp: z.string().trim().optional(),
});

app.post("/admin/login", authLimiter, validate(AdminLoginSchema), async (req, res) => {
  try {
    const ip = getClientIp(req);

    if (IS_PROD && ADMIN_SECRET === "CHANGE_ME_SUPER_SECRET") {
      logError("security.admin_secret_default", { rid: req.rid || "-", ip });
      return res.status(500).json({ success: false, message: "Admin secret not configured" });
    }
    if (!ADMIN_PASSWORD_HASH) {
      logError("security.admin_hash_missing", { rid: req.rid || "-", ip });
      return res.status(500).json({ success: false, message: "Admin login not configured" });
    }

    const { password, otp } = req.body;

    const ok = await bcrypt.compare(String(password || ""), ADMIN_PASSWORD_HASH);
    if (!ok) {
      logWarn("security.admin_bad_password", { rid: req.rid || "-", ip });
      banIp(ip, 15, "admin_login_failed");
      return res.status(401).json({ success: false, message: "Invalid credentials" });
    }

    if (ADMIN_TOTP_SECRET) {
      if (!otp) return res.status(401).json({ success: false, message: "OTP required" });
      return res.status(500).json({ success: false, message: "TOTP secret is set but verification is not implemented." });
    }

    const exp = Date.now() + 1000 * 60 * 60 * 12;
    const jti = randomToken(16);
    const token = createToken({ role: "admin", iat: Date.now(), exp, jti });
    adminJtiMap.set(jti, exp);

    const csrfToken = randomToken(20);
    res.cookie(COOKIE_NAME, token, { ...COOKIE_OPTS, maxAge: 1000 * 60 * 60 * 12 });
    res.cookie(CSRF_COOKIE, csrfToken, { ...CSRF_COOKIE_OPTS, maxAge: 1000 * 60 * 60 * 12 });

    logInfo("security.admin_login_ok", { rid: req.rid || "-", ip });
    res.json({ success: true, csrfToken });
  } catch (e) {
    logError("admin.login_failed", { rid: req.rid || "-", message: String(e?.message || e).slice(0, 600) });
    res.status(500).json({ success: false, message: "Server error" });
  }
});

app.post("/admin/logout", requireAdmin, requireCsrf, (req, res) => {
  const payload = req.admin || {};
  if (payload?.jti) adminJtiMap.delete(payload.jti);

  res.clearCookie(COOKIE_NAME, { ...COOKIE_OPTS });
  res.clearCookie(CSRF_COOKIE, { ...CSRF_COOKIE_OPTS });
  res.json({ success: true });
});

app.get("/admin/me", requireAdmin, (req, res) => {
  res.json({ success: true, admin: req.admin, csrfToken: String(req.cookies?.[CSRF_COOKIE] || "") });
});

app.post("/admin/csrf/rotate", requireAdmin, (req, res) => {
  const csrfToken = randomToken(20);
  res.cookie(CSRF_COOKIE, csrfToken, { ...CSRF_COOKIE_OPTS, maxAge: 1000 * 60 * 60 * 12 });
  res.json({ success: true, csrfToken });
});

/* ===================== PRODUCT IMAGE MODEL ===================== */
function getRowPayload(row) {
  return row?.payload && typeof row.payload === "object" ? row.payload : {};
}

function normalizeKeyArray(v) {
  if (Array.isArray(v)) return v.map(String).map(s => s.trim()).filter(Boolean);
  if (typeof v === "string") {
    try {
      const parsed = JSON.parse(v);
      if (Array.isArray(parsed)) return parsed.map(String).map(s => s.trim()).filter(Boolean);
    } catch {}
  }
  return [];
}

function uniqueArr(arr) {
  const out = [];
  const seen = new Set();
  for (const x of arr) {
    const s = String(x || "").trim();
    if (!s || seen.has(s)) continue;
    seen.add(s);
    out.push(s);
  }
  return out;
}

function looksLikeStorageKey(img) {
  const s = String(img || "").trim();
  if (!s) return false;
  if (s.startsWith("http://") || s.startsWith("https://")) return false;
  if (s.startsWith("/uploads/")) return false;
  return true;
}

function extractDisplayKey(row) {
  const payload = getRowPayload(row);
  const pKey = String(payload.__image_key || "").trim();
  if (pKey) return pKey;

  const img = String(row?.image_url || "").trim();
  if (!img) return "";
  return looksLikeStorageKey(img) ? img : "";
}

function getGalleryKeys(row) {
  const payload = getRowPayload(row);
  return normalizeKeyArray(payload.__gallery_keys);
}

function getDetailKey(row) {
  const payload = getRowPayload(row);
  const dk = String(payload.__detail_image_key || "").trim();
  return dk || extractDisplayKey(row) || "";
}

async function signMany(keys) {
  const list = normalizeKeyArray(keys);
  if (!list.length) return [];
  const urls = await Promise.all(
    list.map(async (k) => {
      try { return await signKey(k); } catch { return ""; }
    })
  );
  return urls.filter(Boolean);
}

async function withSignedProduct(row, { includeKeys = false } = {}) {
  const payload = getRowPayload(row);

  const displayKey = extractDisplayKey(row);
  const detailKey = getDetailKey(row);
  const galleryKeys = getGalleryKeys(row);

  const [displayUrl, detailUrl, galleryUrls] = await Promise.all([
    displayKey ? signKey(displayKey).catch(() => "") : Promise.resolve(""),
    detailKey ? signKey(detailKey).catch(() => "") : Promise.resolve(""),
    signMany(galleryKeys),
  ]);

  const allKeys = uniqueArr([detailKey, displayKey, ...galleryKeys]);
  const allUrls = await signMany(allKeys);

  const out = {
    ...row,
    payload,
    image_url: displayUrl || "",
    detail_image_url: detailUrl || (displayUrl || ""),
    images: galleryUrls,
    all_images: allUrls,
  };

  if (includeKeys) {
    out.image_key = displayKey || "";
    out.detail_image_key = detailKey || "";
    out.images_keys = galleryKeys;
  }

  return out;
}

/* ===================== PRODUCTS DB HELPERS ===================== */
function capsLoadedProducts() { return DB_CAPS.products?.columns && DB_CAPS.products.columns.size > 0; }
function hasProductCol(c) { return DB_CAPS.products?.columns?.has(c); }

function makeSafeProductId() {
  const t = String(DB_CAPS.products?.idType || "").toLowerCase();
  if (t.includes("uuid")) return crypto.randomUUID();
  if (t.includes("bigint")) return String(Date.now()); // safe for route params
  if (t.includes("integer") || t.includes("int")) return String(Math.floor(Date.now() / 1000));
  return String(Date.now());
}

function buildInsertSQL(table, cols) {
  const params = cols.map((_, i) => `$${i + 1}`);
  return `INSERT INTO ${table} (${cols.join(",")}) VALUES (${params.join(",")}) RETURNING *`;
}

function isUndefinedColumnErr(e) { return String(e?.code || "") === "42703"; }
function isNotNullIdErr(e) { return String(e?.code || "") === "23502" && (/column "id"/i.test(String(e?.message || "")) || String(e?.column || "") === "id"); }

async function insertProductRow(client, { id, name, price, description, imageKey, isActive, payload }) {
  const now = new Date();
  const candidates = [];

  if (capsLoadedProducts()) {
    const cols = [];
    const vals = [];

    const includeId = DB_CAPS.products.idHasDefault === false && hasProductCol("id");
    if (includeId) { cols.push("id"); vals.push(id); }
    if (hasProductCol("name")) { cols.push("name"); vals.push(name); }
    if (hasProductCol("price")) { cols.push("price"); vals.push(price); }
    if (hasProductCol("description")) { cols.push("description"); vals.push(description || null); }
    if (hasProductCol("image_url")) { cols.push("image_url"); vals.push(imageKey || null); }
    if (hasProductCol("is_active")) { cols.push("is_active"); vals.push(isActive); }
    if (hasProductCol("created_at")) { cols.push("created_at"); vals.push(now); }
    if (hasProductCol("updated_at")) { cols.push("updated_at"); vals.push(now); }
    if (hasProductCol("payload")) { cols.push("payload"); vals.push(payload || {}); }

    if (cols.length >= 2) candidates.push({ sql: buildInsertSQL("products", cols), vals });
  }

  const baseNoId = [
    { cols: ["name","price","description","image_url","is_active","created_at","updated_at"], vals: [name, price, description || null, imageKey || null, isActive, now, now] },
    { cols: ["name","price","description","image_url","is_active"], vals: [name, price, description || null, imageKey || null, isActive] },
    { cols: ["name","price","description","image_url"], vals: [name, price, description || null, imageKey || null] },
    { cols: ["name","price","description"], vals: [name, price, description || null] },
    { cols: ["name","price"], vals: [name, price] },
  ];
  const baseWithId = [
    { cols: ["id","name","price","description","image_url","is_active","created_at","updated_at"], vals: [id, name, price, description || null, imageKey || null, isActive, now, now] },
    { cols: ["id","name","price","description","image_url","is_active"], vals: [id, name, price, description || null, imageKey || null, isActive] },
    { cols: ["id","name","price"], vals: [id, name, price] },
  ];
  for (const c of baseNoId) candidates.push({ sql: buildInsertSQL("products", c.cols), vals: c.vals });
  for (const c of baseWithId) candidates.push({ sql: buildInsertSQL("products", c.cols), vals: c.vals });

  let lastErr = null;
  for (const cand of candidates) {
    try {
      const r = await client.query(cand.sql, cand.vals);
      if (r.rows?.[0]) return r.rows[0];
    } catch (e) {
      lastErr = e;
      if (isUndefinedColumnErr(e) || isNotNullIdErr(e)) continue;
      continue;
    }
  }
  throw lastErr || new Error("Insert failed");
}

async function updateProductRow(client, id, { name, price, description, imageKey, isActive, payloadMerged }) {
  if (capsLoadedProducts()) {
    const sets = [];
    const vals = [];
    let i = 0;

    if (hasProductCol("name") && name !== undefined) { sets.push(`name=$${++i}`); vals.push(name); }
    if (hasProductCol("price") && price !== undefined) { sets.push(`price=$${++i}`); vals.push(price); }
    if (hasProductCol("description") && description !== undefined) { sets.push(`description=$${++i}`); vals.push(description || null); }
    if (hasProductCol("image_url") && imageKey !== undefined) { sets.push(`image_url=$${++i}`); vals.push(imageKey || null); }
    if (hasProductCol("is_active") && isActive !== undefined) { sets.push(`is_active=$${++i}`); vals.push(isActive); }
    if (hasProductCol("payload") && payloadMerged !== undefined) { sets.push(`payload=$${++i}`); vals.push(payloadMerged || {}); }
    if (hasProductCol("updated_at")) { sets.push(`updated_at=NOW()`); }

    if (!sets.length) throw new Error("No updatable columns found on products table");
    vals.push(id);
    const sql = `UPDATE products SET ${sets.join(", ")} WHERE id=$${++i} RETURNING *`;
    const r = await client.query(sql, vals);
    return r.rows?.[0] || null;
  }

  const candidates = [
    {
      sql: `UPDATE products
            SET image_url=$1, payload=$2, updated_at=NOW()
            WHERE id=$3 RETURNING *`,
      vals: [imageKey || null, payloadMerged || {}, id],
    },
    {
      sql: `UPDATE products
            SET image_url=$1
            WHERE id=$2 RETURNING *`,
      vals: [imageKey || null, id],
    },
  ];

  let lastErr = null;
  for (const cand of candidates) {
    try {
      const r = await client.query(cand.sql, cand.vals);
      if (r.rows?.[0]) return r.rows[0];
      return null;
    } catch (e) {
      lastErr = e;
      if (isUndefinedColumnErr(e)) continue;
      continue;
    }
  }
  throw lastErr || new Error("Update failed");
}

/* ===================== MEDIA LIST (ADMIN) ===================== */
app.get("/admin/media/list", requireAdmin, async (req, res) => {
  try {
    ensureSupabaseReady();

    const prefix = String(req.query.prefix || "").trim();
    const search = String(req.query.search || "").trim();
    const limit = Math.max(1, Math.min(200, Number(req.query.limit || 60)));
    const offset = Math.max(0, Number(req.query.offset || 0));

    const folder = prefix.replace(/^\/+/, "").replace(/^\.\.+/g, "");
    const { data, error } = await supabaseAdmin.storage.from(SUPABASE_BUCKET).list(folder, {
      limit,
      offset,
      search: search || undefined,
    });
    if (error) throw new Error(error.message || "List failed");

    const items = Array.isArray(data) ? data : [];
    const out = await Promise.all(items.map(async (it) => {
      const key = folder ? `${folder.replace(/\/+$/, "")}/${it.name}` : it.name;
      let signedUrl = "";
      try { signedUrl = await signKey(key); } catch {}
      return { name: it.name, key, updated_at: it.updated_at || null, metadata: it.metadata || {}, signedUrl };
    }));

    return res.json({ success: true, items: out, prefix: folder, offset, limit });
  } catch (e) {
    logError("media.list_failed", { rid: req.rid || "-", message: String(e?.message || e).slice(0, 600) });
    return res.status(500).json({ success: false, items: [] });
  }
});

/* ===================== PRODUCTS (PUBLIC) ===================== */
app.get("/api/products", async (req, res) => {
  try {
    await ensureCapsLoaded("products");

    // ✅ Security: ?all=true now requires admin session
    const askedAll = String(req.query.all || "").toLowerCase() === "true";
    const includeAll = askedAll && isAdminAuthed(req);

    const sql = includeAll
      ? `SELECT * FROM products ORDER BY created_at DESC`
      : `SELECT * FROM products WHERE is_active=true ORDER BY created_at DESC`;

    const out = await dbQuery(sql);
    const rows = await Promise.all(out.rows.map((r) => withSignedProduct(r, { includeKeys: false })));
    res.json(rows);
  } catch (e) {
    logError("products.public_list_failed", { rid: req.rid || "-", message: String(e?.message || e).slice(0, 600) });
    res.json([]);
  }
});

const ProductIdParamSchema = z.object({ id: z.string().trim().min(1, "Missing id") });

app.get("/api/products/:id", validate(ProductIdParamSchema, "params"), async (req, res) => {
  try {
    await ensureCapsLoaded("products");
    const id = String(req.params.id);

    const out = await dbQuery(`SELECT * FROM products WHERE id=$1 LIMIT 1`, [id]);
    if (!out.rows.length) return res.status(404).json({ success: false, message: "Product not found" });

    const p = out.rows[0];
    if (!p.is_active) return res.status(404).json({ success: false, message: "Product not found" });

    const signed = await withSignedProduct(p, { includeKeys: false });
    res.json({ success: true, product: signed });
  } catch (e) {
    logError("products.public_get_failed", { rid: req.rid || "-", message: String(e?.message || e).slice(0, 600) });
    res.status(500).json({ success: false, message: "Server error" });
  }
});

/* ===================== PRODUCTS (ADMIN) ===================== */
app.get("/admin/products", requireAdmin, async (req, res) => {
  try {
    await ensureCapsLoaded("products");
    const out = await dbQuery(`SELECT * FROM products ORDER BY created_at DESC`);
    const rows = await Promise.all(out.rows.map((r) => withSignedProduct(r, { includeKeys: true })));
    res.json({ success: true, products: rows });
  } catch (e) {
    logError("products.admin_list_failed", { rid: req.rid || "-", message: String(e?.message || e).slice(0, 600) });
    res.status(500).json({ success: false, products: [] });
  }
});

const CreateProductSchema = z.object({
  name: zNonEmpty("Missing name").max(200, "Name too long"),
  price: z.coerce.number().min(0, "Invalid price").default(0),
  description: z.string().trim().max(5000, "Description too long").optional().default(""),
  is_active: z.string().optional(),
}).passthrough();

const UpdateProductSchema = z.object({
  name: z.string().trim().min(1).max(200).optional(),
  price: z.coerce.number().min(0).optional(),
  description: z.string().trim().max(5000).optional(),
  is_active: z.string().optional(),
  remove_image: z.string().optional(), // remove display image
}).passthrough();

// CREATE: accepts image (display) + images[] (gallery)
app.post("/admin/products", writeLimiter, requireAdmin, requireCsrf, uploadProductMedia, validate(CreateProductSchema), async (req, res) => {
  let uploadedDisplayKey = "";
  let uploadedGalleryKeys = [];

  try {
    await ensureCapsLoaded("products");

    const name = String(req.body.name || "").trim();
    const price = Math.max(0, Math.round(Number(req.body.price || 0)));
    const description = String(req.body.description || "").trim();
    const isActive = String(req.body.is_active || "true").toLowerCase() !== "false";

    const payloadIn = { ...req.body };

    const mainFile = req.files?.image?.[0] || null;
    const galleryFiles = Array.isArray(req.files?.images) ? req.files.images : [];

    const createdRow = await withDbClient(async (client) => {
      await client.query("BEGIN");
      try {
        const id = makeSafeProductId();

        const basePayload = {
          ...payloadIn,
          __gallery_keys: [],
          __detail_image_key: "",
          __image_key: "",
        };

        let row = await insertProductRow(client, {
          id,
          name,
          price,
          description,
          imageKey: null,
          isActive,
          payload: basePayload,
        });

        // upload display image
        if (mainFile?.buffer) {
          const up = await uploadProductImageToSupabase({
            buffer: mainFile.buffer,
            originalName: mainFile.originalname,
            productId: row.id,
          });
          uploadedDisplayKey = up.key;
        }

        // upload gallery images
        const newGalleryKeys = [];
        for (const f of galleryFiles) {
          if (!f?.buffer) continue;
          const up = await uploadProductImageToSupabase({
            buffer: f.buffer,
            originalName: f.originalname,
            productId: row.id,
          });
          newGalleryKeys.push(up.key);
        }
        uploadedGalleryKeys = uploadedGalleryKeys.concat(newGalleryKeys);

        // If no display uploaded, pick first gallery as display
        let displayKey = uploadedDisplayKey;
        let galleryKeys = newGalleryKeys;

        if (!displayKey && galleryKeys.length) {
          displayKey = galleryKeys[0];
          galleryKeys = galleryKeys.slice(1); // avoid duplication
        }

        const detailKey = displayKey || "";

        const mergedPayload = {
          ...basePayload,
          __image_key: displayKey || "",
          __gallery_keys: galleryKeys,
          __detail_image_key: detailKey || "",
        };

        row = await updateProductRow(client, row.id, {
          imageKey: displayKey || null,
          payloadMerged: mergedPayload,
          name,
          price,
          description,
          isActive,
        });

        await client.query("COMMIT");
        return row;
      } catch (err) {
        await client.query("ROLLBACK");
        throw err;
      }
    });

    const signed = await withSignedProduct(createdRow, { includeKeys: true });
    return res.json({ success: true, product: signed });
  } catch (e) {
    if (uploadedDisplayKey) await deleteSupabaseKey(uploadedDisplayKey);
    for (const k of uploadedGalleryKeys) await deleteSupabaseKey(k);

    logError("products.create_failed", { rid: req.rid || "-", message: String(e?.message || e).slice(0, 900) });
    return res.status(500).json({ success: false, message: IS_PROD ? "Create product failed" : `Create product failed: ${String(e?.message || e)}` });
  }
});

// UPDATE: accepts optional new display image (image) + append gallery (images[])
app.put(
  "/admin/products/:id",
  writeLimiter,
  requireAdmin,
  requireCsrf,
  uploadProductMedia,
  validate(ProductIdParamSchema, "params"),
  validate(UpdateProductSchema),
  async (req, res) => {
    let newDisplayKey = "";
    let appendedGalleryKeys = [];

    try {
      await ensureCapsLoaded("products");
      const id = String(req.params.id);

      const mainFile = req.files?.image?.[0] || null;
      const galleryFiles = Array.isArray(req.files?.images) ? req.files.images : [];

      const updatedRow = await withDbClient(async (client) => {
        await client.query("BEGIN");
        try {
          const cur = await client.query(`SELECT * FROM products WHERE id=$1 LIMIT 1`, [id]);
          if (!cur.rows.length) { await client.query("ROLLBACK"); return null; }
          const existing = cur.rows[0];

          const existingPayload = getRowPayload(existing);
          const existingDisplayKey = extractDisplayKey(existing);
          const existingDetailKey = getDetailKey(existing);
          const existingGalleryKeys = getGalleryKeys(existing);

          const name = req.body?.name === undefined ? String(existing.name || "").trim() : String(req.body.name || "").trim();
          const price = req.body?.price === undefined ? Math.max(0, Math.round(Number(existing.price || 0))) : Math.max(0, Math.round(Number(req.body.price)));
          const description = req.body?.description === undefined ? String(existing.description || "").trim() : String(req.body.description || "").trim();
          const isActive = req.body?.is_active === undefined ? Boolean(existing.is_active) : String(req.body.is_active).toLowerCase() !== "false";

          const removeDisplay = String(req.body?.remove_image || "").toLowerCase() === "true";

          let displayKey = existingDisplayKey;
          let detailKey = existingDetailKey;
          let galleryKeys = existingGalleryKeys.slice();

          // Remove display
          if (removeDisplay && displayKey) {
            await deleteSupabaseKey(displayKey);
            displayKey = "";
            if (detailKey === existingDisplayKey) detailKey = "";
          }

          // New display uploaded?
          if (mainFile?.buffer) {
            const up = await uploadProductImageToSupabase({
              buffer: mainFile.buffer,
              originalName: mainFile.originalname,
              productId: id,
            });
            newDisplayKey = up.key;

            // ✅ Keep old display by moving it into gallery (DO NOT delete it)
            if (displayKey && displayKey !== newDisplayKey) {
              if (!galleryKeys.includes(displayKey)) galleryKeys.unshift(displayKey);
            }
            displayKey = newDisplayKey;
          }

          // Append new gallery uploads
          const newKeys = [];
          for (const f of galleryFiles) {
            if (!f?.buffer) continue;
            const up = await uploadProductImageToSupabase({
              buffer: f.buffer,
              originalName: f.originalname,
              productId: id,
            });
            newKeys.push(up.key);
          }
          appendedGalleryKeys = appendedGalleryKeys.concat(newKeys);

          if (newKeys.length) {
            for (const k of newKeys) {
              if (k !== displayKey && !galleryKeys.includes(k)) galleryKeys.push(k);
            }
          }

          // Ensure detailKey valid; default to displayKey
          const validKeys = new Set(uniqueArr([displayKey, ...galleryKeys]));
          if (!detailKey || !validKeys.has(detailKey)) detailKey = displayKey || "";

          const payloadMerged = {
            ...existingPayload,
            ...req.body,
            __image_key: displayKey || "",
            __gallery_keys: galleryKeys,
            __detail_image_key: detailKey || "",
          };

          const row = await updateProductRow(client, id, {
            name,
            price,
            description,
            imageKey: displayKey || null,
            isActive,
            payloadMerged,
          });

          await client.query("COMMIT");
          return row;
        } catch (err) {
          await client.query("ROLLBACK");
          throw err;
        }
      });

      if (!updatedRow) return res.status(404).json({ success: false, message: "Product not found" });

      const signed = await withSignedProduct(updatedRow, { includeKeys: true });
      return res.json({ success: true, product: signed });
    } catch (e) {
      // Cleanup only the NEW uploads if anything failed
      if (newDisplayKey) await deleteSupabaseKey(newDisplayKey);
      for (const k of appendedGalleryKeys) await deleteSupabaseKey(k);

      logError("products.update_failed", { rid: req.rid || "-", message: String(e?.message || e).slice(0, 900) });
      return res.status(500).json({ success: false, message: IS_PROD ? "Update product failed" : `Update product failed: ${String(e?.message || e)}` });
    }
  }
);

/* ===================== SELECT WHICH IMAGE SHOWS WHERE ===================== */
const SetImageKeySchema = z.object({ key: zNonEmpty("Missing key").max(500) });

// Set DISPLAY image (products page)
app.post(
  "/admin/products/:id/display-image",
  writeLimiter,
  requireAdmin,
  requireCsrf,
  validate(ProductIdParamSchema, "params"),
  validate(SetImageKeySchema),
  async (req, res) => {
    try {
      await ensureCapsLoaded("products");
      const id = String(req.params.id);
      const chosen = String(req.body.key || "").trim();

      const updated = await withDbClient(async (client) => {
        await client.query("BEGIN");
        const cur = await client.query(`SELECT * FROM products WHERE id=$1 LIMIT 1`, [id]);
        if (!cur.rows.length) { await client.query("ROLLBACK"); return null; }
        const row = cur.rows[0];

        const payload = getRowPayload(row);
        const oldDisplay = extractDisplayKey(row);
        const detailKey = getDetailKey(row);
        const gallery = getGalleryKeys(row);

        const valid = new Set(uniqueArr([oldDisplay, ...gallery]));
        if (!valid.has(chosen)) {
          await client.query("ROLLBACK");
          return { err: "Key not found on this product" };
        }

        // remove chosen from gallery; move old display into gallery
        let nextGallery = gallery.filter((k) => k !== chosen);
        if (oldDisplay && oldDisplay !== chosen && !nextGallery.includes(oldDisplay)) nextGallery.unshift(oldDisplay);

        // keep existing detail if valid; else default to chosen
        let nextDetail = detailKey || "";
        const nextValid = new Set(uniqueArr([chosen, ...nextGallery]));
        if (!nextDetail || !nextValid.has(nextDetail)) nextDetail = chosen;

        const merged = {
          ...payload,
          __image_key: chosen,
          __gallery_keys: nextGallery,
          __detail_image_key: nextDetail,
        };

        const upd = await updateProductRow(client, id, {
          imageKey: chosen,
          payloadMerged: merged,
        });

        await client.query("COMMIT");
        return upd;
      });

      if (!updated) return res.status(404).json({ success: false, message: "Product not found" });
      if (updated.err) return res.status(400).json({ success: false, message: updated.err });

      const signed = await withSignedProduct(updated, { includeKeys: true });
      return res.json({ success: true, product: signed });
    } catch (e) {
      logError("products.set_display_failed", { rid: req.rid || "-", message: String(e?.message || e).slice(0, 900) });
      return res.status(500).json({ success: false, message: "Failed to set display image" });
    }
  }
);

// Set DETAIL image (product-details hero)
app.post(
  "/admin/products/:id/detail-image",
  writeLimiter,
  requireAdmin,
  requireCsrf,
  validate(ProductIdParamSchema, "params"),
  validate(SetImageKeySchema),
  async (req, res) => {
    try {
      await ensureCapsLoaded("products");
      const id = String(req.params.id);
      const chosen = String(req.body.key || "").trim();

      const updated = await withDbClient(async (client) => {
        await client.query("BEGIN");
        const cur = await client.query(`SELECT * FROM products WHERE id=$1 LIMIT 1`, [id]);
        if (!cur.rows.length) { await client.query("ROLLBACK"); return null; }
        const row = cur.rows[0];

        const payload = getRowPayload(row);
        const displayKey = extractDisplayKey(row);
        const gallery = getGalleryKeys(row);

        const valid = new Set(uniqueArr([displayKey, ...gallery]));
        if (!valid.has(chosen)) {
          await client.query("ROLLBACK");
          return { err: "Key not found on this product" };
        }

        const merged = { ...payload, __detail_image_key: chosen };
        const upd = await updateProductRow(client, id, { payloadMerged: merged });

        await client.query("COMMIT");
        return upd;
      });

      if (!updated) return res.status(404).json({ success: false, message: "Product not found" });
      if (updated.err) return res.status(400).json({ success: false, message: updated.err });

      const signed = await withSignedProduct(updated, { includeKeys: true });
      return res.json({ success: true, product: signed });
    } catch (e) {
      logError("products.set_detail_failed", { rid: req.rid || "-", message: String(e?.message || e).slice(0, 900) });
      return res.status(500).json({ success: false, message: "Failed to set detail image" });
    }
  }
);

// Remove ONE gallery image (does NOT remove display here)
app.post(
  "/admin/products/:id/images/remove",
  writeLimiter,
  requireAdmin,
  requireCsrf,
  validate(ProductIdParamSchema, "params"),
  validate(SetImageKeySchema),
  async (req, res) => {
    try {
      await ensureCapsLoaded("products");
      const id = String(req.params.id);
      const key = String(req.body.key || "").trim();

      const updated = await withDbClient(async (client) => {
        await client.query("BEGIN");
        const cur = await client.query(`SELECT * FROM products WHERE id=$1 LIMIT 1`, [id]);
        if (!cur.rows.length) { await client.query("ROLLBACK"); return null; }
        const row = cur.rows[0];

        const payload = getRowPayload(row);
        const displayKey = extractDisplayKey(row);

        if (key === displayKey) {
          await client.query("ROLLBACK");
          return { err: "This is the DISPLAY image. Set another display first or use remove_image." };
        }

        const gallery = getGalleryKeys(row);
        const nextGallery = gallery.filter((k) => k !== key);

        await deleteSupabaseKey(key);

        let detailKey = getDetailKey(row);
        const valid = new Set(uniqueArr([displayKey, ...nextGallery]));
        if (!detailKey || !valid.has(detailKey)) detailKey = displayKey || "";

        const merged = {
          ...payload,
          __gallery_keys: nextGallery,
          __detail_image_key: detailKey,
          __image_key: displayKey || "",
        };

        const upd = await updateProductRow(client, id, { payloadMerged: merged });
        await client.query("COMMIT");
        return upd;
      });

      if (!updated) return res.status(404).json({ success: false, message: "Product not found" });
      if (updated.err) return res.status(400).json({ success: false, message: updated.err });

      const signed = await withSignedProduct(updated, { includeKeys: true });
      return res.json({ success: true, product: signed });
    } catch (e) {
      logError("products.gallery_remove_failed", { rid: req.rid || "-", message: String(e?.message || e).slice(0, 900) });
      return res.status(500).json({ success: false, message: "Failed to remove image" });
    }
  }
);

// Delete product (deletes display + gallery + detail if unique)
app.delete(
  "/admin/products/:id",
  writeLimiter,
  requireAdmin,
  requireCsrf,
  validate(ProductIdParamSchema, "params"),
  async (req, res) => {
    try {
      await ensureCapsLoaded("products");
      const id = String(req.params.id);

      const cur = await dbQuery(`SELECT * FROM products WHERE id=$1 LIMIT 1`, [id]);
      if (!cur.rows.length) return res.status(404).json({ success: false, message: "Product not found" });

      const row = cur.rows[0];
      const displayKey = extractDisplayKey(row);
      const detailKey = getDetailKey(row);
      const gallery = getGalleryKeys(row);

      const keysToDelete = uniqueArr([displayKey, detailKey, ...gallery]);
      for (const k of keysToDelete) await deleteSupabaseKey(k);

      const out = await dbQuery(`DELETE FROM products WHERE id=$1 RETURNING id`, [id]);
      if (!out.rows.length) return res.status(404).json({ success: false, message: "Product not found" });

      res.json({ success: true });
    } catch (e) {
      logError("products.delete_failed", { rid: req.rid || "-", message: String(e?.message || e).slice(0, 600) });
      res.status(500).json({ success: false, message: "Delete failed" });
    }
  }
);

/* ===================== FEATURED IMAGES (HOMEPAGE) ===================== */
async function withSignedFeatured(row, { includeKeys = false } = {}) {
  const r = { ...row };
  const key = String(row?.image_key || "").trim();
  r.image_url = "";
  if (key) {
    try { r.image_url = await signKey(key); } catch { r.image_url = ""; }
  }
  if (includeKeys) r.image_key = key;
  return r;
}

const FeaturedIdParamSchema = z.object({ id: z.coerce.number().int().positive("Invalid id") });

const FeaturedCreateSchema = z.object({
  title: z.string().trim().max(140).optional().default(""),
  link_url: z.string().trim().max(500).optional().default(""),
  sort_order: z.coerce.number().int().min(0).max(9999).optional().default(0),
  is_active: z.string().optional(),
}).passthrough();

const FeaturedUpdateSchema = z.object({
  title: z.string().trim().max(140).optional(),
  link_url: z.string().trim().max(500).optional(),
  sort_order: z.coerce.number().int().min(0).max(9999).optional(),
  is_active: z.string().optional(),
  remove_image: z.string().optional(),
}).passthrough();

// PUBLIC
app.get("/api/featured", async (req, res) => {
  try {
    const r = await dbQuery(
      `SELECT * FROM homepage_featured
       WHERE is_active=true
       ORDER BY sort_order ASC, updated_at DESC`
    );
    const items = await Promise.all(r.rows.map((x) => withSignedFeatured(x, { includeKeys: false })));
    return res.json({ ok: true, items });
  } catch (e) {
    logError("featured.public_list_failed", { rid: req.rid || "-", message: String(e?.message || e).slice(0, 600) });
    return res.json({ ok: true, items: [] });
  }
});

// ADMIN list
app.get("/admin/featured", requireAdmin, async (req, res) => {
  try {
    const r = await dbQuery(`SELECT * FROM homepage_featured ORDER BY sort_order ASC, updated_at DESC`);
    const items = await Promise.all(r.rows.map((x) => withSignedFeatured(x, { includeKeys: true })));
    return res.json({ success: true, items });
  } catch (e) {
    logError("featured.admin_list_failed", { rid: req.rid || "-", message: String(e?.message || e).slice(0, 600) });
    return res.status(500).json({ success: false, items: [] });
  }
});

// ADMIN create (multipart: image)
app.post("/admin/featured", writeLimiter, requireAdmin, requireCsrf, upload.single("image"), validate(FeaturedCreateSchema), async (req, res) => {
  let uploadedKey = "";
  try {
    const title = String(req.body.title || "").trim();
    const linkUrl = String(req.body.link_url || "").trim();
    const sortOrder = Math.max(0, Math.round(Number(req.body.sort_order || 0)));
    const isActive = String(req.body.is_active || "true").toLowerCase() !== "false";
    const payload = { ...req.body };

    const ins = await dbQuery(
      `INSERT INTO homepage_featured (title, link_url, sort_order, is_active, payload)
       VALUES ($1,$2,$3,$4,$5)
       RETURNING *`,
      [title, linkUrl, sortOrder, isActive, payload]
    );

    let row = ins.rows[0];

    if (req.file?.buffer) {
      const up = await uploadFeaturedImageToSupabase({
        buffer: req.file.buffer,
        originalName: req.file.originalname,
        featuredId: row.id,
      });
      uploadedKey = up.key;

      const upd = await dbQuery(
        `UPDATE homepage_featured
         SET image_key=$1, updated_at=NOW(), payload=$2
         WHERE id=$3
         RETURNING *`,
        [uploadedKey, { ...payload, __image_key: uploadedKey }, row.id]
      );

      row = upd.rows[0] || row;
    }

    const signed = await withSignedFeatured(row, { includeKeys: true });
    return res.json({ success: true, item: signed });
  } catch (e) {
    if (uploadedKey) await deleteSupabaseKey(uploadedKey);
    logError("featured.create_failed", { rid: req.rid || "-", message: String(e?.message || e).slice(0, 900) });
    return res.status(500).json({ success: false, message: "Create featured failed" });
  }
});

// ADMIN update (optional new image)
app.put(
  "/admin/featured/:id",
  writeLimiter,
  requireAdmin,
  requireCsrf,
  upload.single("image"),
  validate(FeaturedIdParamSchema, "params"),
  validate(FeaturedUpdateSchema),
  async (req, res) => {
    let newKey = "";
    try {
      const id = Number(req.params.id);
      const cur = await dbQuery(`SELECT * FROM homepage_featured WHERE id=$1 LIMIT 1`, [id]);
      if (!cur.rows.length) return res.status(404).json({ success: false, message: "Not found" });

      const existing = cur.rows[0];
      const title = req.body.title === undefined ? String(existing.title || "") : String(req.body.title || "");
      const linkUrl = req.body.link_url === undefined ? String(existing.link_url || "") : String(req.body.link_url || "");
      const sortOrder = req.body.sort_order === undefined ? Number(existing.sort_order || 0) : Math.max(0, Math.round(Number(req.body.sort_order)));
      const isActive = req.body.is_active === undefined ? Boolean(existing.is_active) : String(req.body.is_active).toLowerCase() !== "false";

      let imageKey = String(existing.image_key || "").trim();
      const payload = existing.payload && typeof existing.payload === "object" ? { ...existing.payload, ...req.body } : { ...req.body };

      const removeImage = String(req.body.remove_image || "").toLowerCase() === "true";
      if (removeImage && imageKey) { await deleteSupabaseKey(imageKey); imageKey = ""; }

      if (req.file?.buffer) {
        const up = await uploadFeaturedImageToSupabase({
          buffer: req.file.buffer,
          originalName: req.file.originalname,
          featuredId: id,
        });
        newKey = up.key;
        if (imageKey) await deleteSupabaseKey(imageKey);
        imageKey = newKey;
      }

      const upd = await dbQuery(
        `UPDATE homepage_featured
         SET title=$1, link_url=$2, sort_order=$3, is_active=$4, image_key=$5, updated_at=NOW(), payload=$6
         WHERE id=$7
         RETURNING *`,
        [title, linkUrl, sortOrder, isActive, imageKey || null, payload, id]
      );

      const signed = await withSignedFeatured(upd.rows[0], { includeKeys: true });
      return res.json({ success: true, item: signed });
    } catch (e) {
      if (newKey) await deleteSupabaseKey(newKey);
      logError("featured.update_failed", { rid: req.rid || "-", message: String(e?.message || e).slice(0, 900) });
      return res.status(500).json({ success: false, message: "Update featured failed" });
    }
  }
);

// ADMIN delete
app.delete(
  "/admin/featured/:id",
  writeLimiter,
  requireAdmin,
  requireCsrf,
  validate(FeaturedIdParamSchema, "params"),
  async (req, res) => {
    try {
      const id = Number(req.params.id);
      const cur = await dbQuery(`SELECT * FROM homepage_featured WHERE id=$1 LIMIT 1`, [id]);
      if (!cur.rows.length) return res.status(404).json({ success: false, message: "Not found" });

      const key = String(cur.rows[0].image_key || "").trim();
      if (key) await deleteSupabaseKey(key);

      await dbQuery(`DELETE FROM homepage_featured WHERE id=$1`, [id]);
      return res.json({ success: true });
    } catch (e) {
      logError("featured.delete_failed", { rid: req.rid || "-", message: String(e?.message || e).slice(0, 600) });
      return res.status(500).json({ success: false, message: "Delete failed" });
    }
  }
);
/* ===================== HERO SLIDES (HOMEPAGE) ===================== */

const HeroIdParamSchema = z.object({ id: z.coerce.number().int().positive("Invalid id") });

const HeroCreateSchema = z.object({
  title: z.string().trim().max(140).optional().default(""),
  description: z.string().trim().max(500).optional().default(""),
  link_url: z.string().trim().max(500).optional().default(""),
  sort_order: z.coerce.number().int().min(0).max(9999).optional().default(0),
  is_active: z.string().optional(),
}).passthrough();

const HeroUpdateSchema = z.object({
  title: z.string().trim().max(140).optional(),
  description: z.string().trim().max(500).optional(),
  link_url: z.string().trim().max(500).optional(),
  sort_order: z.coerce.number().int().min(0).max(9999).optional(),
  is_active: z.string().optional(),
  remove_image: z.string().optional(),
}).passthrough();

/* ---- PUBLIC hero slides ---- */
app.get("/api/hero", async (req, res) => {
  try {
    const r = await dbQuery(
      `SELECT * FROM homepage_hero
       WHERE is_active=true
       ORDER BY sort_order ASC, updated_at DESC`
    );
    const items = await Promise.all(r.rows.map((x) => withSignedHero(x, { includeKeys: false })));
    return res.json({ ok: true, items });
  } catch (e) {
    logError("hero.public_list_failed", { rid: req.rid || "-", message: String(e?.message || e).slice(0, 600) });
    return res.json({ ok: true, items: [] });
  }
});

/* ---- ADMIN list ---- */
app.get("/admin/hero", requireAdmin, async (req, res) => {
  try {
    const r = await dbQuery(`SELECT * FROM homepage_hero ORDER BY sort_order ASC, updated_at DESC`);
    const items = await Promise.all(r.rows.map((x) => withSignedHero(x, { includeKeys: true })));
    return res.json({ success: true, items });
  } catch (e) {
    logError("hero.admin_list_failed", { rid: req.rid || "-", message: String(e?.message || e).slice(0, 600) });
    return res.status(500).json({ success: false, items: [] });
  }
});

/* ---- ADMIN create (multipart: image) ---- */
app.post(
  "/admin/hero",
  writeLimiter,
  requireAdmin,
  requireCsrf,
  upload.single("image"),
  validate(HeroCreateSchema),
  async (req, res) => {
    let uploadedKey = "";
    try {
      const title = String(req.body.title || "").trim();
      const description = String(req.body.description || "").trim();
      const linkUrl = String(req.body.link_url || "").trim();
      const sortOrder = Math.max(0, Math.round(Number(req.body.sort_order || 0)));
      const isActive = String(req.body.is_active || "true").toLowerCase() !== "false";
      const payload = { ...req.body };

      const ins = await dbQuery(
        `INSERT INTO homepage_hero (title, description, link_url, sort_order, is_active, payload)
         VALUES ($1,$2,$3,$4,$5,$6)
         RETURNING *`,
        [title, description, linkUrl, sortOrder, isActive, payload]
      );

      let row = ins.rows[0];

      if (req.file?.buffer) {
        const up = await uploadHeroImageToSupabase({
          buffer: req.file.buffer,
          originalName: req.file.originalname,
          heroId: row.id,
        });
        uploadedKey = up.key;

        const upd = await dbQuery(
          `UPDATE homepage_hero
           SET image_key=$1, updated_at=NOW(), payload=$2
           WHERE id=$3
           RETURNING *`,
          [uploadedKey, { ...payload, __image_key: uploadedKey }, row.id]
        );

        row = upd.rows[0] || row;
      }

      const signed = await withSignedHero(row, { includeKeys: true });
      return res.json({ success: true, item: signed });
    } catch (e) {
      if (uploadedKey) await deleteSupabaseKey(uploadedKey);
      logError("hero.create_failed", { rid: req.rid || "-", message: String(e?.message || e).slice(0, 900) });
      return res.status(500).json({ success: false, message: "Create hero failed" });
    }
  }
);

/* ---- ADMIN update (optional new image) ---- */
app.put(
  "/admin/hero/:id",
  writeLimiter,
  requireAdmin,
  requireCsrf,
  upload.single("image"),
  validate(HeroIdParamSchema, "params"),
  validate(HeroUpdateSchema),
  async (req, res) => {
    let newKey = "";
    try {
      const id = Number(req.params.id);
      const cur = await dbQuery(`SELECT * FROM homepage_hero WHERE id=$1 LIMIT 1`, [id]);
      if (!cur.rows.length) return res.status(404).json({ success: false, message: "Not found" });

      const existing = cur.rows[0];

      const title = req.body.title === undefined ? String(existing.title || "") : String(req.body.title || "");
      const description = req.body.description === undefined ? String(existing.description || "") : String(req.body.description || "");
      const linkUrl = req.body.link_url === undefined ? String(existing.link_url || "") : String(req.body.link_url || "");
      const sortOrder = req.body.sort_order === undefined ? Number(existing.sort_order || 0) : Math.max(0, Math.round(Number(req.body.sort_order)));
      const isActive = req.body.is_active === undefined ? Boolean(existing.is_active) : String(req.body.is_active).toLowerCase() !== "false";

      let imageKey = String(existing.image_key || "").trim();
      const payload = existing.payload && typeof existing.payload === "object"
        ? { ...existing.payload, ...req.body }
        : { ...req.body };

      const removeImage = String(req.body.remove_image || "").toLowerCase() === "true";
      if (removeImage && imageKey) { await deleteSupabaseKey(imageKey); imageKey = ""; }

      if (req.file?.buffer) {
        const up = await uploadHeroImageToSupabase({
          buffer: req.file.buffer,
          originalName: req.file.originalname,
          heroId: id,
        });
        newKey = up.key;
        if (imageKey) await deleteSupabaseKey(imageKey);
        imageKey = newKey;
      }

      const upd = await dbQuery(
        `UPDATE homepage_hero
         SET title=$1, description=$2, link_url=$3, sort_order=$4, is_active=$5, image_key=$6, updated_at=NOW(), payload=$7
         WHERE id=$8
         RETURNING *`,
        [title, description, linkUrl, sortOrder, isActive, imageKey || null, payload, id]
      );

      const signed = await withSignedHero(upd.rows[0], { includeKeys: true });
      return res.json({ success: true, item: signed });
    } catch (e) {
      if (newKey) await deleteSupabaseKey(newKey);
      logError("hero.update_failed", { rid: req.rid || "-", message: String(e?.message || e).slice(0, 900) });
      return res.status(500).json({ success: false, message: "Update hero failed" });
    }
  }
);

/* ---- ADMIN delete ---- */
app.delete(
  "/admin/hero/:id",
  writeLimiter,
  requireAdmin,
  requireCsrf,
  validate(HeroIdParamSchema, "params"),
  async (req, res) => {
    try {
      const id = Number(req.params.id);
      const cur = await dbQuery(`SELECT * FROM homepage_hero WHERE id=$1 LIMIT 1`, [id]);
      if (!cur.rows.length) return res.status(404).json({ success: false, message: "Not found" });

      const key = String(cur.rows[0].image_key || "").trim();
      if (key) await deleteSupabaseKey(key);

      await dbQuery(`DELETE FROM homepage_hero WHERE id=$1`, [id]);
      return res.json({ success: true });
    } catch (e) {
      logError("hero.delete_failed", { rid: req.rid || "-", message: String(e?.message || e).slice(0, 600) });
      return res.status(500).json({ success: false, message: "Delete failed" });
    }
  }
);

/* ===================== DELIVERY PRICING ===================== */
const DeliveryPricingSchema = z.object({
  defaultFee: z.coerce.number().min(0).optional(),
  updatedAt: z.string().optional(),
  states: z
    .array(
      z.object({
        name: z.string().trim().min(1),
        cities: z
          .array(
            z.object({
              name: z.string().trim().min(1),
              fee: z.coerce.number().min(0),
            })
          )
          .optional()
          .default([]),
      })
    )
    .optional()
    .default([]),
});

const SeedPricingSchema = z.object({ fee: z.coerce.number().min(0).optional() });

function buildDefaultNigeriaPricing(fee = 5000) {
  const FEE = Math.max(0, Math.round(Number(fee) || 0));
  const statesAndCapitals = [
    { name: "Abia", city: "Umuahia" }, { name: "Adamawa", city: "Yola" }, { name: "Akwa Ibom", city: "Uyo" },
    { name: "Anambra", city: "Awka" }, { name: "Bauchi", city: "Bauchi" }, { name: "Bayelsa", city: "Yenagoa" },
    { name: "Benue", city: "Makurdi" }, { name: "Borno", city: "Maiduguri" }, { name: "Cross River", city: "Calabar" },
    { name: "Delta", city: "Asaba" }, { name: "Ebonyi", city: "Abakaliki" }, { name: "Edo", city: "Benin City" },
    { name: "Ekiti", city: "Ado-Ekiti" }, { name: "Enugu", city: "Enugu" }, { name: "FCT", city: "Abuja" },
    { name: "Gombe", city: "Gombe" }, { name: "Imo", city: "Owerri" }, { name: "Jigawa", city: "Dutse" },
    { name: "Kaduna", city: "Kaduna" }, { name: "Kano", city: "Kano" }, { name: "Katsina", city: "Katsina" },
    { name: "Kebbi", city: "Birnin Kebbi" }, { name: "Kogi", city: "Lokoja" }, { name: "Kwara", city: "Ilorin" },
    { name: "Lagos", city: "Ikeja" }, { name: "Nasarawa", city: "Lafia" }, { name: "Niger", city: "Minna" },
    { name: "Ogun", city: "Abeokuta" }, { name: "Ondo", city: "Akure" }, { name: "Osun", city: "Osogbo" },
    { name: "Oyo", city: "Ibadan" }, { name: "Plateau", city: "Jos" }, { name: "Rivers", city: "Port Harcourt" },
    { name: "Sokoto", city: "Sokoto" }, { name: "Taraba", city: "Jalingo" }, { name: "Yobe", city: "Damaturu" },
    { name: "Zamfara", city: "Gusau" },
  ];
  return {
    defaultFee: FEE,
    updatedAt: new Date().toISOString(),
    states: statesAndCapitals
      .map((s) => ({ name: s.name, cities: [{ name: s.city, fee: FEE }] }))
      .sort((a, b) => a.name.localeCompare(b.name)),
  };
}

function sanitizePricing(input) {
  const out = { defaultFee: 5000, updatedAt: new Date().toISOString(), states: [] };
  const def = Number(input?.defaultFee);
  out.defaultFee = Number.isFinite(def) && def >= 0 ? Math.round(def) : 5000;

  const states = Array.isArray(input?.states) ? input.states : [];
  out.states = states
    .map((s) => {
      const name = String(s?.name || "").trim();
      const citiesIn = Array.isArray(s?.cities) ? s.cities : [];
      const cities = citiesIn
        .map((c) => ({
          name: String(c?.name || "").trim(),
          fee: Math.round(Number(c?.fee)),
        }))
        .filter((c) => c.name && Number.isFinite(c.fee) && c.fee >= 0);
      return { name, cities };
    })
    .filter((s) => s.name);

  out.states.sort((a, b) => a.name.localeCompare(b.name));
  out.states.forEach((s) => s.cities.sort((a, b) => a.name.localeCompare(b.name)));
  return out;
}

async function getPricing() {
  const r = await dbQuery(`SELECT default_fee, updated_at, data FROM delivery_pricing WHERE id = 1`);
  if (!r.rows.length) {
    const seeded = buildDefaultNigeriaPricing(5000);
    await dbQuery(`INSERT INTO delivery_pricing (id, default_fee, updated_at, data) VALUES (1, $1, NOW(), $2)`, [
      seeded.defaultFee,
      seeded,
    ]);
    return seeded;
  }
  const row = r.rows[0];
  const obj = row.data && typeof row.data === "object" ? row.data : {};
  return {
    defaultFee: Number(row.default_fee) || 5000,
    updatedAt: row.updated_at ? new Date(row.updated_at).toISOString() : new Date().toISOString(),
    states: Array.isArray(obj.states) ? obj.states : [],
  };
}

app.get("/delivery-pricing", async (req, res) => {
  try {
    const pricing = await getPricing();
    res.json(pricing);
  } catch (e) {
    logError("pricing.get_failed", { rid: req.rid || "-", message: String(e?.message || e).slice(0, 600) });
    res.status(500).json(buildDefaultNigeriaPricing(5000));
  }
});

app.get("/admin/delivery-pricing", requireAdmin, async (req, res) => {
  try {
    const pricing = await getPricing();
    res.json({ success: true, pricing });
  } catch (e) {
    logError("pricing.admin_get_failed", { rid: req.rid || "-", message: String(e?.message || e).slice(0, 600) });
    res.status(500).json({ success: false, pricing: buildDefaultNigeriaPricing(5000) });
  }
});

app.put(
  "/admin/delivery-pricing",
  writeLimiter,
  requireAdmin,
  requireCsrf,
  validate(DeliveryPricingSchema),
  async (req, res) => {
    try {
      const cleaned = sanitizePricing(req.body);
      cleaned.updatedAt = new Date().toISOString();

      await dbQuery(`UPDATE delivery_pricing SET default_fee=$1, updated_at=NOW(), data=$2 WHERE id=1`, [
        cleaned.defaultFee,
        cleaned,
      ]);

      res.json({ success: true, pricing: cleaned });
    } catch (e) {
      logError("pricing.admin_put_failed", { rid: req.rid || "-", message: String(e?.message || e).slice(0, 600) });
      res.status(500).json({ success: false, message: "Failed to update pricing" });
    }
  }
);

app.post(
  "/admin/delivery-pricing/seed",
  writeLimiter,
  requireAdmin,
  requireCsrf,
  validate(SeedPricingSchema),
  async (req, res) => {
    try {
      const fee = Number(req.body?.fee);
      const seedFee = Number.isFinite(fee) && fee >= 0 ? Math.round(fee) : 5000;

      const seeded = buildDefaultNigeriaPricing(seedFee);
      seeded.updatedAt = new Date().toISOString();

      await dbQuery(`UPDATE delivery_pricing SET default_fee=$1, updated_at=NOW(), data=$2 WHERE id=1`, [
        seeded.defaultFee,
        seeded,
      ]);

      res.json({ success: true, pricing: seeded });
    } catch (e) {
      logError("pricing.seed_failed", { rid: req.rid || "-", message: String(e?.message || e).slice(0, 600) });
      res.status(500).json({ success: false, message: "Failed to seed pricing" });
    }
  }
);

/* ===================== ORDERS (PUBLIC + ADMIN) ===================== */
const IdParamSchema = z.object({ id: z.coerce.number().int().positive("Invalid id") });

const CartItemSchema = z.object({
  id: z.union([z.string(), z.number()]).optional(),
  name: zNonEmpty("Item name required").max(250),
  price: z.coerce.number().min(0),
  qty: z.coerce.number().int().min(1),
  image: z.string().optional().nullable(),
  total: z.coerce.number().min(0).optional(),
}).passthrough();

const OrdersSchema = z.object({
  reference: zNonEmpty("Missing reference").max(200),
  name: zNonEmpty("Missing name").max(120),
  email: zEmail,
  phone: zNonEmpty("Missing phone").max(30),
  shippingType: z.enum(["pickup", "delivery"]),
  state: z.string().optional().default(""),
  city: z.string().optional().default(""),
  address: z.string().optional().default(""),
  cart: z.array(CartItemSchema).min(1, "Cart is empty"),
  subtotal: z.coerce.number().min(0),
  deliveryFee: z.coerce.number().min(0),
  total: z.coerce.number().min(0),
  status: z.string().optional().default("Pending"),
  paystackRef: z.string().optional().default(""),
  createdAt: zISODateStr,
  paidAt: z.string().optional(),
  amountPaid: z.coerce.number().optional(),
}).superRefine((data, ctx) => {
  if (data.shippingType === "delivery") {
    if (!String(data.state || "").trim()) ctx.addIssue({ code: "custom", path: ["state"], message: "State is required for delivery" });
    if (!String(data.city || "").trim()) ctx.addIssue({ code: "custom", path: ["city"], message: "City/LGA is required for delivery" });
    if (!String(data.address || "").trim()) ctx.addIssue({ code: "custom", path: ["address"], message: "Address is required for delivery" });
  }
});

async function insertOrderIdempotent(reference, status, payload) {
  const ins = await dbQuery(
    `INSERT INTO orders (reference, status, payload)
     VALUES ($1,$2,$3)
     ON CONFLICT (reference) DO NOTHING
     RETURNING *`,
    [reference, status, payload]
  );
  if (ins.rows.length) return ins.rows[0];
  const sel = await dbQuery(`SELECT * FROM orders WHERE reference=$1 LIMIT 1`, [reference]);
  return sel.rows[0] || null;
}

app.get("/orders/public/:reference", async (req, res) => {
  try {
    const ref = String(req.params.reference || "").trim();
    if (!ref) return res.status(400).json({ ok: false, message: "Missing reference" });

    const r = await dbQuery(`SELECT reference, status, payload, created_at FROM orders WHERE reference=$1 LIMIT 1`, [ref]);
    if (!r.rows.length) return res.status(404).json({ ok: false, message: "Not found" });

    const row = r.rows[0];
    const payload = row.payload && typeof row.payload === "object" ? row.payload : {};

    return res.json({
      ok: true,
      order: {
        reference: row.reference,
        status: String(row.status || payload.status || "Pending"),
        name: payload.name || "",
        email: payload.email || "",
        phone: payload.phone || "",
        shippingType: payload.shippingType || "",
        state: payload.state || "",
        city: payload.city || "",
        address: payload.address || "",
        cart: Array.isArray(payload.cart) ? payload.cart : [],
        subtotal: Number(payload.subtotal || 0),
        deliveryFee: Number(payload.deliveryFee || 0),
        total: Number(payload.total || 0),
        createdAt: payload.createdAt || (row.created_at ? new Date(row.created_at).toISOString() : null),
        paidAt: payload.paidAt || null,
        amountPaid: payload.amountPaid || null,
      },
    });
  } catch (e) {
    logError("orders.public_get_failed", { rid: req.rid || "-", message: String(e?.message || e).slice(0, 600) });
    return res.status(500).json({ ok: false, message: "Server error" });
  }
});

app.post("/orders", writeLimiter, validate(OrdersSchema), async (req, res) => {
  try {
    const payload = req.body;
    const reference = String(payload.reference || payload.paystackRef || "").trim();
    if (!reference) return res.status(400).json({ success: false, message: "Missing reference" });

    payload.status = "Pending";
    const row = await insertOrderIdempotent(reference, "Pending", payload);
    return res.json({ success: true, order: row });
  } catch (err) {
    logError("orders.create_failed", { rid: req.rid || "-", message: String(err?.message || err).slice(0, 600) });
    res.status(500).json({ success: false, message: "Failed to save order" });
  }
});

/* ===================== ORDERS (ADMIN - COMPAT ROUTES) ===================== */

// Accept many payload shapes from different frontend versions
const AdminOrderStatusSchema = z.object({
  status: z.string().trim().min(1).max(40).optional(),
  newStatus: z.string().trim().min(1).max(40).optional(),
  value: z.string().trim().min(1).max(40).optional(),

  id: z.coerce.number().int().positive().optional(),
  orderId: z.coerce.number().int().positive().optional(),
  order_id: z.coerce.number().int().positive().optional(),

  reference: z.string().trim().min(1).max(200).optional(),
}).passthrough();

function pickStatusFromBody(body) {
  const b = body || {};
  const s =
    b.status ??
    b.newStatus ??
    b.value ??
    b.orderStatus ??
    b.order_status ??
    b.state;
  return String(s || "").trim();
}

function pickIdFromBody(body) {
  const b = body || {};
  const id = b.id ?? b.orderId ?? b.order_id;
  const n = Number(id);
  return Number.isFinite(n) && n > 0 ? Math.trunc(n) : null;
}

function pickReferenceFromBody(body) {
  const b = body || {};
  const r = b.reference ?? b.ref ?? b.paystackRef;
  const s = String(r || "").trim();
  return s ? s : null;
}

function mergePayloadStatus(row, status) {
  const payload = row?.payload && typeof row.payload === "object" ? { ...row.payload } : {};
  payload.status = status;
  payload.updatedAt = new Date().toISOString();
  return payload;
}

async function updateOrderStatusById(id, status) {
  const cur = await dbQuery(`SELECT * FROM orders WHERE id=$1 LIMIT 1`, [id]);
  if (!cur.rows.length) return null;

  const row = cur.rows[0];
  const payload = mergePayloadStatus(row, status);

  const upd = await dbQuery(
    `UPDATE orders SET status=$1, payload=$2 WHERE id=$3 RETURNING *`,
    [status, payload, id]
  );
  return upd.rows[0] || null;
}

async function updateOrderStatusByReference(reference, status) {
  const cur = await dbQuery(`SELECT * FROM orders WHERE reference=$1 LIMIT 1`, [reference]);
  if (!cur.rows.length) return null;

  const row = cur.rows[0];
  const payload = mergePayloadStatus(row, status);

  const upd = await dbQuery(
    `UPDATE orders SET status=$1, payload=$2 WHERE reference=$3 RETURNING *`,
    [status, payload, reference]
  );
  return upd.rows[0] || null;
}

// ✅ Keep list routes (compat: some frontends expect raw array)
app.get("/admin/orders", requireAdmin, async (req, res) => {
  try {
    const out = await dbQuery(`SELECT * FROM orders ORDER BY created_at DESC`);
    res.json(out.rows);
  } catch {
    res.status(500).json([]);
  }
});
app.get("/admin/orders/list", requireAdmin, async (req, res) => {
  try {
    const out = await dbQuery(`SELECT * FROM orders ORDER BY created_at DESC`);
    res.json(out.rows);
  } catch {
    res.status(500).json([]);
  }
});

// ✅ NEW: get single order (fixes GET /admin/orders/11 404)
app.get("/admin/orders/:id", requireAdmin, validate(IdParamSchema, "params"), async (req, res) => {
  try {
    const id = Number(req.params.id);
    const r = await dbQuery(`SELECT * FROM orders WHERE id=$1 LIMIT 1`, [id]);
    if (!r.rows.length) return res.status(404).json({ success: false, ok: false, message: "Order not found" });
    return res.json({ success: true, ok: true, order: r.rows[0] });
  } catch (e) {
    logError("orders.admin_get_failed", { rid: req.rid || "-", message: String(e?.message || e).slice(0, 600) });
    return res.status(500).json({ success: false, ok: false, message: "Server error" });
  }
});

// ✅ NEW: update status by id (fixes PUT /admin/orders/11/status 404)
async function handleUpdateById(req, res) {
  const id = Number(req.params.id);
  const status = pickStatusFromBody(req.body);
  if (!status) return res.status(400).json({ success: false, ok: false, message: "Missing status" });

  const updated = await updateOrderStatusById(id, status);
  if (!updated) return res.status(404).json({ success: false, ok: false, message: "Order not found" });

  return res.json({ success: true, ok: true, order: updated });
}

app.put(
  "/admin/orders/:id/status",
  writeLimiter,
  requireAdmin,
  requireCsrf,
  validate(IdParamSchema, "params"),
  validate(AdminOrderStatusSchema),
  async (req, res) => {
    try { return await handleUpdateById(req, res); }
    catch (e) {
      logError("orders.admin_status_put_failed", { rid: req.rid || "-", message: String(e?.message || e).slice(0, 600) });
      return res.status(500).json({ success: false, ok: false, message: "Failed to update status" });
    }
  }
);

app.patch(
  "/admin/orders/:id/status",
  writeLimiter,
  requireAdmin,
  requireCsrf,
  validate(IdParamSchema, "params"),
  validate(AdminOrderStatusSchema),
  async (req, res) => {
    try { return await handleUpdateById(req, res); }
    catch (e) {
      logError("orders.admin_status_patch_failed", { rid: req.rid || "-", message: String(e?.message || e).slice(0, 600) });
      return res.status(500).json({ success: false, ok: false, message: "Failed to update status" });
    }
  }
);

// ✅ NEW: update via PUT /admin/orders/:id (fixes PUT /admin/orders/13 404)
app.put(
  "/admin/orders/:id",
  writeLimiter,
  requireAdmin,
  requireCsrf,
  validate(IdParamSchema, "params"),
  validate(AdminOrderStatusSchema),
  async (req, res) => {
    try { return await handleUpdateById(req, res); }
    catch (e) {
      logError("orders.admin_put_failed", { rid: req.rid || "-", message: String(e?.message || e).slice(0, 600) });
      return res.status(500).json({ success: false, ok: false, message: "Failed to update order" });
    }
  }
);

app.patch(
  "/admin/orders/:id",
  writeLimiter,
  requireAdmin,
  requireCsrf,
  validate(IdParamSchema, "params"),
  validate(AdminOrderStatusSchema),
  async (req, res) => {
    try { return await handleUpdateById(req, res); }
    catch (e) {
      logError("orders.admin_patch_failed", { rid: req.rid || "-", message: String(e?.message || e).slice(0, 600) });
      return res.status(500).json({ success: false, ok: false, message: "Failed to update order" });
    }
  }
);

// ✅ NEW: compat route (fixes PUT /admin/orders/status 404)
// Supports body: {id,status} OR {reference,status}
async function handleUpdateCompat(req, res) {
  const status = pickStatusFromBody(req.body);
  if (!status) return res.status(400).json({ success: false, ok: false, message: "Missing status" });

  const id = pickIdFromBody(req.body);
  const reference = pickReferenceFromBody(req.body);

  let updated = null;
  if (id) updated = await updateOrderStatusById(id, status);
  else if (reference) updated = await updateOrderStatusByReference(reference, status);

  if (!updated) return res.status(404).json({ success: false, ok: false, message: "Order not found (provide id or reference)" });

  return res.json({ success: true, ok: true, order: updated });
}

app.put(
  "/admin/orders/status",
  writeLimiter,
  requireAdmin,
  requireCsrf,
  validate(AdminOrderStatusSchema),
  async (req, res) => {
    try { return await handleUpdateCompat(req, res); }
    catch (e) {
      logError("orders.admin_compat_put_failed", { rid: req.rid || "-", message: String(e?.message || e).slice(0, 600) });
      return res.status(500).json({ success: false, ok: false, message: "Failed to update status" });
    }
  }
);

app.patch(
  "/admin/orders/status",
  writeLimiter,
  requireAdmin,
  requireCsrf,
  validate(AdminOrderStatusSchema),
  async (req, res) => {
    try { return await handleUpdateCompat(req, res); }
    catch (e) {
      logError("orders.admin_compat_patch_failed", { rid: req.rid || "-", message: String(e?.message || e).slice(0, 600) });
      return res.status(500).json({ success: false, ok: false, message: "Failed to update status" });
    }
  }
);

// Some old frontends use POST instead of PUT:
app.post(
  "/admin/orders/status",
  writeLimiter,
  requireAdmin,
  requireCsrf,
  validate(AdminOrderStatusSchema),
  async (req, res) => {
    try { return await handleUpdateCompat(req, res); }
    catch (e) {
      logError("orders.admin_compat_post_failed", { rid: req.rid || "-", message: String(e?.message || e).slice(0, 600) });
      return res.status(500).json({ success: false, ok: false, message: "Failed to update status" });
    }
  }
);

/* ===================== CAPTCHA (HCAPTCHA) ===================== */
const HCAPTCHA_SECRET_KEY = process.env.HCAPTCHA_SECRET_KEY || "";
const CAPTCHA_REQUIRED = String(process.env.CAPTCHA_REQUIRED || "true").toLowerCase() !== "false";

async function verifyHCaptchaToken(token, ip) {
  if (!CAPTCHA_REQUIRED) return true;
  if (!HCAPTCHA_SECRET_KEY) return false;
  if (!token) return false;

  const f = await ensureFetch();
  if (!f) throw new Error("fetch not available (captcha verify)");

  const form = new URLSearchParams();
  form.append("secret", String(HCAPTCHA_SECRET_KEY));
  form.append("response", String(token));
  if (ip) form.append("remoteip", String(ip));

  const r = await f("https://hcaptcha.com/siteverify", {
    method: "POST",
    headers: { "Content-Type": "application/x-www-form-urlencoded" },
    body: form.toString(),
  });
  const data = await r.json().catch(() => null);
  return Boolean(data?.success);
}

/* ===================== CONTACT + NEWSLETTER + MESSAGES ===================== */
const GMAIL_USER = process.env.GMAIL_USER || "";
const GMAIL_APP_PASS = process.env.GMAIL_APP_PASS || "";
const transporter =
  GMAIL_USER && GMAIL_APP_PASS
    ? nodemailer.createTransport({ service: "gmail", auth: { user: GMAIL_USER, pass: GMAIL_APP_PASS } })
    : null;

const ContactSchema = z.object({
  name: zNonEmpty("Name is required").max(120),
  email: zEmail,
  message: zNonEmpty("Message is required").max(5000),
  captchaToken: z.string().optional(),
});

app.post("/api/contact", writeLimiter, validate(ContactSchema), async (req, res) => {
  try {
    await ensureCapsLoaded("messages");
    const ip = getClientIp(req);

    const okCaptcha = await verifyHCaptchaToken(req.body.captchaToken, ip);
    if (!okCaptcha) return res.status(400).json({ success: false, msg: "Captcha failed. Try again." });

    const { name, email, message } = req.body;

    try {
      await dbQuery(`INSERT INTO messages (name, email, message, created_at) VALUES ($1,$2,$3,$4)`, [
        String(name), String(email), String(message), new Date(),
      ]);
    } catch {
      const fallbackId = Math.floor(Date.now() / 1000);
      await dbQuery(`INSERT INTO messages (id, name, email, message, created_at) VALUES ($1,$2,$3,$4,$5)`, [
        fallbackId, String(name), String(email), String(message), new Date(),
      ]);
    }

    if (transporter) {
      await transporter.sendMail({
        from: GMAIL_USER,
        replyTo: email,
        to: GMAIL_USER,
        subject: `New Contact from ${name}`,
        text: `Name: ${name}\nEmail: ${email}\n\nMessage:\n${message}`,
      });
    }

    res.json({ success: true, msg: "Message received — we will reply soon!" });
  } catch (err) {
    logError("contact.failed", { rid: req.rid || "-", message: String(err?.message || err).slice(0, 600) });
    res.status(500).json({ success: false, msg: "Server error" });
  }
});

const NewsletterSchema = z.object({
  email: zEmail,
  captchaToken: z.string().optional(),
});

app.post("/api/newsletter/subscribe", writeLimiter, validate(NewsletterSchema), async (req, res) => {
  try {
    await ensureCapsLoaded("newsletter_subscribers");
    const ip = getClientIp(req);

    const okCaptcha = await verifyHCaptchaToken(req.body.captchaToken, ip);
    if (!okCaptcha) return res.status(400).json({ ok: false, message: "Captcha failed. Try again." });

    const emailRaw = req.body.email;
    const exists = await dbQuery(`SELECT 1 FROM newsletter_subscribers WHERE email=$1`, [emailRaw]);
    const already = exists.rows.length > 0;

    if (!already) {
      try {
        await dbQuery(`INSERT INTO newsletter_subscribers (email, subscribed_at) VALUES ($1,$2)`, [emailRaw, new Date()]);
      } catch {
        const fallbackId = Math.floor(Date.now() / 1000);
        await dbQuery(`INSERT INTO newsletter_subscribers (id, email, subscribed_at) VALUES ($1,$2,$3)`, [
          fallbackId, emailRaw, new Date(),
        ]);
      }
    }

    res.json({ ok: true, already, message: already ? "Already subscribed." : "Subscribed." });
  } catch (err) {
    logError("newsletter.failed", { rid: req.rid || "-", message: String(err?.message || err).slice(0, 600) });
    res.status(500).json({ ok: false, message: "Server error" });
  }
});

app.get("/admin/messages", requireAdmin, async (req, res) => {
  try {
    const out = await dbQuery(`SELECT * FROM messages ORDER BY created_at DESC`);
    res.json(out.rows);
  } catch {
    res.json([]);
  }
});

/* ===================== REVIEWS (PUBLIC) ===================== */
const ReviewCreateSchema = z.object({
  name: zNonEmpty("Missing name").max(80).default("Anonymous"),
  title: zNonEmpty("Missing title").min(3).max(60),
  text: zNonEmpty("Missing text").min(10).max(500),
  rating: z.coerce.number().int().min(1).max(5),
  deviceId: zNonEmpty("Missing deviceId").max(120),
});

const VoteSchema = z.object({
  voteType: z.enum(["up", "down"]),
  deviceId: zNonEmpty("Missing deviceId").max(120),
});

async function getReviewsWithVotes(productId) {
  if (!DB_CAPS.product_reviews.exists) return [];

  if (!DB_CAPS.review_votes.exists) {
    const r = await dbQuery(`SELECT * FROM product_reviews WHERE product_id=$1 ORDER BY created_at DESC LIMIT 200`, [productId]);
    return r.rows.map((x) => ({
      id: x.id,
      product_id: x.product_id,
      name: x.name,
      title: x.title,
      text: x.text,
      rating: x.rating,
      verified: x.verified,
      device_id: x.device_id,
      created_at: x.created_at,
      votes: { up: 0, down: 0 },
    }));
  }

  const r = await dbQuery(
    `
    SELECT
      pr.*,
      COALESCE(SUM(CASE WHEN rv.vote_type='up' THEN 1 ELSE 0 END), 0)::int AS up_votes,
      COALESCE(SUM(CASE WHEN rv.vote_type='down' THEN 1 ELSE 0 END), 0)::int AS down_votes
    FROM product_reviews pr
    LEFT JOIN review_votes rv ON rv.review_id = pr.id
    WHERE pr.product_id = $1
    GROUP BY pr.id
    ORDER BY pr.created_at DESC
    LIMIT 200
    `,
    [productId]
  );

  return r.rows.map((x) => ({
    id: x.id,
    product_id: x.product_id,
    name: x.name,
    title: x.title,
    text: x.text,
    rating: x.rating,
    verified: x.verified,
    device_id: x.device_id,
    created_at: x.created_at,
    votes: { up: x.up_votes, down: x.down_votes },
  }));
}

app.get("/api/products/:id/reviews", validate(ProductIdParamSchema, "params"), async (req, res) => {
  try {
    const productId = String(req.params.id);

    const p = await dbQuery(`SELECT id, is_active FROM products WHERE id=$1 LIMIT 1`, [productId]);
    if (!p.rows.length || !p.rows[0].is_active) return res.status(404).json({ ok: false, reviews: [] });

    const reviews = await getReviewsWithVotes(productId);
    res.json({ ok: true, reviews });
  } catch (e) {
    logError("reviews.list_failed", { rid: req.rid || "-", message: String(e?.message || e).slice(0, 600) });
    res.status(500).json({ ok: false, reviews: [] });
  }
});

app.get("/api/products/:id/reviews/summary", validate(ProductIdParamSchema, "params"), async (req, res) => {
  try {
    const productId = String(req.params.id);

    const p = await dbQuery(`SELECT id, is_active FROM products WHERE id=$1 LIMIT 1`, [productId]);
    if (!p.rows.length || !p.rows[0].is_active)
      return res.status(404).json({ ok: false, summary: { avg: 0, count: 0 } });

    if (!DB_CAPS.product_reviews.exists) return res.json({ ok: true, summary: { avg: 0, count: 0 } });

    const out = await dbQuery(
      `SELECT COALESCE(AVG(rating),0)::float AS avg, COUNT(*)::int AS count
       FROM product_reviews
       WHERE product_id=$1`,
      [productId]
    );

    const row = out.rows[0] || { avg: 0, count: 0 };
    res.json({ ok: true, summary: { avg: Number(row.avg || 0), count: Number(row.count || 0) } });
  } catch (e) {
    logError("reviews.summary_failed", { rid: req.rid || "-", message: String(e?.message || e).slice(0, 600) });
    res.status(500).json({ ok: false, summary: { avg: 0, count: 0 } });
  }
});

app.post(
  "/api/products/:id/reviews",
  writeLimiter,
  validate(ProductIdParamSchema, "params"),
  validate(ReviewCreateSchema),
  async (req, res) => {
    try {
      const productId = String(req.params.id);

      const p = await dbQuery(`SELECT id, is_active FROM products WHERE id=$1 LIMIT 1`, [productId]);
      if (!p.rows.length || !p.rows[0].is_active) return res.status(404).json({ ok: false, message: "Product not found" });

      if (!DB_CAPS.product_reviews.exists) return res.status(500).json({ ok: false, message: "Reviews not configured" });

      const name = String(req.body.name || "Anonymous").trim() || "Anonymous";
      const title = String(req.body.title || "").trim().slice(0, 60);
      const text = String(req.body.text || "").trim().slice(0, 500);
      const rating = Math.max(1, Math.min(5, Number(req.body.rating || 0)));
      const deviceId = String(req.body.deviceId || "").trim();

      const ins = await dbQuery(
        `
        INSERT INTO product_reviews (product_id, name, title, text, rating, verified, device_id)
        VALUES ($1,$2,$3,$4,$5,false,$6)
        ON CONFLICT (product_id, device_id) DO UPDATE
          SET name=EXCLUDED.name,
              title=EXCLUDED.title,
              text=EXCLUDED.text,
              rating=EXCLUDED.rating
        RETURNING *
        `,
        [productId, name, title, text, rating, deviceId]
      );

      const row = ins.rows[0];
      res.json({
        ok: true,
        review: {
          id: row.id,
          product_id: row.product_id,
          name: row.name,
          title: row.title,
          text: row.text,
          rating: row.rating,
          verified: row.verified,
          device_id: row.device_id,
          created_at: row.created_at,
          votes: { up: 0, down: 0 },
        },
      });
    } catch (e) {
      logError("reviews.create_failed", { rid: req.rid || "-", message: String(e?.message || e).slice(0, 600) });
      res.status(500).json({ ok: false, message: "Failed to submit review" });
    }
  }
);

// Vote on a review (up/down) per deviceId (one vote per device per review)
app.post(
  "/api/reviews/:id/vote",
  writeLimiter,
  validate(IdParamSchema, "params"),
  validate(VoteSchema),
  async (req, res) => {
    try {
      const reviewId = Number(req.params.id);

      if (!DB_CAPS.review_votes.exists) return res.status(500).json({ ok: false, message: "Votes not configured" });

      const voteType = String(req.body.voteType);
      const deviceId = String(req.body.deviceId).trim();

      // Ensure review exists
      const r1 = await dbQuery(`SELECT id FROM product_reviews WHERE id=$1 LIMIT 1`, [reviewId]);
      if (!r1.rows.length) return res.status(404).json({ ok: false, message: "Review not found" });

      // Upsert vote
      await dbQuery(
        `
        INSERT INTO review_votes (review_id, device_id, vote_type)
        VALUES ($1,$2,$3)
        ON CONFLICT (review_id, device_id)
        DO UPDATE SET vote_type=EXCLUDED.vote_type
        `,
        [reviewId, deviceId, voteType]
      );

      // Return updated counts
      const counts = await dbQuery(
        `
        SELECT
          COALESCE(SUM(CASE WHEN vote_type='up' THEN 1 ELSE 0 END),0)::int AS up_votes,
          COALESCE(SUM(CASE WHEN vote_type='down' THEN 1 ELSE 0 END),0)::int AS down_votes
        FROM review_votes
        WHERE review_id=$1
        `,
        [reviewId]
      );

      const row = counts.rows[0] || { up_votes: 0, down_votes: 0 };
      res.json({ ok: true, votes: { up: Number(row.up_votes || 0), down: Number(row.down_votes || 0) } });
    } catch (e) {
      logError("reviews.vote_failed", { rid: req.rid || "-", message: String(e?.message || e).slice(0, 600) });
      res.status(500).json({ ok: false, message: "Failed to vote" });
    }
  }
);

/* ===================== ERROR HANDLER ===================== */
app.use((err, req, res, next) => {
  const msg = String(err?.message || err || "");
  logError("unhandled_error", { rid: req?.rid || "-", method: req?.method, path: req?.originalUrl, message: msg.slice(0, 800) });

  if (msg.startsWith("Not allowed by CORS")) return res.status(403).json({ success: false, message: "CORS blocked" });
  res.status(500).json({ success: false, message: "Server error", rid: req?.rid || "-" });
});

/* ===================== START SERVER ===================== */
(async () => {
  try {
    if (!pool) logWarn("boot.no_database", { message: "DATABASE_URL not set (DB routes will fail)" });
    if (pool) await initDbCaps();
    if (!ADMIN_PASSWORD_HASH) logWarn("boot.admin_not_configured", { message: "ADMIN_PASSWORD_HASH missing" });

    app.listen(PORT, () => logInfo("boot", { msg: `Backend running on port ${PORT}` }));
  } catch (e) {
    logError("boot_failed", { message: String(e?.message || e).slice(0, 600) });
    process.exit(1);
  }
})();

/* ===================== GRACEFUL SHUTDOWN ===================== */
process.on("SIGTERM", async () => {
  try {
    logInfo("shutdown", { msg: "SIGTERM received" });
    if (pool) await pool.end();
  } catch {}
  process.exit(0);
});
process.on("SIGINT", async () => {
  try {
    logInfo("shutdown", { msg: "SIGINT received" });
    if (pool) await pool.end();
  } catch {}
  process.exit(0);
});
