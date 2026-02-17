// server.js (SUPABASE POSTGRES - PRODUCTION READY + SUPABASE STORAGE PRIVATE BUCKET + NEWSLETTER + ZOD + SECURITY + SAFE LOGGING + PAYSTACK VERIFY + PAYSTACK WEBHOOK RAW SIGNATURE + WEBHOOK REPLAY PROTECTION)
// Backend on Render: https://kikelara1.onrender.com

/**
 * ✅ IMPORTANT (DB):
 * Create this table in Supabase SQL Editor for webhook replay protection:
 *
 * create table if not exists public.paystack_events (
 *   id bigserial primary key,
 *   event_id text not null,
 *   reference text not null,
 *   event_type text not null,
 *   payload jsonb not null default '{}'::jsonb,
 *   signature text,
 *   received_at timestamptz not null default now()
 * );
 * create unique index if not exists paystack_events_event_ref_uniq
 *   on public.paystack_events (event_id, reference);
 * create unique index if not exists paystack_events_type_ref_uniq
 *   on public.paystack_events (event_type, reference);
 */

const express = require("express");
const cors = require("cors");
const path = require("path");
const fs = require("fs");
const crypto = require("crypto");
const nodemailer = require("nodemailer");
const helmet = require("helmet");
const compression = require("compression");
const multer = require("multer");
const { Pool } = require("pg");
const sharp = require("sharp");
const { z, ZodError } = require("zod");
const cookieParser = require("cookie-parser");

// ✅ Supabase Storage (private bucket)
const { createClient } = require("@supabase/supabase-js");

// ✅ Security middleware
const rateLimit = require("express-rate-limit");
const slowDown = require("express-slow-down");
const xss = require("xss-clean");
const mongoSanitize = require("express-mongo-sanitize");
const hpp = require("hpp");

// ✅ Admin password hashing
const bcrypt = require("bcryptjs");

// OPTIONAL 2FA (only if installed + you set ADMIN_TOTP_SECRET)
// const speakeasy = require("speakeasy");

try { require("dotenv").config(); } catch {}

const app = express();
const PORT = process.env.PORT || 4000;

app.disable("x-powered-by");
app.disable("etag");

/* ===================== CONFIG ===================== */
const SERVICE_NAME = process.env.SERVICE_NAME || "kikelara-api";
const ENV = process.env.NODE_ENV || "development";

const ADMIN_SECRET = process.env.ADMIN_SECRET || "CHANGE_ME_SUPER_SECRET";
const ADMIN_PASSWORD_HASH = process.env.ADMIN_PASSWORD_HASH || "";

// optional 2FA
const ADMIN_TOTP_SECRET = process.env.ADMIN_TOTP_SECRET || "";

// Paystack
const PAYSTACK_SECRET_KEY = process.env.PAYSTACK_SECRET_KEY || "";

// ✅ Cookie/session settings
const IS_PROD = process.env.NODE_ENV === "production";
const COOKIE_NAME = "admin_session";
const CSRF_COOKIE = "admin_csrf";

// ⚠️ If frontend and backend are different domains (Vercel + Render),
// you MUST use SameSite=None; Secure in production.
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

/* ===================== Fetch helper ===================== */
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
  form.append("secret", HCAPTCHA_SECRET_KEY);
  form.append("response", String(token));
  if (ip) form.append("remoteip", String(ip));

  const r = await f("https://hcaptcha.com/siteverify", {
    method: "POST",
    headers: { "Content-Type": "application/x-www-form-urlencoded" },
    body: form.toString()
  });

  const data = await r.json().catch(() => null);
  return Boolean(data?.success);
}

/* ===================== DB ===================== */
const pool = process.env.DATABASE_URL
  ? new Pool({
      connectionString: process.env.DATABASE_URL,
      ssl: IS_PROD ? { rejectUnauthorized: false } : false
    })
  : null;

async function dbQuery(text, params) {
  if (!pool) throw new Error("DATABASE_URL not set");
  return pool.query(text, params);
}

// ✅ For transactions (create/update product with image)
async function withDbClient(fn) {
  if (!pool) throw new Error("DATABASE_URL not set");
  const client = await pool.connect();
  try {
    return await fn(client);
  } finally {
    client.release();
  }
}

/* ===================== CORS ===================== */
const FRONTEND_ORIGINS = (process.env.FRONTEND_ORIGINS || "")
  .split(",")
  .map(s => s.trim())
  .filter(Boolean);

const ALLOW_ORIGINS = [
  "http://localhost:3000",
  "http://localhost:5173",
  "http://127.0.0.1:5500",
  "http://localhost:5500",
  "https://kikelara1.vercel.app",
  "https://www.kikelara1.vercel.app",
  ...FRONTEND_ORIGINS
];

/* ===================== LOGGING (JSON + SECURITY LOGS) ===================== */
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
  "authorization","cookie","set-cookie","token","access_token","refresh_token",
  "password","pass","secret","api_key","apikey","key","pin","code","otp","paystack","card","cvv"
];

function isSensitiveKey(k) {
  const key = String(k || "").toLowerCase();
  return SENSITIVE_KEYWORDS.some(s => key.includes(s));
}

function safeClone(obj, { maxString = 500, maxArray = 40, depth = 3 } = {}) {
  const seen = new WeakSet();
  function walk(x, d) {
    if (x === null || x === undefined) return x;
    if (typeof x === "string") return x.length > maxString ? x.slice(0, maxString) + "…" : x;
    if (typeof x === "number" || typeof x === "boolean") return x;
    if (Buffer.isBuffer(x)) return `[Buffer ${x.length} bytes]`;

    if (typeof x === "object") {
      if (seen.has(x)) return "[Circular]";
      seen.add(x);

      if (Array.isArray(x)) {
        const arr = x.slice(0, maxArray).map(v => walk(v, d - 1));
        return x.length > maxArray ? [...arr, `…(+${x.length - maxArray} more)`] : arr;
      }

      if (d <= 0) return "[Object]";
      const out = {};
      for (const [k, v] of Object.entries(x)) {
        out[k] = isSensitiveKey(k) ? "[REDACTED]" : walk(v, d - 1);
      }
      return out;
    }
    return String(x);
  }
  return walk(obj, depth);
}

function safeHeaders(req) {
  const keep = {};
  const hdrs = req.headers || {};

  for (const [k, v] of Object.entries(hdrs)) {
    const lk = k.toLowerCase();

    if (lk === "authorization" || lk === "cookie" || lk === "set-cookie") {
      keep[lk] = "[REDACTED]";
      continue;
    }

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
    out[k] = isSensitiveKey(k) ? "[REDACTED]" : (typeof v === "string" ? (v.length > 300 ? v.slice(0, 300) + "…" : v) : v);
  }
  return out;
}

function shouldLogBody(req) {
  const p = req.path || "";
  if (req.method === "GET" || req.method === "HEAD") return false;

  if (p.startsWith("/admin/login")) return false;
  if (p.startsWith("/orders") || p.startsWith("/order")) return false;
  if (p.startsWith("/api/contact") || p.startsWith("/api/newsletter")) return false;
  if (p.startsWith("/admin/products")) return false;
  if (p.startsWith("/payments/paystack/webhook")) return false;

  return true;
}

/* ===================== TEMP BAN LIST ===================== */
const banMap = new Map();

function isBanned(ip) {
  const v = banMap.get(ip);
  if (!v) return false;
  if (Date.now() > v.until) {
    banMap.delete(ip);
    return false;
  }
  return true;
}

function banIp(ip, minutes, reason) {
  const until = Date.now() + minutes * 60 * 1000;
  const prev = banMap.get(ip);
  const hits = (prev?.hits || 0) + 1;
  banMap.set(ip, { until, reason, hits });
  logWarn("security.temp_ban", { ip, minutes, reason, until: new Date(until).toISOString(), hits });
}

/* ===================== REQUEST LOGGER ===================== */
app.use((req, res, next) => {
  const rid = makeRid();
  req.rid = rid;
  res.setHeader("X-Request-Id", rid);

  const ip = getClientIp(req);

  if (isBanned(ip)) {
    logWarn("security.banned_request", { rid, ip, method: req.method, path: req.originalUrl });
    return res.status(403).json({ success: false, message: "Access blocked. Try later." });
  }

  const start = process.hrtime.bigint();

  logInfo("http.req", {
    rid,
    ip,
    method: req.method,
    path: req.originalUrl,
    headers: safeHeaders(req),
    query: safeQuery(req)
  });

  res.on("finish", () => {
    const end = process.hrtime.bigint();
    const ms = Number(end - start) / 1e6;

    const payload = { rid, ip, method: req.method, path: req.originalUrl, status: res.statusCode, ms: Math.round(ms) };

    if (shouldLogBody(req) && req.body && typeof req.body === "object") {
      payload.body = safeClone(req.body, { maxString: 400, maxArray: 25, depth: 2 });
    }

    if (res.statusCode >= 500) logError("http.res", payload);
    else if (res.statusCode >= 400) logWarn("http.res", payload);
    else logInfo("http.res", payload);
  });

  res.on("close", () => {
    if (!res.writableEnded) {
      const end = process.hrtime.bigint();
      const ms = Number(end - start) / 1e6;
      logWarn("http.close", { rid, ip, method: req.method, path: req.originalUrl, status: res.statusCode, ms: Math.round(ms), note: "client_aborted" });
    }
  });

  next();
});

/* ===================== ZOD HELPERS ===================== */
function validate(schema, where = "body") {
  return (req, res, next) => {
    try {
      const parsed = schema.parse(req[where]);
      req[where] = parsed;
      next();
    } catch (err) {
      if (err instanceof ZodError) {
        logWarn("zod.validation", {
          rid: req.rid || "-",
          path: req.originalUrl,
          issues: err.issues.map(i => ({ path: i.path.join("."), message: i.message }))
        });

        return res.status(400).json({
          success: false,
          message: "Validation failed",
          details: err.issues.map(i => ({ field: i.path.join("."), message: i.message }))
        });
      }
      next(err);
    }
  };
}

const zEmail = z.string().trim().toLowerCase().email("Invalid email");
const zNonEmpty = (msg) => z.string().trim().min(1, msg);
const zISODateStr = z.string().refine(v => !Number.isNaN(new Date(v).getTime()), "Invalid date");

/* ===================== SECURITY + MIDDLEWARE ===================== */
app.set("trust proxy", 1);

app.use((req, res, next) => {
  if (IS_PROD) {
    const proto = req.headers["x-forwarded-proto"];
    if (proto && proto !== "https") {
      return res.redirect(301, "https://" + req.headers.host + req.originalUrl);
    }
  }
  next();
});

app.use(helmet({
  crossOriginResourcePolicy: false,
  contentSecurityPolicy: false
}));

app.use((req, res, next) => {
  res.setHeader("X-Content-Type-Options", "nosniff");
  res.setHeader("X-Frame-Options", "DENY");
  res.setHeader("Referrer-Policy", "strict-origin-when-cross-origin");
  next();
});

app.use(compression());

function rateLimitWithSecurityLog(name, opts) {
  return rateLimit({
    ...opts,
    standardHeaders: true,
    legacyHeaders: false,
    handler: (req, res) => {
      const ip = getClientIp(req);

      logWarn("security.rate_limit_429", {
        rid: req.rid || "-",
        limiter: name,
        ip,
        method: req.method,
        path: req.originalUrl,
        headers: safeHeaders(req),
        query: safeQuery(req)
      });

      banIp(ip, 10, `rate_limit:${name}`);

      res.status(429).json({ success: false, message: "Too many requests. Please try again later." });
    }
  });
}

const globalLimiter = rateLimitWithSecurityLog("global", { windowMs: 15 * 60 * 1000, max: 500 });
const authLimiter   = rateLimitWithSecurityLog("auth",   { windowMs: 10 * 60 * 1000, max: 25 });
const writeLimiter  = rateLimitWithSecurityLog("write",  { windowMs: 5 * 60 * 1000,  max: 60 });

const speedLimiter = slowDown({
  windowMs: 15 * 60 * 1000,
  delayAfter: 120,
  delayMs: () => 250
});

app.use(globalLimiter);
app.use(speedLimiter);

const corsOptions = {
  origin: function (origin, cb) {
    if (!origin) return cb(null, true);
    if (ALLOW_ORIGINS.includes(origin)) return cb(null, true);
    return cb(new Error("Not allowed by CORS: " + origin));
  },
  methods: ["GET","POST","PUT","PATCH","DELETE","OPTIONS"],
  allowedHeaders: ["Content-Type","X-CSRF-Token","x-csrf-token","x-paystack-signature"],
  credentials: true,
  optionsSuccessStatus: 204
};
app.use(cors(corsOptions));
app.options("*", cors(corsOptions));

app.use(cookieParser(ADMIN_SECRET));

/* ===================== PAYSTACK WEBHOOK RAW ROUTE (MUST be BEFORE express.json) ===================== */
function paystackSignatureValid(rawBodyBuffer, signature) {
  if (!PAYSTACK_SECRET_KEY) return false;
  if (!rawBodyBuffer || !Buffer.isBuffer(rawBodyBuffer)) return false;
  if (!signature) return false;

  const hash = crypto
    .createHmac("sha512", PAYSTACK_SECRET_KEY)
    .update(rawBodyBuffer)
    .digest("hex");

  return hash === signature;
}

async function verifyPaystack(reference) {
  if (!PAYSTACK_SECRET_KEY) throw new Error("PAYSTACK_SECRET_KEY missing");
  const f = await ensureFetch();
  if (!f) throw new Error("fetch not available (use Node 18+ or install node-fetch)");

  const url = `https://api.paystack.co/transaction/verify/${encodeURIComponent(reference)}`;

  const r = await f(url, {
    method: "GET",
    headers: {
      Authorization: `Bearer ${PAYSTACK_SECRET_KEY}`,
      "Content-Type": "application/json"
    }
  });

  const data = await r.json().catch(() => null);
  if (!r.ok) {
    const msg = data?.message || `Paystack verify failed (${r.status})`;
    throw new Error(msg);
  }
  return data;
}

async function recordPaystackEventOnce({ eventId, reference, eventType, payload, signature }) {
  const r = await dbQuery(
    `
      insert into paystack_events (event_id, reference, event_type, payload, signature)
      values ($1, $2, $3, $4, $5)
      on conflict do nothing
      returning id
    `,
    [String(eventId), String(reference), String(eventType), payload || {}, signature ? String(signature) : null]
  );
  return r.rows.length > 0;
}

app.post(
  "/payments/paystack/webhook",
  express.raw({ type: "application/json", limit: "300kb" }),
  async (req, res) => {
    const ip = getClientIp(req);

    try {
      const sig = String(req.headers["x-paystack-signature"] || "");

      if (!paystackSignatureValid(req.body, sig)) {
        logWarn("security.paystack_webhook_bad_sig", { rid: req.rid || "-", ip });
        return res.status(200).json({ received: true, ignored: true });
      }

      const bodyString = req.body.toString("utf8");
      let event = null;
      try { event = JSON.parse(bodyString); }
      catch {
        logWarn("paystack.webhook_bad_json", { rid: req.rid || "-", ip });
        return res.status(200).json({ received: true, ignored: true });
      }

      const evtType = String(event?.event || "");
      const data = event?.data || {};

      if (evtType !== "charge.success") {
        logInfo("paystack.webhook_ignored", { rid: req.rid || "-", ip, evtType });
        return res.status(200).json({ received: true, ignored: true });
      }

      const reference = String(data?.reference || "").trim();
      if (!reference) {
        logWarn("paystack.webhook_missing_ref", { rid: req.rid || "-", ip });
        return res.status(200).json({ received: true, ignored: true });
      }

      const eventId =
        String(event?.id || data?.id || data?.transaction || "").trim() ||
        `no_event_id:${reference}:${evtType}`;

      const firstTime = await recordPaystackEventOnce({
        eventId,
        reference,
        eventType: evtType,
        payload: event,
        signature: sig
      });

      if (!firstTime) {
        logInfo("paystack.webhook_replay_ignored", { rid: req.rid || "-", ip, reference, evtType });
        return res.status(200).json({ received: true, ignored: true, replay: true });
      }

      const verify = await verifyPaystack(reference);
      const ok = Boolean(verify?.status) && verify?.data?.status === "success";
      if (!ok) {
        logWarn("paystack.webhook_verify_failed", { rid: req.rid || "-", ip, reference });
        return res.status(200).json({ received: true, ignored: true });
      }

      const paidKobo = Number(verify?.data?.amount || 0);
      const paidNaira = Math.round(paidKobo / 100);

      const existing = await dbQuery(`SELECT * FROM orders WHERE reference = $1 LIMIT 1`, [reference]);

      if (!existing.rows.length) {
        const payload = {
          reference,
          status: "Paid",
          paystackRef: reference,
          createdAt: new Date().toISOString(),
          paidAt: new Date().toISOString(),
          amountPaid: paidNaira,
          paystackTransactionId: verify?.data?.id ?? null,
          note: "Created via webhook (order not previously posted)"
        };

        await dbQuery(
          `INSERT INTO orders (reference, status, payload)
           VALUES ($1, $2, $3)
           ON CONFLICT (reference) DO NOTHING`,
          [reference, "Paid", payload]
        );

        logInfo("paystack.webhook_created_paid", { rid: req.rid || "-", ip, reference, paidNaira });
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

      logInfo("paystack.webhook_marked_paid", { rid: req.rid || "-", ip, reference, paidNaira });
      return res.status(200).json({ ok: true });
    } catch (e) {
      logError("paystack.webhook_error", { rid: req.rid || "-", message: String(e?.message || e).slice(0, 600) });
      return res.status(200).json({ received: true, ignored: true });
    }
  }
);

/* ✅ Smaller body limits (AFTER webhook raw route) */
app.use(express.json({ limit: "200kb" }));
app.use(express.urlencoded({ extended: true, limit: "200kb" }));

/* ✅ Sanitization */
app.use(mongoSanitize());
app.use(xss());
app.use(hpp());

/* ===================== ✅ PUBLIC ORDER RECEIPT ENDPOINT (NO DB CHANGE) ===================== */
app.get("/orders/public/:reference", async (req, res) => {
  try {
    const ref = String(req.params.reference || "").trim();
    if (!ref) return res.status(400).json({ ok: false, message: "Missing reference" });

    const r = await dbQuery(
      `SELECT reference, status, payload, created_at FROM orders WHERE reference = $1 LIMIT 1`,
      [ref]
    );
    if (!r.rows.length) return res.status(404).json({ ok: false, message: "Not found" });

    const row = r.rows[0];
    const payload = row.payload && typeof row.payload === "object" ? row.payload : {};

    const safe = {
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
      amountPaid: payload.amountPaid || null
    };

    return res.json({ ok: true, order: safe });
  } catch (e) {
    logError("orders.public_get_failed", { rid: req.rid || "-", message: String(e?.message || e).slice(0, 600) });
    return res.status(500).json({ ok: false, message: "Server error" });
  }
});

/* ===================== SUPABASE STORAGE (PRIVATE BUCKET) ===================== */
/**
 * Bucket: private "kikelara"
 * We store the STORAGE KEY (e.g. "products/123/xxx.webp") in products.image_url
 * Then we return a SIGNED URL to browser on fetch.
 */
const SUPABASE_URL = process.env.SUPABASE_URL || "";
const SUPABASE_SERVICE_ROLE_KEY = process.env.SUPABASE_SERVICE_ROLE_KEY || "";
const SUPABASE_BUCKET = process.env.SUPABASE_BUCKET || "kikelara";
const SIGNED_URL_TTL_SECONDS = Math.max(60, Number(process.env.SIGNED_URL_TTL_SECONDS || 604800)); // 7 days default

const supabaseAdmin = (SUPABASE_URL && SUPABASE_SERVICE_ROLE_KEY)
  ? createClient(SUPABASE_URL, SUPABASE_SERVICE_ROLE_KEY, { auth: { persistSession: false } })
  : null;

function ensureSupabaseReady() {
  if (!supabaseAdmin) throw new Error("Supabase Storage not configured (missing SUPABASE_URL or SUPABASE_SERVICE_ROLE_KEY)");
  if (!SUPABASE_BUCKET) throw new Error("SUPABASE_BUCKET missing");
}

function imageOnly(req, file, cb) {
  const okMime = /^image\//.test(file.mimetype || "");
  const ext = (path.extname(file.originalname || "").toLowerCase());
  const okExt = [".png", ".jpg", ".jpeg", ".webp"].includes(ext);
  cb(okMime && okExt ? null : new Error("Only PNG/JPG/JPEG/WEBP images allowed"), okMime && okExt);
}

// ✅ Use memory storage (no disk)
const upload = multer({
  storage: multer.memoryStorage(),
  fileFilter: imageOnly,
  limits: { fileSize: 8 * 1024 * 1024 }
});

function safeKeyPart(str, max = 40) {
  return String(str || "")
    .toLowerCase()
    .replace(/\.[^.]+$/, "")
    .replace(/[^a-z0-9_-]/g, "_")
    .replace(/_+/g, "_")
    .slice(0, max) || "image";
}

async function toWebpSquareBuffer(buf) {
  return sharp(buf)
    .rotate()
    .resize(1080, 1080, { fit: "cover" })
    .webp({ quality: 82 })
    .toBuffer();
}

async function uploadProductImageToSupabase({ buffer, originalName, productId }) {
  ensureSupabaseReady();

  const base = safeKeyPart(originalName);
  const key = `products/${productId}/${Date.now()}_${base}.webp`;

  const webpBuf = await toWebpSquareBuffer(buffer);

  const { error: upErr } = await supabaseAdmin.storage
    .from(SUPABASE_BUCKET)
    .upload(key, webpBuf, {
      contentType: "image/webp",
      cacheControl: "31536000",
      upsert: false
    });

  if (upErr) throw new Error(upErr.message || "Supabase upload failed");
  return { key };
}

async function signKey(key) {
  ensureSupabaseReady();
  const k = String(key || "").trim();
  if (!k) return "";

  const { data, error } = await supabaseAdmin.storage
    .from(SUPABASE_BUCKET)
    .createSignedUrl(k, SIGNED_URL_TTL_SECONDS);

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

function extractImageKey(row) {
  const payload = row?.payload && typeof row.payload === "object" ? row.payload : {};
  const k1 = String(payload.__image_key || "").trim();
  if (k1) return k1;

  const img = String(row?.image_url || "").trim();
  if (!img) return "";

  // legacy external url or legacy /uploads path (leave)
  if (img.startsWith("http://") || img.startsWith("https://") || img.startsWith("/uploads/")) return "";

  // likely already a key
  return img;
}

async function withSignedImage(row) {
  const r = { ...row };
  const img = String(row?.image_url || "").trim();
  if (!img) return r;

  // legacy external url or legacy /uploads path
  if (img.startsWith("http://") || img.startsWith("https://") || img.startsWith("/uploads/")) return r;

  // treat as storage key
  try {
    r.image_url = await signKey(img);
  } catch {
    // keep original key if signing fails (avoid crash)
  }
  return r;
}

/* ===================== ADMIN SESSION (COOKIE + CSRF) ===================== */
function base64url(input) {
  return Buffer.from(input).toString("base64").replace(/=/g, "").replace(/\+/g, "-").replace(/\//g, "_");
}
function unbase64url(input) {
  const b64 = input.replace(/-/g, "+").replace(/_/g, "/");
  return Buffer.from(b64, "base64").toString("utf-8");
}
function sign(payloadB64) {
  return crypto.createHmac("sha256", ADMIN_SECRET).update(payloadB64).digest("base64")
    .replace(/=/g, "").replace(/\+/g, "-").replace(/\//g, "_");
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
  if (sig !== sign(payloadB64)) return null;

  try {
    const payload = JSON.parse(unbase64url(payloadB64));
    if (payload?.exp && Date.now() > payload.exp) return null;
    return payload;
  } catch { return null; }
}

// ✅ In-memory allowlist (optional, but good)
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

function requireAdmin(req, res, next) {
  const token = getAdminTokenFromCookie(req);
  const payload = verifyToken(token);

  if (!payload || payload.role !== "admin") {
    const ip = getClientIp(req);
    logWarn("security.admin_unauthorized", { rid: req.rid || "-", ip, path: req.originalUrl });
    return res.status(401).json({ success: false, message: "Unauthorized" });
  }

  if (payload.jti && adminJtiMap.size > 0) {
    const exp = adminJtiMap.get(payload.jti);
    if (!exp || Date.now() > exp) {
      return res.status(401).json({ success: false, message: "Session expired" });
    }
  }

  req.admin = payload;
  next();
}

function requireCsrf(req, res, next) {
  const method = String(req.method || "").toUpperCase();
  if (method === "GET" || method === "HEAD" || method === "OPTIONS") return next();

  const cookieVal = String(req.cookies?.[CSRF_COOKIE] || "");
  const headerVal = String(req.headers["x-csrf-token"] || req.headers["x-csrf-token".toLowerCase()] || "");

  if (!cookieVal || !headerVal || cookieVal !== headerVal) {
    const ip = getClientIp(req);
    logWarn("security.csrf_block", { rid: req.rid || "-", ip, path: req.originalUrl });
    return res.status(403).json({ success: false, message: "CSRF blocked" });
  }
  next();
}

/* ===================== ZOD SCHEMAS ===================== */
const AdminLoginSchema = z.object({
  password: zNonEmpty("Missing password"),
  otp: z.string().trim().optional()
});

const DeliveryPricingSchema = z.object({
  defaultFee: z.coerce.number().min(0).optional(),
  updatedAt: z.string().optional(),
  states: z.array(
    z.object({
      name: z.string().trim().min(1),
      cities: z.array(
        z.object({
          name: z.string().trim().min(1),
          fee: z.coerce.number().min(0)
        })
      ).optional().default([])
    })
  ).optional().default([])
});

const SeedPricingSchema = z.object({ fee: z.coerce.number().min(0).optional() });

const ContactSchema = z.object({
  name: zNonEmpty("Name is required").max(120, "Name too long"),
  email: zEmail,
  message: zNonEmpty("Message is required").max(5000, "Message too long"),
  captchaToken: z.string().optional()
});

const NewsletterSchema = z.object({
  email: zEmail,
  captchaToken: z.string().optional()
});

const IdParamSchema = z.object({ id: z.coerce.number().int().positive("Invalid id") });

const OrderStatusSchema = z.object({ status: zNonEmpty("Missing status").max(40, "Status too long") });

const CartItemSchema = z.object({
  id: z.union([z.string(), z.number()]).optional(),
  name: zNonEmpty("Item name required").max(250),
  price: z.coerce.number().min(0),
  qty: z.coerce.number().int().min(1),
  image: z.string().optional().nullable(),
  total: z.coerce.number().min(0).optional()
}).passthrough();

const zISO = zISODateStr;

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
  createdAt: zISO,

  paidAt: z.string().optional(),
  amountPaid: z.coerce.number().optional()
}).superRefine((data, ctx) => {
  if (data.shippingType === "delivery") {
    if (!String(data.state || "").trim()) ctx.addIssue({ code: "custom", path: ["state"], message: "State is required for delivery" });
    if (!String(data.city || "").trim()) ctx.addIssue({ code: "custom", path: ["city"], message: "City/LGA is required for delivery" });
    if (!String(data.address || "").trim()) ctx.addIssue({ code: "custom", path: ["address"], message: "Address is required for delivery" });
  }

  const computedSubtotal = (data.cart || []).reduce((sum, it) => sum + (Number(it.price || 0) * Number(it.qty || 0)), 0);
  if (Math.abs(Number(data.subtotal || 0) - computedSubtotal) > 2) {
    ctx.addIssue({ code: "custom", path: ["subtotal"], message: "Subtotal mismatch" });
  }

  const computedTotal = computedSubtotal + Number(data.deliveryFee || 0);
  if (Math.abs(Number(data.total || 0) - computedTotal) > 2) {
    ctx.addIssue({ code: "custom", path: ["total"], message: "Total mismatch" });
  }
});

const VerifyPaystackSchema = z.object({
  reference: zNonEmpty("Missing reference").max(200),
  expectedAmount: z.coerce.number().min(0).optional()
});

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

/* ===================== ADMIN LOGIN (COOKIE SESSION + CSRF) ===================== */
function randomToken(bytes = 32) {
  return crypto.randomBytes(bytes).toString("hex");
}

app.post("/admin/login", authLimiter, validate(AdminLoginSchema), async (req, res) => {
  try {
    const ip = getClientIp(req);

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
      return res.status(500).json({ success: false, message: "2FA enabled but not configured in code (install speakeasy and uncomment)." });
    }

    const exp = Date.now() + 1000 * 60 * 60 * 12; // 12h
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
  res.json({ success: true, admin: req.admin });
});

/* ===================== PRODUCTS (POSTGRES) ===================== */
app.get("/api/products", async (req, res) => {
  try {
    const includeAll = String(req.query.all || "").toLowerCase() === "true";
    const sql = includeAll
      ? `SELECT * FROM products ORDER BY created_at DESC`
      : `SELECT * FROM products WHERE is_active = true ORDER BY created_at DESC`;

    const out = await dbQuery(sql);

    // ✅ SIGN private bucket images
    const rows = await Promise.all(out.rows.map(withSignedImage));

    res.json(rows);
  } catch (e) {
    logError("products.public_list_failed", { rid: req.rid || "-", message: String(e?.message || e).slice(0, 600) });
    res.json([]);
  }
});

/* ===================== PRODUCTS ADMIN ===================== */
app.get("/admin/products", requireAdmin, async (req, res) => {
  try {
    const out = await dbQuery(`SELECT * FROM products ORDER BY created_at DESC`);
    const rows = await Promise.all(out.rows.map(withSignedImage));
    res.json({ success: true, products: rows });
  } catch (e) {
    logError("products.admin_list_failed", { rid: req.rid || "-", message: String(e?.message || e).slice(0, 600) });
    // IMPORTANT: return real message for debugging admin
    res.status(500).json({ success: false, message: String(e?.message || e), products: [] });
  }
});

const CreateProductSchema = z.object({
  name: zNonEmpty("Missing name").max(200, "Name too long"),
  price: z.coerce.number().min(0, "Invalid price").default(0),
  description: z.string().trim().max(5000, "Description too long").optional().default(""),
  is_active: z.string().optional()
}).passthrough();

const UpdateProductSchema = z.object({
  name: z.string().trim().min(1).max(200).optional(),
  price: z.coerce.number().min(0).optional(),
  description: z.string().trim().max(5000).optional(),
  is_active: z.string().optional(),
  remove_image: z.string().optional()
}).passthrough();

app.post("/admin/products",
  writeLimiter,
  requireAdmin,
  requireCsrf,
  upload.single("image"),
  validate(CreateProductSchema),
  async (req, res) => {
    try {
      const name = String(req.body.name || "").trim();
      const price = Math.max(0, Math.round(Number(req.body.price || 0)));
      const description = String(req.body.description || "").trim();
      const isActive = String(req.body.is_active || "true").toLowerCase() !== "false";

      // ✅ Transaction: insert first (DB generates ID), then upload image, then update row
      const createdRow = await withDbClient(async (client) => {
        await client.query("BEGIN");
        let uploadedKey = "";

        try {
          // Insert WITHOUT forcing id (avoids int overflow / schema mismatch)
          const payload = { ...req.body };

          const ins = await client.query(
            `
            INSERT INTO products (name, price, description, image_url, is_active, created_at, updated_at, payload)
            VALUES ($1,$2,$3,$4,$5,NOW(),NOW(),$6)
            RETURNING *
            `,
            [name, price, description || null, null, isActive, payload]
          );

          let row = ins.rows[0];

          // If payload column doesn't exist in your table, fall back gracefully
          if (!row) {
            throw new Error("Insert failed (no row returned)");
          }

          if (req.file?.buffer) {
            const up = await uploadProductImageToSupabase({
              buffer: req.file.buffer,
              originalName: req.file.originalname,
              productId: row.id
            });
            uploadedKey = up.key;

            // store key in payload too (safe), but if payload column doesn't exist, update still works
            const nextPayload = Object.assign({}, (row.payload && typeof row.payload === "object" ? row.payload : {}), payload, { __image_key: uploadedKey });

            const upd = await client.query(
              `
              UPDATE products
              SET image_url=$1, updated_at=NOW(), payload=$2
              WHERE id=$3
              RETURNING *
              `,
              [uploadedKey, nextPayload, row.id]
            );

            row = upd.rows[0] || row;
          }

          await client.query("COMMIT");
          return row;
        } catch (err) {
          await client.query("ROLLBACK");
          if (uploadedKey) {
            // rollback DB but bucket might have an orphan file — delete best-effort
            await deleteSupabaseKey(uploadedKey);
          }
          throw err;
        }
      });

      const signed = await withSignedImage(createdRow);
      res.json({ success: true, product: signed });
    } catch (e) {
      logError("products.create_failed", { rid: req.rid || "-", message: String(e?.message || e).slice(0, 900) });
      // IMPORTANT: show real message in admin
      res.status(500).json({ success: false, message: String(e?.message || e) });
    }
  }
);

app.put("/admin/products/:id",
  writeLimiter,
  requireAdmin,
  requireCsrf,
  upload.single("image"),
  validate(IdParamSchema, "params"),
  validate(UpdateProductSchema),
  async (req, res) => {
    try {
      const id = Number(req.params.id);

      const updatedRow = await withDbClient(async (client) => {
        await client.query("BEGIN");
        let newUploadedKey = "";

        try {
          const current = await client.query(`SELECT * FROM products WHERE id=$1 LIMIT 1`, [id]);
          if (!current.rows.length) {
            await client.query("ROLLBACK");
            return null;
          }
          const existing = current.rows[0];

          const name = String(req.body?.name ?? existing.name).trim();
          const price = Math.max(0, Math.round(Number(req.body?.price ?? existing.price)));
          const description = String(req.body?.description ?? (existing.description || "")).trim();
          const isActive = (req.body?.is_active === undefined)
            ? Boolean(existing.is_active)
            : (String(req.body.is_active).toLowerCase() !== "false");

          const removeImage = String(req.body?.remove_image || "").toLowerCase() === "true";

          // existing key
          let imageKey = String(existing.image_url || "").trim() || null;

          // merge payload safely
          const payload = Object.assign({}, (existing.payload && typeof existing.payload === "object" ? existing.payload : {}), (req.body || {}));

          if (removeImage) {
            const oldKey = extractImageKey(existing) || imageKey;
            if (oldKey) await deleteSupabaseKey(oldKey);
            imageKey = null;
            delete payload.__image_key;
          }

          if (req.file?.buffer) {
            // upload NEW first
            const up = await uploadProductImageToSupabase({
              buffer: req.file.buffer,
              originalName: req.file.originalname,
              productId: id
            });
            newUploadedKey = up.key;

            // delete old after new success
            const oldKey = extractImageKey(existing) || imageKey;
            if (oldKey) await deleteSupabaseKey(oldKey);

            imageKey = newUploadedKey;
            payload.__image_key = imageKey;
          }

          const out = await client.query(
            `
            UPDATE products
            SET name=$1, price=$2, description=$3, image_url=$4, is_active=$5, updated_at=NOW(), payload=$6
            WHERE id=$7
            RETURNING *
            `,
            [name, price, description || null, imageKey, isActive, payload, id]
          );

          await client.query("COMMIT");
          return out.rows[0] || null;
        } catch (err) {
          await client.query("ROLLBACK");
          if (newUploadedKey) await deleteSupabaseKey(newUploadedKey);
          throw err;
        }
      });

      if (!updatedRow) return res.status(404).json({ success: false, message: "Product not found" });

      const signed = await withSignedImage(updatedRow);
      res.json({ success: true, product: signed });
    } catch (e) {
      logError("products.update_failed", { rid: req.rid || "-", message: String(e?.message || e).slice(0, 900) });
      res.status(500).json({ success: false, message: String(e?.message || e) });
    }
  }
);

app.delete("/admin/products/:id",
  writeLimiter,
  requireAdmin,
  requireCsrf,
  validate(IdParamSchema, "params"),
  async (req, res) => {
    try {
      const id = Number(req.params.id);

      const existed = await dbQuery(`SELECT * FROM products WHERE id=$1 LIMIT 1`, [id]);
      if (!existed.rows.length) return res.status(404).json({ success: false, message: "Product not found" });

      const oldKey = extractImageKey(existed.rows[0]);
      if (oldKey) await deleteSupabaseKey(oldKey);

      const out = await dbQuery(`DELETE FROM products WHERE id=$1 RETURNING id`, [id]);
      if (!out.rows.length) return res.status(404).json({ success: false, message: "Product not found" });

      res.json({ success: true });
    } catch (e) {
      logError("products.delete_failed", { rid: req.rid || "-", message: String(e?.message || e).slice(0, 900) });
      res.status(500).json({ success: false, message: String(e?.message || e) });
    }
  }
);

/* ===================== ERROR HANDLER (SAFE) ===================== */
app.use((err, req, res, next) => {
  const msg = String(err?.message || err || "");
  const rid = req?.rid || "-";

  logError("unhandled_error", {
    rid,
    method: req?.method,
    path: req?.originalUrl,
    message: msg.slice(0, 800)
  });

  if (msg.startsWith("Not allowed by CORS")) {
    return res.status(403).json({ success: false, message: "CORS blocked" });
  }

  res.status(500).json({ success: false, message: "Server error" });
});

/* ===================== START SERVER ===================== */
app.listen(PORT, () => {
  logInfo("boot", { msg: `Backend running on port ${PORT}` });
});
