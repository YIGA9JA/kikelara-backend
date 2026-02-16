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

/* ===================== ✅ REVIEWS SCHEMAS (NEW) ===================== */
const ReviewCreateSchema = z.object({
  name: zNonEmpty("Missing name").max(80, "Name too long").default("Anonymous"),
  title: zNonEmpty("Missing title").min(3, "Title too short").max(60, "Title too long"),
  text: zNonEmpty("Missing text").min(10, "Text too short").max(500, "Text too long"),
  rating: z.coerce.number().int().min(1).max(5),
  deviceId: zNonEmpty("Missing deviceId").max(120, "deviceId too long")
});

const VoteSchema = z.object({
  voteType: z.enum(["up", "down"]),
  deviceId: zNonEmpty("Missing deviceId").max(120, "deviceId too long")
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

/* ===================== DELIVERY PRICING (POSTGRES) ===================== */
function buildDefaultNigeriaPricing(fee = 5000) {
  const FEE = Math.max(0, Math.round(Number(fee) || 0));
  const statesAndCapitals = [
    { name: "Abia", city: "Umuahia" },
    { name: "Adamawa", city: "Yola" },
    { name: "Akwa Ibom", city: "Uyo" },
    { name: "Anambra", city: "Awka" },
    { name: "Bauchi", city: "Bauchi" },
    { name: "Bayelsa", city: "Yenagoa" },
    { name: "Benue", city: "Makurdi" },
    { name: "Borno", city: "Maiduguri" },
    { name: "Cross River", city: "Calabar" },
    { name: "Delta", city: "Asaba" },
    { name: "Ebonyi", city: "Abakaliki" },
    { name: "Edo", city: "Benin City" },
    { name: "Ekiti", city: "Ado-Ekiti" },
    { name: "Enugu", city: "Enugu" },
    { name: "FCT", city: "Abuja" },
    { name: "Gombe", city: "Gombe" },
    { name: "Imo", city: "Owerri" },
    { name: "Jigawa", city: "Dutse" },
    { name: "Kaduna", city: "Kaduna" },
    { name: "Kano", city: "Kano" },
    { name: "Katsina", city: "Katsina" },
    { name: "Kebbi", city: "Birnin Kebbi" },
    { name: "Kogi", city: "Lokoja" },
    { name: "Kwara", city: "Ilorin" },
    { name: "Lagos", city: "Ikeja" },
    { name: "Nasarawa", city: "Lafia" },
    { name: "Niger", city: "Minna" },
    { name: "Ogun", city: "Abeokuta" },
    { name: "Ondo", city: "Akure" },
    { name: "Osun", city: "Osogbo" },
    { name: "Oyo", city: "Ibadan" },
    { name: "Plateau", city: "Jos" },
    { name: "Rivers", city: "Port Harcourt" },
    { name: "Sokoto", city: "Sokoto" },
    { name: "Taraba", city: "Jalingo" },
    { name: "Yobe", city: "Damaturu" },
    { name: "Zamfara", city: "Gusau" }
  ];
  return {
    defaultFee: FEE,
    updatedAt: new Date().toISOString(),
    states: statesAndCapitals
      .map(s => ({ name: s.name, cities: [{ name: s.city, fee: FEE }] }))
      .sort((a, b) => a.name.localeCompare(b.name))
  };
}

function sanitizePricing(input) {
  const out = { defaultFee: 5000, updatedAt: new Date().toISOString(), states: [] };
  const def = Number(input?.defaultFee);
  out.defaultFee = Number.isFinite(def) && def >= 0 ? Math.round(def) : 5000;

  const states = Array.isArray(input?.states) ? input.states : [];
  out.states = states
    .map(s => {
      const name = String(s?.name || "").trim();
      const citiesIn = Array.isArray(s?.cities) ? s.cities : [];
      const cities = citiesIn
        .map(c => ({
          name: String(c?.name || "").trim(),
          fee: Math.round(Number(c?.fee))
        }))
        .filter(c => c.name && Number.isFinite(c.fee) && c.fee >= 0);
      return { name, cities };
    })
    .filter(s => s.name);

  out.states.sort((a, b) => a.name.localeCompare(b.name));
  out.states.forEach(s => s.cities.sort((a, b) => a.name.localeCompare(b.name)));
  return out;
}

async function getPricing() {
  const r = await dbQuery(`SELECT default_fee, updated_at, data FROM delivery_pricing WHERE id = 1`);
  if (!r.rows.length) {
    const seeded = buildDefaultNigeriaPricing(5000);
    await dbQuery(
      `INSERT INTO delivery_pricing (id, default_fee, updated_at, data) VALUES (1, $1, NOW(), $2)`,
      [seeded.defaultFee, seeded]
    );
    return seeded;
  }
  const row = r.rows[0];
  const obj = row.data && typeof row.data === "object" ? row.data : {};
  return {
    defaultFee: Number(row.default_fee) || 5000,
    updatedAt: row.updated_at ? new Date(row.updated_at).toISOString() : new Date().toISOString(),
    states: Array.isArray(obj.states) ? obj.states : []
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

app.put("/admin/delivery-pricing", writeLimiter, requireAdmin, requireCsrf, validate(DeliveryPricingSchema), async (req, res) => {
  try {
    const cleaned = sanitizePricing(req.body);
    cleaned.updatedAt = new Date().toISOString();

    await dbQuery(
      `UPDATE delivery_pricing SET default_fee = $1, updated_at = NOW(), data = $2 WHERE id = 1`,
      [cleaned.defaultFee, cleaned]
    );

    res.json({ success: true, pricing: cleaned });
  } catch (e) {
    logError("pricing.admin_put_failed", { rid: req.rid || "-", message: String(e?.message || e).slice(0, 600) });
    res.status(500).json({ success: false, message: "Failed to update pricing" });
  }
});

app.post("/admin/delivery-pricing/seed", writeLimiter, requireAdmin, requireCsrf, validate(SeedPricingSchema), async (req, res) => {
  try {
    const fee = Number(req.body?.fee);
    const seedFee = Number.isFinite(fee) && fee >= 0 ? Math.round(fee) : 5000;

    const seeded = buildDefaultNigeriaPricing(seedFee);
    seeded.updatedAt = new Date().toISOString();

    await dbQuery(
      `UPDATE delivery_pricing SET default_fee = $1, updated_at = NOW(), data = $2 WHERE id = 1`,
      [seeded.defaultFee, seeded]
    );

    res.json({ success: true, pricing: seeded });
  } catch (e) {
    logError("pricing.seed_failed", { rid: req.rid || "-", message: String(e?.message || e).slice(0, 600) });
    res.status(500).json({ success: false, message: "Failed to seed pricing" });
  }
});

/* ===================== ORDERS (IDEMPOTENT UPSERT) ===================== */
async function insertOrderIdempotent(reference, status, payload) {
  const ins = await dbQuery(
    `INSERT INTO orders (reference, status, payload)
     VALUES ($1, $2, $3)
     ON CONFLICT (reference) DO NOTHING
     RETURNING *`,
    [reference, status, payload]
  );

  if (ins.rows.length) return ins.rows[0];

  const sel = await dbQuery(`SELECT * FROM orders WHERE reference = $1 LIMIT 1`, [reference]);
  return sel.rows[0] || null;
}

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

app.post("/order", (req, res) => { req.url = "/orders"; app._router.handle(req, res); });

app.post("/payments/paystack/verify", writeLimiter, validate(VerifyPaystackSchema), async (req, res) => {
  try {
    const ip = getClientIp(req);
    const { reference, expectedAmount } = req.body;

    const verify = await verifyPaystack(reference);

    const ok = Boolean(verify?.status) && verify?.data?.status === "success";
    if (!ok) {
      logWarn("security.paystack_verify_failed", { rid: req.rid || "-", ip, reference });
      return res.status(400).json({ success: false, message: "Payment not verified" });
    }

    const paidKobo = Number(verify?.data?.amount || 0);
    const paidNaira = Math.round(paidKobo / 100);

    if (expectedAmount !== undefined && Number.isFinite(Number(expectedAmount))) {
      const exp = Math.round(Number(expectedAmount));
      if (Math.abs(exp - paidNaira) > 2) {
        logWarn("security.paystack_amount_mismatch", { rid: req.rid || "-", ip, reference, expectedAmount: exp, paidNaira });
        return res.status(400).json({ success: false, message: "Amount mismatch" });
      }
    }

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
        note: "Created via verify endpoint (order not previously posted)"
      };

      const created = await insertOrderIdempotent(reference, "Paid", payload);
      return res.json({ success: true, verified: true, order: created });
    }

    const order = existing.rows[0];
    const payload = order.payload && typeof order.payload === "object" ? order.payload : {};
    payload.status = "Paid";
    payload.paystackRef = reference;
    payload.paidAt = payload.paidAt || new Date().toISOString();
    payload.amountPaid = payload.amountPaid || paidNaira;
    payload.paystackTransactionId = payload.paystackTransactionId || (verify?.data?.id ?? null);

    const upd = await dbQuery(
      `UPDATE orders
       SET status = 'Paid', payload = $2
       WHERE reference = $1
       RETURNING *`,
      [reference, payload]
    );

    logInfo("security.paystack_verified", { rid: req.rid || "-", ip, reference, paidNaira });
    return res.json({ success: true, verified: true, order: upd.rows[0] });
  } catch (e) {
    logError("paystack.verify_error", { rid: req.rid || "-", message: String(e?.message || e).slice(0, 600) });
    return res.status(500).json({ success: false, message: "Verification failed" });
  }
});

/* ===================== ORDERS ADMIN ===================== */
app.get("/orders", requireAdmin, async (req, res) => {
  try {
    const status = String(req.query.status || "").trim();
    const q = String(req.query.q || "").trim().toLowerCase();

    let sql = `SELECT * FROM orders`;
    const where = [];
    const params = [];

    if (status) {
      params.push(status);
      where.push(`status = $${params.length}`);
    }

    if (q) {
      params.push(`%${q}%`);
      const p = `$${params.length}`;
      where.push(`(
        LOWER(reference) LIKE ${p}
        OR LOWER(payload->>'name') LIKE ${p}
        OR LOWER(payload->>'phone') LIKE ${p}
        OR LOWER(payload->>'email') LIKE ${p}
      )`);
    }

    if (where.length) sql += ` WHERE ` + where.join(" AND ");
    sql += ` ORDER BY created_at DESC`;

    const out = await dbQuery(sql, params);
    res.json(out.rows);
  } catch (err) {
    logError("orders.list_failed", { rid: req.rid || "-", message: String(err?.message || err).slice(0, 600) });
    res.status(500).json([]);
  }
});

app.patch("/orders/:id/status",
  writeLimiter,
  requireAdmin,
  requireCsrf,
  validate(IdParamSchema, "params"),
  validate(OrderStatusSchema, "body"),
  async (req, res) => {
    try {
      const orderId = Number(req.params.id);
      const status = String(req.body.status || "").trim();

      const updated = await dbQuery(
        `UPDATE orders SET status = $1 WHERE id = $2 RETURNING *`,
        [status, orderId]
      );

      if (!updated.rows.length) return res.status(404).json({ success: false, message: "Order not found" });
      res.json({ success: true, order: updated.rows[0] });
    } catch (err) {
      logError("orders.status_patch_failed", { rid: req.rid || "-", message: String(err?.message || err).slice(0, 600) });
      res.status(500).json({ success: false, message: "Failed to update status" });
    }
  }
);

/* ===================== CONTACT ===================== */
const GMAIL_USER = process.env.GMAIL_USER || "";
const GMAIL_APP_PASS = process.env.GMAIL_APP_PASS || "";
const transporter = (GMAIL_USER && GMAIL_APP_PASS)
  ? nodemailer.createTransport({
      service: "gmail",
      auth: { user: GMAIL_USER, pass: GMAIL_APP_PASS }
    })
  : null;

app.post("/api/contact", writeLimiter, validate(ContactSchema), async (req, res) => {
  try {
    const ip = getClientIp(req);

    const okCaptcha = await verifyHCaptchaToken(req.body.captchaToken, ip);
    if (!okCaptcha) {
      logWarn("security.captcha_failed", { rid: req.rid || "-", ip, path: req.originalUrl });
      return res.status(400).json({ success: false, msg: "Captcha failed. Try again." });
    }

    const { name, email, message } = req.body;

    await dbQuery(
      `INSERT INTO messages (id, name, email, message, created_at)
       VALUES ($1, $2, $3, $4, $5)`,
      [Date.now(), String(name), String(email), String(message), new Date()]
    );

    if (transporter) {
      await transporter.sendMail({
        from: GMAIL_USER,
        replyTo: email,
        to: GMAIL_USER,
        subject: `New Contact from ${name}`,
        text: `Name: ${name}\nEmail: ${email}\n\nMessage:\n${message}`
      });
    }

    res.json({ success: true, msg: "Message received — we will reply soon!" });
  } catch (err) {
    logError("contact.failed", { rid: req.rid || "-", message: String(err?.message || err).slice(0, 600) });
    res.status(500).json({ success: false, msg: "Server error" });
  }
});

/* ===================== NEWSLETTER ===================== */
app.post("/api/newsletter/subscribe", writeLimiter, validate(NewsletterSchema), async (req, res) => {
  try {
    const ip = getClientIp(req);

    const okCaptcha = await verifyHCaptchaToken(req.body.captchaToken, ip);
    if (!okCaptcha) {
      logWarn("security.captcha_failed", { rid: req.rid || "-", ip, path: req.originalUrl });
      return res.status(400).json({ ok: false, message: "Captcha failed. Try again." });
    }

    const emailRaw = req.body.email;

    const exists = await dbQuery(`SELECT 1 FROM newsletter_subscribers WHERE email = $1`, [emailRaw]);
    const already = exists.rows.length > 0;

    if (!already) {
      await dbQuery(
        `INSERT INTO newsletter_subscribers (id, email, subscribed_at)
         VALUES ($1, $2, $3)`,
        [Date.now(), emailRaw, new Date()]
      );
    }

    if (transporter) {
      await transporter.sendMail({
        from: `KÍKÉLÁRÁ <${GMAIL_USER}>`,
        to: emailRaw,
        subject: "✅ You’re subscribed — welcome to KÍKÉLÁRÁ",
        text:
`Hi,

Thanks for subscribing to KÍKÉLÁRÁ ✨
You’ll be first to know about product drops, restocks, and skincare tips.

If you didn’t subscribe, you can ignore this email.

— KÍKÉLÁRÁ Skincare`,
        html:
`<div style="font-family:Arial,sans-serif;line-height:1.6;color:#2b1d12;">
  <h2 style="margin:0 0 10px;">Welcome to KÍKÉLÁRÁ ✨</h2>
  <p style="margin:0 0 12px;">Thanks for subscribing. You’ll be first to know about product drops, restocks, and skincare tips.</p>
  <p style="margin:0 0 12px;"><b>Your email:</b> ${emailRaw}</p>
  <p style="margin:0;">If you didn’t subscribe, ignore this email.</p>
  <hr style="border:none;border-top:1px solid #e8d7c7;margin:16px 0;">
  <p style="margin:0;font-size:12px;opacity:.75;">© ${new Date().getFullYear()} KÍKÉLÁRÁ Skincare</p>
</div>`
      });
    }

    return res.json({
      ok: true,
      already,
      message: transporter
        ? (already ? "Already subscribed — confirmation sent." : "Subscribed — confirmation sent.")
        : (already ? "Already subscribed." : "Subscribed.")
    });
  } catch (err) {
    logError("newsletter.failed", { rid: req.rid || "-", message: String(err?.message || err).slice(0, 600) });
    return res.status(500).json({ ok: false, message: "Server error" });
  }
});

/* ===================== MESSAGES (ADMIN) ===================== */
app.get("/admin/messages", requireAdmin, async (req, res) => {
  try {
    const out = await dbQuery(`SELECT * FROM messages ORDER BY created_at DESC`);
    res.json(out.rows);
  } catch (e) {
    logError("messages.list_failed", { rid: req.rid || "-", message: String(e?.message || e).slice(0, 600) });
    res.json([]);
  }
});

app.delete("/admin/messages/:id",
  writeLimiter,
  requireAdmin,
  requireCsrf,
  validate(IdParamSchema, "params"),
  async (req, res) => {
    try {
      const id = Number(req.params.id);

      const out = await dbQuery(`DELETE FROM messages WHERE id = $1 RETURNING id`, [id]);
      if (!out.rows.length) return res.status(404).json({ success: false, message: "Message not found" });

      res.json({ success: true });
    } catch (e) {
      logError("messages.delete_failed", { rid: req.rid || "-", message: String(e?.message || e).slice(0, 600) });
      res.status(500).json({ success: false, message: "Delete failed" });
    }
  }
);

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

/* ===================== ✅ PRODUCT DETAILS (PUBLIC) (NEW) ===================== */
app.get("/api/products/:id",
  validate(IdParamSchema, "params"),
  async (req, res) => {
    try {
      const id = Number(req.params.id);

      const out = await dbQuery(`SELECT * FROM products WHERE id = $1 LIMIT 1`, [id]);
      if (!out.rows.length) return res.status(404).json({ success: false, message: "Product not found" });

      const p = out.rows[0];
      if (!p.is_active) return res.status(404).json({ success: false, message: "Product not found" });

      const signed = await withSignedImage(p);
      res.json({ success: true, product: signed });
    } catch (e) {
      logError("products.public_get_failed", { rid: req.rid || "-", message: String(e?.message || e).slice(0, 600) });
      res.status(500).json({ success: false, message: "Server error" });
    }
  }
);

/* ===================== ✅ REVIEWS (PUBLIC) (NEW) ===================== */
async function getReviewsWithVotes(productId) {
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

  return r.rows.map(x => ({
    id: x.id,
    product_id: x.product_id,
    name: x.name,
    title: x.title,
    text: x.text,
    rating: x.rating,
    verified: x.verified,
    device_id: x.device_id,
    created_at: x.created_at,
    votes: { up: x.up_votes, down: x.down_votes }
  }));
}

app.get("/api/products/:id/reviews",
  validate(IdParamSchema, "params"),
  async (req, res) => {
    try {
      const productId = Number(req.params.id);

      const p = await dbQuery(`SELECT id, is_active FROM products WHERE id=$1 LIMIT 1`, [productId]);
      if (!p.rows.length || !p.rows[0].is_active) return res.status(404).json({ ok: false, reviews: [] });

      const reviews = await getReviewsWithVotes(productId);
      res.json({ ok: true, reviews });
    } catch (e) {
      logError("reviews.list_failed", { rid: req.rid || "-", message: String(e?.message || e).slice(0, 600) });
      res.status(500).json({ ok: false, reviews: [] });
    }
  }
);

app.get("/api/products/:id/reviews/summary",
  validate(IdParamSchema, "params"),
  async (req, res) => {
    try {
      const productId = Number(req.params.id);

      const p = await dbQuery(`SELECT id, is_active FROM products WHERE id=$1 LIMIT 1`, [productId]);
      if (!p.rows.length || !p.rows[0].is_active) return res.status(404).json({ ok: false, summary: { avg: 0, count: 0 } });

      const out = await dbQuery(
        `SELECT COALESCE(AVG(rating),0)::float AS avg, COUNT(*)::int AS count
         FROM product_reviews
         WHERE product_id = $1`,
        [productId]
      );

      const row = out.rows[0] || { avg: 0, count: 0 };
      res.json({ ok: true, summary: { avg: Number(row.avg || 0), count: Number(row.count || 0) } });
    } catch (e) {
      logError("reviews.summary_failed", { rid: req.rid || "-", message: String(e?.message || e).slice(0, 600) });
      res.status(500).json({ ok: false, summary: { avg: 0, count: 0 } });
    }
  }
);

app.post("/api/products/:id/reviews",
  writeLimiter,
  validate(IdParamSchema, "params"),
  validate(ReviewCreateSchema),
  async (req, res) => {
    try {
      const productId = Number(req.params.id);

      const p = await dbQuery(`SELECT id, is_active FROM products WHERE id=$1 LIMIT 1`, [productId]);
      if (!p.rows.length || !p.rows[0].is_active) return res.status(404).json({ ok: false, message: "Product not found" });

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
      const review = {
        id: row.id,
        product_id: row.product_id,
        name: row.name,
        title: row.title,
        text: row.text,
        rating: row.rating,
        verified: row.verified,
        device_id: row.device_id,
        created_at: row.created_at,
        votes: { up: 0, down: 0 }
      };

      res.json({ ok: true, review });
    } catch (e) {
      logError("reviews.create_failed", { rid: req.rid || "-", message: String(e?.message || e).slice(0, 600) });
      res.status(500).json({ ok: false, message: "Failed to submit review" });
    }
  }
);

app.post("/api/reviews/:id/vote",
  writeLimiter,
  validate(IdParamSchema, "params"),
  validate(VoteSchema),
  async (req, res) => {
    try {
      const reviewId = Number(req.params.id);
      const voteType = String(req.body.voteType);
      const deviceId = String(req.body.deviceId || "").trim();

      const exists = await dbQuery(`SELECT id FROM product_reviews WHERE id=$1 LIMIT 1`, [reviewId]);
      if (!exists.rows.length) return res.status(404).json({ ok: false, message: "Review not found" });

      await dbQuery(
        `
        INSERT INTO review_votes (review_id, device_id, vote_type)
        VALUES ($1,$2,$3)
        ON CONFLICT (review_id, device_id) DO UPDATE SET vote_type=EXCLUDED.vote_type
        `,
        [reviewId, deviceId, voteType]
      );

      const r = await dbQuery(
        `
        SELECT
          pr.*,
          COALESCE(SUM(CASE WHEN rv.vote_type='up' THEN 1 ELSE 0 END), 0)::int AS up_votes,
          COALESCE(SUM(CASE WHEN rv.vote_type='down' THEN 1 ELSE 0 END), 0)::int AS down_votes
        FROM product_reviews pr
        LEFT JOIN review_votes rv ON rv.review_id = pr.id
        WHERE pr.id = $1
        GROUP BY pr.id
        LIMIT 1
        `,
        [reviewId]
      );

      const x = r.rows[0];
      const review = {
        id: x.id,
        product_id: x.product_id,
        name: x.name,
        title: x.title,
        text: x.text,
        rating: x.rating,
        verified: x.verified,
        device_id: x.device_id,
        created_at: x.created_at,
        votes: { up: x.up_votes, down: x.down_votes }
      };

      res.json({ ok: true, review });
    } catch (e) {
      logError("reviews.vote_failed", { rid: req.rid || "-", message: String(e?.message || e).slice(0, 600) });
      res.status(500).json({ ok: false, message: "Vote failed" });
    }
  }
);

/* ===================== ✅ REVIEWS (ADMIN DELETE) (NEW) ===================== */
app.delete("/admin/reviews/:id",
  writeLimiter,
  requireAdmin,
  requireCsrf,
  validate(IdParamSchema, "params"),
  async (req, res) => {
    try {
      const id = Number(req.params.id);

      const del = await dbQuery(`DELETE FROM product_reviews WHERE id=$1 RETURNING id`, [id]);
      if (!del.rows.length) return res.status(404).json({ success: false, message: "Review not found" });

      res.json({ success: true });
    } catch (e) {
      logError("reviews.admin_delete_failed", { rid: req.rid || "-", message: String(e?.message || e).slice(0, 600) });
      res.status(500).json({ success: false, message: "Delete failed" });
    }
  }
);

/* ===================== PRODUCTS ADMIN ===================== */
app.get("/admin/products", requireAdmin, async (req, res) => {
  try {
    const out = await dbQuery(`SELECT * FROM products ORDER BY created_at DESC`);
    const rows = await Promise.all(out.rows.map(withSignedImage));
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
      const id = Date.now();
      const name = String(req.body.name || "").trim();
      const price = Math.max(0, Math.round(Number(req.body.price || 0)));
      const description = String(req.body.description || "").trim();
      const isActive = String(req.body.is_active || "true").toLowerCase() !== "false";

      let imageKey = null;

      if (req.file?.buffer) {
        const up = await uploadProductImageToSupabase({
          buffer: req.file.buffer,
          originalName: req.file.originalname,
          productId: id
        });
        imageKey = up.key;
      }

      const payload = { ...req.body };
      if (imageKey) payload.__image_key = imageKey;

      const out = await dbQuery(
        `INSERT INTO products (id, name, price, description, image_url, images, is_active, created_at, updated_at, payload)
         VALUES ($1,$2,$3,$4,$5,$6,$7,NOW(),NOW(),$8)
         RETURNING *`,
        [id, name, price, description || null, imageKey, JSON.stringify([]), isActive, payload]
      );

      const signed = await withSignedImage(out.rows[0]);
      res.json({ success: true, product: signed });
    } catch (e) {
      logError("products.create_failed", { rid: req.rid || "-", message: String(e?.message || e).slice(0, 600) });
      res.status(500).json({ success: false, message: "Create product failed" });
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

      const current = await dbQuery(`SELECT * FROM products WHERE id = $1`, [id]);
      if (!current.rows.length) return res.status(404).json({ success: false, message: "Product not found" });

      const existing = current.rows[0];

      const name = String(req.body?.name ?? existing.name).trim();
      const price = Math.max(0, Math.round(Number(req.body?.price ?? existing.price)));
      const description = String(req.body?.description ?? (existing.description || "")).trim();
      const isActive = (req.body?.is_active === undefined)
        ? Boolean(existing.is_active)
        : (String(req.body.is_active).toLowerCase() !== "false");

      const removeImage = String(req.body?.remove_image || "").toLowerCase() === "true";

      const payload = Object.assign({}, existing.payload || {}, req.body || {});

      let imageKey = String(existing.image_url || "").trim();

      if (removeImage) {
        const oldKey = extractImageKey(existing) || imageKey;
        if (oldKey) await deleteSupabaseKey(oldKey);
        imageKey = null;
        delete payload.__image_key;
      }

      if (req.file?.buffer) {
        const oldKey = extractImageKey(existing) || imageKey;
        if (oldKey) await deleteSupabaseKey(oldKey);

        const up = await uploadProductImageToSupabase({
          buffer: req.file.buffer,
          originalName: req.file.originalname,
          productId: id
        });

        imageKey = up.key;
        payload.__image_key = imageKey;
      }

      const out = await dbQuery(
        `UPDATE products
         SET name=$1, price=$2, description=$3, image_url=$4, is_active=$5, updated_at=NOW(), payload=$6
         WHERE id=$7
         RETURNING *`,
        [name, price, description || null, imageKey, isActive, payload, id]
      );

      const signed = await withSignedImage(out.rows[0]);
      res.json({ success: true, product: signed });
    } catch (e) {
      logError("products.update_failed", { rid: req.rid || "-", message: String(e?.message || e).slice(0, 600) });
      res.status(500).json({ success: false, message: "Update product failed" });
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

      const current = await dbQuery(`SELECT * FROM products WHERE id = $1`, [id]);
      if (!current.rows.length) return res.status(404).json({ success: false, message: "Product not found" });

      const oldKey = extractImageKey(current.rows[0]);
      if (oldKey) await deleteSupabaseKey(oldKey);

      const out = await dbQuery(`DELETE FROM products WHERE id = $1 RETURNING id`, [id]);
      if (!out.rows.length) return res.status(404).json({ success: false, message: "Product not found" });

      res.json({ success: true });
    } catch (e) {
      logError("products.delete_failed", { rid: req.rid || "-", message: String(e?.message || e).slice(0, 600) });
      res.status(500).json({ success: false, message: "Delete failed" });
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
