// server.js (POSTGRESQL VERSION - PRODUCTION READY + UPLOADS + NEWSLETTER)
// Render backend: https://kikelara.onrender.com
// Vercel frontend: https://kikelara.vercel.app

const express = require("express");
const cors = require("cors");
const path = require("path");
const crypto = require("crypto");
const nodemailer = require("nodemailer");
const helmet = require("helmet");
const compression = require("compression");
const multer = require("multer");
const { Pool } = require("pg");

try { require("dotenv").config(); } catch {}

const app = express();
const PORT = process.env.PORT || 4000;

/* ===================== CONFIG ===================== */
const ADMIN_CODE = process.env.ADMIN_CODE || "4567";
const ADMIN_SECRET = process.env.ADMIN_SECRET || "CHANGE_ME_SUPER_SECRET";

/**
 * IMPORTANT:
 * Set DATABASE_URL on Render backend service env:
 * DATABASE_URL=postgresql://user:pass@host:5432/db
 */
const pool = process.env.DATABASE_URL
  ? new Pool({
      connectionString: process.env.DATABASE_URL,
      ssl: process.env.NODE_ENV === "production" ? { rejectUnauthorized: false } : false
    })
  : null;

async function dbQuery(text, params) {
  if (!pool) throw new Error("DATABASE_URL not set");
  return pool.query(text, params);
}

// Your frontend domain(s)
const FRONTEND_ORIGINS = (process.env.FRONTEND_ORIGINS || "")
  .split(",")
  .map(s => s.trim())
  .filter(Boolean);

// Default origins if env not set:
const ALLOW_ORIGINS = [
  "http://localhost:3000",
  "http://localhost:5173",
  "http://127.0.0.1:5500",
  "http://localhost:5500",

  "https://kikelara1.vercel.app",
  "https://www.kikelara1.vercel.app",

  ...FRONTEND_ORIGINS
];

/* ===================== MIDDLEWARE ===================== */
app.set("trust proxy", 1);

app.use(helmet({ crossOriginResourcePolicy: false }));
app.use(compression());

app.use(cors({
  origin: function (origin, cb) {
    if (!origin) return cb(null, true);
    if (ALLOW_ORIGINS.includes(origin)) return cb(null, true);
    return cb(new Error("Not allowed by CORS: " + origin));
  },
  methods: ["GET","POST","PUT","PATCH","DELETE","OPTIONS"],
  allowedHeaders: ["Content-Type","Authorization"]
}));

app.use(express.json({ limit: "10mb" }));
app.use(express.urlencoded({ extended: true }));

/* ===================== UPLOADS ===================== */
/**
 * NOTE (Render):
 * Local disk storage may reset on redeploy. For permanent product images,
 * move to Cloudinary/S3 later. This keeps your current behavior.
 */
const uploadsDir = path.join(__dirname, "uploads");
app.use("/uploads", express.static(uploadsDir));

const storage = multer.diskStorage({
  destination: (req, file, cb) => cb(null, uploadsDir),
  filename: (req, file, cb) => {
    const ext = path.extname(file.originalname || "");
    const safeBase = path
      .basename(file.originalname || "file", ext)
      .replace(/[^a-z0-9_-]/gi, "_")
      .slice(0, 40);

    cb(null, `${Date.now()}_${safeBase}${ext || ".jpg"}`);
  }
});

function imageOnly(req, file, cb) {
  const ok = /^image\//.test(file.mimetype || "");
  cb(ok ? null : new Error("Only image files allowed"), ok);
}

const upload = multer({
  storage,
  fileFilter: imageOnly,
  limits: { fileSize: 8 * 1024 * 1024 } // 8MB
});

/* ===================== ADMIN AUTH (TOKEN) ===================== */
function base64url(input) {
  return Buffer.from(input)
    .toString("base64")
    .replace(/=/g, "")
    .replace(/\+/g, "-")
    .replace(/\//g, "_");
}
function unbase64url(input) {
  const b64 = input.replace(/-/g, "+").replace(/_/g, "/");
  return Buffer.from(b64, "base64").toString("utf-8");
}
function sign(payloadB64) {
  return crypto
    .createHmac("sha256", ADMIN_SECRET)
    .update(payloadB64)
    .digest("base64")
    .replace(/=/g, "")
    .replace(/\+/g, "-")
    .replace(/\//g, "_");
}
function createToken(payloadObj) {
  const payloadStr = JSON.stringify(payloadObj);
  const payloadB64 = base64url(payloadStr);
  const signature = sign(payloadB64);
  return `${payloadB64}.${signature}`;
}
function verifyToken(token) {
  if (!token || typeof token !== "string") return null;

  const parts = token.split(".");
  if (parts.length !== 2) return null;

  const [payloadB64, sig] = parts;
  const expected = sign(payloadB64);
  if (sig !== expected) return null;

  try {
    const payload = JSON.parse(unbase64url(payloadB64));
    if (payload?.exp && Date.now() > payload.exp) return null;
    return payload;
  } catch {
    return null;
  }
}
function requireAdmin(req, res, next) {
  const auth = req.headers.authorization || "";
  const token = auth.startsWith("Bearer ") ? auth.slice(7) : "";
  const payload = verifyToken(token);

  if (!payload || payload.role !== "admin") {
    return res.status(401).json({ success: false, message: "Unauthorized" });
  }
  req.admin = payload;
  next();
}

/* ===================== HEALTH ===================== */
app.get("/health", (req, res) => res.json({ ok: true, uptime: process.uptime() }));

/* Optional DB test */
app.get("/db-test", async (req, res) => {
  try {
    const r = await dbQuery("SELECT NOW() as now");
    res.json({ ok: true, now: r.rows[0].now });
  } catch (e) {
    res.status(500).json({ ok: false, error: String(e.message || e) });
  }
});

/* ===================== ADMIN LOGIN ===================== */
app.post("/admin/login", (req, res) => {
  const code = String(req.body?.code || "").trim();
  if (!code) return res.status(400).json({ success: false, message: "Missing code" });
  if (code !== ADMIN_CODE) return res.status(401).json({ success: false, message: "Invalid code" });

  const token = createToken({
    role: "admin",
    iat: Date.now(),
    exp: Date.now() + 1000 * 60 * 60 * 12 // 12 hours
  });

  res.json({ success: true, token });
});
app.get("/admin/me", requireAdmin, (req, res) => {
  res.json({ success: true, admin: req.admin });
});

/* ===================== DELIVERY PRICING (POSTGRES) ===================== */
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
    // create row if missing
    const seeded = buildDefaultNigeriaPricing(5000);
    await dbQuery(
      `INSERT INTO delivery_pricing (id, default_fee, updated_at, data) VALUES (1, $1, NOW(), $2)`,
      [seeded.defaultFee, seeded]
    );
    return seeded;
  }
  const row = r.rows[0];
  // data holds full object (states, etc)
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
    console.error(e);
    res.status(500).json(buildDefaultNigeriaPricing(5000));
  }
});

app.get("/admin/delivery-pricing", requireAdmin, async (req, res) => {
  try {
    const pricing = await getPricing();
    res.json({ success: true, pricing });
  } catch (e) {
    console.error(e);
    res.status(500).json({ success: false, pricing: buildDefaultNigeriaPricing(5000) });
  }
});

app.put("/admin/delivery-pricing", requireAdmin, async (req, res) => {
  try {
    const body = req.body;
    if (!body || typeof body !== "object") {
      return res.status(400).json({ success: false, message: "Invalid payload" });
    }
    const cleaned = sanitizePricing(body);
    cleaned.updatedAt = new Date().toISOString();

    await dbQuery(
      `UPDATE delivery_pricing
       SET default_fee = $1, updated_at = NOW(), data = $2
       WHERE id = 1`,
      [cleaned.defaultFee, cleaned]
    );

    res.json({ success: true, pricing: cleaned });
  } catch (e) {
    console.error(e);
    res.status(500).json({ success: false, message: "Failed to update pricing" });
  }
});

app.post("/admin/delivery-pricing/seed", requireAdmin, async (req, res) => {
  try {
    const fee = Number(req.body?.fee);
    const seedFee = Number.isFinite(fee) && fee >= 0 ? Math.round(fee) : 5000;
    const seeded = buildDefaultNigeriaPricing(seedFee);
    seeded.updatedAt = new Date().toISOString();

    await dbQuery(
      `UPDATE delivery_pricing
       SET default_fee = $1, updated_at = NOW(), data = $2
       WHERE id = 1`,
      [seeded.defaultFee, seeded]
    );

    res.json({ success: true, pricing: seeded });
  } catch (e) {
    console.error(e);
    res.status(500).json({ success: false, message: "Failed to seed pricing" });
  }
});

/* ===================== ORDERS (POSTGRES) ===================== */
app.post("/orders", async (req, res) => {
  try {
    const payload = req.body || {};
    const id = Date.now();

    const reference =
      payload.reference || payload.paystack_ref || payload.id || `ORDER_${id}`;

    const createdAtRaw = payload.createdAt || payload.created_at || new Date().toISOString();
    const createdAt = new Date(createdAtRaw);
    const status = String(payload.status || "Pending");

    const r = await dbQuery(
      `INSERT INTO orders (id, reference, created_at, status, payload)
       VALUES ($1, $2, $3, $4, $5)
       RETURNING *`,
      [id, reference, isNaN(createdAt.getTime()) ? new Date() : createdAt, status, payload]
    );

    res.json({ success: true, order: r.rows[0] });
  } catch (err) {
    console.error(err);
    res.status(500).json({ success: false, message: "Failed to save order" });
  }
});
app.post("/order", (req, res) => { req.url = "/orders"; app._router.handle(req, res); });

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
    console.error(err);
    res.status(500).json([]);
  }
});

app.patch("/orders/:id/status", requireAdmin, async (req, res) => {
  try {
    const orderId = Number(req.params.id);
    const status = String(req.body?.status || "").trim();

    if (!Number.isFinite(orderId) || orderId <= 0 || !status) {
      return res.status(400).json({ success: false, message: "Missing orderId or status" });
    }

    const updated = await dbQuery(
      `UPDATE orders SET status = $1 WHERE id = $2 RETURNING *`,
      [status, orderId]
    );

    if (!updated.rows.length) {
      return res.status(404).json({ success: false, message: "Order not found" });
    }

    res.json({ success: true, order: updated.rows[0] });
  } catch (err) {
    console.error(err);
    res.status(500).json({ success: false, message: "Failed to update status" });
  }
});

/* ===================== CONTACT (EMAIL + SAVE) ===================== */
const GMAIL_USER = process.env.GMAIL_USER || "";
const GMAIL_APP_PASS = process.env.GMAIL_APP_PASS || "";
const transporter = (GMAIL_USER && GMAIL_APP_PASS)
  ? nodemailer.createTransport({
      service: "gmail",
      auth: { user: GMAIL_USER, pass: GMAIL_APP_PASS }
    })
  : null;

app.post("/api/contact", async (req, res) => {
  try {
    const { name, email, message } = req.body || {};
    if (!name || !email || !message) {
      return res.status(400).json({ success: false, msg: "All fields required" });
    }

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
    console.error(err);
    res.status(500).json({ success: false, msg: "Server error" });
  }
});

/* ===================== NEWSLETTER (POSTGRES + CONFIRM EMAIL) ===================== */
app.post("/api/newsletter/subscribe", async (req, res) => {
  try {
    const emailRaw = String(req.body?.email || "").trim().toLowerCase();

    if (!emailRaw || !/^\S+@\S+\.\S+$/.test(emailRaw)) {
      return res.status(400).json({ ok: false, message: "Invalid email" });
    }

    const exists = await dbQuery(
      `SELECT 1 FROM newsletter_subscribers WHERE email = $1`,
      [emailRaw]
    );

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
    console.error("NEWSLETTER_SUBSCRIBE_ERROR:", err);
    return res.status(500).json({ ok: false, message: "Server error" });
  }
});

/* ===================== MESSAGES (ADMIN - POSTGRES) ===================== */
app.get("/admin/messages", requireAdmin, async (req, res) => {
  try {
    const out = await dbQuery(`SELECT * FROM messages ORDER BY created_at DESC`);
    res.json(out.rows);
  } catch (e) {
    console.error(e);
    res.json([]);
  }
});

app.delete("/admin/messages/:id", requireAdmin, async (req, res) => {
  try {
    const id = Number(req.params.id);
    if (!Number.isFinite(id)) {
      return res.status(400).json({ success: false, message: "Invalid id" });
    }

    const out = await dbQuery(`DELETE FROM messages WHERE id = $1 RETURNING id`, [id]);
    if (!out.rows.length) {
      return res.status(404).json({ success: false, message: "Message not found" });
    }

    res.json({ success: true });
  } catch (e) {
    console.error(e);
    res.status(500).json({ success: false, message: "Delete failed" });
  }
});

/* ===================== PRODUCTS (POSTGRES) ===================== */
/**
 * Public list products
 * - returns only active products by default
 */
app.get("/api/products", async (req, res) => {
  try {
    const includeAll = String(req.query.all || "").toLowerCase() === "true";
    const sql = includeAll
      ? `SELECT * FROM products ORDER BY created_at DESC`
      : `SELECT * FROM products WHERE is_active = true ORDER BY created_at DESC`;

    const out = await dbQuery(sql);
    res.json(out.rows);
  } catch (e) {
    console.error(e);
    res.json([]);
  }
});

/**
 * Admin list products
 */
app.get("/admin/products", requireAdmin, async (req, res) => {
  try {
    const out = await dbQuery(`SELECT * FROM products ORDER BY created_at DESC`);
    res.json({ success: true, products: out.rows });
  } catch (e) {
    console.error(e);
    res.status(500).json({ success: false, products: [] });
  }
});

/**
 * Admin create product (optional image upload)
 * FormData fields: name, price, description, is_active
 * File field: image
 */
app.post("/admin/products", requireAdmin, upload.single("image"), async (req, res) => {
  try {
    const id = Date.now();
    const name = String(req.body?.name || "").trim();
    const price = Math.max(0, Math.round(Number(req.body?.price || 0)));
    const description = String(req.body?.description || "").trim();
    const isActive = String(req.body?.is_active || "true").toLowerCase() !== "false";

    if (!name) return res.status(400).json({ success: false, message: "Missing name" });

    const imageUrl = req.file ? `/uploads/${req.file.filename}` : null;

    const payload = {
      ...req.body,
      // keep extra fields in payload so you can extend later without changing schema
    };

    const out = await dbQuery(
      `INSERT INTO products (id, name, price, description, image_url, images, is_active, created_at, updated_at, payload)
       VALUES ($1,$2,$3,$4,$5,$6,$7,NOW(),NOW(),$8)
       RETURNING *`,
      [id, name, price, description || null, imageUrl, JSON.stringify([]), isActive, payload]
    );

    res.json({ success: true, product: out.rows[0] });
  } catch (e) {
    console.error(e);
    res.status(500).json({ success: false, message: "Create product failed" });
  }
});

/**
 * Admin update product (optional image upload)
 */
app.put("/admin/products/:id", requireAdmin, upload.single("image"), async (req, res) => {
  try {
    const id = Number(req.params.id);
    if (!Number.isFinite(id)) return res.status(400).json({ success: false, message: "Invalid id" });

    const current = await dbQuery(`SELECT * FROM products WHERE id = $1`, [id]);
    if (!current.rows.length) return res.status(404).json({ success: false, message: "Product not found" });

    const existing = current.rows[0];

    const name = String(req.body?.name ?? existing.name).trim();
    const price = Math.max(0, Math.round(Number(req.body?.price ?? existing.price)));
    const description = String(req.body?.description ?? (existing.description || "")).trim();
    const isActive = (req.body?.is_active === undefined)
      ? Boolean(existing.is_active)
      : (String(req.body.is_active).toLowerCase() !== "false");

    const imageUrl = req.file ? `/uploads/${req.file.filename}` : existing.image_url;

    // merge payload
    const payload = Object.assign({}, existing.payload || {}, req.body || {});

    const out = await dbQuery(
      `UPDATE products
       SET name=$1, price=$2, description=$3, image_url=$4, is_active=$5, updated_at=NOW(), payload=$6
       WHERE id=$7
       RETURNING *`,
      [name, price, description || null, imageUrl, isActive, payload, id]
    );

    res.json({ success: true, product: out.rows[0] });
  } catch (e) {
    console.error(e);
    res.status(500).json({ success: false, message: "Update product failed" });
  }
});

/**
 * Admin delete product
 */
app.delete("/admin/products/:id", requireAdmin, async (req, res) => {
  try {
    const id = Number(req.params.id);
    if (!Number.isFinite(id)) return res.status(400).json({ success: false, message: "Invalid id" });

    const out = await dbQuery(`DELETE FROM products WHERE id = $1 RETURNING id`, [id]);
    if (!out.rows.length) return res.status(404).json({ success: false, message: "Product not found" });

    res.json({ success: true });
  } catch (e) {
    console.error(e);
    res.status(500).json({ success: false, message: "Delete failed" });
  }
});

/* ===================== NIGERIA DEFAULT PRICING (SEED) ===================== */
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

/* ===================== START SERVER ===================== */
app.listen(PORT, () => {
  console.log(`Backend running on port ${PORT}`);
});
