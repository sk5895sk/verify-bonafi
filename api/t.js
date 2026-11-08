// Bonafi Verify — secure tap endpoint for NTAG 424 DNA (SUN / Secure Dynamic Messaging)
//
// The tag is configured to open:
//   https://verify.bonafi.io/t?picc=<32 hex>&cmac=<16 hex>
//
// picc = AES-128-CBC encryption (zero IV) of: tag byte | UID (7) | tap counter (3, LSB first) | padding
//        using the SDM Meta Read key
// cmac = truncated AES-CMAC computed with a session key derived from the SDM File Read key
//
// Environment variables (Vercel → Project → Settings → Environment Variables):
//   SDM_META_KEY   32 hex chars. If unset, the factory default (all zeros) is used and the page shows a test warning.
//   SDM_FILE_KEY   32 hex chars. Same default behavior.
//   KV_REST_API_URL / KV_REST_API_TOKEN (or UPSTASH_REDIS_REST_URL / UPSTASH_REDIS_REST_TOKEN)
//                  Redis store used to reject replayed taps. Added automatically by Vercel's Upstash integration.

const crypto = require("crypto");

// ---------------------------------------------------------------------------
// Registry: tag UID (from TagWriter "Read") → artwork serial
// ---------------------------------------------------------------------------
const TAGS = {
  // "04A1B2C3D4E5F6": "MADS-ASH-2026-0001",   // ← replace with your tag's UID
};

const ARTWORKS = {
  "MADS-ASH-2026-0001": {
    title: "Conception Dream",
    artist: "Aaron Shim",
    location: "Los Angeles",
    year: "2026 (to be confirmed)",
    medium: "To be confirmed",
    dimensions: "To be confirmed",
    gallery: "MADS, Los Angeles",
    galleryUrl: "https://www.mads.la/aaron-shim-(new)",
    registered: "November 7, 2026",
    image: "", // e.g. "/images/MADS-ASH-2026-0001-front.jpg"
  },
};

// ---------------------------------------------------------------------------
// Crypto
// ---------------------------------------------------------------------------
const ZERO_KEY = "00000000000000000000000000000000";
const ZERO_IV = Buffer.alloc(16);

function aesEcb(key, block) {
  const c = crypto.createCipheriv("aes-128-ecb", key, null);
  c.setAutoPadding(false);
  return Buffer.concat([c.update(block), c.final()]);
}

function aesCbcDecrypt(key, data) {
  const d = crypto.createDecipheriv("aes-128-cbc", key, ZERO_IV);
  d.setAutoPadding(false);
  return Buffer.concat([d.update(data), d.final()]);
}

function shiftLeft(buf) {
  const out = Buffer.alloc(16);
  for (let i = 0; i < 16; i++) {
    out[i] = ((buf[i] << 1) | (i < 15 ? buf[i + 1] >> 7 : 0)) & 0xff;
  }
  if (buf[0] & 0x80) out[15] ^= 0x87;
  return out;
}

// AES-CMAC (RFC 4493)
function aesCmac(key, msg) {
  const L = aesEcb(key, Buffer.alloc(16));
  const K1 = shiftLeft(L);
  const K2 = shiftLeft(K1);
  const n = Math.max(1, Math.ceil(msg.length / 16));
  const complete = msg.length > 0 && msg.length % 16 === 0;
  const last = Buffer.alloc(16);
  if (complete) {
    msg.copy(last, 0, (n - 1) * 16, n * 16);
    for (let i = 0; i < 16; i++) last[i] ^= K1[i];
  } else {
    const rem = msg.subarray((n - 1) * 16);
    rem.copy(last);
    last[rem.length] = 0x80;
    for (let i = 0; i < 16; i++) last[i] ^= K2[i];
  }
  let x = Buffer.alloc(16);
  for (let b = 0; b < n - 1; b++) {
    const blk = msg.subarray(b * 16, b * 16 + 16);
    for (let i = 0; i < 16; i++) x[i] ^= blk[i];
    x = aesEcb(key, x);
  }
  for (let i = 0; i < 16; i++) x[i] ^= last[i];
  return aesEcb(key, x);
}

function parseKey(hex) {
  const h = (hex || ZERO_KEY).trim();
  if (!/^[0-9a-fA-F]{32}$/.test(h)) throw new Error("Key must be 32 hex characters");
  return Buffer.from(h, "hex");
}

/**
 * Verify a SUN tap. Returns { ok, uid, counter } or { ok:false, reason }.
 */
function verifySun(piccHex, cmacHex, metaKeyHex, fileKeyHex) {
  if (!/^[0-9a-fA-F]{32}$/.test(piccHex || "") || !/^[0-9a-fA-F]{16}$/.test(cmacHex || "")) {
    return { ok: false, reason: "malformed" };
  }
  const metaKey = parseKey(metaKeyHex);
  const fileKey = parseKey(fileKeyHex);

  const plain = aesCbcDecrypt(metaKey, Buffer.from(piccHex, "hex"));
  const tag = plain[0];
  const hasUid = (tag & 0x80) !== 0;
  const hasCtr = (tag & 0x40) !== 0;
  const uidLen = tag & 0x0f;
  if (!hasUid || !hasCtr || uidLen !== 7) return { ok: false, reason: "bad_picc" };

  const uid = plain.subarray(1, 8);
  const ctrBytes = plain.subarray(8, 11);
  const counter = ctrBytes[0] | (ctrBytes[1] << 8) | (ctrBytes[2] << 16);

  // Session key: CMAC(fileKey, SV2), SV2 = 3C C3 00 01 00 80 | UID | counter
  const sv2 = Buffer.concat([Buffer.from("3CC300010080", "hex"), uid, ctrBytes]);
  const sessionKey = aesCmac(fileKey, sv2);

  // MAC over empty input, truncated to the odd-indexed bytes
  const full = aesCmac(sessionKey, Buffer.alloc(0));
  const mac = Buffer.from([1, 3, 5, 7, 9, 11, 13, 15].map((i) => full[i]));

  const given = Buffer.from(cmacHex, "hex");
  if (!crypto.timingSafeEqual(mac, given)) return { ok: false, reason: "bad_cmac" };

  return { ok: true, uid: uid.toString("hex").toUpperCase(), counter };
}

// ---------------------------------------------------------------------------
// Replay protection (tap counter must always increase)
// ---------------------------------------------------------------------------
const COUNTER_SCRIPT =
  "local c=tonumber(redis.call('GET',KEYS[1]) or '-1') " +
  "local n=tonumber(ARGV[1]) " +
  "if n>c then redis.call('SET',KEYS[1],ARGV[1]) return 1 else return 0 end";

async function acceptCounter(uid, counter) {
  const url = process.env.KV_REST_API_URL || process.env.UPSTASH_REDIS_REST_URL;
  const token = process.env.KV_REST_API_TOKEN || process.env.UPSTASH_REDIS_REST_TOKEN;
  if (!url || !token) return "unavailable";
  const r = await fetch(url, {
    method: "POST",
    headers: { Authorization: `Bearer ${token}`, "Content-Type": "application/json" },
    body: JSON.stringify(["EVAL", COUNTER_SCRIPT, "1", `ctr:${uid}`, String(counter)]),
  });
  if (!r.ok) return "unavailable";
  const j = await r.json();
  return j.result === 1 ? "fresh" : "replayed";
}

// ---------------------------------------------------------------------------
// Page rendering
// ---------------------------------------------------------------------------
const esc = (s) =>
  String(s).replace(/[&<>"']/g, (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" }[c]));

const STYLES = {
  good: "background:var(--accent-soft);color:var(--accent)",
  warn: "background:var(--warn-soft);color:var(--warn)",
  bad: "background:#fbe4e4;color:#9b1c1c",
};

function page({ tone, heading, message, serial, art, extra = "" }) {
  const details = art
    ? `<section class="card">
        <p class="serial">${esc(serial)}</p>
        <h1>${esc(art.title)}</h1>
        <p class="artist">${esc(art.artist)} · ${esc(art.location)}</p>
        <div class="photo">${
          art.image
            ? `<img src="${esc(art.image)}" alt="${esc(art.title)} by ${esc(art.artist)}">`
            : "Reference photo pending"
        }</div>
        <dl>
          <dt>Year</dt><dd>${esc(art.year)}</dd>
          <dt>Medium</dt><dd>${esc(art.medium)}</dd>
          <dt>Dimensions</dt><dd>${esc(art.dimensions)}</dd>
          <dt>Represented by</dt><dd><a href="${esc(art.galleryUrl)}">${esc(art.gallery)}</a></dd>
          <dt>Registered</dt><dd>${esc(art.registered)}</dd>
        </dl>
      </section>`
    : "";
  return `<!doctype html>
<html lang="en"><head>
<meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1">
<meta name="robots" content="noindex">
<title>${esc(heading)} · Bonafi Verify</title>
<link rel="stylesheet" href="/styles.css">
<style>@media (prefers-color-scheme: dark){.status.bad{background:#3a1d1d!important;color:#f3a9a9!important}}</style>
</head><body><main class="wrap">
<div class="brand"><strong>Bonafi Verify</strong><span>Certificate</span></div>
<div class="status ${tone}" style="${STYLES[tone]}"><span class="dot"></span>
<div><b>${esc(heading)}</b>${esc(message)}</div></div>
${extra}
${details}
<section class="card"><h2>About this certificate</h2>
<p class="note">This page confirms that the artwork above was registered with Bonafi Verify, by whom, and when. It is not an expert opinion on the work's authorship. Compare the physical artwork with the reference photos, and contact the gallery with any questions.</p></section>
<footer>Bonafi, Inc. · Chatsworth, CA · <a href="https://www.bonafi.io">bonafi.io</a></footer>
</main></body></html>`;
}

async function handler(req, res) {
  res.setHeader("Content-Type", "text/html; charset=utf-8");
  res.setHeader("Cache-Control", "no-store");
  const q = req.query || {};
  const picc = String(q.picc || q.picc_data || "");
  const cmac = String(q.cmac || "");

  let result;
  try {
    result = verifySun(picc, cmac, process.env.SDM_META_KEY, process.env.SDM_FILE_KEY);
  } catch (e) {
    res.statusCode = 500;
    return res.end(page({ tone: "bad", heading: "Verification unavailable", message: "The server's keys are misconfigured." }));
  }

  if (!result.ok) {
    res.statusCode = 400;
    return res.end(
      page({
        tone: "bad",
        heading: "Not authentic",
        message:
          result.reason === "malformed"
            ? "This link is incomplete. Tap the NFC tag on the artwork directly."
            : "This tag's signature is invalid. Do not rely on it, and contact the seller or gallery.",
      })
    );
  }

  const serial = TAGS[result.uid];
  const art = serial && ARTWORKS[serial];
  if (!art) {
    return res.end(
      page({
        tone: "warn",
        heading: "Genuine tag, not yet assigned",
        message: `This is a valid Bonafi tag (ID ${result.uid}), but it isn't linked to an artwork yet.`,
      })
    );
  }

  const freshness = await acceptCounter(result.uid, result.counter).catch(() => "unavailable");
  const testKeys = !process.env.SDM_META_KEY || !process.env.SDM_FILE_KEY;
  const testNote = testKeys
    ? `<p class="note" style="margin:-8px 0 16px">Test mode: this tag uses factory default keys.</p>`
    : "";

  if (freshness === "replayed") {
    return res.end(
      page({
        tone: "warn",
        heading: "Link already used",
        message: "This link was copied or reloaded. Tap the NFC tag on the artwork again to authenticate.",
        serial,
        art,
        extra: testNote,
      })
    );
  }

  if (freshness === "unavailable") {
    return res.end(
      page({
        tone: "warn",
        heading: "Signature valid — freshness unchecked",
        message: "The tag's signature is genuine, but this server can't yet confirm the tap is new.",
        serial,
        art,
        extra: testNote,
      })
    );
  }

  return res.end(
    page({
      tone: testKeys ? "warn" : "good",
      heading: testKeys ? "Authenticated (test keys)" : "Authenticated",
      message: `Genuine tag, fresh tap #${result.counter}. Registered to ${art.title} by ${art.artist}.`,
      serial,
      art,
      extra: testNote,
    })
  );
}

module.exports = handler;
module.exports.verifySun = verifySun;
module.exports.aesCmac = aesCmac;
