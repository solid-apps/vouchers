import { parseTxoUri, isValidTxoUri, formatTxoUri } from 'https://esm.sh/txo_parser'
import { secp256k1, schnorr } from 'https://esm.sh/@noble/curves@1.8.1/secp256k1'
// Pod I/O uses the active xlogin session (Solid here) — authenticates silently
// with the session you're already signed in with, no extra login prompt.
const authFetch = (url, opts) => ((window.xlogin && window.xlogin.authFetch) || fetch)(url, opts)

// ── Crypto helpers ──────────────────────────────────────

const B58 = '123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz'

function b58decode(str) {
  const bytes = []
  for (const c of str) {
    let carry = B58.indexOf(c)
    if (carry < 0) throw new Error('Invalid base58 character: ' + c)
    for (let j = 0; j < bytes.length; j++) {
      carry += bytes[j] * 58
      bytes[j] = carry & 0xff
      carry >>= 8
    }
    while (carry > 0) { bytes.push(carry & 0xff); carry >>= 8 }
  }
  for (const c of str) { if (c === '1') bytes.push(0); else break }
  return new Uint8Array(bytes.reverse())
}

async function sha256(data) {
  const buf = data instanceof Uint8Array ? data : new TextEncoder().encode(data)
  return new Uint8Array(await crypto.subtle.digest('SHA-256', buf))
}

async function doubleSha256(data) {
  return sha256(await sha256(data))
}

async function wifDecode(wif) {
  const raw = b58decode(wif)
  if (raw.length < 5) throw new Error('WIF too short')
  const payload = raw.slice(0, -4)
  const checksum = raw.slice(-4)
  const hash = await doubleSha256(payload)
  for (let i = 0; i < 4; i++) {
    if (hash[i] !== checksum[i]) throw new Error('Invalid WIF checksum')
  }
  const version = payload[0]
  const isTestnet = version === 0xef
  const isMainnet = version === 0x80
  if (!isTestnet && !isMainnet) throw new Error('Unknown WIF version: 0x' + version.toString(16))
  const compressed = payload.length === 34 && payload[33] === 0x01
  return { privkey: payload.slice(1, 33), compressed, testnet: isTestnet }
}

function hexToBytes(hex) {
  if (hex.length !== 64 || !/^[0-9a-fA-F]{64}$/.test(hex)) throw new Error('Invalid 64-char hex key')
  const bytes = new Uint8Array(32)
  for (let i = 0; i < 32; i++) bytes[i] = parseInt(hex.slice(i * 2, i * 2 + 2), 16)
  return bytes
}

function isHexKey(s) {
  return s.length === 64 && /^[0-9a-fA-F]{64}$/.test(s)
}

async function decodeKey(input) {
  if (isHexKey(input)) {
    return { privkey: hexToBytes(input), compressed: true, testnet: true }
  }
  return wifDecode(input)
}

function privkeyToXOnly(privkeyBytes) {
  const pub = secp256k1.getPublicKey(privkeyBytes, true)
  return pub.slice(1)
}

// ── Bech32m (for p2tr addresses) ────────────────────────

const BECH32_CHARSET = 'qpzry9x8gf2tvdw0s3jn54khce6mua7l'
const BECH32M = 0x2bc830a3

function polymod(values) {
  const GEN = [0x3b6a57b2, 0x26508e6d, 0x1ea119fa, 0x3d4233dd, 0x2a1462b3]
  let chk = 1
  for (const v of values) {
    const b = chk >> 25
    chk = ((chk & 0x1ffffff) << 5) ^ v
    for (let i = 0; i < 5; i++) if ((b >> i) & 1) chk ^= GEN[i]
  }
  return chk
}

function hrpExpand(hrp) {
  const r = []
  for (const c of hrp) r.push(c.charCodeAt(0) >> 5)
  r.push(0)
  for (const c of hrp) r.push(c.charCodeAt(0) & 31)
  return r
}

function convertBits(data, from, to, pad) {
  let acc = 0, bits = 0
  const ret = [], maxv = (1 << to) - 1
  for (const v of data) {
    acc = (acc << from) | v
    bits += from
    while (bits >= to) { bits -= to; ret.push((acc >> bits) & maxv) }
  }
  if (pad && bits > 0) ret.push((acc << (to - bits)) & maxv)
  return ret
}

function bech32mEncode(hrp, version, program) {
  const conv = convertBits(program, 8, 5, true)
  const values = [version, ...conv]
  const enc = [...hrpExpand(hrp), ...values, 0, 0, 0, 0, 0, 0]
  const mod = polymod(enc) ^ BECH32M
  const checksum = [0,1,2,3,4,5].map(i => (mod >> (5 * (5 - i))) & 31)
  let result = hrp + '1'
  for (const v of [...values, ...checksum]) result += BECH32_CHARSET[v]
  return result
}

function privkeyToAddress(privkeyBytes, testnet = true) {
  const xonly = privkeyToXOnly(privkeyBytes)
  return bech32mEncode(testnet ? 'tb' : 'bc', 1, xonly)
}

// ── Byte helpers ─────────────────────────────────────────

function bytesToHex(bytes) {
  return Array.from(bytes).map(b => b.toString(16).padStart(2, '0')).join('')
}

function hexToU8(hex) {
  const bytes = new Uint8Array(hex.length / 2)
  for (let i = 0; i < bytes.length; i++) bytes[i] = parseInt(hex.slice(i * 2, i * 2 + 2), 16)
  return bytes
}

function concatBytes(...arrays) {
  const total = arrays.reduce((s, a) => s + a.length, 0)
  const result = new Uint8Array(total)
  let off = 0
  for (const a of arrays) { result.set(a, off); off += a.length }
  return result
}

// ── Tagged hash (BIP340/341) ─────────────────────────────

async function taggedHash(tag, ...msgs) {
  const tagHash = await sha256(new TextEncoder().encode(tag))
  return sha256(concatBytes(tagHash, tagHash, ...msgs))
}

// ── Taproot key tweaking (BIP86) ─────────────────────────

const SECP_N = BigInt('0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141')

function bytesToBigInt(bytes) {
  let r = 0n
  for (const b of bytes) r = (r << 8n) | BigInt(b)
  return r
}

function bigIntToBytes(n) {
  const hex = n.toString(16).padStart(64, '0')
  return hexToU8(hex)
}

async function getTweakedKeys(privkeyBytes) {
  const xonly = privkeyToXOnly(privkeyBytes)
  const tweak = await taggedHash('TapTweak', xonly)
  const t = bytesToBigInt(tweak)
  let d = bytesToBigInt(privkeyBytes)
  const fullPub = secp256k1.getPublicKey(privkeyBytes, false)
  if (fullPub[64] & 1) d = SECP_N - d // negate if y is odd
  const tweakedD = (d + t) % SECP_N
  const tweakedPriv = bigIntToBytes(tweakedD)
  const tweakedXOnly = schnorr.getPublicKey(tweakedPriv)
  return { tweakedPriv, tweakedXOnly, internalXOnly: xonly }
}

// ── P2TR script ──────────────────────────────────────────

function p2trScript(xonlyPubkey) {
  return concatBytes(new Uint8Array([0x51, 0x20]), xonlyPubkey)
}

// ── Transaction serialization ────────────────────────────

function writeU32LE(val) {
  const b = new Uint8Array(4)
  b[0] = val & 0xff; b[1] = (val >> 8) & 0xff; b[2] = (val >> 16) & 0xff; b[3] = (val >> 24) & 0xff
  return b
}

function writeU64LE(val) {
  const b = new Uint8Array(8)
  const n = BigInt(val)
  for (let i = 0; i < 8; i++) b[i] = Number((n >> BigInt(i * 8)) & 0xffn)
  return b
}

function writeVarInt(val) {
  if (val < 0xfd) return new Uint8Array([val])
  if (val <= 0xffff) return new Uint8Array([0xfd, val & 0xff, (val >> 8) & 0xff])
  throw new Error('VarInt too large')
}

function reverseTxid(txidHex) {
  const bytes = hexToU8(txidHex)
  bytes.reverse()
  return bytes
}

function estimateVsize(numInputs, numOutputs) {
  return Math.ceil((42 + 230 * numInputs + 172 * numOutputs) / 4)
}

// ── Build & sign taproot transaction ─────────────────────

async function buildTransaction(inputs, outputs, privkeyBytes) {
  const internalXOnly = privkeyToXOnly(privkeyBytes)
  const { tweakedPriv } = await getTweakedKeys(privkeyBytes)
  const untweakedHex = '5120' + bytesToHex(internalXOnly)
  const signingKey = bytesToHex(inputs[0].scriptPubKey) === untweakedHex ? privkeyBytes : tweakedPriv

  const version = 2, locktime = 0, sequence = 0xfffffffd

  const serOutputs = outputs.map(o =>
    concatBytes(writeU64LE(o.amount), writeVarInt(o.scriptPubKey.length), o.scriptPubKey)
  )

  // BIP341 sighash precomputations
  const shaPrevouts = await sha256(concatBytes(...inputs.map(i =>
    concatBytes(reverseTxid(i.txid), writeU32LE(i.vout))
  )))
  const shaAmounts = await sha256(concatBytes(...inputs.map(i => writeU64LE(i.amount))))
  const shaScriptPubKeys = await sha256(concatBytes(...inputs.map(i =>
    concatBytes(writeVarInt(i.scriptPubKey.length), i.scriptPubKey)
  )))
  const shaSequences = await sha256(concatBytes(...inputs.map(() => writeU32LE(sequence))))
  const shaOutputs = await sha256(concatBytes(...serOutputs))

  // Sign each input
  const sigs = []
  for (let i = 0; i < inputs.length; i++) {
    const sigMsg = concatBytes(
      new Uint8Array([0x00, 0x00]), // epoch, sighash_type (SIGHASH_DEFAULT)
      writeU32LE(version), writeU32LE(locktime),
      shaPrevouts, shaAmounts, shaScriptPubKeys, shaSequences, shaOutputs,
      new Uint8Array([0x00]), // spend_type (keypath, no annex)
      writeU32LE(i)
    )
    const sighash = await taggedHash('TapSighash', sigMsg)
    sigs.push(schnorr.sign(sighash, signingKey))
  }

  // Assemble raw transaction
  const parts = [
    writeU32LE(version),
    new Uint8Array([0x00, 0x01]), // segwit marker + flag
    writeVarInt(inputs.length)
  ]
  for (const inp of inputs) {
    parts.push(reverseTxid(inp.txid), writeU32LE(inp.vout), new Uint8Array([0x00]), writeU32LE(sequence))
  }
  parts.push(writeVarInt(outputs.length))
  for (const so of serOutputs) parts.push(so)
  for (const sig of sigs) {
    parts.push(new Uint8Array([0x01]), writeVarInt(sig.length), sig)
  }
  parts.push(writeU32LE(locktime))
  return bytesToHex(concatBytes(...parts))
}

// ── Mempool API ─────────────────────────────────────────

const NETWORKS = {
  btc:   { label: 'MAINNET',  mempool: 'https://mempool.space/api',          explorer: 'https://mempool.guide/tx',          testnet: false },
  tbtc3: { label: 'TESTNET3', mempool: 'https://mempool.space/testnet/api',  explorer: 'https://mempool.guide/testnet/tx',  testnet: true },
  tbtc4: { label: 'TESTNET4', mempool: 'https://mempool.space/testnet4/api', explorer: 'https://mempool.guide/testnet4/tx', testnet: true },
}
const DEFAULT_NETWORK = 'tbtc4'

function mempoolApi(network) {
  return (NETWORKS[network] || NETWORKS[DEFAULT_NETWORK]).mempool
}

async function fetchUtxos(address, network = DEFAULT_NETWORK) {
  const res = await fetch(`${mempoolApi(network)}/address/${address}/utxo`)
  if (!res.ok) throw new Error('Mempool API error: ' + res.status)
  return res.json()
}

async function checkOutspend(txid, vout, network = DEFAULT_NETWORK) {
  try {
    const res = await fetch(`${mempoolApi(network)}/tx/${txid}/outspend/${vout}`)
    if (!res.ok) return null
    return res.json()
  } catch { return null }
}

async function fetchTxDetails(txid, network = DEFAULT_NETWORK) {
  const res = await fetch(`${mempoolApi(network)}/tx/${txid}`)
  if (!res.ok) throw new Error('Failed to fetch tx: ' + res.status)
  return res.json()
}

async function broadcastTx(rawTxHex, network = DEFAULT_NETWORK) {
  const res = await fetch(`${mempoolApi(network)}/tx`, {
    method: 'POST',
    headers: { 'Content-Type': 'text/plain' },
    body: rawTxHex
  })
  if (!res.ok) {
    const err = await res.text()
    throw new Error(err)
  }
  return res.text()
}

async function getFeeRate(network = DEFAULT_NETWORK) {
  try {
    const res = await fetch(`${mempoolApi(network)}/v1/fees/recommended`)
    if (!res.ok) return 2
    const data = await res.json()
    return data.fastestFee || data.halfHourFee || 2
  } catch { return 2 }
}

// ── Pod storage ─────────────────────────────────────────

// Vouchers contain PRIVATE KEYS — keep owner-only under /private/, never /public/.
const CONTAINER = new URL('../../../private/vouchers/', location.href).href
const DATA_PATH = CONTAINER + 'voucher-data.jsonld'

async function loadFromPod() {
  if (!(window.xlogin && window.xlogin.id)) return []   // /private/ is owner-only — only read when signed in
  try {
    const res = await authFetch(DATA_PATH + '?t=' + Date.now(), { cache: 'no-store' })
    if (!res.ok) return []
    const data = await res.json()
    const items = data['schema:itemListElement'] || []
    return items.map(item => {
      const txoUri = item['schema:identifier'] || ''
      let txid = '', vout = 0, amount = 0, privkey = '', network = DEFAULT_NETWORK
      // Parse stored TXO URI
      if (txoUri) {
        try {
          const parsed = parseTxoUri(txoUri)
          txid = parsed.txid || ''
          vout = parsed.output || 0
          amount = toSats(parsed.amount)
          privkey = parsed.privkey || ''
          network = parsed.network || DEFAULT_NETWORK
        } catch {
          // Try manual parse: txo:<network>:<txid>:<vout>?amount=<n>&key=<k>
          // or legacy space-separated: txo:<network>:<txid>:<vout> <amount> <key>
          try {
            const [uriPart, ...rest] = txoUri.split(' ')
            const [path, qs] = uriPart.split('?')
            const segs = path.replace(/^txo:/, '').split(':')
            if (segs.length >= 3) {
              network = segs[0] || DEFAULT_NETWORK
              txid = segs[1] || ''
              vout = parseInt(segs[2]) || 0
            }
            if (qs) {
              const params = new URLSearchParams(qs)
              if (params.has('amount')) amount = toSats(parseFloat(params.get('amount')))
              if (params.has('key')) privkey = params.get('key')
            }
            // Legacy space-separated fallback
            if (!amount && rest[0]) amount = toSats(parseFloat(rest[0]))
            if (!privkey && rest[1]) privkey = rest[1]
          } catch {}
        }
      }
      return {
        id: item['@id'] || Date.now().toString(36) + Math.random().toString(36).slice(2, 6),
        txid,
        vout,
        amount,
        privkey,
        address: item['schema:address'] || '',
        network,
        status: item['schema:status'] || 'unknown',
        dateAdded: item['schema:dateCreated'] || new Date().toISOString()
      }
    })
  } catch (e) {
    console.warn('Failed to load from pod:', e)
    return []
  }
}

async function saveToPod() {
  const jsonLd = {
    '@context': { schema: 'https://schema.org/' },
    '@id': '#this',
    '@type': 'schema:CreativeWork',
    'schema:additionalType': 'VoucherPool',
    'schema:name': 'Voucher Pool',
    'schema:description': 'Multi-network voucher pool',
    'schema:itemListElement': vouchers.map(v => ({
      '@type': 'schema:ListItem',
      '@id': v.id,
      'schema:identifier': buildTxoUri(v),
      'schema:address': v.address,
      'schema:status': v.status,
      'schema:dateCreated': v.dateAdded
    }))
  }
  if (window.xlogin && window.xlogin.id) {   // only write to /private/ when signed in (else just localStorage)
    try {
      // ensure the owner-only /private/vouchers/ container exists, then write
      await authFetch(CONTAINER, { method: 'PUT', headers: { 'Content-Type': 'text/turtle', 'Link': '<http://www.w3.org/ns/ldp#BasicContainer>; rel="type"' }, body: '' }).catch(() => {})
      await authFetch(DATA_PATH, {
        method: 'PUT',
        headers: { 'Content-Type': 'application/ld+json' },
        body: JSON.stringify(jsonLd, null, 2)
      })
    } catch (e) {
      console.warn('Pod save failed:', e)
    }
  }
  // Also cache in localStorage as fallback
  try { localStorage.setItem('voucher-pool-testnet4', JSON.stringify(vouchers)) } catch {}
}

// ── State ───────────────────────────────────────────────

let vouchers = []
let importing = false
let refreshing = false
let mergeMode = false
let mergeSelected = new Set()

// ── Helpers ─────────────────────────────────────────────

function truncate(s, start = 8, end = 6) {
  if (!s || s.length <= start + end + 3) return s
  return s.slice(0, start) + '...' + s.slice(-end)
}

function maskKey(wif) {
  if (!wif || wif.length < 6) return '***'
  return wif.slice(0, 3) + '...' + wif.slice(-3)
}

function satsBtc(sats) {
  return (sats / 1e8).toFixed(8)
}

function toSats(amount) {
  if (!amount) return 0
  // If already looks like sats (integer >= 1), return as-is
  if (Number.isInteger(amount) && amount >= 1) return amount
  // Otherwise treat as BTC and convert
  const converted = Math.round(amount * 1e8)
  if (converted > 2_100_000_000_000_000) return Math.round(amount)
  return converted
}

function escHtml(s) {
  return String(s).replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;')
}

function toast(msg) {
  const t = document.createElement('div')
  t.className = 'v-toast'
  t.textContent = msg
  document.body.appendChild(t)
  setTimeout(() => t.remove(), 2000)
}

function copyText(text) {
  navigator.clipboard.writeText(text).then(() => toast('Copied to clipboard'))
}

// ── Import ──────────────────────────────────────────────

async function importKey(input) {
  input = input.trim()
  if (!input) return

  // Try as TXO URI first
  if (input.startsWith('txo:') || isValidTxoUri(input)) {
    try {
      // Manual parse: txo:<network>:<txid>:<vout>?amount=<n>&key=<k>
      const [uriPart] = input.split(' ')
      const [path, qs] = uriPart.split('?')
      const segs = path.replace(/^txo:/, '').split(':')
      if (segs.length < 3) throw new Error('Invalid TXO URI')
      const params = qs ? new URLSearchParams(qs) : null
      const parsed = {
        network: segs[0] || DEFAULT_NETWORK,
        txid: segs[1],
        output: parseInt(segs[2]) || 0,
        amount: params?.get('amount') ? parseFloat(params.get('amount')) : 0,
        privkey: params?.get('key') || '',
      }
      const exists = vouchers.some(v => v.txid === parsed.txid && v.vout === parsed.output)
      if (exists) { toast('Voucher already in pool'); return }
      const v = {
        id: Date.now().toString(36),
        txid: parsed.txid,
        vout: parsed.output,
        amount: toSats(parsed.amount),
        privkey: parsed.privkey,
        address: '',
        network: parsed.network,
        status: 'unknown',
        dateAdded: new Date().toISOString()
      }
      if (v.privkey) {
        try {
          const decoded = await decodeKey(v.privkey)
          v.address = privkeyToAddress(decoded.privkey, decoded.testnet)
        } catch {}
      }
      vouchers.unshift(v)
      await saveToPod()
      toast('Voucher imported & saved')
      render()
      refreshStatus(vouchers.indexOf(v))
      return
    } catch (e) {
      console.warn('TXO parse failed, trying as WIF:', e)
    }
  }

  // Try as bare WIF key — check if it unlocks an existing keyless voucher
  try {
    const decoded = await decodeKey(input)
    const address = privkeyToAddress(decoded.privkey, decoded.testnet)
    const keyNetwork = decoded.testnet ? 'tbtc4' : 'btc'

    // Check if any existing voucher has this address but no key
    const keyless = vouchers.filter(v => !v.privkey)
    let matched = false

    if (keyless.length > 0) {
      // Look up UTXOs for this key's address
      const utxos = await fetchUtxos(address, keyNetwork)
      for (const v of keyless) {
        const matchesUtxo = utxos.some(u => u.txid === v.txid && u.vout === v.vout)
        if (matchesUtxo) {
          v.privkey = input
          v.address = address
          v.status = 'unspent'
          const u = utxos.find(u => u.txid === v.txid && u.vout === v.vout)
          if (u && u.value) v.amount = u.value
          matched = true
        }
      }
      if (matched) {
        await saveToPod()
        toast('Key added to voucher & saved')
        render()
        return
      }
    }

    // No existing match — fetch UTXOs and import as new vouchers
    toast('Looking up UTXOs...')
    const utxos = await fetchUtxos(address, keyNetwork)

    if (utxos.length === 0) {
      toast('No UTXOs found for this key')
      return
    }

    let added = 0
    for (const u of utxos) {
      const exists = vouchers.some(v => v.txid === u.txid && v.vout === u.vout)
      if (exists) continue
      vouchers.unshift({
        id: Date.now().toString(36) + added,
        txid: u.txid,
        vout: u.vout,
        amount: u.value,
        privkey: input,
        address,
        network: keyNetwork,
        status: u.status?.confirmed ? 'unspent' : 'unconfirmed',
        dateAdded: new Date().toISOString()
      })
      added++
    }

    if (added === 0) {
      toast('All UTXOs already in pool')
    } else {
      await saveToPod()
      toast(`Imported ${added} voucher${added > 1 ? 's' : ''} & saved`)
    }
    render()
  } catch (e) {
    toast('Import failed: ' + e.message)
    console.error(e)
  }
}

// ── Refresh status ──────────────────────────────────────

async function refreshStatus(index) {
  if (index !== undefined) {
    const v = vouchers[index]
    if (!v) return
    const result = await checkOutspend(v.txid, v.vout, v.network)
    if (result) {
      v.status = result.spent ? 'spent' : 'unspent'
      await saveToPod()
      render()
    }
    return
  }

  refreshing = true
  render()
  for (let i = 0; i < vouchers.length; i++) {
    const v = vouchers[i]
    try {
      const result = await checkOutspend(v.txid, v.vout, v.network)
      if (result) {
        v.status = result.spent ? 'spent' : 'unspent'
      }
    } catch {}
  }
  await saveToPod()
  refreshing = false
  render()
}

// ── Delete ──────────────────────────────────────────────

async function deleteVoucher(id) {
  vouchers = vouchers.filter(v => v.id !== id)
  await saveToPod()
  render()
}

// ── Split ────────────────────────────────────────────────

async function splitVoucher(voucherId, numSplits) {
  const v = vouchers.find(x => x.id === voucherId)
  if (!v || !v.privkey || v.status !== 'unspent') {
    toast('Voucher must be unspent with a key'); return
  }
  const decoded = await decodeKey(v.privkey)

  // Fetch actual scriptPubKey from chain
  const txDetails = await fetchTxDetails(v.txid, v.network)
  const prevOut = txDetails.vout[v.vout]
  if (!prevOut) { toast('Could not find output'); return }
  const scriptPubKey = hexToU8(prevOut.scriptpubkey)

  const feeRate = await getFeeRate(v.network)
  const vsize = estimateVsize(1, numSplits)
  const fee = Math.ceil(vsize * feeRate)
  const available = v.amount - fee
  if (available <= 0) { toast('Not enough funds for fee'); return }

  const perOutput = Math.floor(available / numSplits)
  if (perOutput <= 546) { toast('Split amounts too small (dust)'); return }

  // Output script matches the input's scriptPubKey
  const outputScript = scriptPubKey

  const outputs = []
  let remaining = available
  for (let i = 0; i < numSplits; i++) {
    const amt = i === numSplits - 1 ? remaining : perOutput
    outputs.push({ amount: amt, scriptPubKey: outputScript })
    remaining -= amt
  }

  if (!confirm(`Split ${v.amount.toLocaleString()} sats into ${numSplits} outputs of ~${perOutput.toLocaleString()} sats each?\nFee: ${fee} sats (${feeRate} sat/vB)`)) return

  toast('Building transaction...')
  const rawTx = await buildTransaction(
    [{ txid: v.txid, vout: v.vout, amount: v.amount, scriptPubKey }],
    outputs, decoded.privkey
  )
  const newTxid = await broadcastTx(rawTx, v.network)
  toast('Split broadcast! ' + truncate(newTxid))

  v.status = 'spent'
  for (let i = 0; i < outputs.length; i++) {
    vouchers.unshift({
      id: Date.now().toString(36) + i,
      txid: newTxid, vout: i,
      amount: outputs[i].amount,
      privkey: v.privkey, address: v.address,
      network: v.network, status: 'unspent',
      dateAdded: new Date().toISOString()
    })
  }
  await saveToPod()
  render()
}

// ── Merge ────────────────────────────────────────────────

async function mergeVouchers() {
  const selected = [...mergeSelected].map(id => vouchers.find(x => x.id === id)).filter(Boolean)
  if (selected.length < 2) { toast('Select at least 2 vouchers'); return }
  if (selected.some(v => !v.privkey || v.status !== 'unspent')) { toast('All must be unspent with keys'); return }

  const key = selected[0].privkey
  const net = selected[0].network
  if (!selected.every(v => v.privkey === key)) { toast('All vouchers must use the same key'); return }
  if (!selected.every(v => v.network === net)) { toast('All vouchers must be on the same network'); return }

  const decoded = await decodeKey(key)

  // Fetch scriptPubKeys for each input
  const inputs = []
  for (const v of selected) {
    const details = await fetchTxDetails(v.txid, net)
    const out = details.vout[v.vout]
    if (!out) { toast('Could not find output for ' + truncate(v.txid)); return }
    inputs.push({ txid: v.txid, vout: v.vout, amount: v.amount, scriptPubKey: hexToU8(out.scriptpubkey) })
  }

  const feeRate = await getFeeRate(net)
  const vsize = estimateVsize(selected.length, 1)
  const fee = Math.ceil(vsize * feeRate)
  const totalInput = selected.reduce((s, v) => s + v.amount, 0)
  const outputAmount = totalInput - fee
  if (outputAmount <= 546) { toast('Not enough funds for fee'); return }

  if (!confirm(`Merge ${selected.length} vouchers (${totalInput.toLocaleString()} sats) into one?\nOutput: ${outputAmount.toLocaleString()} sats\nFee: ${fee} sats (${feeRate} sat/vB)`)) return

  toast('Building transaction...')
  const outputScript = inputs[0].scriptPubKey
  const rawTx = await buildTransaction(inputs, [{ amount: outputAmount, scriptPubKey: outputScript }], decoded.privkey)
  const newTxid = await broadcastTx(rawTx, net)
  toast('Merge broadcast! ' + truncate(newTxid))

  for (const v of selected) v.status = 'spent'
  vouchers.unshift({
    id: Date.now().toString(36),
    txid: newTxid, vout: 0,
    amount: outputAmount,
    privkey: key, address: selected[0].address,
    network: net, status: 'unspent',
    dateAdded: new Date().toISOString()
  })
  mergeSelected.clear()
  mergeMode = false
  await saveToPod()
  render()
}

// ── Build TXO URI ───────────────────────────────────────

function buildTxoUri(v) {
  const base = `txo:${v.network || DEFAULT_NETWORK}:${v.txid}:${v.vout}`
  const params = []
  if (v.amount) params.push(`amount=${v.amount}`)
  if (v.privkey) params.push(`key=${v.privkey}`)
  return params.length ? `${base}?${params.join('&')}` : base
}

// ── Render ──────────────────────────────────────────────

const app = document.getElementById('app')

// ── Identity address (your key → testnet4 taproot) ──────
// Your secp256k1 identity key IS a taproot key. Nostr login: the x-only pubkey is
// window.nostr.getPublicKey(). Solid login: the WebID's CID Multikey
// (publicKeyMultibase) — strip the multibase + multicodec prefix to the x-only.
// Then bech32m("tb", 1, x-only) = your testnet4 address (key = address, no tweak).
let identityAddr = null, identityType = null, identityBalance = 0

function decodeMultibaseXOnly(mb) {
  try {
    let bytes
    if (mb[0] === 'f') bytes = hexToU8(mb.slice(1))          // base16 multibase
    else if (mb[0] === 'z') bytes = b58decode(mb.slice(1))   // base58btc multibase
    else return null
    if (bytes[0] === 0xe7 && bytes[1] === 0x01) bytes = bytes.slice(2)                    // secp256k1-pub multicodec
    if (bytes.length === 33 && (bytes[0] === 2 || bytes[0] === 3)) bytes = bytes.slice(1) // compressed -> x-only
    return bytes.length === 32 ? bytes : null
  } catch { return null }
}
async function identityXOnly() {
  const x = window.xlogin
  if (!x || !x.id) return null
  if (x.type === 'nostr') {
    try { const pk = window.nostr ? await window.nostr.getPublicKey() : String(x.id); if (isHexKey(pk)) { identityType = 'Nostr'; return hexToBytes(pk) } } catch {}
    return null
  }
  try {  // Solid: read the WebID's CID Multikey (public profile, plain fetch)
    const webid = String(x.id).replace(/#.*$/, '')
    const doc = await fetch(webid, { headers: { Accept: 'application/ld+json' } }).then(r => r.ok ? r.json() : null)
    let vms = (doc && doc.verificationMethod) || []
    if (!Array.isArray(vms)) vms = [vms]
    for (const vm of vms) { const xonly = vm && vm.publicKeyMultibase && decodeMultibaseXOnly(vm.publicKeyMultibase); if (xonly) { identityType = 'Solid WebID'; return xonly } }
  } catch {}
  return null
}
async function computeIdentity() {
  identityAddr = null; identityType = null; identityBalance = 0
  const xonly = await identityXOnly()
  if (xonly) identityAddr = bech32mEncode('tb', 1, xonly)   // testnet4 taproot, witness v1
  render()
  if (identityAddr) {   // show what's been received at it (read-only, public address)
    try { const u = await fetchUtxos(identityAddr, 'tbtc4'); identityBalance = u.reduce((s, x) => s + (x.value || 0), 0); render() } catch {}
  }
}

// Import your identity address as a spendable voucher, sourcing the secret from
// the JSS-provisioned owner key at /private/privkey.jsonld (--provision-keys):
// CID Multikey, secretKeyMultibase = "f" + "8126" (secp256k1-priv) + 64-hex secret.
// Only imports if the key derives to the address shown (no wrong-key imports).
async function importIdentityVoucher() {
  try {
    const keyUrl = new URL('../../../private/privkey.jsonld', location.href).href
    const doc = await authFetch(keyUrl, { headers: { Accept: 'application/ld+json' } }).then(r => r.ok ? r.json() : null)
    const node = doc && (doc.secretKeyMultibase ? doc : (Array.isArray(doc['@graph']) ? doc['@graph'].find(n => n && n.secretKeyMultibase) : null))
    const skmb = node && node.secretKeyMultibase
    if (!skmb) { toast('No owner key at /private/privkey.jsonld (start JSS with --provision-keys)'); return }
    let h = skmb[0] === 'f' ? skmb.slice(1) : ''
    if (h.startsWith('8126')) h = h.slice(4)                        // secp256k1-priv multicodec
    if (!/^[0-9a-f]{64}$/i.test(h)) { toast("Couldn't parse the provisioned key"); return }
    const secretHex = h.toLowerCase()
    if (privkeyToAddress(hexToBytes(secretHex), true) !== identityAddr) { toast('Provisioned key does not match your address — not importing'); return }
    importing = true; render()
    await importKey(secretHex)
    importing = false; render()
  } catch (e) { importing = false; toast('Import failed: ' + (e.message || e)); render() }
}

function render() {
  const unspent = vouchers.filter(v => v.status === 'unspent')
  const totalSats = unspent.reduce((s, v) => s + (v.amount || 0), 0)

  // Group unspent balances by network
  const balByNet = {}
  for (const v of unspent) {
    const net = v.network || DEFAULT_NETWORK
    balByNet[net] = (balByNet[net] || 0) + (v.amount || 0)
  }
  const netKeys = Object.keys(balByNet)

  // Collect all networks present in pool
  const allNets = [...new Set(vouchers.map(v => v.network || DEFAULT_NETWORK))]

  let html = `
    <div class="v-header">
      <div class="v-title">\u{1F3AB} Voucher Pool ${allNets.map(n => `<span class="v-net">${(NETWORKS[n] || {}).label || n.toUpperCase()}</span>`).join(' ')}</div>
    </div>

    <div class="v-hero">
      <div class="v-hero-label">Available Balance</div>
      <div class="v-hero-sats">${totalSats.toLocaleString()} <span style="font-size:0.4em;color:rgba(255,255,255,0.35)">sats</span></div>
      ${netKeys.length > 1 ? `<div class="v-hero-nets">${netKeys.map(n =>
        `<span style="font-size:0.85rem;color:rgba(255,255,255,0.45)">${(NETWORKS[n] || {}).label || n}: ${balByNet[n].toLocaleString()} sats</span>`
      ).join(' &middot; ')}</div>` : `<div class="v-hero-btc">${satsBtc(totalSats)} ${netKeys[0] === 'btc' ? 'BTC' : 'tBTC'}</div>`}
    </div>

    <div class="v-stats">
      <div class="v-stat">
        <div class="v-stat-val">${vouchers.length}</div>
        <div class="v-stat-label">Total Vouchers</div>
      </div>
      <div class="v-stat">
        <div class="v-stat-val" style="color:#10b981">${unspent.length}</div>
        <div class="v-stat-label">Unspent</div>
      </div>
      <div class="v-stat">
        <div class="v-stat-val" style="color:#ef4444">${vouchers.filter(v => v.status === 'spent').length}</div>
        <div class="v-stat-label">Spent</div>
      </div>
    </div>

    ${identityAddr ? `<div class="v-card">
      <h2>Your testnet4 address <a href="${((NETWORKS['tbtc4'] || {}).explorer || 'https://mempool.guide/testnet4/tx').replace('/tx', '/address')}/${identityAddr}" target="_blank" rel="noopener" style="font-size:.72rem;font-weight:600;color:#60a5fa;text-decoration:none">open in explorer &#8599;</a></h2>
      <div class="v-item-val" id="v-idaddr" style="cursor:pointer" title="from your ${identityType || 'identity'} key — click to copy">${escHtml(identityAddr)}</div>
      <div class="v-help">Derived from your ${identityType || 'identity'} key.${identityBalance > 0 ? ` <b style="color:#10b981">${identityBalance.toLocaleString()} sats</b> received here.` : ' Receive testnet4 coins here (faucets below).'}</div>
      ${identityBalance > 0 ? `<button class="v-btn v-btn-primary" id="v-id-import" style="margin-top:10px">${importing ? '<span class="v-spinner"></span>' : 'Import as voucher'}</button>` : ''}
    </div>` : ''}

    <div class="v-card">
      <h2>Import Voucher</h2>
      <div class="v-import-row">
        <input class="v-input" id="v-import-input" placeholder="Paste hex key, WIF, or TXO URI..." />
        <button class="v-btn v-btn-primary" id="v-import-btn">${importing ? '<span class="v-spinner"></span>' : 'Import'}</button>
      </div>
      <div class="v-help">
        Accepts 64-char hex keys, WIF private keys (testnet4), or TXO URIs.<br/>
        Tip: use <code>?key=cN...</code> in the URL to auto-import from a faucet link.
      </div>
    </div>

    <div class="v-card">
      <h2>
        Vouchers
        <div style="display:flex;gap:6px">
          ${vouchers.filter(v => v.privkey && v.status === 'unspent').length >= 2 ?
            `<button class="v-btn v-btn-sm" id="v-merge-toggle" style="${mergeMode ? 'color:#a78bfa;border-color:rgba(167,139,250,0.4)' : ''}">${mergeMode ? '\u2716 Cancel' : '\u{1F500} Merge'}</button>` : ''}
          <button class="v-btn v-btn-sm" id="v-refresh-btn" ${refreshing ? 'disabled' : ''}>
            ${refreshing ? '<span class="v-spinner"></span> Checking...' : '\u21BB Refresh'}
          </button>
          ${vouchers.length > 0 ? '<button class="v-btn v-btn-sm v-btn-danger" id="v-clear-btn">\u2716 Clear All</button>' : ''}
        </div>
      </h2>
      <div id="v-list">
  `

  if (vouchers.length === 0) {
    html += '<div class="v-empty">No vouchers yet. Import a key or TXO URI to get started.</div>'
  } else {
    for (const v of vouchers) {
      const hasKey = !!v.privkey
      const badgeClass = v.status === 'unspent' ? 'v-badge-unspent' : v.status === 'spent' ? 'v-badge-spent' : 'v-badge-unknown'
      const badgeLabel = v.status === 'unspent' ? 'Unspent' : v.status === 'spent' ? 'Spent' : 'Unknown'
      html += `
        <div class="v-item" data-id="${v.id}" style="${!hasKey ? 'border-color:rgba(251,191,36,0.2)' : mergeSelected.has(v.id) ? 'border-color:rgba(167,139,250,0.4)' : ''}">
          <div class="v-item-top">
            <div class="v-item-amount" style="display:flex;align-items:center;gap:8px">
              ${mergeMode && hasKey && v.status === 'unspent' ? `<input type="checkbox" data-action="merge-check" data-id="${v.id}" ${mergeSelected.has(v.id) ? 'checked' : ''} style="width:16px;height:16px;accent-color:#7c3aed;cursor:pointer" />` : ''}
              ${(v.amount || 0).toLocaleString()} <small>sats</small>
              <span class="v-badge ${badgeClass}"><span class="v-badge-dot"></span>${badgeLabel}</span>
              <span class="v-badge v-badge-net">${(NETWORKS[v.network] || {}).label || (v.network || '').toUpperCase()}</span>
              ${!hasKey ? '<span class="v-badge v-badge-locked"><span class="v-badge-dot"></span>No Key</span>' : ''}
            </div>
            <div class="v-item-actions">
              ${!hasKey ? `<button class="v-btn v-btn-sm" data-action="add-key" data-id="${v.id}" style="color:#fbbf24;border-color:rgba(251,191,36,0.3)">\u{1F511} Add Key</button>` : ''}
              ${hasKey && v.status === 'unspent' && !mergeMode ? `<button class="v-btn v-btn-sm" data-action="split" data-id="${v.id}" title="Split voucher">\u2702 Split</button>` : ''}
              ${hasKey ? `<button class="v-btn v-btn-icon" data-action="copy-txo" data-id="${v.id}" title="Copy TXO URI">\u2398</button>` : ''}
              ${hasKey ? `<button class="v-btn v-btn-icon" data-action="share" data-id="${v.id}" title="Copy share link">\u{1F517}</button>` : ''}
              ${hasKey ? `<button class="v-btn v-btn-icon" data-action="copy-key" data-id="${v.id}" title="Copy private key">\u{1F511}</button>` : ''}
              <button class="v-btn v-btn-icon" data-action="save" data-id="${v.id}" title="Save to pod">\u{1F4BE}</button>
              <button class="v-btn v-btn-icon v-btn-danger" data-action="delete" data-id="${v.id}" title="Delete">\u2716</button>
            </div>
          </div>
          <div class="v-item-details">
            <span class="v-item-label">TXID</span>
            <a class="v-item-val" href="${(NETWORKS[v.network] || NETWORKS[DEFAULT_NETWORK]).explorer}/${v.txid}" target="_blank" rel="noopener" style="color:rgba(167,139,250,0.8);text-decoration:none">${truncate(v.txid)}:${v.vout}</a>
            ${v.address ? `
              <span class="v-item-label">Address</span>
              <span class="v-item-val" data-action="copy-raw" data-val="${v.address}">${truncate(v.address, 10, 6)}</span>
            ` : ''}
            ${hasKey ? `
              <span class="v-item-label">Key</span>
              <span class="v-item-val v-masked" data-action="reveal" data-full="${escHtml(v.privkey)}">${maskKey(v.privkey)}</span>
            ` : ''}
          </div>
          <div class="v-add-key-row" style="display:none;margin-top:10px">
            <div class="v-import-row">
              <input class="v-input" placeholder="Paste hex or WIF private key..." data-keyinput="${v.id}" />
              <button class="v-btn v-btn-primary v-btn-sm" data-action="submit-key" data-id="${v.id}">\u{1F511} Unlock</button>
            </div>
          </div>
          <div class="v-split-row" style="display:none;margin-top:10px">
            <div style="display:flex;gap:8px;align-items:center;flex-wrap:wrap">
              <span style="color:rgba(255,255,255,0.5);font-size:0.82rem">Split into</span>
              <input type="number" class="v-input" value="2" min="2" max="100" style="width:70px;text-align:center" data-split-count="${v.id}" />
              <span style="color:rgba(255,255,255,0.5);font-size:0.82rem">outputs</span>
              <button class="v-btn v-btn-primary v-btn-sm" data-action="confirm-split" data-id="${v.id}">\u2702 Confirm</button>
              <button class="v-btn v-btn-sm" data-action="cancel-split" data-id="${v.id}">\u2716</button>
            </div>
          </div>
        </div>
      `
    }
  }

  if (mergeMode && mergeSelected.size >= 2) {
    const mergeSats = [...mergeSelected].reduce((s, id) => {
      const v = vouchers.find(x => x.id === id)
      return s + (v?.amount || 0)
    }, 0)
    html += `
      <div style="margin-top:12px;padding:14px;background:rgba(124,58,237,0.1);border:1px solid rgba(124,58,237,0.3);border-radius:10px;display:flex;align-items:center;justify-content:space-between;flex-wrap:wrap;gap:8px">
        <span style="font-size:0.88rem">Merge <strong>${mergeSelected.size}</strong> vouchers (${mergeSats.toLocaleString()} sats)</span>
        <button class="v-btn v-btn-primary" id="v-merge-confirm">\u{1F500} Merge Now</button>
      </div>
    `
  }

  html += `
      </div>
    </div>
  `

  app.innerHTML = html
  bindEvents()
}

function bindEvents() {
  document.getElementById('v-idaddr')?.addEventListener('click', () => copyText(identityAddr))
  document.getElementById('v-id-import')?.addEventListener('click', importIdentityVoucher)
  // Import
  const importBtn = document.getElementById('v-import-btn')
  const importInput = document.getElementById('v-import-input')
  if (importBtn && importInput) {
    const doImport = async () => {
      if (importing) return
      importing = true
      render()
      await importKey(importInput.value)
      importing = false
      render()
    }
    importBtn.addEventListener('click', doImport)
    importInput.addEventListener('keydown', e => { if (e.key === 'Enter') doImport() })
    importInput.addEventListener('input', () => { if (isHexKey(importInput.value.trim())) doImport() })
  }

  // Refresh
  document.getElementById('v-refresh-btn')?.addEventListener('click', () => refreshStatus())

  // Clear all
  document.getElementById('v-clear-btn')?.addEventListener('click', async () => {
    if (!confirm('Delete all vouchers?')) return
    vouchers = []
    await saveToPod()
    render()
  })

  // Merge toggle
  document.getElementById('v-merge-toggle')?.addEventListener('click', () => {
    mergeMode = !mergeMode
    mergeSelected.clear()
    render()
  })

  // Merge checkboxes
  document.querySelectorAll('[data-action="merge-check"]').forEach(cb => {
    cb.addEventListener('change', () => {
      if (cb.checked) mergeSelected.add(cb.dataset.id)
      else mergeSelected.delete(cb.dataset.id)
      render()
    })
  })

  // Merge confirm
  document.getElementById('v-merge-confirm')?.addEventListener('click', async () => {
    try { await mergeVouchers() } catch (e) { toast('Merge failed: ' + e.message); console.error(e) }
  })

  // Split toggle
  document.querySelectorAll('[data-action="split"]').forEach(btn => {
    btn.addEventListener('click', () => {
      const item = btn.closest('.v-item')
      const row = item?.querySelector('.v-split-row')
      if (row) {
        const visible = row.style.display !== 'none'
        row.style.display = visible ? 'none' : 'block'
        if (!visible) row.querySelector('input[type="number"]')?.focus()
      }
    })
  })

  // Confirm split
  document.querySelectorAll('[data-action="confirm-split"]').forEach(btn => {
    btn.addEventListener('click', async () => {
      const item = btn.closest('.v-item')
      const countInput = item?.querySelector('input[type="number"]')
      const n = parseInt(countInput?.value) || 2
      if (n < 2 || n > 100) { toast('Split into 2-100 outputs'); return }
      try { await splitVoucher(btn.dataset.id, n) } catch (e) { toast('Split failed: ' + e.message); console.error(e) }
    })
  })

  // Cancel split
  document.querySelectorAll('[data-action="cancel-split"]').forEach(btn => {
    btn.addEventListener('click', () => {
      const row = btn.closest('.v-split-row')
      if (row) row.style.display = 'none'
    })
  })

  // Add Key toggle
  document.querySelectorAll('[data-action="add-key"]').forEach(btn => {
    btn.addEventListener('click', () => {
      const item = btn.closest('.v-item')
      const row = item?.querySelector('.v-add-key-row')
      if (row) {
        const visible = row.style.display !== 'none'
        row.style.display = visible ? 'none' : 'block'
        if (!visible) row.querySelector('input')?.focus()
      }
    })
  })

  // Submit key for a specific voucher
  document.querySelectorAll('[data-action="submit-key"]').forEach(btn => {
    btn.addEventListener('click', async () => {
      const id = btn.dataset.id
      const input = btn.closest('.v-add-key-row')?.querySelector('input')
      const wif = input?.value?.trim()
      if (!wif) { toast('Paste a WIF key'); return }
      const v = vouchers.find(x => x.id === id)
      if (!v) return
      try {
        const decoded = await decodeKey(wif)
        const address = privkeyToAddress(decoded.privkey, decoded.testnet)
        // Verify key matches this UTXO
        const utxos = await fetchUtxos(address, v.network)
        const match = utxos.find(u => u.txid === v.txid && u.vout === v.vout)
        if (!match) {
          toast('Key does not match this UTXO')
          return
        }
        v.privkey = wif
        v.address = address
        v.status = 'unspent'
        if (match.value) v.amount = match.value
        await saveToPod()
        toast('Key added & saved!')
        render()
      } catch (e) {
        toast('Invalid key: ' + e.message)
      }
    })
  })

  // Auto-submit on 64-char hex paste, or Enter key
  document.querySelectorAll('.v-add-key-row input').forEach(input => {
    const submit = () => input.closest('.v-add-key-row')?.querySelector('[data-action="submit-key"]')?.click()
    input.addEventListener('keydown', e => { if (e.key === 'Enter') submit() })
    input.addEventListener('input', () => {
      const val = input.value.trim()
      if (isHexKey(val)) submit()
    })
  })

  document.querySelectorAll('[data-action="copy-txo"]').forEach(btn => {
    btn.addEventListener('click', () => {
      const v = vouchers.find(x => x.id === btn.dataset.id)
      if (v) copyText(buildTxoUri(v))
    })
  })

  document.querySelectorAll('[data-action="share"]').forEach(btn => {
    btn.addEventListener('click', () => {
      const v = vouchers.find(x => x.id === btn.dataset.id)
      if (v?.privkey) {
        const url = `${location.origin}${location.pathname}?key=${v.privkey}`
        copyText(url)
      }
    })
  })

  document.querySelectorAll('[data-action="copy-key"]').forEach(btn => {
    btn.addEventListener('click', () => {
      const v = vouchers.find(x => x.id === btn.dataset.id)
      if (v?.privkey) copyText(v.privkey)
      else toast('No private key')
    })
  })

  document.querySelectorAll('[data-action="save"]').forEach(btn => {
    btn.addEventListener('click', async () => {
      await saveToPod()
      toast('Saved to pod')
    })
  })

  document.querySelectorAll('[data-action="delete"]').forEach(btn => {
    btn.addEventListener('click', () => deleteVoucher(btn.dataset.id))
  })

  document.querySelectorAll('[data-action="copy-raw"]').forEach(el => {
    el.addEventListener('click', () => copyText(el.dataset.val))
  })

  document.querySelectorAll('[data-action="reveal"]').forEach(el => {
    el.addEventListener('click', () => {
      if (el.classList.contains('v-masked')) {
        el.textContent = el.dataset.full
        el.classList.remove('v-masked')
      } else {
        el.textContent = maskKey(el.dataset.full)
        el.classList.add('v-masked')
      }
    })
  })
}

// ── Init ────────────────────────────────────────────────

async function init() {
  const params = new URLSearchParams(location.search)
  const keyParam = params.get('key')

  // Load from pod and localStorage, merge by txid:vout
  const podVouchers = await loadFromPod()
  let localVouchers = []
  try {
    localVouchers = JSON.parse(localStorage.getItem('voucher-pool-testnet4') || '[]')
  } catch {}

  // Index by txid:vout to deduplicate (pod wins on conflicts)
  const seen = new Map()
  for (const v of podVouchers) seen.set(`${v.txid}:${v.vout}`, v)
  for (const v of localVouchers) {
    const key = `${v.txid}:${v.vout}`
    if (!seen.has(key)) seen.set(key, v)
  }
  vouchers = [...seen.values()]

  render()
  computeIdentity()   // derive + show your testnet4 address from your nostr/Solid identity key

  if (keyParam) {
    history.replaceState({}, '', location.pathname)
    importing = true
    render()
    await importKey(keyParam)
    importing = false
    render()
  }

  if (vouchers.length > 0) {
    refreshStatus()
  }
}

init()
// re-load /private/ vouchers when the xlogin session changes (uses xlogin.authFetch)
document.addEventListener('xlogin', () => init())
document.addEventListener('xlogout', () => render())
