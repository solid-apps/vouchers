# vouchers

Organize your **Bitcoin vouchers** on your [Solid](https://solidproject.org) pod.
A voucher is a funded key recorded as a **TXO URI**
(`txo:<network>:<txid>:<vout>?amount=<sats>&key=<privkey>`); the app derives its
taproot address, checks balance + spent status via mempool.space, and can sweep
funds.

Ported from [melvincarvalho/gamestr-adjacent Voucher Pool] — the proven Bitcoin
crypto (BIP340/341/86 taproot, transaction building/signing/broadcast) is kept
**verbatim**; only storage and the app shell were adapted for the suite.

## ⚠️ Security — keys are private

Voucher data **contains private keys**. This build stores it **owner-only** at
`<pod>/private/vouchers/voucher-data.jsonld` (not `/public/`), and reads it with
authenticated requests. Keep it that way. Networks include testnet3/4 **and
mainnet** (`btc`) — treat mainnet keys accordingly.

## Data model

```
<pod>/private/vouchers/voucher-data.jsonld
{ "@context": { "schema": "https://schema.org/" },
  "@type": "schema:CreativeWork", "schema:additionalType": "VoucherPool",
  "schema:itemListElement": [
    { "@type": "schema:ListItem",
      "schema:identifier": "txo:tbtc4:<txid>:<vout>?amount=<sats>&key=<privkey>",
      "schema:address": "tb1p…", "schema:status": "unspent",
      "schema:dateCreated": "…" } ] }
```

## Notes

- Auth uses **nip98** (NIP-98 HTTP auth) for pod read/write, as in the original —
  i.e. it authenticates with a nostr key, not the Solid OIDC login pill.
- Balance / spent / sweep use the public `mempool.space` APIs (no key needed).
- Crypto deps load at runtime from esm.sh (`txo_parser`, `@noble/curves`, `nip98`).

## Run

Static — open `index.html`, or install via the **store** to
`/public/apps/vouchers/`.

AGPL-3.0-only.
