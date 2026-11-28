---
upstream: none
checked: 2026-11-28
links: []
blocks-proof: no
---

# cache: a cache whose prefix is all `0xff` bytes rejects every key under it

`Cache.validateRange` (`cache/cache.go`) bounds a request by `[c.prefix,
clientv3.GetPrefixRangeEnd(c.prefix))`. For a prefix made only of `0xff` bytes (`"\xff"`,
`"\xff\xff"`), `GetPrefixRangeEnd` returns `"\x00"`, the from-key marker, which `validateRange` then
compares as a literal key: a single key `k` under the prefix fails `bytes.Compare(k, "\x00") < 0`, a
range fails `bytes.Compare(endKey, "\x00") <= 0`, and the prefix's own from-key request is refused by
the `isFromKey` case (`c.prefix != ""`). Every `Get` and `Watch` of such a cache returns
`ErrKeyRangeInvalid`, although the cache's own watch (`WithPrefix`, which the watch server turns into
a from-key range) does serve the keys under the prefix.

**Why not an issue:** no test; found by code reading (N1b-3, removing the proofs' premise excluding
such prefixes). The cache is experimental and best-effort; no caller in etcd, this repository's
examples or Kubernetes builds a cache on an all-`0xff` prefix. A test could promote it: `New(cl,
"\xff")`, then `Get("\xff1")`, expecting no `ErrKeyRangeInvalid`.

## Proof

no: `Cache.validateRange.spec`'s `validRange` (`Proof/go_etcd_io/etcd/cache/v3/InvCache.lean`)
states what the code does (the literal `prefixRangeEnd pfx` bound), so the cache's specs allow the
error; the end-to-end results hold for every non-empty prefix (since N1b-3).

## Notes

A fix would treat a `"\x00"` prefix end as unbounded in `validateRange`.
