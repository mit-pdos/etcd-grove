# No proof-only premises, stage N1b

Rule (Upamanyu): a top-level statement takes no premise that only simplifies a proof. Ledger entries:
`notes/specs-only/ledger.md`, 2026-11-28.

## N1b-3: the cache's "prefix not all `0xff`" premise

The cache's results over etcd's client took `prefixRangeEnd pfx ≠ [W8 0]`: the prefix is not made
only of `0xff` bytes, where `clientv3.GetPrefixRangeEnd` returns `"\x00"` (the from-key marker,
`getPrefix` in `client/v3/op.go`).

**Why it was not needed.** For a non-empty `p` all `0xff`, `¬ (k < p) ↔ p <+: k` in Go's byte order
(no byte exceeds `0xff`, so a key not below `p` agrees with `p` on its first `|p|` bytes, and is not
shorter); `concurrency.inRange_prefix` already proved `inRange p (prefixRangeEnd p) k ↔ p <+: k` for
every non-empty `p`, the from-key case included (`ff_not_lt_iff`). Go treats the end `"\x00"` as
from-key where the cache's watch is served: the watch server's `recvLoop` turns `RangeEnd ==
"\x00"` into `[]byte{}` (`v3rpc.createRangeOk`'s `some []`), and `inRange` (the KV model's ranges)
reads `[0]` as from-key. The only use of the premise was a proof-internal range: `pfxRange pfx`
(`KMWatchDefs.lean`) registered `some (prefixRangeEnd pfx)`, i.e. a literal end `[0]`, which covers
no key; it now registers `[]` for that case, as the watch server does, and `pfxRange_covers` holds
for every non-empty prefix. `WatchCompl.covers_prefix` (unused) dropped it too, through
`rangeExact_of_ne`. The empty prefix is still excluded by the separate premise `pfx ≠ []` (not this
stage's).

Go divergence found on the way (not used by any proof): the cache's own `validateRange` compares the
literal `"\x00"`, so a cache on an all-`0xff` prefix rejects every request
(`nonissues/etcd-cache-all-ff-prefix-rejects-keys.md`); `Cache.validateRange.spec` states that
behaviour, so the results stay true (such requests return `ErrKeyRangeInvalid`).

**Top-level statements** (`Proof/go_etcd_io/etcd/cache/v3/Results.lean`, roots of
`etc/tcb-collections/cache-client.txt`). Before:

```lean
theorem cache_end_to_end_client (cl w api : Loc) (γ : client.KMNames) (dup : Bool)
    (pfx : GoString) (hp : pfx ≠ []) (hff : prefixRangeEnd pfx ≠ [W8 0])
    (hpl : pfx.length ≤ 2 ^ 28) (sl : GoSlice) (gs : List (Config → Config)) : {{ … }} … {{ … }}

theorem cache_end_to_end_new … (hst : kvSame γr.kv γ.kv) (hrb : receiptBound GF ≤ 2 ^ 62)
    (hff : prefixRangeEnd V.pfx ≠ [W8 0]) (hpl : V.pfx.length ≤ 2 ^ 28) (sl : GoSlice) … 
```

After (the triples unchanged):

```lean
theorem cache_end_to_end_client (cl w api : Loc) (γ : client.KMNames) (dup : Bool)
    (pfx : GoString) (hp : pfx ≠ [])
    (hpl : pfx.length ≤ 2 ^ 28) (sl : GoSlice) (gs : List (Config → Config)) : {{ … }} … {{ … }}

theorem cache_end_to_end_new … (hst : kvSame γr.kv γ.kv) (hrb : receiptBound GF ≤ 2 ^ 62)
    (hpl : V.pfx.length ≤ 2 ^ 28) (sl : GoSlice) …
```

Intermediate statements that lost it: `client.pfxRange_covers`, `pfxRange_cov`, `rangeEvents_take`,
`watchRespOk_of_km`, `etcdWatchElem_of_km` (`KMWatchDefs.lean`), `isEtcdWatcher_of_km`
(`KMWatch.lean`), `isEtcdClient_of_km` (`KMClient.lean`), `covers_prefix` (`WatchCompl.lean`),
`isEtcdClient_of_dist` (`dist/client/CacheWorkDefs.lean`), `isEtcdWatcher_of_kmW`
(`dist/client/WatchWorkDefs.lean`); their callers (`examples/etcd/cache/Main`, `dist/client/RunCache`,
`RunWatch`, `partition/MainWatch`) no longer prove it by `decide`. Strengthening; no axiom or premise
added.
