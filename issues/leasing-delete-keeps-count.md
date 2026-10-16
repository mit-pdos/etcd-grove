---
upstream: known
checked: 2026-10-16
links:
  - etcd-io/etcd#22417 issue open: same bug (a cached Get after a Delete returns Kvs=[] with Count=1)
  - etcd-io/etcd#22418 pr open: same fix (Count = 0 in leaseCache.delete), with tests
  - etcd-io/etcd#22507 pr open: same fix, with an integration test
  - etcd-io/etcd#22585 pr open: same fix, with a unit test
---

# clientv3/leasing: a cached Get after a Delete returns no key-values but the old Count

## Status

A bug (a wrong result). After a `Delete` of a key it has cached, the leasing KV's `Get` of the key
returns `Kvs = []` with `Count = 1`. etcd returns `Count = 0`. Reported upstream as #22417.

## Where

`client/v3/leasing/cache.go:160-165` at the etcd pin `107edf7e4` (unchanged on upstream `main`,
`b25719d10`): `leaseCache.delete` clears `li.response.Kvs` and replaces the header, and leaves
`li.response.Count` alone. `leaseKey.get` (`cache.go:212-228`) builds every cached answer from
`copyGetResponseMetadataOnly(resp)` (`util.go`), which copies `Count`. So the stale count reaches
every later cached `Get`. `delete` is reached from `leasingKV.delete` (`kv.go:390-420`, through
`Delete`) and from a transaction's `commitToCache` (`txn.go`).

## What happens

```
Put("k", "v"); Get("k")   -> Kvs=[k], Count=1   (the key is cached)
Delete("k"); Get("k")     -> Kvs=[],  Count=1   (etcd: Count=0)
```

Reproduced at the pin by a unit test in package `leasing`,
`issues/leasing-delete-keeps-count/delete_keeps_count_test.go` (the issue's integration test reduced
to the cache):

```go
lc := &leaseCache{entries: map[string]*leaseKey{}, revokes: map[string]time.Time{}}
lc.Add("k", &v3.GetResponse{Header: &v3pb.ResponseHeader{Revision: 2},
	Kvs: []*mvccpb.KeyValue{{Key: []byte("k"), Value: []byte("v"), CreateRevision: 2, ModRevision: 2, Version: 1}},
	Count: 1}, v3.OpGet("k"))
lc.Delete("k", &v3pb.ResponseHeader{Revision: 3})
resp, _ := lc.Get(context.Background(), v3.OpGet("k"))
// resp.Kvs is empty, resp.Count == 1
```

`go test ./leasing -run TestTriageDeleteKeepsCount` in `client/v3` prints `len(Kvs)=0 Count=1`.
A `WithCountOnly()` Get, the one that reads only `Count`, answers 1 for a deleted key.

## Expected

The cached answer is the one etcd would give: `Count = 0` for a deleted key, as for a key cached
as absent by its acquisition. The package says it "serves linearizable reads from a local cache"
(`doc.go:15`).

## How the proof handles it

The specs state the behavior exactly. `LeaseEntry.del`
(`Proof/go_etcd_io/etcd/client/v3/leasing/InvLeaseCache.lean:192-195`), the transition of
`leaseCache.Delete.spec`, is `{ e with kvsSl := slice.nil, kvs := [], hdr := h, hm := hm }`, with
`count` unchanged. `leaseKey.get.spec` and `getCached` (`InvLeasingKV.lean:414-417`) return
`freshGetResp ret e.hm e.more e.count (getResult o e)`. The cached-read theorems
(`leasing_cached_get_stable`, `leasing_getResult_acq`, `Results.lean:180-196`) relate only the key-value
`getResult o e` to etcd's record, not `Count`. No invariant ties `e.count` to `e.kvs`
(`LeaseCacheWf`, `InvLeaseCache.lean:240-247`). Adding `e.count = W64 e.kvs.length` to it would
make `del`'s proof fail exactly here.

## Possible fixes

Set `li.response.Count = 0` together with `li.response.Kvs = nil` in `leaseCache.delete` (all three
open PRs). With the fix, the invariant above holds: `Add` gets a response whose `Count` is its
`Kvs`' length for a single-key get, `Update` sets `Count = 1` when it appends, and `delete` sets 0.

## Found

2026-10-16, by the bug triage of etcd-io/etcd#22417 against the leasing specs
(`notes/bug-triage/etcd-22417.md`). The specs had recorded the behavior, but not as a finding.
