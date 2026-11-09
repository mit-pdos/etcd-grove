---
upstream: fixed
checked: 2026-11-03
links:
  - etcd-io/etcd#22608 issue closed: the same unsynchronized read of the current revision in `store.hash` (found with `Restore`; also `s.b`), by shubham3-ucb
  - etcd-io/etcd#22609 pr merged: the fix (reads `currentRev` under `revMu`, `s.b` under `s.mu`), merged 2026-10-20 as 7ff040cb8
blocks-proof: no
---

# mvcc: the Hash RPC reads the store's current revision without a lock, racing with every write

`Maintenance.Hash` (`HashStorage().Hash()`) returned the store's current revision read with no
lock, while the apply loop's write transactions increment it under `revMu`: a data race (the race
detector reports it) on every member serving a `Hash` request during writes. Every other reader of
the revision takes `revMu`.

**Reproduction:** `TestHashConcurrentWithWrites` in
[`issues/etcd-mvcc-hash-currentrev-race/hash_concurrent_writes_test.go`](etcd-mvcc-hash-currentrev-race/hash_concurrent_writes_test.go),
copied (as `zz_hash_concurrent_writes_test.go`) into `server/storage/mvcc` at
etcd-io/etcd@6782f5229b8a6dbc5f6d421107fd70d66de98694 (2026-10-19, the parent of #22609's merge),
go1.27.3 linux/amd64; it passes at etcd-io/etcd@4b0b745025716b893c64dbee443e3f969931a16b
(2026-11-03, `main`):

```
$ (cd server && go test -race ./storage/mvcc -run '^TestHashConcurrentWithWrites$' -count=1)
WARNING: DATA RACE
Write at 0x00c000162d90 by goroutine 89:
  go.etcd.io/etcd/server/v3/storage/mvcc.(*storeTxnWrite).End()
      server/storage/mvcc/kvstore_txn.go:214 +0xa4
  ...
Previous read at 0x00c000162d90 by goroutine 82:
  go.etcd.io/etcd/server/v3/storage/mvcc.(*store).hash()
      server/storage/mvcc/kvstore.go:164 +0x139
  go.etcd.io/etcd/server/v3/storage/mvcc.(*hashStorage).Hash()
      server/storage/mvcc/hash.go:136 +0x35
  ...
    testing.go:1867: race detected during execution of test
FAIL	go.etcd.io/etcd/server/v3/storage/mvcc	0.657s
```

## Proof

Stated, not fixed: batch 3e's (specs-only) trusted `HashStorage.Hash.contract` and
`HashByRev.contract` (`Spec/go_etcd_io/etcd/server/v3/storage/mvcc/Api.lean`) take a share of
`mvccRestoreGate`, which `Restore` takes whole, so no hash runs concurrently with a restore: the
torn read of the interface `s.b` (two words) and `hashByRev`'s read of the old storage after
`s.mu` is released are excluded by that premise, an obligation of the server (its snapshot install
excludes hashing). The unlocked read of `s.currentRev` (one word) still races the writers' bump; Go's
memory model gives it some value written, and the spec states no value. The open alternative is to
cherry-pick #22609 into the goosed fork (then the premise can go).

## Notes

The revision #22609 returns is still read after the hash, so it may be newer than the hashed state
(the TODO in `store.hash` stays); a spec states it as a revision the store had at or after the hash.
