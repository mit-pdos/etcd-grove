---
upstream: none
checked: 2026-11-03
links:
blocks-proof: no
---

# mvcc: after a compaction at revision 0, HashKV of the latest revision returns the hash of revision 0

After a client's `Compact(0)` (accepted: nothing was compacted before), every later `HashKV` at
revision `0`, which means the latest revision, returns the hash stored by that compaction, of the
empty revision 0, with hash revision `0`, instead of hashing the current keys. `etcdctl endpoint
hashkv` (whose `--rev` defaults to `0`) reports it, and it stays until ten later compactions push it
out of the stored hashes.

**Expected:** `HashKV` with revision `0` should hash "all keys" at the latest revision, as
[`Maintenance.HashKV`'s documentation](https://github.com/etcd-io/etcd/blob/4b0b745025716b893c64dbee443e3f969931a16b/client/v3/maintenance.go#L66-L69)
says and as it does without a stored hash at revision `0`.

**Impact:** a cluster on which a client ran `Compact(0)` (no etcd compactor issues it: the periodic
one compacts at a revision it read, the revision one skips revisions at or below `0`). From then on
`HashKV(0)` and `etcdctl endpoint hashkv` report the same constant hash on every member whatever
the data. By reading, not reproduced: the periodic corruption check (when enabled) asks the leader's
`HashByRev(0)` and then the peers at the returned hash's revision, `0`, which they also answer from
their stored hash, so it compares the empty revision's hashes and cannot detect a divergence until
the stored hash is evicted (ten later compactions; never, without compactions). Reproduced on
`main`; release branches not checked.

**Reproduction:** `TestHashKVLatestAfterCompactZero` in
[`issues/etcd-mvcc-hashbyrev-zero-stored/hashkv_after_compact_zero_test.go`](etcd-mvcc-hashbyrev-zero-stored/hashkv_after_compact_zero_test.go),
copied (as `zz_hashkv_after_compact_zero_test.go`) into `tests/integration/clientv3` at
etcd-io/etcd@4b0b745025716b893c64dbee443e3f969931a16b (2026-11-03), go1.27.3 linux/amd64 (a
1-member cluster: `Compact(0)`, three puts, then `HashKV` at `0` and at the last put's revision):

```
$ (cd tests && go test ./integration/clientv3 -run '^TestHashKVLatestAfterCompactZero$' -count=1)
--- FAIL: TestHashKVLatestAfterCompactZero (0.23s)
    zz_hashkv_after_compact_zero_test.go:52:
        	Error:      	Not equal:
        	            	expected: 4
        	            	actual  : 0
        	Test:       	TestHashKVLatestAfterCompactZero
        	Messages:   	HashKV(0) should hash the latest revision
FAIL
```

**Cause:** [`hashStorage.HashByRev`](https://github.com/etcd-io/etcd/blob/4b0b745025716b893c64dbee443e3f969931a16b/server/storage/mvcc/hash.go#L139-L153)
first returns any stored hash with `Revision == rev`, before
[`store.hashByRev`](https://github.com/etcd-io/etcd/blob/4b0b745025716b893c64dbee443e3f969931a16b/server/storage/mvcc/kvstore.go#L193-L195)
resolves `rev == 0` to the current revision; a compaction at `0` passes
[`updateCompactRev`](https://github.com/etcd-io/etcd/blob/4b0b745025716b893c64dbee443e3f969931a16b/server/storage/mvcc/kvstore.go#L207-L232)
(`0 > compactMainRev = -1`) and
[stores](https://github.com/etcd-io/etcd/blob/4b0b745025716b893c64dbee443e3f969931a16b/server/storage/mvcc/kvstore.go#L260)
a hash with `Revision: 0`.

## Proof

no: the mvcc API has no spec of `HashByRev` yet (`Spec/go_etcd_io/etcd/server/v3/storage/mvcc/Api.lean`,
"Still out"), no top-level result reads `HashKV`, and `EtcdServer.Compact.spec` takes the scope
restriction `1 ≤ r` (no `Compact(0)`, `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__Compact.lean`).

## Fix

Skip the stored hashes when `rev == 0` (or resolve `0` to the current revision before the lookup);
or reject `Compact` at a revision `≤ 0`, which deletes nothing.

## Notes

Another edge of a compaction at revision 0: [`etcd-restore-scheduled-compact-zero`](etcd-restore-scheduled-compact-zero.md)
(rejecting `Compact(0)` would close both).
