---
upstream: none
checked: 2026-11-03
links:
  - etcd-io/etcd#22608 issue closed: related, not this bug (`store.hash`, not `HashByRev`, racing with `Restore`)
  - etcd-io/etcd#22609 pr merged: related (the fix of #22608); leaves `HashByRev`'s stored-hash path as it was
blocks-proof: no
---

# mvcc: HashKV of a compacted revision during a snapshot restore reports current revision 1

While a member restores a snapshot from the leader, `HashKV` for a revision whose hash was stored
at its compaction (what the compaction hash check and `etcdctl endpoint hashkv --rev` ask) answers
with the stored hash and a response header revision of `1`: the store's revision goes back to `1`
in the reply, below the revision just hashed, then forward again once the restore finishes.

**Expected:** the response's revision should be a revision the member's store had (before or after
the restore), at least the hashed revision, as every other response header's.

**Impact:** a member catching up by a snapshot (a partition, a slow or restarted member) while
`HashKV` requests reach it, from clients or from the leader's corruption checks. The header
revision is wrong for the length of the restore (which grows with the number of keys); the hash
and compact revision are right. The leader's checks compare hashes and compact revisions, and a
follower revision below the leader's raises no alarm, so they are unaffected; a client or monitor
reading the header revision gets `1`. Reproduced on `main`; release branches not checked.

**Reproduction:** `TestHashByRevDuringRestore` in
[`issues/etcd-mvcc-hashbyrev-restore-rev1/hashbyrev_restore_test.go`](etcd-mvcc-hashbyrev-restore-rev1/hashbyrev_restore_test.go),
copied (as `zz_hashbyrev_restore_test.go`) into `server/storage/mvcc` at
etcd-io/etcd@4b0b745025716b893c64dbee443e3f969931a16b (2026-11-03), go1.27.3 linux/amd64: 1000
puts, a compaction at 500 (which stores its hash), then `HashByRev(500)` in a loop on one goroutine
while the main one restores the store from its backend 100 times; 10 of 10 runs fail:

```
$ (cd server && go test ./storage/mvcc -run '^TestHashByRevDuringRestore$' -count=1)
--- FAIL: TestHashByRevDuringRestore (0.62s)
    zz_hashbyrev_restore_test.go:72: HashByRev(500) returned current revision 1, below the revision hashed (the store is at 1001)
FAIL
```

**Cause:** [`Restore`](https://github.com/etcd-io/etcd/blob/4b0b745025716b893c64dbee443e3f969931a16b/server/storage/mvcc/kvstore.go#L302-L324)
holds `s.mu` and sets `currentRev = 1` under `revMu` before `restore()` reloads the revision from the
new backend. [`hashStorage.HashByRev`](https://github.com/etcd-io/etcd/blob/4b0b745025716b893c64dbee443e3f969931a16b/server/storage/mvcc/hash.go#L139-L153)
answers a stored hash with `currentRev` read under `revMu` alone, so it sees the placeholder; the
path that hashes (`store.hashByRev`) takes `s.mu.RLock` too and waits out the restore.

## Proof

no: the mvcc API has no spec of `HashByRev` yet (`Spec/go_etcd_io/etcd/server/v3/storage/mvcc/Api.lean`,
"Still out"); the candidate's `HashByRev` takes a share of the store's open token, which `Restore`
takes whole, so the two do not overlap under it (`notes/mvcc-api-candidate.md`, decision 10), and
no top-level result reads `HashKV`'s header revision.

## Fix

Read `currentRev` in the stored-hash path under `s.mu.RLock` as well (as `store.hashByRev` does), or
have `Restore` set `currentRev` once, after `restore()` has read it, instead of publishing `1`.
