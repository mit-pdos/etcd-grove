---
upstream: unchecked
checked: 2026-10-19
links:
  - etcd-io/etcd#22609 pr open: makes `hash` race-free but keeps the behavior (`currentRev` read after `s.mu` is released); verified on branch pr-verify/etcd-22609, notes/pr-verify/etcd-22609.md
  - etcd-io/etcd#22608 issue open: the data race of `hash` with `Restore`; related, does not mention the revision
---

# mvcc: `store.hash` can pair a backend's hash with another store's revision, or `Restore`'s transient revision 1

**Status**: a bug, a wrong result (minor: `Maintenance.Hash` is documented as for testing, "does
not hold MVCC locks"). `hash` hashes one backend and reads `currentRev` after it, with no lock
that keeps `Restore` out in between. If a snapshot is applied in that window, the RPC returns the
hash of the old backend with `Restore`'s transient `currentRev = 1` (set before `restore()`
recomputes it) or with the new store's revision: a revision below the one hashed, or one of a
different keyspace. The code's TODO ("hash and revision could be inconsistent") is about writes
committed between the two reads, where the revision is at least the hashed state's; this is not.

**Where**: `server/storage/mvcc/kvstore.go:156` (`store.hash`; the revision at line 164) at the
pinned `goose-lean` revision `8a24be2a3`; `Restore`'s transient values at `kvstore.go:303-306`
(fork, PR applied: 314-317).

**What happens**: `notes/pr-verify/etcd-22609/kvstore_hash_restore_rev_test.go` (branch
`pr-verify/etcd-22609`; `TestHashRevisionDuringRestore`, written by the reviewer of that run)
gates the old backend's `Hash` and the new backend's first `ReadTx` so that `Restore` runs between
`hash`'s hash and its read of `currentRev`. On upstream `b25719d10` and on etcd-io/etcd#22609's
head `afd94a12c`: `hash of the old backend (at revision 11) returned with revision 1; store now
at 21`, FAIL (3 runs of 3).

**Expected**: the revision `hash` returns is one of the store whose backend it hashed, at least
the revision of the state hashed.

**How the proof handles it**: the store invariant keeps `s.b` fixed (`isStore`'s `Hb`; `Restore`
is out of scope), so the spec of `store.hash` (branch `pr-verify/etcd-22609`) cannot state it.

**Possible fixes**: read `currentRev` (under `s.revMu.RLock()`) before `s.mu.RUnlock()`, as
`hashByRev` does; with etcd-io/etcd#22609 and that change, the test passes under `-race` (the
reviewer's run).

**Found**: 2026-10-19, by the reviewer of the etcd-io/etcd#22609 verification
(`.claude/skills/etcd-pr-verify`).
