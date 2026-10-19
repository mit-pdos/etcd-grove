---
upstream: known
checked: 2026-10-19
links:
  - etcd-io/etcd#22608 issue open: reports `hash`'s race with `Restore` (on `s.b` and `currentRev`); does not say that the read of `currentRev` also races with every write transaction, without `Restore`
  - etcd-io/etcd#22609 pr open: fixes both (reads `currentRev` under `revMu.RLock`); verified on branch pr-verify/etcd-22609, notes/pr-verify/etcd-22609.md
---

# mvcc: `store.hash` reads `currentRev` without `revMu`, racing with every write transaction

**Status**: a bug, a data race. `currentRev` is documented as protected by `revMu` ("revMuLock
protects currentRev and compactMainRev"), and every write transaction's `End` increments it under
`revMu.Lock`; `hash` reads it with no lock. The `Maintenance.Hash` RPC reaches it
(`maintenanceServer.Hash` → `HashStorage.Hash` → `store.hash`) on any member taking writes, not
only during a snapshot restore. The value is one word, so in practice the effect is a revision read
without ordering against the hash (Go's memory model promises nothing for a racy program); the race
detector reports it.

**Where**: `server/storage/mvcc/kvstore.go:164` (`return h, s.currentRev, err` in `store.hash`,
line 156) at the pinned `goose-lean` revision `8a24be2a3` (as at upstream main `b25719d10`); the
write is at `kvstore_txn.go:214` (`storeTxnWrite.End`, under `revMu.Lock` at 213); the field's
comment is at `kvstore.go:67`.

**What happens**: `notes/pr-verify/etcd-22609/kvstore_hash_put_race_test.go` (branch
`pr-verify/etcd-22609`) runs `Hash` while `Put`s commit. Copied into `server/storage/mvcc/` of
upstream `b25719d10`, `go test -race -count=5 -run '^TestHashConcurrentWithPut$' ./storage/mvcc/`
(from `server/`) reports `WARNING: DATA RACE` (the write in `storeTxnWrite.End`,
kvstore_txn.go:214; the read in `store.hash`) and fails. With etcd-io/etcd#22609 applied it passes
50 runs out of 50.

**Expected**: `hash` reads `currentRev` under `revMu`, as `hashByRev` and the metrics reporter do.

**How the proof handles it**: `store.hash` is not translated on `lean` (mvcc's hashing is
names-only: `Code/go_etcd_io/etcd/server/v3/storage/mvcc.toml`). The store invariant
(`Proof/go_etcd_io/etcd/server/v3/storage/mvcc/InvStore.lean`) holds `currentRev`'s points-to
in halves, one in `revMu`'s invariant and one with the writer, so an unlocked read has nothing to
read with: the old code cannot be proved, the PR's can (branch `pr-verify/etcd-22609`).

**Possible fixes**: read `s.currentRev` under `s.revMu.RLock()` (etcd-io/etcd#22609).

**Found**: 2026-10-19, verifying etcd-io/etcd#22609 (`.claude/skills/etcd-pr-verify`), from the
store invariant's ownership of `currentRev`.
