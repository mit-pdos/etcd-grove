---
upstream: unchecked
checked: 2026-10-30
links: []
---

# mvcc: `restore()` ignores a scheduled, unfinished compaction at revision 0, so a member's compaction revision can differ from the log's

- **Status**: a (benign) divergence between members, reproduced (2026-10-30, below): after a
  snapshot install, or a restart, a member's `compactMainRev` is `-1` where the members that applied
  the same log have `0`. Reads cannot tell (`Range`/`Watch` at revision `0` mean "current"); a
  re-issued `Compact(0)` can (success on one member, `ErrCompacted` on the others), as can
  `HashKV`'s `compact_revision`. Found by review round 3 of the M2 storage plan (S3) while checking
  what `restore()` computes; filed here because the spec of `store.Restore` must say it.
- **Where**: etcd at `etc/goose.py`'s pin (`249d76bea7` in `.lake/go-src/etcd`).
  `server/storage/mvcc/store.go:30-36` (`UnsafeReadScheduledCompact`: an absent record reads
  `(0, false)`), `server/storage/mvcc/kvstore.go:330-342`, `:389-391`, `:411` (`restore()`: the
  found flag of the scheduled record is dropped, and `scheduledCompact != 0` is the test for "a
  compaction to resume"), `kvstore.go:197-222` (`updateCompactRev` accepts `rev = 0` on a fresh
  store: `0 > -1`), `server/etcdserver/api/v3rpc/key.go:139` (`Compact` passes any revision).
- **What happens**: a client's `Compact(0)` on a fresh cluster is applied by every member:
  `updateCompactRev` persists `scheduledCompactRev = 0` (`ForceCommit`), sets `compactMainRev = 0`,
  and the job writes `finishedCompactRev = 0` in its last batch. A snapshot of a member's backend
  taken between the two (a leader sending a snapshot while the job runs), or a member that crashes
  between them and restarts, holds `scheduledCompactRev = 0` and no finished record; `restore()`
  then leaves `compactMainRev = -1` and does not resume. A follower that installs that snapshot
  goes from `0` to `-1`; the restarted member stays at `-1` (and never writes the finished record).
  Reproduction: `etcd-restore-scheduled-compact-zero/repro_test.go`, a test of
  `server/storage/mvcc` (copy it there; `go test ./storage/mvcc/ -run
  TestRestoreScheduledCompactZero -v` from `server/`): fails, `compactMainRev = -1` after `Restore`
  and a re-issued `Compact(0)` succeeds where the member that applied it answers `ErrCompacted`.
- **Expected**: the compaction revision is a function of the applied log (every member that applied
  the same entries has the same `compactMainRev`), as `restore()` arranges for every other revision
  (it resumes a scheduled compaction above the finished one).
- **How the proof handles it**: as M2's scope restriction (the user's Q7 (a), switched 2026-10-30):
  `EtcdServer.Compact.spec` takes `1 ≤ r` (no compaction at revision `0`; a client's `Compact(0)` RPC
  is out of M2's scope, M2's compactor never issues it: `compactableOk_server`), and the committed
  log's compactions are past `0` (`compactPropOk`, `plainLogC_compaction_pos`, `CompactMode.lean`).
  The restored images' records are then past `0` (`mvcc.recsPos`, `recsPos_crev`: still a Draft with
  the restore chain), so `store.Restore.specM`'s premise `c ≤ c'` (the user's Q5 (a)) has no corner.
  Until then it was false in this corner (`c = 0`, `c' = -1`): `notes/m2-storage-plan.md`, "After
  review round 3", Q7.
- **Possible fixes**: read the scheduled record's found flag and resume when it is found and above
  `compactMainRev` (`scheduledCompact, scheduledFound := ...; if scheduledFound && scheduledCompact >
  s.compactMainRev`), or reject `Compact(rev)` with `rev <= 0` in the RPC or the applier (it deletes
  nothing).
- **Found**: 2026-10-30, M2 storage plan, review round 3 (S3), reproduced while repairing it.
