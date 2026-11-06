/-
The trust boundary: `Spec/go_etcd_io/etcd/server/v3/storage/backend/backend__Snapshot.lean`
(`backend.Snapshot` is names only: its body begins a bbolt read transaction outside the batch
lock, which the backend's model of bbolt, whose `ownDB` the batch lock holds, does not cover, and
starts a ticker goroutine). D22 S-f, 2026-10-19; `notes/decisions.md`, "D22 S-f carried out".
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__Snapshot

@[expose] public section

set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.backend backend

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- **Trust boundary** (D22 S-f): `b.Snapshot()` commits the batch transaction, then begins a bbolt
read transaction (which on an open database does not fail: `lg.Fatal` is not reached) over
bbolt's committed data `D` at that moment, and returns it as the snapshot. Why `Q` holds of `D`:
`D` is what the last bbolt commit before the read transaction began left (bbolt's isolation of
`DB.Begin(false)`), and that commit was the call's own (`batchTx.Commit`) or a later one (the
`run` goroutine's, an `Unlock`'s), or the call's own found nothing pending, the writer's contents
then being the committed data and the read buffer empty; at the end of each, its committer held
the batch lock's resources `W ∗ Pk`, the lock's ghost shares were `viewAt γ (sData P C)`,
`hkOwn γ (hkData P C)` and (D22, 2026-10-23) `rbOwn γ (rbData P C)` of the committed `C` (a
commit makes the writer's contents committed: the hook's shares are of the writer's contents), and
the caller held `R`, so the observation gives `Q`. (Question 2, option (a), the user's, 2026-10-29:
`viewAt γ (sData P C)` is the batch lock's quarter at a logical view the committed data reads thin
of, as `batchGhostAt` holds it after a commit, `batchViewQ`; a weaker observation than the quarter
at `sData P C` itself, which a compaction's deletes would make false. To be checked by the `axiom`
skill before the backend stage's Freeze.) (2026-11-02, the merged snapshot's window; reviewed with
the `axiom` skill, `notes/axiom-review/backend-snapshot-fk.md`: survives) Why the post's `fkRd γ P
(D, ⟨∅, W64 0⟩)` holds: at the end of that last commit the batch lock's half of the flag is at some
`f` with `fkOkG` of the committed state `D` (`fkOkG_commit`), so its lower bound
(`monoNatLbOwn_get`) with `fkOkRvG` of `D` and an empty read buffer (`fkHalf_rd`,
`fkOkRvG_of`) is a reader's, as `batchTxBuffered.unsafeCommit` gives its readers over the
committed data; the flag only grows, so a later put of a compaction key cannot falsify it. What
would discharge it: bbolt's `DB.Begin(false)` read isolation and the backend's
commit protocol (`batchTxBuffered.commit`) with a read transaction begun outside the batch lock,
in a model of bbolt where the database's committed state is shared (a fraction of `ownDB`)
rather than the batch lock's alone. (F2, stage 3, 2026-11-03; `notes/image-cmp-f2-plan.md`) Why the
observation may also take `pvHalf γ vd` and `ckHalf γ v`, with the post's `Q` at `fkVals D`: the
two ghosts beside `hkOwn`/`rbOwn` are the batch lock's halves at the writer's contents (the
physical view of the non-hook buckets, `sData`, and the compaction keys' values, `fkVals`; every
write to a non-hook bucket and every put of a compaction key moves both halves, the client's and
the lock's, `batchGhostAt`), and a commit makes the writer's contents committed, so at the end of
that last commit, with the lock free, they are at `sData P D` and `fkVals D`. `Snapshot` commits
first, so a write made before the call, committed or only pending in the writer's contents, is in
`D`, and a session holding the lock during the call is in it whole or not at all. Go tests:
`TestSnapshotPendingWrites` (an unlocked, uncommitted put of a compaction key and a delete in `Key`
are in the snapshot), `TestSnapshotWaitsForSession` (a session holding the lock during `Snapshot`
is in it whole), `TestImageCmpMidJob` (the records and the job's cut, mid-job and with a second
compaction queued). (2026-11-06, branch `begin-tok`, `notes/begin-tok-plan.md`) Why the pre's
`threadTok` and `ThreadBoundLe GF (2 ^ 29)`: `Snapshot` (etcd `server/storage/backend/backend.go:381`)
calls `b.db.Begin(false)` (`:386`), whose `beginTx` takes bbolt's `db.mmaplock.RLock()` (bbolt
`db.go:875`) and keeps it past `Snapshot`'s return (the `b.mu.RUnlock()` deferred at `:385` is the
backend's own lock, not `mmaplock`), until `snapshot.Close`'s `s.Tx.Rollback()` (`backend.go:1132`)
reaches `removeTx`'s `db.mmaplock.RUnlock()` (`db.go:951`). Each open snapshot is so charged a
thread's token, as `bbolt.DB.Begin_kv` charges a read transaction; the bound keeps the slots below
`sync.RWMutex`'s `2 ^ 30` readers. The goroutine it starts (`backend.go:393`) lives until `Close`'s
`<-s.donec` (`:1131`), as long as the read transaction: the same token pays for it (Q4). -/
axiom backend.backend.Snapshot.wp_proof : backend.backend.Snapshot.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
