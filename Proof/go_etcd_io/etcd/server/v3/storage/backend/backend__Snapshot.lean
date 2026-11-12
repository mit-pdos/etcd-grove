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
`hkOwn γ (hkData P C)`, (D22, 2026-10-23) `rbOwn γ (rbData P C)` and (the user's decision,
2026-11-04, round 16's F1) `fkdOwn γ (fkVals C)` of the committed `C` (a commit makes the writer's
contents committed: the hook's shares, the tracked buckets' and the compaction keys' values are of
the writer's contents, `fkHalf`'s `fkdOwn γ (fkVals st.S)`; the latter is updated only by a put of
a compaction key, `fkHalf_raise`, every other operation keeping `fkVals` of the writer's contents,
`fkVals_put`/`_del`/`_create`/`_delBucket`, and a commit or a write-back leaving them unchanged),
and the caller held `R`, so the observation gives `Q` of the committed `C`, hence of `D` at its
compaction keys (`fkVals D`) as at the hook's own keys. The compaction keys' clause is the hook keys'
argument again, over a second ghost variable of the same shape; it adds nothing the existing
`fkRd` clause relies on (that clause's flag is unchanged; the values' half is a separate ghost
name). (Question 2, option (a), the user's, 2026-10-29:
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
rather than the batch lock's alone. (The user's decision, 2026-11-04, probe M2: a snapshot restored
from gives a correct view of the abstract state it is of.) Why the deleted entries' clause holds:
at the end of that last commit the batch lock's state `st` is out of an `Unlock`'s commit window
(`commitSt` resets `win`), so its quarter's agreement (`batchViewQ`'s `dlsW`) is the full one,
`dlsOk P st L` with its logical view `L`: the safe-range entries of `L` missing from the writer's
contents are exactly the deleted ones `dlR P st.dl`, which are `L`'s; the committed data is the
writer's contents and the read buffer is empty, so the physical view is `sData P st.S`, and
`dlVd P (sData P st.S) L (dlR P st.dl)` (`dlVd_of_dlsOk`); the lock's half of the deleted entries is
at `dlR P st.dl` (`fkHalf`'s `dlsOwn`). The agreement is the backend's own proved invariant: every
operation keeps it (a delete from a safe-range bucket records the entry, both halves updated with
the client's, `fkHalf_dl`; a put there is not of a deleted entry, `UnsafeSeqPut`'s and
`UnsafePut`'s premise; a put session's `Unlock` deleted no safe-range entry the readers see,
`sbKept`, so `relog` keeps the deleted entries, `dlsOk_relog`; an `Unlock`'s commit window is the
one exemption, its commit's close re-establishing the agreement at `relog`). So the clause is the
hook keys' argument again, over a ghost variable of the same shape and the quarter's pure
agreement; it adds nothing the other clauses rely on. Attacked with the `axiom` skill, survives
(`notes/axiom-review/backend-snapshot-dls.md`, 2026-11-04; the compaction keys' clause:
`backend-snapshot-fkd.md`). (2026-11-06, branch `begin-tok`, `notes/begin-tok-plan.md`) Why the pre's
`threadTok` and `ThreadBoundLe GF (2 ^ 29)`: `Snapshot` (etcd `server/storage/backend/backend.go:381`)
calls `b.db.Begin(false)` (`:386`), whose `beginTx` takes bbolt's `db.mmaplock.RLock()` (bbolt
`db.go:875`) and keeps it past `Snapshot`'s return (the `b.mu.RUnlock()` deferred at `:385` is the
backend's own lock, not `mmaplock`), until `snapshot.Close`'s `s.Tx.Rollback()` (`backend.go:1132`)
reaches `removeTx`'s `db.mmaplock.RUnlock()` (`db.go:951`). Each open snapshot is so charged a
thread's token, as `bbolt.DB.Begin_kv` charges a read transaction; the bound keeps the slots below
`sync.RWMutex`'s `2 ^ 30` readers (`bbolt.Open_kv`'s count). The goroutine it starts
(`backend.go:393`, living until `Close`'s `<-s.donec`, `:1131`) is a live thread paid by its own
fork's fuel; the caller's token pays the reader slot: net one token per open snapshot until `Close`
(reviewed with the `axiom` skill, survives: `notes/axiom-review/begin-tok-restated.md`). -/
axiom backend.backend.Snapshot.wp_proof : backend.backend.Snapshot.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
