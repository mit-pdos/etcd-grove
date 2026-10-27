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
the caller held `R`, so the observation gives `Q`. What would discharge it: bbolt's `DB.Begin(false)` read isolation and the backend's
commit protocol (`batchTxBuffered.commit`) with a read transaction begun outside the batch lock,
in a model of bbolt where the database's committed state is shared (a fraction of `ownDB`)
rather than the batch lock's alone. -/
axiom backend.backend.Snapshot.wp_proof : backend.backend.Snapshot.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
