/-
`(*raftNode).onStop()` (raft.go): the loop's deferred shutdown.
Lean-first (no Rocq counterpart); see `InvRaftNode.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRaftNode

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `r.onStop()`, with the right to stop the transport (`E.ST`, which `<-r.stopped` gave; D43 M5c):
stops the node, the ticker and the transport, closes the WAL (which succeeds, the WAL's I/O not failing,
`storage.walCloseOk`: else `lg.Panic`) and then `done`. -/
abbrev raftNode.onStop.spec : Prop :=
  ∀ (E : RNEnv GF) (γ : RNNames) (r : Loc),
  -- (2026-10-31, `notes/axiom-review/savesnap.md`) `Close` not failing (I/O)
  storage.walCloseOk →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isRaftNode E γ r ∗ rnDoneTok γ r ∗
      E.ST ∗
      -- (2026-10-30, the repair) the node's whole running token (the loop's half and the apply
      -- side's, `stopped`'s), which `node.Stop` takes
      (letI := srvStor (GF := GF) γ.node; nodeRunning γ.nl γ.node.cl srvClusterN 1) ∗
      -- (2026-10-31) the WAL's whole open token (the loop's half and the apply side's), which
      -- `Close` takes; (2026-11-03, R2b-1 stage 6) the records, which `Close` also takes, from the
      -- durability invariant (`rnDur_take`): the stop's claim, the apply thread's token, the loop's
      -- view at no pending snapshot; and the metadata and the purge's right
      rnWalTok r 1 ∗ token γ.wal.stop ∗ token γ.wal.app ∗
      (∃ v : WalView, rnWalView γ v ∗ ⌜v.pend = none⌝) ∗
      (∃ (st : GoInterface) (id cid : w64), rnStorageAddr r ↦□ st ∗
        walMetaIs (storage.walOf st) id cid ∗ walPurgeRight (walDirOf (storage.walOf st))) }}
    (App (Val (r @!! go.GoType.PointerType raftNode.ty @!! go!"onStop")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
