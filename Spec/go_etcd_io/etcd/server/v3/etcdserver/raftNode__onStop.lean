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
`storage.walCloseOk`: else `lg.Panic`) and then `done`, (2026-11-03, R2b-3b) with the stop's image
escrowed (`rnDoneEsc`: the id vacant, the durable state, the WAL's files holding it). -/
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
      -- (2026-11-03, R2b-3b) the node's durable state `S`, the loop's view at it (no pending
      -- snapshot, the handed log `L`), and `applyc`'s producer token with `cum` at its count, for
      -- the stop's escrow (`rnDoneEsc`); (S1, 2026-11-11) the restart point's backend log at or
      -- below the hard state's commit (`rnRestartOk_a0_le`, from the loop's fact) and the handed log
      -- committed, for the image's `a0` bound and its committed log (`rnStopImage`)
      (∃ (S : RaftState) (p : HardStateM) (L : List EntryModel) (sent : List toApply),
        raftState γ.node.cl γ.id S ∗ rnWalView γ ⟨S, p, none, srvLE γ.srv L⟩ ∗
        sspscProducer γ.ap sent ∗ monoListIdxOwn γ.cum sent.length L ∗
        ⌜γ.a0.length ≤ uint.nat p.Commit'⌝ ∗ isCommittedLogLb γ.node.cl (srvLE γ.srv L)) ∗
      (∃ (st : GoInterface) (cid : w64), rnStorageAddr r ↦□ st ∗
        walMetaIs (storage.walOf st) γ.id cid ∗ walPurgeRight (walDirOf (storage.walOf st))) }}
    (App (Val (r @!! go.GoType.PointerType raftNode.ty @!! go!"onStop")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
