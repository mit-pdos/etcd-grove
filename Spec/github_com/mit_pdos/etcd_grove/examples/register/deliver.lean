/- Lean-first (no Rocq counterpart).

`deliver(peers, ms)` (cluster.go): the transport. For the messages of a `Ready` (each
legitimately sent, `isRaftMsg`, and of a term within the budget, `termLB`: what `Ready`
gives with them) and a read-only peer table whose node at each id is that id's (`peerOk`),
it steps each deliverable message into its target, which takes it (`Node.Step`'s `stepP`).
(2026-10-13) It takes each message's read credit (`Ready`'s) and passes a delivered
message's on to `Step`, dropping the others' with their messages; a read-index request is
stepped only in a configuration of more than one voter (`Node.Step`'s premise).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.register.Cluster

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace register

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.register.Assumptions]
variable [StorageModel GF]

/-- See the file header. -/
abbrev deliver.spec : Prop :=
  ∀ (γ : RaftNames) (bud : BudgetNames) (peers : Loc) (P : GMap w64 GoInterface)
    (msl : GoSlice) (ms : List raftpb.Message),
  1 < GMap.size γ.reCfg →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.register ∗ peers ↦${DFrac.discard} P ∗ ([∗map] id ↦ nd ∈ P, peerOk γ bud id nd) ∗
      msl ↦* ms ∗ ([∗list] m ∈ ms, isRaftMsg γ m ∗ termLB bud m.Term') ∗
      [∗list] m ∈ ms, rdCred γ (if m.Type' = MsgReadIndex then 1 else 0) }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.register.deliver))
      (Val #peers)) (Val #msl))
  {{ RET #(); True }}

end spec

end register
end EtcdGrove
end Perennial
