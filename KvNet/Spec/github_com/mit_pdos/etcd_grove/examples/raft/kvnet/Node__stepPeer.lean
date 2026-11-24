/-
`n.stepPeer(m)` (`node.go`, 2026-11-24 G5): a message a peer sent, read back and addressed to this
replica, stepped on the current incarnation's node (`stepLaw`: `node.Step`'s `stepIn`), within
`stepTimeout`. The transports' receivers call it (TCP's `Node.servePeer`, UDP's).
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.NodeDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Net go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. -/
abbrev Node.stepPeer.spec (F : KvFacts GF) (rep : Loc → w64 → IProp GF) (stp : NodeStopper GF) : Prop :=
  ∀ (nd : Loc) (γ : Cluster) (N : Namespace) (id : w64) (ml : Loc) (src : w64) (st : MsgSt),
  st.msg.To' = id →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet ∗ isNodeS F rep stp nd γ N id ∗ context.isClosedchanInit ∗ F.msgOk src st ∗
      msgPtsC ml (DFrac.own 1) (DFrac.own 1) true { st with resps := [] } }}
    (App (Val (nd @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Node.ty @!! go!"stepPeer")) (Val #ml))
  {{ RET #(); True }}

end spec

end raft_kvnet
end EtcdGrove
end Perennial
