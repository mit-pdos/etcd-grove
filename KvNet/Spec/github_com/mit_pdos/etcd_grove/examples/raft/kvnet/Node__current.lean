/-
`n.current()` (`node.go`, 2026-11-24 G5): the current incarnation's replica, read under `mu`: its
raft node, the store's facts of it (`rep`), `isNode`.
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
abbrev Node.current.spec (F : KvFacts GF) (rep : Loc → w64 → IProp GF) (stp : NodeStopper GF) : Prop :=
  ∀ (nd : Loc) (γ : Cluster) (N : Namespace) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet ∗ isNodeS F rep stp nd γ N id }}
    (App (Val (nd @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Node.ty @!! go!"current")) (Val #()))
  {{ (r : Loc), RET #r; ∃ n : NodeH,
      r.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Replica, go!"node"] ↦□ interface.mkOk (go.GoType.PointerType node.ty) #n.loc ∗
      □ rep r id ∗ isNode n γ N id }}

end spec

end raft_kvnet
end EtcdGrove
end Perennial
