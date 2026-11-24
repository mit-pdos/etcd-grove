/-
`nd.status()` (`examples/raft/kvnet/node.go`): the replica's status now (`ReqStatus`'s answer,
which the protocol promises nothing of): what `PutStatus` reads of it, a fresh copy of the store's map
and the configuration, read-only (`Replica.contents`'s post). **A spec at the store's seam** `rep`.
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
abbrev Node.status.spec (F : KvFacts GF) (rep : Loc → w64 → IProp GF) (stp : NodeStopper GF) : Prop :=
  ∀ (nd : Loc) (γ : Cluster) (N : Namespace) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet ∗ isNodeS F rep stp nd γ N id }}
    (App (Val (nd @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Node.ty @!! go!"status")) (Val #()))
  {{ (s : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Status), RET #s;
      ∃ (M : GMap GoString GoString) (c : ConfStateM), s.Contents' ↦$ M ∗
        csOpt s.Conf' DFrac.discard c ∗ ⌜s.Stats'.arr.length = 24⌝ }}

end spec

end raft_kvnet
end EtcdGrove
end Perennial
