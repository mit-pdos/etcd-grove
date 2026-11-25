/-
`n.accept(l)` (`node.go`, 2026-11-24 G5: `Run`'s accept loop): serves every connection the listener
accepts at the replica's address, each in a goroutine (`serve`). It never returns.
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.NodeDefs
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.listen

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
variable [package_sem' : net.Assumptions] [field_sem : net.FieldAssumptions]

/-- See the file header. -/
abbrev Node.accept.spec (F : KvFacts GF) (rep : Loc → w64 → IProp GF) (stp : NodeStopper GF)
    (cf : GoInterface → List w8 → IProp GF) : Prop :=
  ∀ (nd : Loc) (γ : Cluster) (N : Namespace) (id : w64) (li : GoInterface) (l : w64) (a : GoString)
    (eof ed : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet ∗
      isNodeS F rep stp nd γ N id ∗ confLaw F rep cf γ N id ∗ addrProto a (kvP F id) (kvQ F id) ∗
      net.isListener li l ∗ netLis (extLocalGS netExt (L := hG.goose_localGS)) l a true ∗
      netLisAt (extLocalGS netExt (L := hG.goose_localGS)) l a ∗
      globalAddr io.EOF ↦□ eof ∗ globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed ∗
      context.isClosedchanInit }}
    (App (Val (nd @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Node.ty @!! go!"accept")) (Val #li))
  {{ RET #(); True }}

end spec

end raft_kvnet
end EtcdGrove
end Perennial
