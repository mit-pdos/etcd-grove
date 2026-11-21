/-
kvnet's node (`node.go`), its vocabulary for the server's specs (`Node.serve`, `serveClient`,
`handle`), over the wire protocol (`Proto.lean`) and the transport's (`TransportDefs.lean`).

* `rep : Loc → w64 → IProp GF`, **the seam to the store**: what the replica `r` of id `id` is
  (persistent), a parameter of the node's specs, fixed by the store layer (kvnet's `isReplica`, after
  decision B), with the replica's methods' specs (`Replica.propose`, `Replica.read`, ...) stated over
  it and taken by `Node.handle`'s proof as callee hypotheses.
* `isNodeS F rep nd γ N id n` (persistent): the node `nd`: its replica (`rep r id`), its transport
  (`isTransportCore`), its stats, and the replica's raft node (the interface over `*node` at `n`).
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.TransportDefs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Iris.ProofMode Net go_etcd_io.raft.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

/-- The node `nd` (see the file header). -/
def isNodeS (F : KvFacts GF) (rep : Loc → w64 → IProp GF) (nd : Loc) (γ : Cluster) (N : Namespace)
    (id : w64) (n : Loc) : IProp GF :=
  iprop(∃ (r t sp : Loc),
    nd.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Node, go!"r"] ↦□ r ∗
    nd.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Node, go!"t"] ↦□ t ∗
    nd.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Node, go!"stats"] ↦□ sp ∗ isStats sp ∗
    r.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Replica, go!"node"] ↦□
      interface.mkOk (go.GoType.PointerType node.ty) #n ∗
    □ rep r id ∗ isTransportCore F t γ N id n)

instance isNodeS_persistent F rep nd γ N id n : Persistent (isNodeS (GF := GF) F rep nd γ N id n) := by
  unfold isNodeS; infer_instance

end defs

end raft_kvnet
end EtcdGrove
end Perennial
