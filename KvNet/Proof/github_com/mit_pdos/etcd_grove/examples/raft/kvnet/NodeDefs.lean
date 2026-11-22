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
    (id : w64) (n : NodeH) : IProp GF :=
  iprop(∃ (r t sp : Loc),
    nd.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Node, go!"r"] ↦□ r ∗
    nd.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Node, go!"t"] ↦□ t ∗
    nd.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Node, go!"stats"] ↦□ sp ∗ isStats sp ∗
    r.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Replica, go!"node"] ↦□
      interface.mkOk (go.GoType.PointerType node.ty) #n.loc ∗
    □ rep r id ∗ isTransportCore F t γ N id n)

instance isNodeS_persistent F rep nd γ N id n : Persistent (isNodeS (GF := GF) F rep nd γ N id n) := by
  unfold isNodeS; infer_instance

/-- **The conf law** (persistent), the seam to the store's decision on configuration changes: a
change `GetConfChange` read back from a `ReqConf` payload `pl` (`cf c pl`: what its spec gives) whose
fact the request carried (`F.confOk pl`) is one `node.ProposeConfChange` takes at the replica `r`:
its content, its size within the cluster's bound, and the proposal's atomic update (built from the
store's invariant: kvdurable's `Cluster.Reconfigure`'s, after decision B). -/
def confLaw (F : KvFacts GF) (rep : Loc → w64 → IProp GF) (cf : GoInterface → List w8 → IProp GF)
    (γ : Cluster) (N : Namespace) (id : w64) : IProp GF :=
  iprop(□ ∀ (r : Loc) (c : GoInterface) (pl : List w8), rep r id -∗ cf c pl -∗ ⌜F.confOk pl⌝ ={⊤}=∗
    ∃ (o : ConfChangeIM) (cc : ConfChangeIC) (dq : DFrac), ccPtsCC c dq cc ∗
      ⌜cc.model = o ∧ ∀ b, γ.maxData = some b → ccSize cc + 64 ≤ b⌝ ∗
      □?γ.dup (AU <{ ∃∃ (ops : List LogEntry), ownCommittedOps γ ops }> @ ⊤ \ ↑N, ∅
         <{ ∀∀ (t : w64) (bs : List w8), ⌜MarshalsConfChange (some o) bs⌝ ∗
              ownCommittedOps γ (ops ++ opsOf [⟨t, confChangeEntryType (some o), bs⟩]),
            COMM True }>))

instance confLaw_persistent F rep cf γ N id : Persistent (confLaw (GF := GF) F rep cf γ N id) := by
  unfold confLaw; infer_instance

end defs

end raft_kvnet
end EtcdGrove
end Perennial
