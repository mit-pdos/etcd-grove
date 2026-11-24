/-
kvnet's node (`node.go`), its vocabulary for the server's specs (`Node.serve`, `serveClient`,
`handle`), over the wire protocol (`Proto.lean`) and the transport's (`TransportDefs.lean`).

* `rep : Loc → w64 → IProp GF`, **the seam to the store**: what the replica `r` of id `id` is
  (persistent), a parameter of the node's specs, fixed by the store layer (kvnet's `isReplica`, after
  decision B), with the replica's methods' specs (`Replica.propose`, `Replica.read`, ...) stated over
  it and taken by `Node.handle`'s proof as callee hypotheses.
* `stp : NodeConfig → GMap w64 GoString → Loc → GoInterface → IProp GF`, **the incarnation's stopper**
  (2026-11-24, G5: `notes/kvnet-g5-stop.md`), a parameter like `rep`: what `start` gives with an
  incarnation (replica `r`, transport `tv`) and `stopIncarnation` spends to give the start resource back.
  The store layer fixes it (`repStopper` and the transport's `ptStop`, with the start resource's
  persistent part).
* `nodeLockInv` (`Node.mu`'s): the current incarnation: the fields `r` and `t`, the replica's raft
  node `n` (`isNode`), `rep r id`, and the stopper.
* `stopLaw`/`startLaw` (persistent), **the restart's laws**, at a resource `R` (the start resource,
  `S cfg.ID cfg.Dir cfg.Opts M` where `StartNode` builds them): `stopIncarnation` turns the stopper into
  `R`, and `start` turns `R` into a new incarnation with its stopper. `Node.restart`'s proof uses
  only these, so it is generic; `startNode` takes them, `StartNode`'s proof gives them from
  `start.spec`/`stopIncarnation.spec` at the cluster `isNodeS` names.
* `isNodeS F rep stp nd γ N id` (persistent): the node `nd`: its configuration (with the address
  map), stats, transport constructor (`ptCtor`, at its per-address premise `AP`), the step law, the
  restart's laws, and its mutex.
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.TransportDefs
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.PeerTransport

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

/-- The node's stopper parameter's type (see the file header). -/
abbrev NodeStopper (GF : BundledGFunctors) [GoGlobalContext] :=
  github_com.mit_pdos.etcd_grove.examples.raft.kvnet.NodeConfig → GMap w64 GoString → Loc → GoInterface →
    IProp GF

/-- **`Node.mu`'s invariant**: the current incarnation (see the file header). -/
def nodeLockInv (rep : Loc → w64 → IProp GF) (stp : NodeStopper GF) (nd : Loc)
    (cfg : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.NodeConfig) (M : GMap w64 GoString)
    (γ : Cluster) (N : Namespace) (id : w64) : IProp GF :=
  iprop(∃ (r : Loc) (tv : GoInterface) (n : NodeH),
    nd.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Node, go!"r"] ↦ r ∗
    nd.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Node, go!"t"] ↦ tv ∗
    r.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Replica, go!"node"] ↦□
      interface.mkOk (go.GoType.PointerType node.ty) #n.loc ∗
    □ rep r id ∗ isNode n γ N id ∗ stp cfg M r tv)

/-- `stopIncarnation` turns the stopper into `R` (see the file header). -/
def stopLaw (stp : NodeStopper GF) (cfg : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.NodeConfig) (M : GMap w64 GoString) (R : IProp GF) :
    IProp GF :=
  iprop(□ ∀ (r : Loc) (tv : GoInterface),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet ∗ stp cfg M r tv }}
      (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvnet.stopIncarnation)) (Val #r)) (Val #tv))
    {{ RET #(); R }})

instance stopLaw_persistent stp cfg M R : Persistent (stopLaw (GF := GF) stp cfg M R) := by
  unfold stopLaw; infer_instance

/-- `start` turns `R` into a new incarnation and its stopper (see the file header). -/
def startLaw (F : KvFacts GF) (AP : w64 → GoString → IProp GF) (rep : Loc → w64 → IProp GF)
    (stp : NodeStopper GF)
    (cfg : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.NodeConfig) (M : GMap w64 GoString) (R : IProp GF) (γ : Cluster) (N : Namespace) :
    IProp GF :=
  iprop(□ ∀ (sts : Loc) (f : GoFunc),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet ∗ cfg.Addrs' ↦$□ M ∗ R ∗ isStats sts ∗
        ptCtor F γ N cfg.ID' AP f }}
      (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvnet.start)) (Val #cfg)) (Val #sts)) (Val #f))
    {{ (r : Loc) (tv : GoInterface), RET (PairV #r #tv); ∃ n : NodeH,
        r.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Replica, go!"node"] ↦□ interface.mkOk (go.GoType.PointerType node.ty) #n.loc ∗
        □ rep r cfg.ID' ∗ isNode n γ N cfg.ID' ∗ stp cfg M r tv }})

instance startLaw_persistent F AP rep stp cfg M R γ N :
    Persistent (startLaw (GF := GF) F AP rep stp cfg M R γ N) := by
  unfold startLaw; infer_instance

/-- The node `nd` (see the file header). -/
def isNodeS (F : KvFacts GF) (rep : Loc → w64 → IProp GF) (stp : NodeStopper GF) (nd : Loc)
    (γ : Cluster) (N : Namespace) (id : w64) : IProp GF :=
  iprop(∃ (cfg : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.NodeConfig) (M : GMap w64 GoString)
      (sp : Loc) (f : GoFunc),
    nd.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Node, go!"cfg"] ↦□ cfg ∗ ⌜cfg.ID' = id⌝ ∗
    cfg.Addrs' ↦$□ M ∗
    nd.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Node, go!"stats"] ↦□ sp ∗ isStats sp ∗
    nd.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Node, go!"newT"] ↦□ f ∗
    stepLaw F γ N id ∗ ⌜Cluster.trace γ = none⌝ ∗
    (∃ (AP : w64 → GoString → IProp GF) (R : IProp GF), ptCtor F γ N id AP f ∗
      stopLaw stp cfg M R ∗ startLaw F AP rep stp cfg M R γ N) ∗
    sync.isMutex (nd.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Node, go!"mu"])
      (nodeLockInv rep stp nd cfg M γ N id))

instance isNodeS_persistent F rep stp nd γ N id :
    Persistent (isNodeS (GF := GF) F rep stp nd γ N id) := by
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
