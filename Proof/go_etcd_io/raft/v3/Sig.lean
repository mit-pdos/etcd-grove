/- Lean-first (no Rocq counterpart).

## raft's signature, proved (2026-10-14)

`raftSig.ghostLaws : raftSig.GhostLaws` and `raftSig.laws : raftSig.Laws`
(`Spec/go_etcd_io/raft/v3/Sig.lean`): each law is a theorem of raft's proof, but for the
two stated for the signature, which a client proved before by opening raft's predicates:
* `deposited_fresh`, from `raftCommitInv`'s registry (`propsOwn`): the register's
  `reg_deposited_minted` opened it;
* `isNode_commitInv`, from `isNode`'s body: the register's apply loop unfolded it
  (`open_node`).

### How the API is proved (from the former `Results.lean`, removed 2026-10-14)

Every Hoare triple lives in its own spec/proof pair, and `Link.lean` instantiates every
proof with its callees' results. At the bottom is `raft.wp_Step`: running `Step` on a
message takes the physical raft struct from a state refining the protocol state `s` to one
refining `s'`, and the ghost protocol state can be moved from `s` to `s'` at the same time,
i.e. the implementation refines the protocol of `Protocol/`. The `RawNode` results are
client-facing (since 2026-10-09): stated on `ownRawNode γ rn id rs` (`InvRawnode.lean`), with
no protocol state in them; the refinement is how they are proved, and `node.go`'s results
(`isNode`, `nodeDriver`) are built on them.

Trust boundary, two kinds:
  - A `Proof/<fn>.lean` of a function outside the proof's scope is an `axiom <fn>.wp_proof`.
    The client-supplied interfaces are not: `isLogger` is a definition (the triples a client
    supplies), and `ownStorage` is a field of `StorageModel GF`, so the results hold for
    every storage predicate.
  - A function that is in scope but unfinished is a `sorry` inside its own
    `Proof/<fn>.lean`.
A callee spec taken as a hypothesis is discharged in `Link.lean` by the callee's own
result and adds nothing to the trust base; `etc/tcb-report.py --collection
etc/tcb-collections/raft.txt` prints what the results rest on.
-/
module

public import Spec.go_etcd_io.raft.v3.Sig
public import Proof.go_etcd_io.raft.v3.Protocol.LeaderCompleteness

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

namespace raftSig

section ghost
variable [FfiSyntax]
variable {GF : BundledGFunctors} [AllG GF] [InvGS GF]

theorem deposited_fresh (γ : RaftNames) (d : List w8) (M : GMap (List w8) Unit) (E : CoPset)
    (HE : ↑raftN ⊆ E) :
    ⊢ raftCommitInv (GF := GF) γ -∗ deposited γ d -∗ ghostMapAuth γ.reFresh 1 M ={E}=∗
      ⌜M.lookup d = some ()⌝ ∗ ghostMapAuth γ.reFresh 1 M := by
  iintro #Hcinv #Hdep HM
  unfold raftCommitInv
  iinv Hcinv with ⟨%l, %R, >HP, >Hj, >Htbl, Hpo⟩ Hclose
  imod propsOwn_open γ _ l R $$ Hpo with Hpo
  unfold propsOwnL
  icases Hpo with ⟨%ods, #Hds, Hv, Hra, Hs⟩
  unfold deposited
  icases Hdep with ⟨%γp, #Hfr⟩
  icases ghost_map_lookup $$ Hra Hfr with %HR
  icases (BigSepM.bigSepM_lookup_acc (Φ := fun d γp =>
    iprop(▷ (propSlot (GF := GF) γ d γp (firstOcc ods) ∗ propFresh γ d))) HR).1 $$ Hs
    with ⟨⟨Hsl, >Hf⟩, Hsback⟩
  iunfold propFresh at Hf
  icases ghost_map_lookup $$ HM Hf with %HMd
  ihave Hs := Hsback $$ [Hsl Hf]
  · inext; iframe Hsl; unfold propFresh; iexact Hf
  ihave Hpo : propsOwnL γ l R $$ [Hv Hra Hs]
  · unfold propsOwnL
    iexists ods
    iframe Hds Hv Hra Hs
  ihave Hpo := propsOwn_close γ l R $$ Hpo
  imod Hclose $$ [HP Hj Htbl Hpo] with -
  · inext
    iexists l, R
    iframe
  imodintro
  iframe HM
  ipureintro; exact HMd

theorem ghostLaws : GhostLaws (GF := GF) where
  isCommitted_agree := isCommitted_agree
  isCommitted_mono := isCommitted_mono
  ownRaftGhost_alloc := ownRaftGhost_alloc
  entDataIs_list_prefix := entDataIs_list_prefix
  deposited_fresh := deposited_fresh

end ghost

section program
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem isNode_commitInv (γ : NodeNames) (id : w64) (n : Loc) :
    isNode (GF := GF) γ id n ⊢ raftCommitInv γ.raft := by
  iintro #Hnode
  open_node Hnode
  iexact Hcinv

theorem laws : Laws (GF := GF) where
  budget_alloc := budget_alloc
  propDataInv_alloc := propDataInv_alloc
  tickCred_split := tickCred_split
  isNode_commitInv := isNode_commitInv
  node_collect := node_collect
  node_committed_data := node_committed_data
  node_entData_heap := node_entData_heap
  node_ready_receive := node_ready_receive
  memStorage_absorb := memStorage_absorb
  memStorage_handout := memStorage_handout
  ownMemoryStorage_bounded := ownMemoryStorage_bounded
  ownMemoryStorage_init := ownMemoryStorage_init

end program

end raftSig

end EtcdGrove
end Perennial
