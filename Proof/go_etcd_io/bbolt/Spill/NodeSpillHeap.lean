/-
`node.spill`'s heap accessors (U9j, `notes/bbolt-proof-plan.md`): **a live node's struct and
children, out of `wtxW` and back** (`wtxW_children_acc`): what the children loop reads
(`len(n.children)`, `n.children[i]`) without changing the writer's records.
-/
module

public import Proof.go_etcd_io.bbolt.Spill.DerefHeap
public import Proof.go_etcd_io.bbolt.Rebalance.Heap
public import Proof.go_etcd_io.bbolt.Rebalance.NodeRblBase

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

omit [GooseSemantics] [GooseInterp] go_gctx hos in
theorem node_bs_of {X : WX} {bl n : Loc} {rn : NRec} (h : X.node bl n = some rn) :
    ∃ B, X.t.bs !! bl = some B ∧ B.ns !! n = some rn := by
  unfold WX.node at h
  cases hb : X.t.bs !! bl with
  | none => rw [hb] at h; cases h
  | some B => rw [hb] at h; exact ⟨B, rfl, h⟩

/-- **A live node's struct and children, out of `wtxW` and back** (see the module doc). -/
theorem wtxW_children_acc (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (bl n : Loc)
    (rn : NRec) (hn : X.node bl n = some rn) (hl : n ∈ X.live) :
    wtxW (GF := GF) K tx r m X ⊢ n ↦ rn.nv ∗ rn.nv.children' ↦* rn.cs ∗
      (n ↦ rn.nv ∗ rn.nv.children' ↦* rn.cs -∗ wtxW K tx r m X) := by
  obtain ⟨B, HB, Hrn⟩ := node_bs_of hn
  iintro Hw
  icases wtxW_open K tx r m X $$ Hw with ⟨#Hpk, #Hcore, #Hreg, Hh, Hv, Hst, Hclose⟩
  ihave %Hok := wtxHeap_heapOK tx (DFrac.own 1) X $$ Hh
  icases wtxHeap_setNode_bkt tx (DFrac.own 1) X bl B n rn HB Hrn $$ Hh with ⟨Hno, Hbo, Hf, Hback⟩
  rw [decide_eq_true hl]
  icases (objOwn_live_node _ _ _ _ _).1 $$ Hno with ⟨Hn, Hins, Hcap, Hws, Hch, Hchcap, Hkey⟩
  iframe Hn Hch
  iintro ⟨Hn, Hch⟩
  ihave Hno : objOwn X.v n (DFrac.own 1) true (.node bl rn) $$ [Hn Hins Hcap Hws Hch Hchcap Hkey]
  · iapply (objOwn_live_node _ _ _ _ _).2; iframe
  ihave Hh := Hback $$ %rn %(Hok.2.2.2.1 bl B n rn HB Hrn) [Hno] [Hbo] [Hf]
  · iexact Hno
  · iexact Hbo
  · iexact Hf
  rw [setNode_self X bl n B rn HB Hrn]
  iapply Hclose $$ %X [] Hh Hv Hst
  ipureintro; exact ⟨rfl, rfl, rfl⟩

end heap

end Spill

end bbolt
end EtcdGrove
end Perennial
