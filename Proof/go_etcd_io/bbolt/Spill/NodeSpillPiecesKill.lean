/-
`node.spill` after its children's loop (U9l, `notes/bbolt-proof-plan.md`): **`n.children = nil`**
(`wtxW_nilCh`): `n`'s `children` field out of `wtxW`, and back as `nil` with `n`'s record's
children cleared and its old children killed (`WX.nilCh`: they are spilled pieces nothing reaches
any more; `liveReach`, `derefPre` need them dead).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.NodeSpillHeap

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section model
variable [GooseExts]

/-- `X` with the nodes `L` dead. -/
def WX.killL (X : WX) (L : List Loc) : WX := { X with live := L.foldr (fun c m => m.delete c) X.live }

/-- A node's record with its children cleared (`n.children = nil`). -/
def NRec.nilCh (r : NRec) : NRec := { r with nv := { r.nv with children' := slice.nil }, cs := [] }

/-- **`X` after `n.children = nil`** (`n`'s record `r` in bucket `bl`): `n`'s children cleared and
its old children dead. -/
def WX.nilCh (X : WX) (bl n : Loc) (r : NRec) : WX := (X.setNode bl n r.nilCh).killL r.cs

theorem killL_live (X : WX) (L : List Loc) (l : Loc) :
    l ∈ (X.killL L).live ↔ l ∈ X.live ∧ l ∉ L := by
  unfold WX.killL
  induction L with
  | nil => simp
  | cons c L ih =>
    simp only [List.foldr_cons, List.mem_cons, not_or]
    rw [GMap.mem_iff] at ih ⊢
    rw [GMap.lookup_delete_iff]
    by_cases hc : c = l
    · subst hc; simp
    · simp only [hc, ↓reduceIte, ih]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, Ne.symm hc, h2⟩
      · rintro ⟨h1, -, h2⟩; exact ⟨h1, h2⟩

end model

namespace Spill

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

theorem wtxHeap_killL (tx : Loc) (dq : DFrac) (X : WX) (L : List Loc) :
    wtxHeap (GF := GF) tx dq X ⊢ wtxHeap tx dq (X.killL L) := by
  induction L with
  | nil => exact .rfl
  | cons c L ih =>
    refine ih.trans ?_
    have := wtxHeap_kill (GF := GF) tx dq (X.killL L) c
    unfold WX.killL at this ⊢
    exact this

/-- **`n.children = nil`** (see the module doc). -/
theorem wtxW_nilCh (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (bl n : Loc)
    (rn : NRec) (hn : X.node bl n = some rn) (hl : n ∈ X.live) :
    wtxW (GF := GF) K tx r m X ⊢ n.[node, go!"children"] ↦ rn.nv.children' ∗
      (n.[node, go!"children"] ↦ slice.nil -∗ wtxW K tx r m (X.nilCh bl n rn)) := by
  obtain ⟨B, HB, Hrn⟩ := node_bs_of hn
  iintro Hw
  icases wtxW_open K tx r m X $$ Hw with ⟨#Hpk, #Hcore, #Hreg, Hh, Hv, Hst, Hclose⟩
  ihave %Hok := wtxHeap_heapOK tx (DFrac.own 1) X $$ Hh
  icases wtxHeap_setNode tx (DFrac.own 1) X bl B n rn HB Hrn $$ Hh with ⟨Hno, Hback⟩
  rw [decide_eq_true hl]
  icases (objOwn_live_node _ _ _ _ _).1 $$ Hno with ⟨Hn, Hins, Hcap, Hws, Hch, Hchcap, Hkey⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hn with ⟨Hn, %Hnn⟩
  iStructNamed Hn
  iframe children
  iintro children
  ihave Hn : (n ↦ rn.nilCh.nv : IProp GF)
    $$ [bucket isLeaf unbalanced spilled key pgid parent children inodes]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef, NRec.nilCh]
    iframe
  ihave Hno : objOwn X.v n (DFrac.own 1) true (.node bl rn.nilCh) $$ [Hn Hins Hcap Hws Hchcap Hkey]
  · iapply (objOwn_live_node _ _ _ _ _).2
    simp only [NRec.nilCh]
    iframe
    isplitl []
    · iapply ownSlice_nil
    · iapply ownSliceCap_nil
  ihave Hh := Hback $$ %rn.nilCh [] [Hno]
  · ipureintro; exact Hok.2.2.2.1 bl B n rn HB Hrn
  · iexact Hno
  ihave Hh := wtxHeap_killL tx (DFrac.own 1) _ rn.cs $$ Hh
  unfold WX.nilCh
  iapply Hclose $$ %((X.setNode bl n rn.nilCh).killL rn.cs) [] Hh Hv Hst
  ipureintro
  simp only [WX.killL, setNode_eq X bl n B _ HB]
  trivial

end heap

end Spill

end bbolt
end EtcdGrove
end Perennial
