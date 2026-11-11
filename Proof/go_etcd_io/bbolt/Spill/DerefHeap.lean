/-
The writer's heap under `dereference` (U9b, `notes/bbolt-proof-plan.md`): `wtxW` opened to its
heap, its view's cells and its statistics' token (and closed on a heap of the same view, handles
and registry), and the heap's facts kept by a `derefStep`.
-/
module

public import Proof.go_etcd_io.bbolt.Spill.DerefRel
public import Proof.go_etcd_io.bbolt.Inv.Ctx
public import Proof.go_etcd_io.bbolt.Rebalance.Heap
public import Proof.go_etcd_io.bbolt.Txn.Heap
public import Proof.go_etcd_io.bbolt.Rebalance.Objs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance BC.core_persistent' (K : BC) : Persistent (K.core (GF := GF)) := by
  unfold BC.core; infer_instance

/-- **`wtxW`, opened**: its heap, its view's cells and its statistics' token; it closes on any heap
`X'` of the same view, handles and node registry. -/
theorem wtxW_open (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) :
    wtxW (GF := GF) K tx r m X ⊢
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ K.core ∗ reg tx K.B r ∗
      wtxHeap tx (DFrac.own 1) X ∗ viewCells wq X.v ∗ statsTok r m 1 ∗
      (∀ X', ⌜X'.v = X.v ∧ X'.handles = X.handles ∧ (X'.nloc, X'.t.t) = (X.nloc, X.t.t)⌝ -∗
        wtxHeap tx (DFrac.own 1) X' -∗ viewCells wq X.v -∗ statsTok r m 1 -∗ wtxW K tx r m X') := by
  unfold wtxW wtxCore
  iintro ⟨⟨#Hpk, #Hcore, %Hr, #Hreg, Hh, Hf, Hbk, Hnl, Hdb, Hvo, Hst⟩, Hv, Hmap⟩
  iframe Hh Hv Hst
  isplitr
  · iexact Hpk
  isplitr
  · iexact Hcore
  isplitr
  · iexact Hreg
  iintro %X' %He Hh Hv Hst
  obtain ⟨hv, hh, hnt⟩ := He
  have hn : X'.nloc = X.nloc := congrArg Prod.fst hnt
  have htt : X'.t.t = X.t.t := congrArg Prod.snd hnt
  rw [hv, hh, hn, htt]
  iframe
  isplitr
  · iexact Hpk
  isplitr
  · iexact Hcore
  isplitr
  · ipureintro; exact Hr
  iexact Hreg

/-- The heap's facts are kept by a `derefStep` (no object moves, no bucket or parent changes). -/
theorem heapOK_step (tx : Loc) (X X' : WX) (h : derefStep X X') (hok : heapOK (GF := GF) tx X) :
    heapOK (GF := GF) tx X' := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hok
  have hbs := derefStep_bs h
  refine ⟨by rw [h.2.2.2.2.1]; exact h1, objsDisj_step h h2, ?_, ?_, ?_, ?_⟩
  · intro bl B' hB'
    obtain ⟨B, hB, hs⟩ := optRel_some_r (hB' ▸ hbs bl)
    rw [(bktStep_fields hs).1]; exact h3 bl B hB
  · intro bl B' n r' hB' hr'
    obtain ⟨B, hB, hs⟩ := optRel_some_r (hB' ▸ hbs bl)
    obtain ⟨r, hr, hrs⟩ := optRel_some_r (hr' ▸ hs.2 n)
    rw [(nodeStep_nv hrs).1]; exact h4 bl B n r hB hr
  · intro n y hn
    rw [h.2.2.2.1] at hn
    rw [objs_isSome_step h h2]; exact h5 n y hn
  · intro bl B' hB'
    obtain ⟨B, hB, -⟩ := optRel_some_r (hB' ▸ hbs bl)
    rw [h.2.2.2.2.1, h.2.2.1]; exact h6 bl B hB

theorem setNode_self (X : WX) (bl l : Loc) (B : BRec) (r : NRec) (hB : X.t.bs !! bl = some B)
    (hr : B.ns !! l = some r) : X.setNode bl l r = X := by
  unfold WX.setNode WX.setBkt
  rw [hB]
  simp only
  rw [GMap.insert_id _ _ _ hr]
  rw [show ({ B with ns := B.ns } : BRec) = B from rfl, GMap.insert_id _ _ _ hB]

theorem setBkt_self (X : WX) (bl : Loc) (B : BRec) (hB : X.t.bs !! bl = some B) :
    X.setBkt bl B = X := by
  unfold WX.setBkt
  rw [GMap.insert_id _ _ _ hB]

/-- A live node of the heap, out and back unchanged. -/
theorem wtxHeap_node_peek (tx : Loc) (dq : DFrac) (X : WX) (bl l : Loc) (B : BRec) (r : NRec)
    (hB : X.t.bs !! bl = some B) (hr : B.ns !! l = some r) (hl : l ∈ X.live) :
    wtxHeap (GF := GF) tx dq X ⊢ objOwn X.v l dq true (WObj.node bl r) ∗
      (objOwn X.v l dq true (WObj.node bl r) -∗ wtxHeap tx dq X) := by
  exact wtxHeap_live_node_acc tx dq X bl B l r hB hr hl

/-- A live bucket of the heap, out and back unchanged. -/
theorem wtxHeap_bkt_peek (tx : Loc) (dq : DFrac) (X : WX) (bl : Loc) (B : BRec)
    (hB : X.t.bs !! bl = some B) (hl : bl ∈ X.liveB) :
    wtxHeap (GF := GF) tx dq X ⊢ objOwn X.v bl dq true (WObj.bkt B) ∗
      (objOwn X.v bl dq true (WObj.bkt B) -∗ wtxHeap tx dq X) := by
  iintro Hh
  ihave %Hok := wtxHeap_heapOK tx dq X $$ Hh
  icases wtxHeap_bkt_acc tx dq X bl B hB hl $$ Hh with ⟨Ho, Hback⟩
  iframe Ho
  iintro Ho
  ihave Hh := Hback $$ %B %(Hok.2.2.1 bl B hB) Ho
  rw [show ({ B with ns := B.ns } : BRec) = B from rfl, setBkt_self X bl B hB]
  iexact Hh

end heap

end bbolt
end EtcdGrove
end Perennial
