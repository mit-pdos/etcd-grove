/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/queue/Methods.lean`, run `rabia-r1wake-1`.)

`PQueue`'s methods `Less`, `Swap`, `Push`, `Pop` through `&q` (the `heap.Interface` value
`pqIface q`), on `pqOwn`: lemmas (Go methods of this package without a spec of the interface;
`Len` has its spec, `PQueue.Len.spec`).
-/
module

public import Dsverify.Proof.rabia.internal.queue.Basics

@[expose] public section

noncomputable section

namespace Perennial.rabia.internal.queue

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model rabia.internal.message

/-- Discharge the bounds check of an `IndexRef` (`slice_index_if` of `std_core.Shuffle`). -/
local macro "slice_index_if" : tactic =>
  `(tactic| (rw [ite_eq_left_of_eq_true _ _ (eq_true (by constructor <;> word))]))

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem : rabia.internal.queue.Assumptions]

theorem wp_pq_Swap (q : Loc) (xs : List ObjV) (i j : w64) (a b : ObjV)
    (hi : 0 ≤ sint.Z i) (hj : 0 ≤ sint.Z j)
    (ha : xs[sint.nat i]? = some a) (hb : xs[sint.nat j]? = some b) :
    {{ pqOwn (GF := GF) q xs }}
      (App (App (Val #(methods (go.GoType.PointerType PQueue.ty) go!"Swap" #q)) (Val #i)) (Val #j))
    {{ RET #(); pqOwn q ((xs.set (sint.nat i) b).set (sint.nat j) a) }} := by
  wp_start as H
  simp only [pqOwn_unfold]
  icases H with ⟨%sl, %vs, Hq, Hs, Hcap, %Hlen, #Hr⟩
  ihave %Hl := ownSlice_len _ _ _ $$ Hs
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  have hil : sint.nat i < vs.length := by
    have := (List.getElem?_eq_some_iff.mp ha).1; omega
  have hjl : sint.nat j < vs.length := by
    have := (List.getElem?_eq_some_iff.mp hb).1; omega
  list_elem vs (sint.nat i) as vi
  list_elem vs (sint.nat j) as vj
  slice_index_if
  wp_auto
  slice_index_if
  wp_auto
  slice_index_if
  wp_apply wp_load_slice_index sl (sint.Z j) vs _ vj hj $$ [Hs] with Hs
  · iframe Hs; ipureintro; exact Hvj_lookup
  wp_auto
  slice_index_if
  wp_apply wp_load_slice_index sl (sint.Z i) vs _ vi hi $$ [Hs] with Hs
  · iframe Hs; ipureintro; exact Hvi_lookup
  wp_apply wp_store_slice_index sl (sint.Z i) vs vj $$ [Hs] with Hs
  · iframe Hs; ipureintro; constructor <;> word
  wp_apply wp_store_slice_index sl (sint.Z j) _ vi $$ [Hs] with Hs
  · iframe Hs; ipureintro; simp only [List.length_set]; constructor <;> word
  iapply HΦ
  iexists sl, _
  iframe Hq Hs Hcap
  isplitr
  · ipureintro; simp only [List.length_set]; exact Hlen
  iapply reps_transport vs _ xs _ ?_ $$ Hr
  have hi' : (sint.Z i).toNat = sint.nat i := rfl
  have hj' : (sint.Z j).toNat = sint.nat j := rfl
  rw [hi', hj']
  exact swap_transport vs xs _ _ vi vj a b Hvi_lookup Hvj_lookup ha hb

omit package_sem in
/-- A slice points-to in two halves. -/
theorem ownSlice_half_split {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (sl : GoSlice)
    (vs : List V) :
    (sl ↦* vs : IProp GF) ⊣⊢ sl ↦*{DFrac.own (1 : Qp).half} vs ∗ sl ↦*{DFrac.own (1 : Qp).half} vs := by
  have h := (ownSlice_dfractional (GF := GF) sl vs).dfractional (DFrac.own (1 : Qp).half)
    (DFrac.own (1 : Qp).half)
  have e : DFrac.own (1 : Qp).half • DFrac.own (1 : Qp).half = DFrac.own 1 := by
    rw [show DFrac.own (1 : Qp).half • DFrac.own (1 : Qp).half =
      DFrac.own ((1 : Qp).half + (1 : Qp).half) from rfl, Qp.half_add_half]
  rw [e] at h
  exact h

theorem wp_pq_Push (q : Loc) (xs : List ObjV) (v : ConsensusObj) (o : ObjV) :
    {{ pqOwn (GF := GF) q xs ∗ objRep v o }}
      (App (Val #(methods (go.GoType.PointerType PQueue.ty) go!"Push" #q))
        (Val #(interface.mkOk ConsensusObj.ty #v)))
    {{ RET #(); pqOwn q (xs ++ [o]) }} := by
  wp_start as ⟨H, #Ho⟩
  simp only [pqOwn_unfold]
  icases H with ⟨%sl, %vs, Hq, Hs, Hcap, %Hlen, #Hr⟩
  wp_auto
  wp_apply wp_slice_literal (V := ConsensusObj) (t := ConsensusObj.ty) [v]
  isplitr
  · ipureintro; rfl
  iintro %lp ⟨Hl1, Hl1c⟩
  wp_auto
  wp_apply wp_slice_append (V := ConsensusObj) (t := ConsensusObj.ty) sl vs _ [v] _
    $$ [$Hs $Hcap $Hl1] as %s' ⟨Hs', Hs'c, -⟩
  iapply HΦ
  iexists s', _
  iframe Hq Hs' Hs'c
  isplitr
  · ipureintro; simp [Hlen]
  iapply reps_snoc vs xs v o Hlen
  iframe Hr Ho

theorem wp_pq_Pop (q : Loc) (xs : List ObjV) (hne : xs ≠ []) :
    {{ pqOwn (GF := GF) q xs }}
      (App (Val #(methods (go.GoType.PointerType PQueue.ty) go!"Pop" #q)) (Val #()))
    {{ (v : ConsensusObj), RET #(interface.mkOk ConsensusObj.ty #v);
        ∃ o, ⌜xs.dropLast ++ [o] = xs⌝ ∗ objRep v o ∗ pqOwn q xs.dropLast }} := by
  wp_start as H
  simp only [pqOwn_unfold]
  icases H with ⟨%sl, %vs, Hq, Hs, Hcap, %Hlen, #Hr⟩
  ihave %Hl := ownSlice_len _ _ _ $$ Hs
  wp_auto
  have hpos : 0 < vs.length := by
    rw [Hlen]; exact List.length_pos_iff.mpr hne
  have hidx : sint.nat (sl.len - W64 1) < vs.length := by word
  list_elem vs (sint.nat (sl.len - W64 1)) as vl
  slice_index_if
  wp_apply wp_load_slice_index sl (sint.Z (sl.len - W64 1)) vs _ vl (by word) $$ [Hs] with Hs
  · iframe Hs; ipureintro; exact Hvl_lookup
  wp_auto
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hs
  rw [ite_eq_left_of_eq_true _ _ (eq_true (by refine ⟨?_, ?_, ?_⟩ <;> word))]
  icases ownSlice_slice_with_cap (W64 0) (sl.len - W64 1) sl vs ⟨by word, by word, by word⟩ $$ [$Hs $Hcap]
    with ⟨-, Hs, Hcap⟩
  wp_auto
  have hn : sint.nat (sl.len - W64 1) = xs.length - 1 := by word
  rw [hn] at Hvl_lookup
  icases reps_lookup vs xs _ vl Hvl_lookup $$ Hr with ⟨%o, %Ho, #Hro⟩
  iapply HΦ
  iexists o
  iframe Hro
  isplitr
  · ipureintro
    have hl : xs.getLast hne = o := by
      rw [List.getLast_eq_getElem] at *
      rw [List.getElem?_eq_some_iff] at Ho
      obtain ⟨_, h⟩ := Ho; exact h
    rw [← hl]; exact List.dropLast_concat_getLast hne
  iexists _, _
  iframe Hq Hs Hcap
  rw [hn, show sint.nat (W64 0) = 0 from rfl]
  isplitr
  · ipureintro; simp [subslice, Hlen]
  iapply reps_transport vs _ xs _ ?_ $$ Hr
  intro k v' hk
  refine ⟨k, ?_, ?_⟩
  · simp only [subslice, List.drop_zero, List.getElem?_take] at hk
    split at hk
    · exact hk
    · cases hk
  · simp only [subslice, List.drop_zero, List.getElem?_take] at hk
    split at hk
    · rw [List.dropLast_eq_take, List.getElem?_take]; simp_all
    · cases hk

omit package_sem in
theorem pqOwn_len (q : Loc) (xs : List ObjV) :
    pqOwn (GF := GF) q xs ⊢ pqOwn q xs ∗ ⌜xs.length < 2 ^ 63⌝ := by
  simp only [pqOwn_unfold]
  iintro ⟨%sl, %vs, Hq, Hs, Hcap, %Hlen, #Hr⟩
  ihave %Hl := ownSlice_len _ _ _ $$ Hs
  isplitl
  · iexists sl, vs
    iframe Hq Hs Hcap Hr
    ipureintro; exact Hlen
  ipureintro
  rw [← Hlen, Hl.1]; word

end proof

section run
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem : rabia.internal.queue.Assumptions]

theorem wp_pq_Less
    (wp_lt : ProxySeqIdLessThan.spec (GF := GF) (hG := hG))
    (q : Loc) (xs : List ObjV) (i j : w64) (a b : ObjV)
    (hi : 0 ≤ sint.Z i) (hj : 0 ≤ sint.Z j)
    (ha : xs[sint.nat i]? = some a) (hb : xs[sint.nat j]? = some b) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.message ∗ pqOwn (GF := GF) q xs }}
      (App (App (Val #(methods (go.GoType.PointerType PQueue.ty) go!"Less" #q)) (Val #i)) (Val #j))
    {{ (r : Bool), RET #r; pqOwn q xs ∗ ⌜r = true ↔ objLt a b⌝ }} := by
  wp_start as H
  simp only [pqOwn_unfold]
  icases H with ⟨%sl, %vs, Hq, Hs, Hcap, %Hlen, #Hr⟩
  ihave %Hl := ownSlice_len _ _ _ $$ Hs
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  have hil : sint.nat i < vs.length := by
    have := (List.getElem?_eq_some_iff.mp ha).1; omega
  have hjl : sint.nat j < vs.length := by
    have := (List.getElem?_eq_some_iff.mp hb).1; omega
  list_elem vs (sint.nat i) as vi
  list_elem vs (sint.nat j) as vj
  slice_index_if
  wp_auto
  slice_index_if
  wp_auto
  icases (ownSlice_half_split sl vs).1 $$ Hs with ⟨Hs1, Hs2⟩
  icases ownSlice_elem_acc (sint.Z i) vi sl _ vs hi Hvi_lookup $$ Hs1 with ⟨Hvi, Hs1⟩
  icases ownSlice_elem_acc (sint.Z j) vj sl _ vs hj Hvj_lookup $$ Hs2 with ⟨Hvj, Hs2⟩
  wp_apply wp_lt $$ [$Hpkg $Hvi $Hvj] as ⟨Hvi, Hvj⟩
  ihave Hs1 := Hs1 $$ Hvi
  ihave Hs2 := Hs2 $$ Hvj
  rw [list_set_lookup_self vs _ vi Hvi_lookup, list_set_lookup_self vs _ vj Hvj_lookup]
  ihave Hs := (ownSlice_half_split sl vs).2 $$ [$Hs1 $Hs2]
  icases reps_lookup vs xs _ vi Hvi_lookup $$ Hr with ⟨%oi, %Hoi, #Hri⟩
  icases reps_lookup vs xs _ vj Hvj_lookup $$ Hr with ⟨%oj, %Hoj, #Hrj⟩
  icases objRep_fields _ _ $$ Hri with %Hi
  icases objRep_fields _ _ $$ Hrj with %Hj
  rw [ha] at Hoi; cases Hoi
  rw [hb] at Hoj; cases Hoj
  iapply HΦ
  isplitl [Hq Hs Hcap]
  · iexists sl, vs
    iframe Hq Hs Hcap Hr
    ipureintro; exact Hlen
  ipureintro
  unfold objLt
  obtain ⟨h1, h2, -⟩ := Hi
  obtain ⟨h3, h4, -⟩ := Hj
  rw [h1, h2, h3, h4]
  simp

/-- `&q` is a sorter (`sort`'s `isSorter`) of the `PQueue`'s records by `objLt`. -/
theorem pq_isSorter
    (wp_Len : PQueue.Len.spec (GF := GF) (hG := hG))
    (wp_lt : ProxySeqIdLessThan.spec (GF := GF) (hG := hG)) (q : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.queue ⊢
      sort.isSorter (pqx q) (pqOwn q) objLt := by
  iintro #Hq
  ihave #Hm : isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.message $$ [Hq]
  · iPkgInit
  iapply sort.isSorter_intro
  simp only [pqx]
  isplitr
  · imodintro
    iintro %l %Φ
    imodintro
    iintro Hl HΦ
    iapply wp_Len q l slice.nil $$ [$Hq $Hl] HΦ
  isplitr
  · imodintro
    iintro %l %i %j %a %b %Hb %Φ
    imodintro
    iintro Hl HΦ
    obtain ⟨hi, hj, ha, hb⟩ := Hb
    iapply wp_pq_Less wp_lt q l i j a b hi hj ha hb $$ [$Hm $Hl] HΦ
  · imodintro
    iintro %l %i %j %a %b %Hb %Φ
    imodintro
    iintro Hl HΦ
    obtain ⟨hi, hj, ha, hb⟩ := Hb
    iapply wp_pq_Swap q l i j a b hi hj ha hb $$ Hl HΦ


end run

end Perennial.rabia.internal.queue
