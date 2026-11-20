/-
`value.lexicalKeyOrderedMapZip`: proved (Prove step, notes/smd-plan.md), over the premise that the
two maps have at most `2^62` keys together (post-freeze change B2c). The keys collected (the
left's, then the right's not on the left) are a permutation of `zipKeys`, so `sort.Strings`
leaves `zipKeys` (`ValuePure.eq_zipKeys_of_perm_sorted`); the loop calls the callback on its
prefixes. Each `if lhs != nil` / `rhs != nil` is joined (`wp_join`) so the rest is proved once.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.lexicalKeyOrderedMapZip
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.heapAllocator__Free
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.freelistAllocator__Free
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.mapUnstructuredString__GetUsing
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.mapUnstructuredString__Has
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.mapUnstructuredString__IterateUsing
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.mapUnstructuredString__Length
public import Perennial.Spec.sort.Strings
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.LawProofs
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.LawProofsDispatch
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.LawProofsSort

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- A wrapper's interface is not nil (kept). -/
theorem isValF_shape (v : value.Value) (dq : DFrac) (x : UVal) :
    isValF (GF := GF) v dq x ⊢ isValF v dq x ∗
      ⌜∃ p : Loc, v = interface.mkOk (go.GoType.PointerType value.valueUnstructured.ty) #p⌝ :=
  pure_elim (∃ p : Loc, v = interface.mkOk (go.GoType.PointerType value.valueUnstructured.ty) #p)
    ((isValF_concrete_law_holds v dq x).trans (by
    iintro ⟨%p, %h⟩; ipureintro; exact ⟨p, h⟩)) (fun h => by
      iintro H; iframe; ipureintro; exact h)

end lemmas

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : value.Assumptions]

theorem value.lexicalKeyOrderedMapZip.wp_proof
    (h_heapAllocator_Free : value.heapAllocator.Free.spec (GF := GF))
    (h_freelistAllocator_Free : value.freelistAllocator.Free.spec (GF := GF))
    (h_mapUnstructuredString_GetUsing : value.mapUnstructuredString.GetUsing.spec (GF := GF))
    (h_mapUnstructuredString_Has : value.mapUnstructuredString.Has.spec (GF := GF))
    (h_mapUnstructuredString_IterateUsing : value.mapUnstructuredString.IterateUsing.spec (GF := GF))
    (h_mapUnstructuredString_Length : value.mapUnstructuredString.Length.spec (GF := GF))
    (h_sort_Strings : _root_.Perennial.sort.Strings.spec (GF := GF)) :
    value.lexicalKeyOrderedMapZip.spec (GF := GF) := fun al lm rm ol or_ fn I Q => by
  wp_start as ⟨Ha, #Hl, #Hr, %Hzl, #Hfn, HI⟩
  ihave %Hlc := isMapO_cases $$ Hl
  ihave %Hrc := isMapO_cases $$ Hr
  ihave ⟨Ha, %ia, %Hia, #HFree⟩ := isAlloc_Free h_heapAllocator_Free h_freelistAllocator_Free al $$ [Ha]
  · iframe; iexact Hpkg
  subst Hia
  ihave %hsl : ⌜keysSorted (kvsOrEmpty ol) = true⌝ $$ []
  · rcases Hlc with ⟨rfl, -⟩ | ⟨kl, gml, rfl, rfl⟩
    · ipureintro; rfl
    · iunfold isMapO at Hl; ihave %h := isMapV_sorted_law_holds _ _ $$ Hl; ipureintro; exact h
  ihave %hsr : ⌜keysSorted (kvsOrEmpty or_) = true⌝ $$ []
  · rcases Hrc with ⟨rfl, -⟩ | ⟨kr, gmr, rfl, rfl⟩
    · ipureintro; rfl
    · iunfold isMapO at Hr; ihave %h := isMapV_sorted_law_holds _ _ $$ Hr; ipureintro; exact h
  wp_auto
  -- the lengths
  wp_join iprop(∃ nl : w64, lhs_ptr ↦ lm ∗ lhsLength_ptr ↦ nl ∗ orderedLength_ptr ↦ nl ∗
      ⌜nl.toInt = (kvsOrEmpty ol).length⌝) at next with [lhs lhsLength orderedLength]
      as ⟨%nl, lhs, lhsLength, orderedLength, %Hnl⟩
  · rcases Hlc with ⟨rfl, rfl⟩ | ⟨kl, gml, rfl, rfl⟩
    · try wp_auto
      wp_join_done
      iexists _; iframe; ipureintro; rfl
    · iunfold isMapO at Hl
      wp_auto
      wp_apply h_mapUnstructuredString_Length gml kl as %n %hn
      · iexact Hl
      try wp_auto
      wp_join_done
      iexists _; iframe; ipureintro; exact hn
  wp_join iprop(∃ nr no : w64, rhs_ptr ↦ rm ∗ rhsLength_ptr ↦ nr ∗ orderedLength_ptr ↦ no ∗
      ⌜nr.toInt = (kvsOrEmpty or_).length ∧ 0 ≤ no.toInt ∧ no.toInt ≤ 2 ^ 62⌝) at next
      with [rhs rhsLength orderedLength]
      as ⟨%nr, %no, rhs, rhsLength, orderedLength, %Hnr⟩
  · rcases Hrc with ⟨rfl, rfl⟩ | ⟨kr, gmr, rfl, rfl⟩
    · try wp_auto
      wp_join_done
      iexists _, _; iframe; ipureintro; refine ⟨rfl, ?_, ?_⟩ <;> omega
    · iunfold isMapO at Hr
      wp_auto
      wp_apply h_mapUnstructuredString_Length gmr kr as %n %hn
      · iexact Hr
      try wp_auto
      wp_if_destruct
      · try wp_auto
        wp_join_done
        iexists _, _; iframe; ipureintro; refine ⟨hn, ?_, ?_⟩ <;> simp [kvsOrEmpty] at Hzl hn ⊢ <;> omega
      · try wp_auto
        wp_join_done
        iexists _, _; iframe; ipureintro; refine ⟨hn, ?_, ?_⟩ <;> omega
  -- both empty: `true`
  have hw0 : ∀ (w : w64) (n : Nat), w.toInt = n → n ≤ 2 ^ 62 → (w = W64 0 ↔ n = 0) := by
    intro w n h hn
    constructor
    · rintro rfl; simp at h; omega
    · intro h0; subst h0; apply BitVec.eq_of_toInt_eq; simpa using h
  have hnl0 := hw0 nl _ Hnl (by omega)
  have hnr0 := hw0 nr _ Hnr.1 (by omega)
  by_cases hz : (kvsOrEmpty ol).length = 0 ∧ (kvsOrEmpty or_).length = 0
  · have e1 : nl = W64 0 := hnl0.2 hz.1
    have e2 : nr = W64 0 := hnr0.2 hz.2
    subst e1 e2
    wp_auto
    iapply HΦ
    iframe
    have hzk : zipKeys ol or_ = [] := by
      unfold zipKeys
      rw [List.eq_nil_of_length_eq_zero hz.1, List.eq_nil_of_length_eq_zero hz.2]
      rfl
    rw [hzk]
    simp only [mapIterPost, ↓reduceIte]
    iexists []
    iframe
    ipureintro
    simp [mapIterDone]
  wp_join iprop(rhsLength_ptr ↦ nr) at next with [rhsLength] as rhsLength
  · wp_if_destruct
    · have : nr ≠ W64 0 := fun h => hz ⟨hnl0.1 rfl, hnr0.1 h⟩
      simp only [this, decide_false]
      wp_auto
      wp_join_done
    · try wp_auto
      wp_join_done
  wp_apply wp_slice_make3 (V := GoString) (W64 0) no
    (by have : sint.Z no = no.toInt := rfl; simp; omega) as %sl0 ⟨Hsl0, Hcap0, -⟩
  simp only [List.replicate_zero]
  try wp_auto
  ipersist lhs
  ipersist rhs
  ipersist a
  ipersist fn
  -- the left map's keys
  wp_join iprop(∃ (s : GoSlice) (d1 : List GoString), ordered_ptr ↦ s ∗ s ↦* d1 ∗
      ownSliceCap GoString s (DFrac.own 1) ∗ isAlloc (GoInterface.ok ia) ∗
      ⌜d1.Perm (kvKeys (kvsOrEmpty ol))⌝) at next with [ordered Hsl0 Hcap0 Ha]
      as ⟨%s1, %d1, ordered, Hs1, Hcap1, Ha, %Hd1⟩
  · rcases Hlc with ⟨rfl, rfl⟩ | ⟨kl, gml, rfl, rfl⟩
    · try wp_auto
      wp_join_done
      iexists _, []; iframe; ipureintro; simp [kvsOrEmpty, kvKeys]
    · iunfold isMapO at Hl
      wp_auto
      wp_func_lits
      wp_apply h_mapUnstructuredString_IterateUsing gml kl (GoInterface.ok ia) _
        (fun d => iprop(∃ s : GoSlice, ordered_ptr ↦ s ∗ s ↦* d ∗
          ownSliceCap GoString s (DFrac.own 1))) iprop(False) $$ [Ha ordered Hsl0 Hcap0]
        as %r1 ⟨Ha, Hr1⟩
      · iframe
        isplitr
        · iexact Hl
        iunfold iterUFnOk
        imodintro
        iintro %done %k %x %v %Hst %Φ' !> ⟨Ha, ⟨%s, ordered, Hs, Hcap⟩, Hv⟩ HΦ'
        simp only [← recv_eq_func_mk]
        wp_call
        wp_auto
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %nsl ⟨Hnsl, -⟩
        wp_auto
        wp_apply wp_slice_append $$ [$Hs $Hcap $Hnsl] as %s' ⟨Hs, Hcap, -⟩
        try wp_auto
        iapply HΦ'
        iframe
        simp only [↓reduceIte]
        iexists _
        iframe
      irevert Hr1
      cases r1
      · simp only [mapIterPost, Bool.false_eq_true, ↓reduceIte]
        iintro %h; cases h
      simp only [mapIterPost, ↓reduceIte, mapIterDone, Bool.false_eq_true]
      iintro ⟨%done1, %hd1, ⟨%s, ordered, Hs, Hcap⟩⟩
      try wp_auto
      wp_join_done
      iexists _, _; iframe; ipureintro; exact hd1
  -- the right map's keys not on the left
  wp_join iprop(∃ (s : GoSlice) (col : List GoString), ordered_ptr ↦ s ∗ s ↦* col ∗
      ownSliceCap GoString s (DFrac.own 1) ∗ isAlloc (GoInterface.ok ia) ∗
      ⌜col.Perm (zipKeys ol or_)⌝) at next with [ordered Hs1 Hcap1 Ha]
      as ⟨%s2, %col, ordered, Hs2, Hcap2, Ha, %Hcol⟩
  · rcases Hrc with ⟨rfl, rfl⟩ | ⟨kr, gmr, rfl, rfl⟩
    · try wp_auto
      wp_join_done
      iexists _, _; iframe; ipureintro
      have := ValuePure.zipKeys_perm_collect ol none hsl hsr d1 [] Hd1 (by simp [kvsOrEmpty, kvKeys])
      simpa using this
    · iunfold isMapO at Hr
      wp_auto
      wp_func_lits
      wp_apply h_mapUnstructuredString_IterateUsing gmr kr (GoInterface.ok ia) _
        (fun d => iprop(∃ s : GoSlice, ordered_ptr ↦ s ∗
          s ↦* (d1 ++ d.filter (fun k => !(lookupKV k (kvsOrEmpty ol)).isSome)) ∗
          ownSliceCap GoString s (DFrac.own 1))) iprop(False) $$ [Ha ordered Hs1 Hcap1]
        as %r2 ⟨Ha, Hr2⟩
      · iframe
        isplitr
        · iexact Hr
        isplitr
        · iunfold iterUFnOk
          imodintro
          iintro %done %k %x %v %Hst %Φ' !> ⟨Ha, ⟨%s, ordered, Hs, Hcap⟩, Hv⟩ HΦ'
          simp only [← recv_eq_func_mk]
          wp_call
          wp_auto
          -- whether the left map has the key
          wp_join iprop(∃ s : GoSlice, ordered_ptr ↦ s ∗
              s ↦* (d1 ++ (done ++ [k]).filter (fun k => !(lookupKV k (kvsOrEmpty ol)).isSome)) ∗
              ownSliceCap GoString s (DFrac.own 1)) at next with [ordered Hs Hcap key]
              as ⟨%s', ordered, Hs, Hcap⟩
          · rcases Hlc with ⟨rfl, rfl⟩ | ⟨kl, gml, rfl, rfl⟩
            · wp_auto
              wp_apply wp_slice_literal
              isplitr
              · ipureintro; rfl
              iintro %nsl ⟨Hnsl, -⟩
              wp_auto
              wp_apply wp_slice_append $$ [$Hs $Hcap $Hnsl] as %s'' ⟨Hs, Hcap, -⟩
              try wp_auto
              wp_join_done
              iexists _; iframe
              simp [kvsOrEmpty, lookupKV]
              iexact Hs
            · iunfold isMapO at Hl
              wp_auto
              wp_apply h_mapUnstructuredString_Has gml kl k as %h %hh
              · iexact Hl
              cases hlk : lookupKV k kl with
              | none =>
                simp only [hlk, Option.isSome_none] at hh
                subst hh
                wp_auto
                wp_apply wp_slice_literal
                isplitr
                · ipureintro; rfl
                iintro %nsl ⟨Hnsl, -⟩
                wp_auto
                wp_apply wp_slice_append $$ [$Hs $Hcap $Hnsl] as %s'' ⟨Hs, Hcap, -⟩
                try wp_auto
                wp_join_done
                iexists _; iframe
                simp [kvsOrEmpty, hlk]
                iexact Hs
              | some _ =>
                simp only [hlk, Option.isSome_some] at hh
                subst hh
                wp_auto
                wp_join_done
                iexists _; iframe
                simp [kvsOrEmpty, hlk]
                iexact Hs
          try wp_auto
          iapply HΦ'
          iframe
          simp only [↓reduceIte]
          iexists _
          iframe
        · simp only [List.filter_nil, List.append_nil]; iexact Hs1
      irevert Hr2
      cases r2
      · simp only [mapIterPost, Bool.false_eq_true, ↓reduceIte]
        iintro %h; cases h
      simp only [mapIterPost, ↓reduceIte, mapIterDone, Bool.false_eq_true]
      iintro ⟨%done2, %hd2, ⟨%s, ordered, Hs, Hcap⟩⟩
      try wp_auto
      wp_join_done
      iexists _, _; iframe; ipureintro
      exact ValuePure.zipKeys_perm_collect ol (some kr) hsl hsr d1 done2 Hd1 hd2
  -- sorted: the zip's keys
  have hzlen := ValuePure.zipKeys_length_le ol or_ hsl hsr
  wp_apply h_sort_Strings s2 col $$ [Hs2] as %zk ⟨Hs2, %Hzp, %Hzs⟩
  · iframe; ipureintro; rw [Hcol.length_eq]; omega
  have hzk : zk = zipKeys ol or_ :=
    ValuePure.eq_zipKeys_of_perm_sorted ol or_ hsl hsr zk (Hzp.symm.trans Hcol) Hzs
  subst hzk
  try wp_auto
  -- the loop over the sorted keys
  ihave %Hsl2 := ownSlice_len $$ Hs2
  ihave HInv : (∃ (j : w64) (kv : GoString), "i" ∷ i_ptr ↦ j ∗ "key" ∷ key_ptr ↦ kv ∗
      "Ha" ∷ isAlloc (GoInterface.ok ia) ∗ "HI" ∷ I ((zipKeys ol or_).take (sint.nat j)) ∗
      "Hs2" ∷ s2 ↦* zipKeys ol or_ ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z s2.len⌝ : IProp GF) $$ [i key Ha HI Hs2]
  · iexists (W64 0), _; iframe; ipureintro; refine ⟨by word, by word⟩
  wp_for HInv
  wp_if_destruct
  · -- an item: its key, both sides' values, the callback
    have hjn : sint.nat j < (zipKeys ol or_).length := by rw [Hsl2.1]; word
    list_elem (zipKeys ol or_) (sint.nat j) as k
    simp only [Hj.1, Hif, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index s2 (sint.Z j) _ _ k Hj.1 $$ [Hs2] as Hs2
    · iframe; ipureintro; exact Hk_lookup
    try wp_auto
    wp_join iprop(∃ v : value.Value, litem_ptr ↦ v ∗ optValF v (lookupKV k (kvsOrEmpty ol)) ∗
        isAlloc (GoInterface.ok ia) ∗ key_ptr ↦ k) at next with [litem Ha key]
        as ⟨%vl, litem, Hvl, Ha, key⟩
    · rcases Hlc with ⟨rfl, rfl⟩ | ⟨kl, gml, rfl, rfl⟩
      · try wp_auto
        wp_join_done
        iexists _; iframe; simp [kvsOrEmpty, lookupKV, optValF]
        try (ipureintro; trivial)
      · iunfold isMapO at Hl
        wp_auto
        wp_apply h_mapUnstructuredString_GetUsing gml kl (GoInterface.ok ia) k $$ [Ha]
          as %v %okb ⟨Ha, -, Hv⟩
        · iframe; iexact Hl
        try wp_auto
        wp_join_done
        iexists _; iframe
        simp only [kvsOrEmpty, Option.getD]; iexact Hv
    wp_join iprop(∃ v : value.Value, ritem_ptr ↦ v ∗ optValF v (lookupKV k (kvsOrEmpty or_)) ∗
        isAlloc (GoInterface.ok ia) ∗ key_ptr ↦ k) at next with [ritem Ha key]
        as ⟨%vr, ritem, Hvr, Ha, key⟩
    · rcases Hrc with ⟨rfl, rfl⟩ | ⟨kr, gmr, rfl, rfl⟩
      · try wp_auto
        wp_join_done
        iexists _; iframe; simp [kvsOrEmpty, lookupKV, optValF]
        try (ipureintro; trivial)
      · iunfold isMapO at Hr
        wp_auto
        wp_apply h_mapUnstructuredString_GetUsing gmr kr (GoInterface.ok ia) k $$ [Ha]
          as %v %okb ⟨Ha, -, Hv⟩
        · iframe; iexact Hr
        try wp_auto
        wp_join_done
        iexists _; iframe
        simp only [kvsOrEmpty, Option.getD]; iexact Hv
    have hstep : mapIterStep true (zipKeys ol or_) ((zipKeys ol or_).take (sint.nat j)) k := by
      simp only [mapIterStep, ↓reduceIte]
      have := ValuePure.take_append_getElem_prefix (zipKeys ol or_) (sint.nat j) hjn
      rwa [show (zipKeys ol or_)[sint.nat j] = k from
        (List.getElem?_eq_some_iff.1 Hk_lookup).2] at this
    iunfold zipFnOk at Hfn
    wp_apply Hfn $$ %_ %k %vl %vr %hstep [Ha HI Hvl Hvr] as %b ⟨Ha, Hvl, Hvr, Hb⟩
    · iframe
    try wp_auto
    wp_join iprop(isAlloc (GoInterface.ok ia)) at next with [Ha Hvl litem] as Ha
    · cases hlk : lookupKV k (kvsOrEmpty ol) with
      | none =>
        irevert Hvl; simp only [optValF]; iintro %hv; subst hv
        try wp_auto
        wp_join_done
      | some x =>
        irevert Hvl; simp only [optValF]; iintro Hv
        ihave ⟨Hv, %hsh⟩ := isValF_shape _ _ _ $$ Hv
        obtain ⟨p, rfl⟩ := hsh
        wp_auto
        ihave Hfr := isValF_freeable_law_holds _ _ $$ Hv
        wp_apply HFree $$ %_ [Ha Hfr] as Ha
        · iframe
        try wp_auto
        wp_join_done
    wp_join iprop(isAlloc (GoInterface.ok ia)) at next with [Ha Hvr ritem] as Ha
    · cases hlk : lookupKV k (kvsOrEmpty or_) with
      | none =>
        irevert Hvr; simp only [optValF]; iintro %hv; subst hv
        try wp_auto
        wp_join_done
      | some x =>
        irevert Hvr; simp only [optValF]; iintro Hv
        ihave ⟨Hv, %hsh⟩ := isValF_shape _ _ _ $$ Hv
        obtain ⟨p, rfl⟩ := hsh
        wp_auto
        ihave Hfr := isValF_freeable_law_holds _ _ $$ Hv
        wp_apply HFree $$ %_ [Ha Hfr] as Ha
        · iframe
        try wp_auto
        wp_join_done
    cases b
    · wp_auto
      wp_for_post
      iapply HΦ
      iframe
      simp only [mapIterPost, Bool.false_eq_true, ↓reduceIte]
      iexact Hb
    · try wp_auto
      wp_for_post
      iframe
      iexists j + 1, k
      simp only [↓reduceIte]
      have e : sint.nat (j + 1) = sint.nat j + 1 := by word
      rw [e, ← List.take_append_getElem hjn,
        show (zipKeys ol or_)[sint.nat j] = k from (List.getElem?_eq_some_iff.1 Hk_lookup).2]
      iframe
      ipureintro; constructor <;> word
  · -- the end
    iapply HΦ
    iframe
    simp only [mapIterPost, ↓reduceIte, mapIterDone]
    iexists _
    iframe
    ipureintro
    apply List.take_of_length_le
    rw [Hsl2.1]; word

end proof

end smd
end EtcdGrove
end Perennial
