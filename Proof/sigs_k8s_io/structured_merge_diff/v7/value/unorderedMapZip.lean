/-
`value.unorderedMapZip`: proved (Prove step, notes/smd-plan.md): the left map's iteration (each
key's right value got and freed by a `defer`), then the right map's keys the left lacks. Its callees' specs (and the interface bundles' laws, `Objects.lean`) are its
hypotheses. Lean-first (2026-11-19), Draft.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.unorderedMapZip
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.heapAllocator__Free
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.freelistAllocator__Free
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.mapUnstructuredString__Empty
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.mapUnstructuredString__GetUsing
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.mapUnstructuredString__Has
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.mapUnstructuredString__IterateUsing
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.LawProofs
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.LawProofsDispatch

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7

/-- The keys an unordered zip visits: the left map's, then the right map's the left lacks. -/
theorem unorderedZip_perm (ol or_ : Option (List (GoString × UVal)))
    (hl : keysSorted (kvsOrEmpty ol) = true) (hr : keysSorted (kvsOrEmpty or_) = true)
    (d1 d2 : List GoString) (h1 : d1.Perm (kvKeys (kvsOrEmpty ol)))
    (h2 : d2.Perm (kvKeys (kvsOrEmpty or_))) :
    (d1 ++ d2.filter (fun k => !(lookupKV k (kvsOrEmpty ol)).isSome)).Perm (zipKeys ol or_) := by
  have hn1 : d1.Nodup := h1.nodup_iff.2 (ValuePure.keysSorted_nodup _ hl)
  have hn2 : d2.Nodup := h2.nodup_iff.2 (ValuePure.keysSorted_nodup _ hr)
  apply ValuePure.perm_of_nodup_mem
  · rw [List.nodup_append]
    refine ⟨hn1, hn2.filter _, ?_⟩
    intro a ha b hb hab
    subst hab
    have ha' := (ValuePure.lookupKV_isSome_iff a _).2 (h1.mem_iff.1 ha)
    simp [ha'] at hb
    rw [hb.2] at ha'; cases ha'
  · apply zipKeys_nodup_law_holds
    · intro kvs h; subst h; exact hl
    · intro kvs h; subst h; exact hr
  · intro a
    rw [zipKeys_mem_law_holds, List.mem_append, List.mem_filter, h1.mem_iff, h2.mem_iff,
      ← ValuePure.lookupKV_isSome_iff, ← ValuePure.lookupKV_isSome_iff]
    by_cases h : (lookupKV a (kvsOrEmpty ol)).isSome <;> simp [h]

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : value.Assumptions]

theorem value.unorderedMapZip.wp_proof
    (h_heapAllocator_Free : value.heapAllocator.Free.spec (GF := GF))
    (h_freelistAllocator_Free : value.freelistAllocator.Free.spec (GF := GF))
    (h_mapUnstructuredString_Empty : value.mapUnstructuredString.Empty.spec (GF := GF))
    (h_mapUnstructuredString_GetUsing : value.mapUnstructuredString.GetUsing.spec (GF := GF))
    (h_mapUnstructuredString_Has : value.mapUnstructuredString.Has.spec (GF := GF))
    (h_mapUnstructuredString_IterateUsing : value.mapUnstructuredString.IterateUsing.spec (GF := GF)) :
    value.unorderedMapZip.spec (GF := GF) := fun al lm rm ol or_ fn I Q => by
  wp_start as ⟨Ha, Hl, Hr, #Hfn, HI⟩
  ihave %Hlc := isMapO_cases $$ Hl
  ihave %Hrc := isMapO_cases $$ Hr
  ihave ⟨Ha, %ia, %Hia, #HFree⟩ := isAlloc_Free h_heapAllocator_Free h_freelistAllocator_Free al $$ [Ha]
  · iframe; iexact Hpkg
  subst Hia
  rcases Hlc with ⟨rfl, rfl⟩ | ⟨kl, gml, rfl, rfl⟩ <;>
    rcases Hrc with ⟨rfl, rfl⟩ | ⟨kr, gmr, rfl, rfl⟩
  rotate_left 3
  · iunfold isMapO at Hl Hr
    ihave #Hl := Hl
    ihave #Hr := Hr
    ihave %hsl := isMapV_sorted_law_holds _ _ $$ Hl
    ihave %hsr := isMapV_sorted_law_holds _ _ $$ Hr
    wp_auto
    wp_apply h_mapUnstructuredString_Empty gml kl as %e1 %he1
    · iexact Hl
    wp_if_destruct
    rotate_left
    wp_apply h_mapUnstructuredString_Empty gmr kr as %e2 %he2
    · iexact Hr
    wp_if_destruct
    rotate_left
    · iapply HΦ
      iframe
      have h1 : kl = [] := he1.1 rfl
      have h2 : kr = [] := he2.1 rfl
      subst h1 h2
      simp only [mapIterPost, ↓reduceIte]
      iexists []
      iframe
      ipureintro
      simp [mapIterDone]
      rfl
    all_goals
      ipersist fn
      ipersist rhs
      ipersist lhs
      ipersist a
      wp_func_lits
      wp_apply h_mapUnstructuredString_IterateUsing gml kl (GoInterface.ok ia) _ I Q $$ [Ha HI] as %r1 ⟨Ha, Hr1⟩
      · iframe
        isplitr
        · iexact Hl
        iunfold iterUFnOk
        imodintro
        iintro %done %k %x %v %Hst %Φ' !> ⟨Ha, HI, Hv⟩ HΦ'
        simp only [← recv_eq_func_mk]
        wp_call
        wp_auto
        wp_apply wp_with_defer as %defer defer
        wp_apply h_mapUnstructuredString_GetUsing gmr kr (GoInterface.ok ia) k $$ [Ha] as %rv %ok ⟨Ha, %hok, Hrv⟩
        · iframe; iexact Hr
        have hstep : mapIterStep false (zipKeys (some kl) (some kr)) done k := by
          simp only [mapIterStep, Bool.false_eq_true, ↓reduceIte] at Hst ⊢
          refine ⟨?_, Hst.2.2⟩
          rw [zipKeys_mem_law_holds]
          left; simp [kvsOrEmpty, Hst.1]
        have hx : lookupKV k (kvsOrEmpty (some kl)) = some x := Hst.1
        cases hlk : lookupKV k kr with
        | none =>
          simp only [hlk, Option.isSome_none] at hok
          subst hok
          iclear Hrv
          wp_auto
          iunfold zipFnOk at Hfn
          wp_apply Hfn $$ %done %k %v %GoInterface.nil %hstep [Ha HI Hv] as %b ⟨Ha, Hv, -, Hb⟩
          · rw [hx]
            simp only [kvsOrEmpty, Option.getD, hlk, optValF]
            iframe
          irevert Hv
          rw [hx]
          simp only [optValF]
          iintro Hv
          iapply HΦ'
          iframe
        | some y =>
          simp only [hlk, Option.isSome_some] at hok
          subst hok
          irevert Hrv
          simp only [optValF]
          iintro Hrv
          wp_auto
          iunfold zipFnOk at Hfn
          wp_apply Hfn $$ %done %k %v %rv %hstep [Ha HI Hv Hrv] as %b ⟨Ha, Hv, Hrv, Hb⟩
          · rw [hx]
            simp only [kvsOrEmpty, Option.getD, hlk, optValF]
            iframe
          irevert Hv Hrv
          rw [hx]
          simp only [kvsOrEmpty, Option.getD, hlk, optValF]
          iintro Hv Hrv
          ihave Hfr := isValF_freeable_law_holds _ _ $$ Hrv
          wp_apply HFree $$ %rv [Ha Hfr] as Ha
          · iframe
          iapply HΦ'
          iframe
      irevert Hr1
      cases r1
      · simp only [mapIterPost, Bool.false_eq_true, ↓reduceIte]
        iintro HQ
        wp_auto
        iapply HΦ
        iframe
        simp only [mapIterPost, Bool.false_eq_true, ↓reduceIte]
        iexact HQ
      simp only [mapIterPost, ↓reduceIte]
      iintro Hr1
      icases Hr1 with ⟨%done1, %hd1, HI⟩
      simp only [mapIterDone, Bool.false_eq_true, ↓reduceIte] at hd1
      wp_auto
      wp_func_lits
      wp_apply h_mapUnstructuredString_IterateUsing gmr kr (GoInterface.ok ia) _
        (fun d2 => I (done1 ++ d2.filter (fun k => !(lookupKV k kl).isSome))) Q $$ [Ha HI] as %r2 ⟨Ha, Hr2⟩
      · iframe
        isplitr
        · iexact Hr
        isplitr
        · iunfold iterUFnOk
          imodintro
          iintro %done %k %x %v %Hst %Φ' !> ⟨Ha, HI, Hv⟩ HΦ'
          simp only [← recv_eq_func_mk]
          wp_call
          wp_auto
          wp_apply h_mapUnstructuredString_Has gml kl k as %h %hh
          · iexact Hl
          simp only [mapIterStep, Bool.false_eq_true, ↓reduceIte] at Hst
          have hxr : lookupKV k (kvsOrEmpty (some kr)) = some x := Hst.1
          cases hl : lookupKV k kl with
          | some _ =>
            simp only [hl, Option.isSome_some] at hh
            subst hh
            wp_auto
            iapply HΦ'
            iframe
            simp only [↓reduceIte, List.filter_append, List.filter_cons, List.filter_nil, hl,
              Option.isSome_some, Bool.not_true, Bool.false_eq_true, List.append_nil]
            iexact HI
          | none =>
            simp only [hl, Option.isSome_none] at hh
            subst hh
            have hstep : mapIterStep false (zipKeys (some kl) (some kr))
                (done1 ++ List.filter (fun k => !(lookupKV k kl).isSome) done) k := by
              simp only [mapIterStep, Bool.false_eq_true, ↓reduceIte]
              refine ⟨?_, ?_⟩
              · rw [zipKeys_mem_law_holds]
                right; simp [kvsOrEmpty, Hst.1]
              · simp only [List.mem_append, List.mem_filter, not_or, not_and]
                refine ⟨?_, fun h _ => Hst.2.2 h⟩
                intro hm
                have := (ValuePure.lookupKV_isSome_iff k kl).2 (hd1.mem_iff.1 hm)
                rw [hl] at this; cases this
            wp_auto
            iunfold zipFnOk at Hfn
            wp_apply Hfn $$ %_ %k %GoInterface.nil %v %hstep [Ha HI Hv] as %b ⟨Ha, -, Hv, Hb⟩
            · rw [hxr]
              simp only [kvsOrEmpty, Option.getD, hl, optValF]
              iframe
            irevert Hv
            rw [hxr]
            simp only [optValF]
            iintro Hv
            iapply HΦ'
            iframe
            simp only [List.filter_append, List.filter_cons, List.filter_nil, hl,
              Option.isSome_none, Bool.not_false, ↓reduceIte, List.append_assoc]
            iexact Hb
        · simp only [List.filter_nil, List.append_nil]
          iexact HI
      iapply HΦ
      iframe
      irevert Hr2
      cases r2
      · simp only [mapIterPost, Bool.false_eq_true, ↓reduceIte]
        iintro HQ; iexact HQ
      simp only [mapIterPost, ↓reduceIte, mapIterDone, Bool.false_eq_true]
      iintro ⟨%done2, %hd2, HI⟩
      iexists _
      iframe
      ipureintro
      exact unorderedZip_perm (some kl) (some kr) hsl hsr done1 done2 hd1 hd2
  · -- both nil
    wp_auto
    iapply HΦ
    iframe
    rw [ValuePure.zipKeys_none_none]
    simp only [mapIterPost, ↓reduceIte]
    iexists []
    iframe
    ipureintro
    simp [mapIterDone]
  · -- left nil
    iunfold isMapO at Hl Hr
    ihave #Hr := Hr
    ihave %hsr := isMapV_sorted_law_holds _ _ $$ Hr
    wp_auto
    wp_apply h_mapUnstructuredString_Empty gmr kr as %e2 %he2
    · iexact Hr
    wp_if_destruct
    rotate_left
    · iapply HΦ
      iframe
      have h2 : kr = [] := he2.1 rfl
      subst h2
      simp only [mapIterPost, ↓reduceIte]
      iexists []
      iframe
      ipureintro
      simp [mapIterDone]
      rfl
    ipersist fn
    ipersist lhs
    wp_func_lits
    wp_apply h_mapUnstructuredString_IterateUsing gmr kr (GoInterface.ok ia) _ I Q $$ [Ha HI] as %r2 ⟨Ha, Hr2⟩
    · iframe
      isplitr
      · iexact Hr
      iunfold iterUFnOk
      imodintro
      iintro %done %k %x %v %Hst %Φ' !> ⟨Ha, HI, Hv⟩ HΦ'
      simp only [← recv_eq_func_mk]
      wp_call
      wp_auto
      simp only [mapIterStep, Bool.false_eq_true, ↓reduceIte] at Hst
      have hxr : lookupKV k (kvsOrEmpty (some kr)) = some x := Hst.1
      have hstep : mapIterStep false (zipKeys none (some kr)) done k := by
        simp only [mapIterStep, Bool.false_eq_true, ↓reduceIte]
        refine ⟨?_, Hst.2.2⟩
        rw [zipKeys_mem_law_holds]
        right; simp [kvsOrEmpty, Hst.1]
      iunfold zipFnOk at Hfn
      wp_apply Hfn $$ %_ %k %GoInterface.nil %v %hstep [Ha HI Hv] as %b ⟨Ha, -, Hv, Hb⟩
      · rw [hxr]
        simp only [kvsOrEmpty, Option.getD, lookupKV, optValF]
        iframe
      irevert Hv
      rw [hxr]
      simp only [optValF]
      iintro Hv
      iapply HΦ'
      iframe
    iapply HΦ
    iframe
    irevert Hr2
    cases r2
    · simp only [mapIterPost, Bool.false_eq_true, ↓reduceIte]
      iintro HQ; iexact HQ
    simp only [mapIterPost, ↓reduceIte, mapIterDone, Bool.false_eq_true]
    iintro ⟨%done2, %hd2, HI⟩
    iexists _
    iframe
    ipureintro
    have := unorderedZip_perm none (some kr) rfl hsr [] done2 (by simp [kvsOrEmpty, kvKeys]) hd2
    rwa [show List.filter (fun k => !(lookupKV k (kvsOrEmpty (none : Option (List (GoString × UVal))))).isSome) done2 = done2 from List.filter_eq_self.2 (by simp [kvsOrEmpty, lookupKV]), List.nil_append] at this
  · -- right nil
    iunfold isMapO at Hl Hr
    ihave #Hl := Hl
    ihave %hsl := isMapV_sorted_law_holds _ _ $$ Hl
    wp_auto
    wp_apply h_mapUnstructuredString_Empty gml kl as %e1 %he1
    · iexact Hl
    wp_if_destruct
    rotate_left
    · iapply HΦ
      iframe
      have h1 : kl = [] := he1.1 rfl
      subst h1
      simp only [mapIterPost, ↓reduceIte]
      iexists []
      iframe
      ipureintro
      simp [mapIterDone]
      rfl
    ipersist fn
    ipersist rhs
    ipersist a
    wp_func_lits
    wp_apply h_mapUnstructuredString_IterateUsing gml kl (GoInterface.ok ia) _ I Q $$ [Ha HI] as %r1 ⟨Ha, Hr1⟩
    · iframe
      isplitr
      · iexact Hl
      iunfold iterUFnOk
      imodintro
      iintro %done %k %x %v %Hst %Φ' !> ⟨Ha, HI, Hv⟩ HΦ'
      simp only [← recv_eq_func_mk]
      wp_call
      wp_auto
      wp_apply wp_with_defer as %defer defer
      simp only [mapIterStep, Bool.false_eq_true, ↓reduceIte] at Hst
      have hx : lookupKV k (kvsOrEmpty (some kl)) = some x := Hst.1
      have hstep : mapIterStep false (zipKeys (some kl) none) done k := by
        simp only [mapIterStep, Bool.false_eq_true, ↓reduceIte]
        refine ⟨?_, Hst.2.2⟩
        rw [zipKeys_mem_law_holds]
        left; simp [kvsOrEmpty, Hst.1]
      iunfold zipFnOk at Hfn
      wp_apply Hfn $$ %done %k %v %GoInterface.nil %hstep [Ha HI Hv] as %b ⟨Ha, Hv, -, Hb⟩
      · rw [hx]
        simp only [kvsOrEmpty, Option.getD, lookupKV, optValF]
        iframe
      irevert Hv
      rw [hx]
      simp only [optValF]
      iintro Hv
      iapply HΦ'
      iframe
    irevert Hr1
    cases r1
    · simp only [mapIterPost, Bool.false_eq_true, ↓reduceIte]
      iintro HQ
      wp_auto
      iapply HΦ
      iframe
      simp only [mapIterPost, Bool.false_eq_true, ↓reduceIte]
      iexact HQ
    simp only [mapIterPost, ↓reduceIte, mapIterDone, Bool.false_eq_true]
    iintro ⟨%done1, %hd1, HI⟩
    wp_auto
    iapply HΦ
    iframe
    simp only [mapIterPost, ↓reduceIte, mapIterDone]
    iexists _
    iframe
    ipureintro
    have := unorderedZip_perm (some kl) none hsl rfl done1 [] hd1 (by simp [kvsOrEmpty, kvKeys])
    simpa using this

end proof

end smd
end EtcdGrove
end Perennial
