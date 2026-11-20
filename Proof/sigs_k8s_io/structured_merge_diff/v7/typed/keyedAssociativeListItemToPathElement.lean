/-
`typed.keyedAssociativeListItemToPathElement`: proved. `FieldList.Sort`'s premise that the key field
list has at most `2^62` fields: the list type's key count is bounded by `Atom.wf`
(`LawA3.list_wf_len`), the fields a sublist of the keys. The keys
looked up (`Get`; an absent key's default is nil), the `FieldList` sorted (`mergeSort` = `keyOf`'s
`flSort`, `LawA3.sort_pairs`), the `PathElement{Key: &keyMap}` (`LawA3.isPE_key_intro`).

Callees without a spec file here (other packages', the standard library's, or the
walker's own interface calls through a bundle): `errors.New`, `fmt.Errorf`.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.keyedAssociativeListItemToPathElement
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.heapAllocator__Free
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.freelistAllocator__Free
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.mapUnstructuredString__Get
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__AsMapUsing_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__IsMap_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__IsNull_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.getAssociativeKeyDefault
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.FieldList__Sort
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.NewValueInterface
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsA3
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsA2
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsAPure
public import Proof.sigs_k8s_io.structured_merge_diff.v7.schema.LawProofs
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.LawProofsDispatch

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : typed.Assumptions]

theorem typed.keyedAssociativeListItemToPathElement.wp_proof
    (h_heapAllocator_Free : value.heapAllocator.Free.spec (GF := GF))
    (h_freelistAllocator_Free : value.freelistAllocator.Free.spec (GF := GF))
    (h_mapUnstructuredString_Get : value.mapUnstructuredString.Get.spec (GF := GF))
    (h_valueUnstructured_AsMapUsing_ptr : value.valueUnstructured.AsMapUsing_ptr.spec (GF := GF))
    (h_valueUnstructured_IsMap_ptr : value.valueUnstructured.IsMap_ptr.spec (GF := GF))
    (h_valueUnstructured_IsNull_ptr : value.valueUnstructured.IsNull_ptr.spec (GF := GF))
    (h_getAssociativeKeyDefault : typed.getAssociativeKeyDefault.spec (GF := GF))
    (h_FieldList_Sort : value.FieldList.Sort.spec (GF := GF))
    (h_NewValueInterface : value.NewValueInterface.spec (GF := GF)) :
    typed.keyedAssociativeListItemToPathElement.spec (GF := GF) :=
    fun a sc S lp e rel ks fs el r child dq x tn => by
  wp_start as ⟨Ha, #Hsc, #Hl, Hv, %Hpre⟩
  obtain ⟨Hwf, hrel, Hne, Hfe, Hft, Hc, Hk⟩ := Hpre
  subst hrel
  obtain ⟨-, hksnd, fs', em', rel', hfe', hkf⟩ := LawB.list_wf S Hwf ({ name := tn } : TypeRef) e .associative ks Hft (by decide)
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 Hk
  obtain ⟨kvs, rfl⟩ := LawB.keyOf_map ks x k hk
  icases isListRep_elim_law_holds lp e .associative ks $$ Hl with ⟨%lv, %ksl, #Hlv, %Hlv', #Hks, -⟩
  ihave %Hkl := ownSlice_len _ _ _ $$ Hks
  ihave ⟨Hlv2, %Hnn⟩ := typedPointsto_not_null_dup _ _ _ $$ Hlv
  iStructNamed Hlv2
  ihave ⟨Hv, %hsh⟩ := LawA3.isValF_shape _ _ _ $$ Hv
  obtain ⟨p, rfl⟩ := hsh
  ihave ⟨Ha, %ia, %Hia, #Hfree⟩ := isAlloc_Free h_heapAllocator_Free h_freelistAllocator_Free a $$ [Ha]
  · iframe Ha; iPkgInit
  subst Hia
  wp_auto
  wp_bind (App (Val wrapDefer) _)
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  wp_apply h_valueUnstructured_IsNull_ptr p dq _ $$ [Hv] as %r1 ⟨Hv, %hr1⟩
  · iframe
  subst hr1
  simp only [UVal.isNullB]
  wp_auto
  wp_apply h_valueUnstructured_IsMap_ptr p dq _ $$ [Hv] as %r2 ⟨Hv, %hr2⟩
  · iframe
  subst hr2
  simp only [UVal.isMapB]
  wp_auto
  wp_apply (wp_slice_literal (V := value.Field) [])
  isplitr
  · ipureintro; rfl
  iintro %sl0 ⟨Hsl0, Hcap0⟩
  wp_auto
  wp_apply h_valueUnstructured_AsMapUsing_ptr p dq kvs _ $$ [Hv] as %mv ⟨Hv, Hmv⟩
  · iframe
  ihave %Hmc := isMapV_concrete_law_holds mv kvs $$ Hmv
  obtain ⟨gm, rfl⟩ := Hmc
  ihave ⟨Hmv, Hfm⟩ := freeable_view_law_holds.1 _ kvs $$ Hmv
  ihave #Hmv := isMapV_persistent_law_holds _ kvs $$ Hmv
  have hks0 := Hkl
  let pref : Nat → FieldList := fun j =>
    (ks.take j).filterMap (fun k => (lookupKV k kvs).map (fun v => (k, v)))
  ihave HI : (∃ (j : w64) (fn : GoString) (sl : GoSlice) (fls : List value.Field),
      "i" ∷ i_ptr ↦ j ∗ "fieldName" ∷ fieldName_ptr ↦ fn ∗
      "keyMap" ∷ keyMap_ptr ↦ sl ∗ "Hsl" ∷ sl ↦* fls ∗ "Hcap" ∷ ownSliceCap value.Field sl (DFrac.own 1) ∗
      "%Hfl" ∷ ⌜fls.length = (pref (sint.nat j)).length⌝ ∗
      "%Hnm" ∷ ⌜fls.map (·.Name') = (pref (sint.nat j)).map (·.1)⌝ ∗
      "#Hfv" ∷ □ (∀ q : value.Field × (GoString × UVal), ⌜q ∈ fls.zip (pref (sint.nat j))⌝ -∗
        ⌜q.1.Name' = q.2.1⌝ ∗ isVal q.1.Value' q.2.2) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ ks.length⌝ : IProp GF)
    $$ [i fieldName keyMap Hsl0 Hcap0]
  · iexists _, _, _, []
    iframe
    isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; rfl
    isplitr
    · imodintro; iintro %q %hq; simp at hq
    ipureintro; constructor <;> word
  wp_for HI
  have hkl' : sint.Z lv.Keys'.len = ks.length := by rw [Hlv'.2]; have := Hkl; word
  by_cases hlt0 : sint.Z j < sint.Z lv.Keys'.len
  · rw [if_pos (by simp [hlt0])]
    have hlt : sint.Z j < ks.length := by rw [← hkl']; exact hlt0
    have hjl : sint.nat j < ks.length := by have := Hj.1; word
    obtain ⟨kn, hkn⟩ : ∃ kn, ks[sint.nat j]? = some kn := ⟨_, List.getElem?_eq_getElem hjl⟩
    wp_auto
    rw [if_pos ⟨Hj.1, hlt0⟩, Hlv'.2]
    wp_apply (wp_load_slice_index ksl (sint.Z j) ks DFrac.discard kn Hj.1) $$ [Hks]
    · iframe #; ipureintro; exact hkn
    iintro -
    wp_auto
    have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by
      have : sint.Z j < 2 ^ 63 - 1 := by have := Hkl; word
      word
    have hpref : pref (sint.nat j + 1) = pref (sint.nat j) ++
        ((lookupKV kn kvs).map (fun v => (kn, v))).toList := by
      simp only [pref]
      rw [List.take_add_one, hkn, List.filterMap_append]
      cases h : lookupKV kn kvs <;> simp [h]
    wp_apply h_mapUnstructuredString_Get gm kvs kn $$ [] as %vv %ok ⟨%hok, Hvv⟩
    · iframe #
    cases hlk : lookupKV kn kvs with
    | some xv =>
      rw [hlk] at hok hpref; simp only [Option.isSome_some] at hok; subst hok
      irevert Hvv; simp only [hlk, optValF]; iintro Hvv
      imod isValF_persist_law_holds _ _ _ $$ Hvv with #Hvv
      wp_auto
      wp_apply (wp_slice_literal (V := value.Field) [value.Field.mk kn vv])
      isplitr
      · ipureintro; rfl
      iintro %sl1 ⟨Hsl1, -⟩
      wp_auto
      wp_apply (wp_slice_append (V := value.Field) sl fls _ [value.Field.mk kn vv] (DFrac.own 1))
        $$ [Hsl Hcap Hsl1] as %sl2 ⟨Hsl2, Hcap2, -⟩
      · iframe
      try wp_auto
      wp_for_post
      iframe
      iexists (j + W64 1), kn, sl2, (fls ++ [value.Field.mk kn vv])
      iframe
      isplitr
      · ipureintro; rw [hj1, hpref]; simp [Hfl]
      isplitr
      · ipureintro; rw [hj1, hpref]; simp [Hnm]
      isplitr
      · imodintro
        iintro %q %hq
        rw [hj1, hpref] at hq
        simp only [Option.map_some, Option.toList_some] at hq
        rw [List.zip_append Hfl] at hq
        rcases List.mem_append.1 hq with hq | hq
        · iapply Hfv; ipureintro; exact hq
        · simp at hq; subst hq; iframe #; ipureintro; rfl
      ipureintro; constructor <;> word
    | none =>
      rw [hlk] at hok hpref; simp only [Option.isSome_none] at hok; subst hok
      simp only [Option.map_none, Option.toList_none, List.append_nil] at hpref
      wp_auto
      wp_apply h_getAssociativeKeyDefault sc S lp e .associative ks fs el r kn $$ []
      · iframe #; ipureintro; exact ⟨Hwf, Hfe⟩
      try wp_auto
      wp_for_post
      iframe
      iexists (j + W64 1), kn, sl, fls
      iframe
      rw [hj1, hpref]
      iframe #
      ipureintro; refine ⟨Hfl, Hnm, ?_, ?_⟩ <;> word
  · rw [if_neg (by simp [hlt0])]
    have hjk : sint.nat j = ks.length := by have := Hj.2; rw [hkl'] at hlt0; word
    have hpk : pref (sint.nat j) = ks.filterMap (fun k => (lookupKV k kvs).map (fun v => (k, v))) := by
      simp only [pref, hjk, List.take_length]
    rw [hpk] at Hfl Hnm; rw [hpk]
    have hfl0 : ks.filterMap (fun k => (lookupKV k kvs).map (fun v => (k, v))) ≠ [] := by
      intro h; simp only [keyOf, h, ↓reduceIte] at hk; cases hk
    ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
    rw [if_neg (by simpa using hlt0)]
    wp_auto
    have hpos : decide (sint.Z (W64 0) < sint.Z lv.Keys'.len) = true := by
      have : ks.length ≠ 0 := by simpa using Hne
      simp only [decide_eq_true_eq]; rw [hkl']; have h0 : sint.Z (W64 0) = 0 := rfl; omega
    rw [hpos]
    wp_auto
    have hlen0 : sl.len ≠ W64 0 := by
      intro h; rw [h] at Hsll; apply hfl0; apply List.eq_nil_of_length_eq_zero; rw [← Hfl, Hsll.1]; rfl
    rw [decide_eq_false hlen0]
    wp_auto
    have hnd : (fls.map (·.Name')).Nodup := by
      rw [Hnm]; exact hksnd.sublist (LawA3.keyNames_sublist ks kvs)
    have hbound : ks.length ≤ 2 ^ 62 := by
      exact LawA3.list_wf_len S Hwf _ e ks Hft
    have hflen : fls.length ≤ 2 ^ 62 := by
      rw [Hfl]; exact Nat.le_trans (List.length_filterMap_le _ _) hbound
    rw [method_unfold (t := go.GoType.PointerType value.FieldList.ty) (m := go!"Sort") #keyMap_ptr]
    wp_auto
    wp_apply h_FieldList_Sort sl fls $$ [Hsl] as Hsl
    · iframe; ipureintro; exact ⟨hnd, hflen⟩
    imod ownSlice_persist _ _ _ $$ Hsl with #Hsl
    try wp_auto
    ipersist keyMap
    wp_apply Hfree $$ %_ [Ha Hfm] as Ha
    · iframe
    try wp_auto
    -- the key: the item's key fields, sorted
    obtain ⟨fl, hfldef⟩ : ∃ fl, fl = ks.filterMap (fun k => (lookupKV k kvs).map (fun v => (k, v))) :=
      ⟨_, rfl⟩
    rw [← hfldef] at Hfl Hnm hfl0
    rw [← hfldef]
    have hkk : k = .key (flSort fl) := by
      simp only [keyOf] at hk; rw [← hfldef] at hk; simp only [hfl0, ↓reduceIte] at hk
      exact (Option.some.inj hk).symm
    subst hkk
    have hfeq := hfe'.symm.trans Hfe
    simp only [Option.some.injEq, Atom.map.injEq] at hfeq
    obtain ⟨rfl, rfl, rfl⟩ := hfeq
    have hlens : ∀ f ∈ flSort fl, f.2.mapLensOk = true := by
      intro f hf
      have hf' := (LawB.flSort_perm fl).mem_iff.1 hf
      obtain ⟨kf, vf⟩ := f
      rw [hfldef, LawB.mem_keyFields] at hf'
      obtain ⟨hkin, hlk⟩ := hf'
      have hkfo := hkf kf hkin
      simp only [keyFieldOk] at hkfo
      split at hkfo
      · rename_i kt hkt
        split at hkfo
        · rename_i sc' hsc
          obtain ⟨t', ht', hct⟩ := conforms_entry_law_holds S e _ _ _ kvs Hfe Hc kf vf
            (LawA2.lookupKV_mem kf vf kvs hlk)
          simp only [fieldType, hkt] at ht'
          cases ht'
          exact LawA3.keyVal_mapLensOk S kt vf sc' hsc hct
        · cases hkfo
      · cases hkfo
    have hz1 : (fls.zip fl).map (·.1) = fls := List.map_fst_zip (by omega)
    have hz2 : (fls.zip fl).map (·.2) = fl := List.map_snd_zip (by omega)
    have hname := LawA3.zip_names (fun f : value.Field => f.Name') (fun p : GoString × UVal => p.1) fls fl Hnm
    have hnd2 : ((fls.zip fl).map (·.2.1)).Nodup := by
      have : (fls.zip fl).map (·.2.1) = fl.map (·.1) := by
        rw [show (fun x : value.Field × (GoString × UVal) => x.2.1) = (fun p => p.1) ∘ (fun x => x.2)
          from rfl, ← List.map_map, hz2]
      rw [this, hfldef]; exact hksnd.sublist (LawA3.keyNames_sublist ks kvs)
    obtain ⟨P', hperm, hfs, hfl'⟩ := LawA3.sort_pairs (fls.zip fl) hname hnd2
    rw [hz1] at hfs
    rw [hz2] at hfl'
    iapply HΦ
    iframe
    rw [hk]
    isplitr
    · ipureintro; rfl
    iapply LawA3.isPE_key_intro _ sl (flSort fl) rfl (List.all_eq_true.2 hlens)
    iframe #
    rw [hfs]
    iapply isFieldList_intro_law_holds sl (P'.map (·.1)) (flSort fl) (by rw [hfl']; simp)
    · iexact Hsl
    rw [hfl', LawA3.zip_map_fst_snd]
    iapply LawA3.sepL_of_forall
    imodintro
    iintro %q %hq
    iapply Hfv
    ipureintro; exact hperm.mem_iff.1 hq

end proof

end smd
end EtcdGrove
end Perennial
