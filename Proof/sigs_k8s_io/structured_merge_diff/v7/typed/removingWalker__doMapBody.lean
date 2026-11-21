/-
`typed.removingWalker.doMap`: a member of the recursion cluster `typed.removingWalkerRec` (`removingWalkerRec.lean`); its proof is the
projection of the cluster's (its body is `removingWalker__doMapBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.removingWalker__doMapBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.MakePath
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__Empty
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__Has
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__WithPrefix
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.heapAllocator__Free
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.freelistAllocator__Free
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.mapUnstructuredString__Empty
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.mapUnstructuredString__Iterate
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__AsMapUsing_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__IsMap_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__Unstructured_ptr
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsA5
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsBPers
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsBList
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.LawProofsDispatch
public import Proof.sigs_k8s_io.structured_merge_diff.v7.LawProofs.Intro
public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsRep
public import Proof.sigs_k8s_io.structured_merge_diff.v7.schema.LawProofs

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

theorem typed.removingWalker.doMap.wp_proofBody
    (h_MakePath : fieldpath.MakePath.spec (GF := GF))
    (h_Set_Empty : fieldpath.Set.Empty.spec (GF := GF))
    (h_Set_Has : fieldpath.Set.Has.spec (GF := GF))
    (h_Set_WithPrefix : fieldpath.Set.WithPrefix.spec (GF := GF))
    (h_heapAllocator_Free : value.heapAllocator.Free.spec (GF := GF))
    (h_freelistAllocator_Free : value.freelistAllocator.Free.spec (GF := GF))
    (h_mapUnstructuredString_Empty : value.mapUnstructuredString.Empty.spec (GF := GF))
    (h_mapUnstructuredString_Iterate : value.mapUnstructuredString.Iterate.spec (GF := GF))
    (h_valueUnstructured_AsMapUsing_ptr : value.valueUnstructured.AsMapUsing_ptr.spec (GF := GF))
    (h_valueUnstructured_IsMap_ptr : value.valueUnstructured.IsMap_ptr.spec (GF := GF))
    (h_valueUnstructured_Unstructured_ptr : value.valueUnstructured.Unstructured_ptr.spec (GF := GF)) :
    typed.removingWalker.doMap.specBody (GF := GF) := by
  unfold typed.removingWalker.doMap.specBody typed.removingWalkerRec.specI
    typed.removeItemsWithSchema.specI typed.removingWalker.doList.specI
    typed.removingWalker.doMap.specI
  iintro #IH
  icases IH with ⟨#HRm, -, -⟩
  iintro %w %sc %S %v %dq %x %rp %R %a %t %tp %fs %e %rel
  wp_start as ⟨Hown, Hv, #Hmr, %Hpre⟩
  wp_method_call; wp_call
  obtain ⟨Hfind, Hc⟩ := Hpre
  ihave ⟨Hv, %hsh⟩ := LawA3.isValF_shape _ _ _ $$ Hv
  obtain ⟨p, rfl⟩ := hsh
  unfold rmOwn
  icases Hown with ⟨Hw, #Hsc, %Hwf, #HR, Ha⟩
  ihave ⟨Ha, %ia, %Hia, #Hfree⟩ := isAlloc_Free h_heapAllocator_Free h_freelistAllocator_Free a $$ [Ha]
  · iframe Ha; iPkgInit
  subst Hia
  wp_auto
  wp_bind (App (Val wrapDefer) _)
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  wp_apply h_valueUnstructured_IsMap_ptr p dq x $$ [Hv] as %r1 ⟨Hv, %hr1⟩
  · iframe
  subst hr1
  cases hxm : x.isMapB
  · wp_auto
    iapply HΦ
    iexists GoInterface.nil
    iframe; iframe #
    rw [LawA5.removeAt_map_nonmap S t fs e rel R x Hfind hxm]
    isplitr
    · ipureintro; exact Hwf
    iapply (isIface_scalar_law_holds (GF := GF)).1
    ipureintro; trivial
  obtain ⟨kvs, rfl⟩ : ∃ kvs, x = .map kvs := by cases x <;> simp_all [UVal.isMapB]
  wp_auto
  wp_apply h_valueUnstructured_AsMapUsing_ptr p dq kvs (GoInterface.ok ia) $$ [Hv] as %mv ⟨Hv, Hmv⟩
  · iframe
  ihave %Hmc := isMapV_concrete_law_holds mv kvs $$ Hmv
  obtain ⟨gm, rfl⟩ := Hmc
  ihave ⟨HmvS, HfM⟩ := (freeable_view_law_holds).1 _ kvs $$ Hmv
  ihave #Hmv := isMapV_persistent_law_holds _ kvs $$ HmvS
  try iclear HmvS
  ihave %hsorted := isMapV_sorted_law_holds _ kvs $$ Hmv
  wp_auto
  wp_apply h_mapUnstructuredString_Empty gm kvs $$ [Hmv] as %r2 %Hr2
  · iframe #
  obtain rfl : r2 = decide (kvs = []) := by cases r2 <;> simp_all
  by_cases hkvs : kvs = []
  · subst hkvs
    simp only [decide_true]
    wp_auto
    wp_apply Hfree $$ %_ [Ha HfM] as Ha
    · iframe
    iapply HΦ
    iexists GoInterface.nil
    iframe; iframe #
    rw [LawA5.removeAt_map_leaf S t fs e rel R [] Hfind (Or.inl rfl)]
    isplitr
    · ipureintro; exact Hwf
    iapply (isIface_scalar_law_holds (GF := GF)).1
    ipureintro; trivial
  simp only [hkvs, decide_false]
  icases isMapRep_elim_law_holds tp fs e rel $$ Hmr with
    ⟨%fsl, %sfs, %etv, #Hfsl, #Hsfs, %Hlen, #Hsf, -, #Het, #Hetv, #Hrel⟩
  wp_auto
  rw [show decide (ElemRel.goName rel = go!"atomic") = decide (rel = ElemRel.atomic) by
    simp [LawB.goName_atomic]]
  by_cases hat : rel = .atomic
  · simp only [hat, decide_true]
    wp_auto
    wp_apply Hfree $$ %_ [Ha HfM] as Ha
    · iframe
    iapply HΦ
    iexists GoInterface.nil
    iframe; iframe #
    rw [LawA5.removeAt_map_leaf S t fs e rel R kvs Hfind (Or.inr hat)]
    isplitr
    · ipureintro; exact Hwf
    iapply (isIface_scalar_law_holds (GF := GF)).1
    ipureintro; trivial
  simp only [hat, decide_false]
  wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := schema.TypeRef)) as %ftm Hftm
  try wp_auto
  ihave %Hsl := ownSlice_len _ _ _ $$ Hsfs
  have Hnd : (fs.map (·.1)).Nodup := Schema.WF_fields_nodup_law_holds S _ fs e rel Hwf Hfind
  ipersist fieldTypes
  ihave HFI : (∃ (j : Nat) (MF : GMap GoString schema.TypeRef) (sv : schema.StructField),
      "i" ∷ i_ptr ↦ W64 j ∗ "structField" ∷ structField_ptr ↦ sv ∗ "Hftm" ∷ ftm ↦$ MF ∗
      "%Hj" ∷ ⌜j ≤ sfs.length ∧ ∀ n, (MF !! n).isSome = (lookupKV n (fs.take j)).isSome⌝ ∗
      "#HMt" ∷ □ (∀ n tr t', ⌜MF !! n = some tr ∧ lookupKV n (fs.take j) = some t'⌝ -∗ isTypeRef tr t') :
      IProp GF) $$ [i structField Hftm]
  · iexists 0, ∅, _
    iframe
    isplitr
    · ipureintro; refine ⟨by omega, fun n => ?_⟩; simp [lookupKV]
    imodintro; iintro %n %tr %t' ⟨%h1, -⟩; simp at h1
  wp_for HFI
  by_cases hj : j < sfs.length
  · have hc : sint.Z (W64 (j : Int)) < sint.Z fsl.len := by word
    simp only [decide_eq_true hc, ↓reduceIte]
    wp_auto
    have h0 : 0 ≤ sint.Z (W64 (j : Int)) := by word
    simp only [h0, hc, and_self, ↓reduceIte]
    have hsj : (sint.Z (W64 (j : Int))).toNat = j := by word
    obtain ⟨sf, hsf⟩ : ∃ x, sfs[j]? = some x := ⟨_, List.getElem?_eq_getElem hj⟩
    obtain ⟨f, hf⟩ : ∃ x, fs[j]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    wp_apply (wp_load_slice_index (t := schema.StructField.ty) fsl (sint.Z (W64 (j : Int))) sfs
      DFrac.discard sf h0) $$ [] as -
    · iframe #; ipureintro; rw [hsj]; exact hsf
    try wp_auto
    have hsff : sfs[j]? = some sf ∧ fs[j]? = some f := ⟨hsf, hf⟩
    ihave #Hsff := Hsf $$ %j %sf %f %hsff
    icases (isStructField_elim_law_holds sf f).1 $$ Hsff with ⟨%hname, #Hty⟩
    wp_apply (wp_mapInsert go.string ftm MF sf.Name' sf.Type') $$ [Hftm] as Hftm
    · iframe
    wp_for_post
    iframe
    iexists (j + 1), _, _
    have hw : W64 (j : Int) + W64 1 = W64 ((j + 1 : Nat) : Int) := by word
    rw [hw]
    iframe
    isplitr
    · ipureintro
      refine ⟨hj, fun n => ?_⟩
      rw [LawA5.lkv_take_succ fs j f hf Hnd n, hname.1]
      by_cases hn : f.1 = n
      · subst hn; simp
      · rw [GMap.lookup_insert_ne MF _ hn, ite_eq_right hn]; exact Hj.2 n
    imodintro
    iintro %n %tr %t' ⟨%h1, %h2⟩
    rw [LawA5.lkv_take_succ fs j f hf Hnd n, hname.1] at *
    by_cases hn : f.1 = n
    · subst hn
      rw [GMap.lookup_insert] at h1
      simp at h1 h2
      subst h1; subst h2
      iexact Hty
    · rw [GMap.lookup_insert_ne MF _ hn] at h1
      rw [ite_eq_right hn] at h2
      iapply HMt; ipureintro; exact ⟨h1, h2⟩
  have hc : ¬ sint.Z (W64 (j : Int)) < sint.Z fsl.len := by word
  simp only [decide_eq_false hc, Bool.false_eq_true, ↓reduceIte]
  have hjl : j = fs.length := by omega
  subst hjl
  rw [List.take_length] at Hj
  irevert HMt; rw [List.take_length]; iintro #HMt
  wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %om Hom
  try wp_auto
  ipersist w
  ipersist t
  ipersist fieldTypes
  ipersist newMap
  ipersist Hftm
  wp_func_lits
  have Hent := conforms_entry_law_holds S t fs e rel kvs Hfind Hc
  let g := LawA5.gRm S fs e R kvs
  wp_apply h_mapUnstructuredString_Iterate gm kvs _
    (fun done => iprop(∃ (M : GMap GoString GoInterface),
      w ↦ (typed.removingWalker.mk (interface.mkOk (go.GoType.PointerType value.valueUnstructured.ty) #p)
        GoInterface.nil sc rp (GoInterface.ok ia) false) ∗
      om ↦$ M ∗ ⌜LawBMZ.MInv M done g⌝ ∗
      (□ ∀ (k : GoString) (x : UVal), ⌜k ∈ done ∧ g k = some x⌝ -∗
        ∃ i, ⌜M !! k = some i⌝ ∗ isIface i x)))
    iprop(False) $$ [Hw Hom] as %r Hr
  · iframe #
    isplitr
    · iunfold iterFnOk
      imodintro
      iintro %done %k %x %vv %Hst %Φ' !> ⟨⟨%M, Hw, Hom, %HM, #HMi⟩, Hvv⟩ HΦ'
      simp only [← recv_eq_func_mk]
      wp_call
      wp_auto
      have hxk : (k, x) ∈ kvs := LawA2.lookupKV_mem k x kvs Hst.1
      obtain ⟨t', ht', hct⟩ := Hent k x hxk
      ipersist k
      ihave #Hpe := isPE_field_intro { FieldName' := k_ptr, Key' := null, Value' := null, Index' := null } k $$ k
      wp_apply (wp_slice_literal (V := GoInterface) [interface.mkOk fieldpath.PathElement.ty
        #({ FieldName' := k_ptr, Key' := null, Value' := null, Index' := null } : fieldpath.PathElement)])
      isplitr
      · ipureintro; rfl
      iintro %sl1 ⟨Hsl1, -⟩
      wp_auto
      ihave #Hpes : isPEs (GF := GF) [({ FieldName' := k_ptr, Key' := null, Value' := null, Index' := null } : fieldpath.PathElement)] [.field k] $$ []
      · iapply (isPEs_cons_law_holds _ [] (.field k) []).2
        iframe #
        iapply (show iprop(True) ⊢ isPEs (GF := GF) [] [] from isPEs_nil_law_holds)
        ipureintro; trivial
      wp_apply h_MakePath _ (DFrac.own 1) _ _ [.field k] $$ [Hsl1] as %fp %err2 ⟨%herr2, Hsl1, Hfp⟩
      · iframe; iframe #; ipureintro; rfl
      subst herr2
      try wp_auto
      wp_apply (wp_map_lookup2 go.string schema.TypeRef.ty ftm MF k DFrac.discard) $$ [Hftm] as -
      · iframe #
      try wp_auto
      wp_join iprop(∃ trv : schema.TypeRef, fieldType_ptr ↦ trv ∗ isTypeRef trv t') at next
        with [fieldType ft] as ⟨%trv, fieldType, #Htrv⟩
      · cases hl : MF !! k with
        | some tr0 =>
          obtain ⟨t0, ht0⟩ : ∃ t0, lookupKV k fs = some t0 := by
            have := Hj.2 k; rw [hl] at this; exact Option.isSome_iff_exists.1 this.symm
          have h0 : t0 = t' := by simpa [fieldType, ht0] using ht'
          subst h0
          have hh : MF !! k = some tr0 ∧ lookupKV k fs = some t0 := ⟨hl, ht0⟩
          ihave #Htr0 := HMt $$ %k %tr0 %t0 %hh
          simp only [Option.isSome_some, decide_true, Option.getD_some]
          wp_auto
          isplitr
          · ipureintro; rfl
          iexists tr0
          iframe
          iexact Htr0
        | none =>
          have hl0 : lookupKV k fs = none := by
            have := Hj.2 k; rw [hl] at this
            cases h : lookupKV k fs <;> simp_all
          have he : e = some t' := by simpa [fieldType, hl0] using ht'
          subst he
          ihave #Hetv' := (isTypeRefOpt_some_law_holds etv t').1 $$ Hetv
          simp only [Option.isSome_none, Bool.false_eq_true, decide_false]
          wp_auto
          isplitr
          · ipureintro; rfl
          iexists etv
          iframe
          iexact Hetv'
      have hgk : g k = LawA5.rmEntry S fs e R k x := by
        simp only [g, LawA5.gRm, Hst.1, Option.bind_some]
      wp_apply h_Set_Has rp R fp (DFrac.own 1) [.field k] $$ [Hfp] as %hm ⟨Hfp, %Hhm⟩
      · iframe #; iframe
      try wp_auto
      cases hm
      · have hnin : [PE.field k] ∉ R := fun h => by simpa using Hhm.2 h
        wp_auto
        wp_apply h_Set_WithPrefix rp R _ (.field k) $$ [] as %rp2 #Hrp2
        · iframe #
        wp_apply h_Set_Empty rp2 (R.under (.field k)) $$ [] as %emp %Hemp
        · iframe #
        try wp_auto
        cases emp
        · have hne : ¬ (R.under (.field k)).IsEmpty := fun h => by simpa using Hemp.2 h
          have hg : g k = some (removeAt S t' (R.under (.field k)) x) := by
            rw [hgk]; simp [LawA5.rmEntry, hnin, hne, ht']
          wp_auto
          wp_func_call
          wp_apply HRm $$ %vv %(DFrac.own 1) %x %rp2 %sc %(R.under (.field k)) %S %trv %t' [Hvv]
            as %v' ⟨Hvv, Hv'⟩
          · iframe; iframe #; ipureintro; exact ⟨Hwf, hct⟩
          try wp_auto
          ihave ⟨Hy, %hsh'⟩ := LawA3.isValF_shape _ _ _ $$ Hv'
          obtain ⟨p', rfl⟩ := hsh'
          wp_apply h_valueUnstructured_Unstructured_ptr p' _ (removeAt S t' (R.under (.field k)) x) $$ [Hy]
            as %u ⟨Hy, #Hu⟩
          · iframe
          try wp_auto
          wp_apply (wp_mapInsert go.string om M k u) $$ [Hom] as Hom
          · iframe
          try wp_auto
          iapply HΦ'
          iframe
          simp only [↓reduceIte]
          iexists (<[k := u]> M)
          iframe
          isplitr
          · ipureintro; exact LawBMZ.minv_some u HM hg
          imodintro
          iintro %k' %x' ⟨%hk1, %hk2⟩
          by_cases hkk : k = k'
          · subst hkk
            rw [hg] at hk2; cases hk2
            iexists u
            isplitr
            · ipureintro; exact GMap.lookup_insert M k u
            · iexact Hu
          · rcases List.mem_append.1 hk1 with h | h
            · have hh : k' ∈ done ∧ g k' = some x' := ⟨h, hk2⟩
              ihave ⟨%i', %hi', #Hi'⟩ := HMi $$ %k' %x' %hh
              iexists i'
              isplitr
              · ipureintro; rw [GMap.lookup_insert_ne M u hkk]; exact hi'
              · iexact Hi'
            · simp only [List.mem_singleton] at h; exact absurd h.symm hkk
        · have he : (R.under (.field k)).IsEmpty := Hemp.1 rfl
          have hg : g k = some x := by
            rw [hgk]; simp [LawA5.rmEntry, hnin, he]
          wp_auto
          ihave ⟨Hy, %hsh'⟩ := LawA3.isValF_shape _ _ _ $$ Hvv
          obtain ⟨p', rfl⟩ := hsh'
          wp_apply h_valueUnstructured_Unstructured_ptr p' _ x $$ [Hy] as %u ⟨Hvv, #Hu⟩
          · iframe
          try wp_auto
          wp_apply (wp_mapInsert go.string om M k u) $$ [Hom] as Hom
          · iframe
          try wp_auto
          iapply HΦ'
          iframe
          simp only [↓reduceIte]
          iexists (<[k := u]> M)
          iframe
          isplitr
          · ipureintro; exact LawBMZ.minv_some u HM hg
          imodintro
          iintro %k' %x' ⟨%hk1, %hk2⟩
          by_cases hkk : k = k'
          · subst hkk
            rw [hg] at hk2; cases hk2
            iexists u
            isplitr
            · ipureintro; exact GMap.lookup_insert M k u
            · iexact Hu
          · rcases List.mem_append.1 hk1 with h | h
            · have hh : k' ∈ done ∧ g k' = some x' := ⟨h, hk2⟩
              ihave ⟨%i', %hi', #Hi'⟩ := HMi $$ %k' %x' %hh
              iexists i'
              isplitr
              · ipureintro; rw [GMap.lookup_insert_ne M u hkk]; exact hi'
              · iexact Hi'
            · simp only [List.mem_singleton] at h; exact absurd h.symm hkk
      · have hin : [PE.field k] ∈ R := Hhm.1 rfl
        have hg : g k = none := by rw [hgk]; simp [LawA5.rmEntry, hin]
        wp_auto
        iapply HΦ'
        iframe
        simp only [↓reduceIte]
        iexists M
        iframe
        isplitr
        · ipureintro; exact LawBMZ.minv_none HM hg
        imodintro
        iintro %k' %x' ⟨%hk1, %hk2⟩
        rcases List.mem_append.1 hk1 with h | h
        · iapply HMi; ipureintro; exact ⟨h, hk2⟩
        · simp only [List.mem_singleton] at h; subst h; rw [hg] at hk2; cases hk2
    iexists ∅
    iframe
    isplitr
    · ipureintro; exact LawBMZ.minv_nil g
    imodintro; iintro %k %x %h; simp at h
  iunfold mapIterPost at Hr
  cases r
  · simp only [Bool.false_eq_true, ↓reduceIte]
    iexfalso; iexact Hr
  simp only [↓reduceIte]
  icases Hr with ⟨%done, %Hdone, %M, Hw, Hom, %HM, #HMi⟩
  simp only [mapIterDone, Bool.false_eq_true, ↓reduceIte, kvKeys] at Hdone
  have hknd := ValuePure.keysSorted_nodup kvs hsorted
  have hrm := LawA5.removeM_entriesOf S fs e R kvs hknd
  have hemp := LawBMZ.minv_empty HM Hdone
  have hpw : (kvs.map (·.1)).Pairwise (fun a b => gsLt a b = true) :=
    List.pairwise_map.2 ((LawProofs.keysSorted_iff_pairwise _).1 hsorted)
  have hsortedE := LawBMZ.entriesOf_sorted g _ hpw
  rw [LawA5.removeAt_map_items S t fs e rel R kvs Hfind hkvs hat, hrm]
  wp_apply (wp_map_len_lt om M (DFrac.own 1)) $$ Hom as ⟨Hom, %Hsz⟩
  cases hE : (LawBMZ.entriesOf g (kvs.map (·.1))).isEmpty
  · have hne : M.size ≠ 0 := fun h => by rw [hemp.1 h] at hE; cases hE
    have hpos : decide (sint.Z (W64 0) < sint.Z (W64 (M.size : Nat))) = true := by
      apply decide_eq_true
      have h1 : 0 < M.size := Nat.pos_of_ne_zero hne
      have h2 : M.size < 2 ^ 63 := Hsz
      have h3 : sint.Z (W64 (M.size : Int)) = (M.size : Int) := by word
      rw [h3]
      have h4 : sint.Z (W64 0) = 0 := by word
      rw [h4]
      omega
    rw [hpos]
    have hne' : LawBMZ.entriesOf g (kvs.map (·.1)) ≠ [] := by
      intro h; rw [h] at hE; cases hE
    rw [ite_eq_right hne']
    iapply wp_fupd
    wp_auto
    wp_apply Hfree $$ %_ [Ha HfM] as Ha
    · iframe
    try wp_auto
    ipersist Hom
    imodintro
    ihave #Hiface := LawBMZ.isIface_entries om M
      (LawBMZ.entriesOf g (kvs.map (·.1))) hsortedE
      (fun k => LawBMZ.minv_final HM Hdone k) $$ Hom []
    · imodintro
      iintro %k %x %hkx
      rw [LawBMZ.lkv_entriesOf] at hkx
      by_cases hk : k ∈ kvs.map (·.1)
      · simp only [hk, ↓reduceIte] at hkx
        have hh : k ∈ done ∧ g k = some x := ⟨Hdone.mem_iff.2 hk, hkx⟩
        iapply HMi $$ %k %x %hh
      · simp only [hk, ↓reduceIte] at hkx; cases hkx
    wp_auto
    iapply HΦ
    iexists _
    iframe; iframe #
    ipureintro; exact Hwf
  · have hz : M.size = 0 := hemp.2 hE
    have hpos : decide (sint.Z (W64 0) < sint.Z (W64 (M.size : Nat))) = false := by
      rw [hz]; rfl
    rw [hpos]
    have he' : LawBMZ.entriesOf g (kvs.map (·.1)) = [] := List.isEmpty_iff.1 hE
    rw [ite_eq_left he']
    wp_auto
    wp_apply Hfree $$ %_ [Ha HfM] as Ha
    · iframe
    try wp_auto
    iapply HΦ
    iexists GoInterface.nil
    iframe; iframe #
    isplitr
    · ipureintro; exact Hwf
    iapply (isIface_scalar_law_holds (GF := GF)).1
    ipureintro; trivial

end proof

end smd
end EtcdGrove
end Perennial
