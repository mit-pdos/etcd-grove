/-
`typed.toFieldSetWalker.visitMapItems`: a member of the recursion cluster `typed.toFieldSetWalkerRec` (`toFieldSetWalkerRec.lean`); its proof is the
projection of the cluster's (its body is `toFieldSetWalker__visitMapItemsBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.toFieldSetWalker__visitMapItemsBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__Insert
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.mapUnstructuredString__Iterate
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.mapUnstructuredString__Length
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__AsMap_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__IsMap_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__IsNull_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.schema.Map__FindField
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.toFieldSetWalker__finishDescent
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.toFieldSetWalker__prepareDescent
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsA
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsA2
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsA3
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsAPure
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsBPers
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsB2
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

set_option synthInstance.maxHeartbeats 200000 in
set_option synthInstance.maxSize 4096 in
theorem typed.toFieldSetWalker.visitMapItems.wp_proofBody
    (h_Set_Insert : fieldpath.Set.Insert.spec (GF := GF))
    (h_mapUnstructuredString_Iterate : value.mapUnstructuredString.Iterate.spec (GF := GF))
    (h_mapUnstructuredString_Length : value.mapUnstructuredString.Length.spec (GF := GF))
    (h_valueUnstructured_AsMap_ptr : value.valueUnstructured.AsMap_ptr.spec (GF := GF))
    (h_valueUnstructured_IsMap_ptr : value.valueUnstructured.IsMap_ptr.spec (GF := GF))
    (h_valueUnstructured_IsNull_ptr : value.valueUnstructured.IsNull_ptr.spec (GF := GF))
    (h_Map_FindField : schema.Map.FindField.spec (GF := GF))
    (h_toFieldSetWalker_finishDescent : typed.toFieldSetWalker.finishDescent.spec (GF := GF))
    (h_toFieldSetWalker_prepareDescent : typed.toFieldSetWalker.prepareDescent.spec (GF := GF)) :
    typed.toFieldSetWalker.visitMapItems.specBody (GF := GF) := by
  unfold typed.toFieldSetWalker.visitMapItems.specBody typed.toFieldSetWalkerRec.specI
    typed.toFieldSetWalker.toFieldSet.specI typed.toFieldSetWalker.doList.specI
    typed.toFieldSetWalker.doMap.specI typed.toFieldSetWalker.visitListItems.specI
    typed.toFieldSetWalker.visitMapItems.specI
  iintro #IH
  icases IH with ⟨-, -, #HT, -, -⟩
  iintro %w %sc %S %st %s %F %tp %fs %e %rel %m %kvs %sp
  wp_start as ⟨Hown, #Hm, #Hmv, %Hpre⟩
  obtain ⟨Hfind, Hc, Hcard⟩ := Hpre
  ihave %Hmc := isMapV_concrete_law_holds m kvs $$ Hmv
  obtain ⟨gm, rfl⟩ := Hmc
  ihave %Hsorted := isMapV_sorted_law_holds _ kvs $$ Hmv
  have hknd := ValuePure.keysSorted_nodup kvs Hsorted
  iunfold twOwn at Hown
  icases Hown with ⟨%ps, Hcore, Hps, Hsp, Ha, Hs⟩
  iunfold twCore at Hcore
  icases Hcore with ⟨%tr0, Hw, #Htr0, #Hsc, %Hwf⟩
  icases isMapRep_elim_law_holds tp fs e rel $$ Hm with
    ⟨%fsl, %sfs, %etv, -, -, -, -, -, #Het, #Hetv, -⟩
  have Hnd : (fs.map (·.1)).Nodup := Schema.WF_fields_nodup_law_holds S _ fs e rel Hwf Hfind
  have Hent := conforms_entry_law_holds S st.t fs e rel kvs Hfind Hc
  wp_auto
  ipersist v
  ipersist t
  wp_func_lits
  wp_apply h_mapUnstructuredString_Iterate gm kvs _
    (fun done => iprop(∃ (psj : fieldpath.Path) (spj : Loc) (trj : schema.TypeRef) (el : GoSlice),
      errs_ptr ↦ el ∗ noErrs el ∗
      w ↦ (typed.toFieldSetWalker.mk st.value sc trj s psj spj st.alloc) ∗ isTypeRef trj st.t ∗
      ownPath psj st.path ∗ spareWalkers typed.toFieldSetWalker spj ∗ ⌜sp ≠ null → spj = sp⌝ ∗
      isAlloc st.alloc ∗
      ownSet s (PathSet.union F (fieldsM S fs e st.path (kvs.filter (fun kv => decide (kv.1 ∈ done)))))))
    iprop(False) $$ [errs Hw Hps Hsp Ha Hs] as %r Hr
  · iframe Hmv
    isplitr
    · iunfold iterFnOk
      imodintro
      iintro %done %k %x %vv %Hst %Φ' !> ⟨⟨%psj, %spj, %trj, %el, errs, Herrs, Hw, #Htrj, Hps, Hsp, %Hspj, Ha, Hs⟩, Hvv⟩ HΦ'
      simp only [← recv_eq_func_mk]
      wp_call
      wp_auto
      have hxk : (k, x) ∈ kvs := LawA2.lookupKV_mem k x kvs Hst.1
      obtain ⟨t', ht', hct⟩ := Hent k x hxk
      let Fd := PathSet.union F (fieldsM S fs e st.path (kvs.filter (fun kv => decide (kv.1 ∈ done))))
      have hsubFd : ∀ q, q ∈ Fd → q ∈ PathSet.union F (fieldsM S fs e st.path kvs) := by
        intro q hq
        rcases (LawA3.mem_pu _ _ _).1 hq with h | h
        · exact (LawA3.mem_pu _ _ _).2 (Or.inl h)
        · obtain ⟨kv, hkv, hq⟩ := (LawA3.mem_fieldsM _ _ _ _ _ _).1 h
          exact (LawA3.mem_pu _ _ _).2 (Or.inr ((LawA3.mem_fieldsM _ _ _ _ _ _).2
            ⟨kv, (List.mem_filter.1 hkv).1, hq⟩))
      have hsubE : ∀ q, q ∈ LawA3.entryF S fs e st.path (k, x) →
          q ∈ PathSet.union F (fieldsM S fs e st.path kvs) := fun q hq =>
        (LawA3.mem_pu _ _ _).2 (Or.inr ((LawA3.mem_fieldsM _ _ _ _ _ _).2 ⟨(k, x), hxk, hq⟩))
      have hEA : ∀ q, q ∈ fieldsAt S t' (st.path ++ [.field k]) x → q ∈ LawA3.entryF S fs e st.path (k, x) := by
        intro q hq
        simp only [LawA3.entryF, ht', union, LawA3.mem_pu]
        exact Or.inl hq
      have hcard2 : (PathSet.union Fd (fieldsAt S t' (st.path ++ [.field k]) x)).CardLt (2 ^ 63 - 1) := by
        apply LawA3.cardLt_sub _ _ _ _ Hcard
        intro q hq
        rcases (LawA3.mem_pu _ _ _).1 hq with h | h
        · exact hsubFd q h
        · exact hsubE q (hEA q h)
      wp_apply h_Map_FindField tp fs e rel k $$ [] as %sf %ok Hff
      · iframe #; ipureintro; exact Hnd
      wp_join iprop(∃ trv : schema.TypeRef, tr_ptr ↦ trv ∗ isTypeRef trv t') at next
        with [tr Hff sf] as ⟨%trv, tr, #Htrv⟩
      · cases hl : lookupKV k fs with
        | some t'' =>
          have : t'' = t' := by simpa [fieldType, hl] using ht'
          subst this
          simp only [hl]
          icases Hff with ⟨%hok, Hsf⟩
          subst hok
          icases (isStructField_elim_law_holds sf (k, t'')).1 $$ Hsf with ⟨-, #Hst'⟩
          wp_auto
          isplitr
          · ipureintro; rfl
          iexists sf.Type'
          iframe tr
          iexact Hst'
        | none =>
          have he : e = some t' := by simpa [fieldType, hl] using ht'
          subst he
          simp only [hl]
          icases Hff with %Hff
          obtain ⟨rfl, rfl⟩ := Hff
          ihave #Hetv' := (isTypeRefOpt_some_law_holds etv t').1 $$ Hetv
          wp_auto
          isplitr
          · ipureintro; rfl
          iexists etv
          iframe
          iexact Hetv'
      ipersist key
      ihave #Hpe := isPE_field_intro { FieldName' := key_ptr, Key' := null, Value' := null, Index' := null } k $$ key
      wp_apply h_toFieldSetWalker_prepareDescent w sc S st psj s spj st.alloc _ (.field k) trv t'
        $$ [Hw Hps Hsp] as %w2 ⟨%sp', %ps2, Hcore, Hcore2, Hps2, Hsp, %Hspn, %Hspe⟩
      · iframe; iframe #; unfold twCore; iexists trj; iframe; iframe #; ipureintro; exact Hwf
      iunfold twCore at Hcore2
      icases Hcore2 with ⟨%tr2, Hw2, #Htr2, -, -⟩
      try wp_auto
      wp_apply HT $$ %w2 %sc %S %(TWSt.mk vv t' (st.path ++ [.field k]) st.alloc) %s %Fd
        %(DFrac.own 1) %x %sp' [Hw2 Hps2 Hsp Ha Hs Hvv] as %errs2 ⟨Herrs2, Hvv, %sp'', Hown2, %Hsp''⟩
      · iframe Hvv
        isplitl [Hw2 Hps2 Hsp Ha Hs]
        · unfold twOwn twCore
          iexists ps2
          iframe
          iframe #
          ipureintro; exact Hwf
        ipureintro; exact ⟨hct, hcard2⟩
      have hsp2 := (Hsp'' Hspn).symm
      subst hsp2
      wp_apply LawA2.wp_append_noErrs el errs2 $$ [Herrs Herrs2] as %el' Hel'
      · iframe
      unfold twOwn
      icases Hown2 with ⟨%ps3, Hcore2, Hps3, Hsp, Ha, Hs⟩
      iunfold twCore at Hcore2
      icases Hcore2 with ⟨%tr3, Hw2, #Htr3, -, -⟩
      simp only
      ihave ⟨Hvv, %hsh⟩ := LawA3.isValF_shape _ _ _ $$ Hvv
      obtain ⟨pv, rfl⟩ := hsh
      unfold ownPath
      icases Hps3 with ⟨Hpf, Hpc⟩
      try wp_auto
      have hEq : ∀ q, q ∈ LawA3.entryF S fs e st.path (k, x) ↔
          q ∈ fieldsAt S t' (st.path ++ [.field k]) x ∨
          ((x = .null ∨ x = .map [] ∨ lookupKV k fs = none) ∧ q ∈ ins (st.path ++ [.field k])) := by
        intro q
        have he : q ∉ (empty : PathSet) := FSet.mem_empty q
        simp only [LawA3.entryF, ht', union, LawA3.mem_pu]
        by_cases h : (x = .null ∨ x = .map [] ∨ lookupKV k fs = none)
        · simp only [h, if_true, true_and]
        · simp only [h, if_false, he, false_and, or_false]
      wp_bind (If _ _ _)
      iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ ∃ G : PathSet, ownSet s G ∗
          ⌜∀ q, q ∈ G ↔ q ∈ PathSet.union Fd (LawA3.entryF S fs e st.path (k, x))⌝ ∗
          isPathF ps3 (DFrac.own 1) (st.path ++ [.field k]) ∗
          isValF (interface.mkOk (go.GoType.PointerType value.valueUnstructured.ty) #pv) (DFrac.own 1) x ∗
          val_ptr ↦ interface.mkOk (go.GoType.PointerType value.valueUnstructured.ty) #pv ∗
          v2_ptr ↦ w2 ∗ w2 ↦ (typed.toFieldSetWalker.mk
            (interface.mkOk (go.GoType.PointerType value.valueUnstructured.ty) #pv) sc tr3 s ps3 sp' st.alloc))))
        $$ [Hs Hpf Hvv val v2 Hw2]
      · wp_apply h_valueUnstructured_IsNull_ptr pv _ x $$ [Hvv] as %b1 ⟨Hvv, %hb1⟩
        · iframe
        subst hb1
        by_cases hxn : x = .null
        · subst hxn
          simp only [UVal.isNullB]
          wp_auto
          wp_apply h_Set_Insert s _ ps3 (DFrac.own 1) (st.path ++ [.field k]) $$ [Hs Hpf] as ⟨Hs, Hpf⟩
          · iframe; ipureintro; exact hcard2
          try wp_auto
          isplitr
          · ipureintro; rfl
          iexists _
          iframe
          ipureintro
          intro q
          have hcond : UVal.null = .null ∨ UVal.null = .map [] ∨ lookupKV k fs = none := Or.inl rfl
          simp only [LawA3.mem_pu, hEq, _root_.or_assoc]
          exact LawA3.ins_iff (by simp_all)
        have hn1 : x.isNullB = false := by cases x <;> simp_all [UVal.isNullB]
        rw [hn1]
        wp_auto
        wp_apply h_valueUnstructured_IsMap_ptr pv _ x $$ [Hvv] as %b2 ⟨Hvv, %hb2⟩
        · iframe
        subst hb2
        by_cases hxm : ∃ kvs', x = .map kvs'
        · obtain ⟨kvs', rfl⟩ := hxm
          simp only [UVal.isMapB]
          wp_auto
          wp_apply h_valueUnstructured_AsMap_ptr pv _ kvs' $$ [Hvv] as %mv ⟨Hvv, Hmv'⟩
          · iframe
          ihave %Hmc' := isMapV_concrete_law_holds mv kvs' $$ Hmv'
          obtain ⟨gm', rfl⟩ := Hmc'
          wp_auto
          wp_apply h_mapUnstructuredString_Length gm' kvs' $$ [Hmv'] as %ln %hln
          · iframe
          try wp_auto
          by_cases he0 : kvs' = []
          · subst he0
            have hl0 : ln = W64 0 := by simp at hln; word
            subst hl0
            simp only [_root_.decide_true]
            wp_auto
            wp_apply h_Set_Insert s _ ps3 (DFrac.own 1) (st.path ++ [.field k]) $$ [Hs Hpf] as ⟨Hs, Hpf⟩
            · iframe; ipureintro; exact hcard2
            try wp_auto
            isplitr
            · ipureintro; rfl
            iexists _
            iframe
            ipureintro
            intro q
            have hcond : UVal.map [] = .null ∨ UVal.map [] = .map [] ∨ lookupKV k fs = none := Or.inr (Or.inl rfl)
            simp only [LawA3.mem_pu, hEq, _root_.or_assoc]
            exact LawA3.ins_iff (by simp_all)
          · have hl0 : decide (ln = W64 0) = false := by
              simp only [decide_eq_false_iff_not]
              intro h; subst h; apply he0; apply List.eq_nil_of_length_eq_zero; simp at hln; omega
            rw [hl0]
            wp_auto
            wp_apply h_Map_FindField tp fs e rel k $$ [] as %sf2 %ok2 Hff2
            · iframe #; ipureintro; exact Hnd
            cases hl : lookupKV k fs with
            | some t'' =>
              simp only [hl]
              icases Hff2 with ⟨%hok, -⟩
              subst hok
              wp_auto
              isplitr
              · ipureintro; rfl
              iexists _
              iframe
              ipureintro
              intro q
              have hcond : ¬ (UVal.map kvs' = .null ∨ UVal.map kvs' = .map [] ∨ lookupKV k fs = none) := by
                rw [hl]; simp [he0]
              have he : q ∉ (empty : PathSet) := FSet.mem_empty q
              simp only [LawA3.mem_pu, hEq, _root_.or_assoc]
              exact LawA3.noins_iff hcond
            | none =>
              simp only [hl]
              icases Hff2 with %Hff2
              obtain ⟨rfl, rfl⟩ := Hff2
              wp_auto
              wp_apply h_Set_Insert s _ ps3 (DFrac.own 1) (st.path ++ [.field k]) $$ [Hs Hpf] as ⟨Hs, Hpf⟩
              · iframe; ipureintro; exact hcard2
              try wp_auto
              isplitr
              · ipureintro; rfl
              iexists _
              iframe
              ipureintro
              intro q
              have hcond : UVal.map kvs' = .null ∨ UVal.map kvs' = .map [] ∨ lookupKV k fs = none := Or.inr (Or.inr hl)
              simp only [LawA3.mem_pu, hEq, _root_.or_assoc]
              exact LawA3.ins_iff (by simp_all)
        · have hm1 : x.isMapB = false := by
            cases x <;> simp_all [UVal.isMapB]
          rw [hm1]
          wp_auto
          wp_apply h_Map_FindField tp fs e rel k $$ [] as %sf2 %ok2 Hff2
          · iframe #; ipureintro; exact Hnd
          cases hl : lookupKV k fs with
          | some t'' =>
            simp only [hl]
            icases Hff2 with ⟨%hok, -⟩
            subst hok
            wp_auto
            isplitr
            · ipureintro; rfl
            iexists _
            iframe
            ipureintro
            intro q
            have hcond : ¬ (x = .null ∨ x = .map [] ∨ lookupKV k fs = none) := by
              rw [hl]; cases x <;> simp_all
            have he : q ∉ (empty : PathSet) := FSet.mem_empty q
            simp only [LawA3.mem_pu, hEq, _root_.or_assoc]
            exact LawA3.noins_iff hcond
          | none =>
            simp only [hl]
            icases Hff2 with %Hff2
            obtain ⟨rfl, rfl⟩ := Hff2
            wp_auto
            wp_apply h_Set_Insert s _ ps3 (DFrac.own 1) (st.path ++ [.field k]) $$ [Hs Hpf] as ⟨Hs, Hpf⟩
            · iframe; ipureintro; exact hcard2
            try wp_auto
            isplitr
            · ipureintro; rfl
            iexists _
            iframe
            ipureintro
            intro q
            have hcond : x = .null ∨ x = .map [] ∨ lookupKV k fs = none := Or.inr (Or.inr hl)
            simp only [LawA3.mem_pu, hEq, _root_.or_assoc]
            exact LawA3.ins_iff (by simp_all)
      iintro %v ⟨%hv, %G, Hs, %HG, Hpf, Hvv, val, v2, Hw2⟩
      subst hv
      wp_auto
      wp_apply h_toFieldSetWalker_finishDescent w w2 sc S st
        (TWSt.mk (interface.mkOk (go.GoType.PointerType value.valueUnstructured.ty) #pv) t'
          (st.path ++ [.field k]) st.alloc) psj ps3 s sp' st.alloc (.field k)
        $$ [Hcore Hw2 Hpf Hpc Hsp] as ⟨%ps4, Hcore, Hps4, Hsp⟩
      · iframe
        isplitl [Hw2]
        · unfold twCore; iexists tr3; iframe; iframe #; ipureintro; exact Hwf
        isplitl [Hpf Hpc]
        · unfold ownPath; iframe
        ipureintro; exact Hspn
      try wp_auto
      have hGeq : G = PathSet.union F
          (fieldsM S fs e st.path (kvs.filter (fun kv => decide (kv.1 ∈ done ++ [k])))) := by
        rw [← LawA3.fieldsM_step F S fs e st.path kvs hknd done k x Hst.1
          (LawA3.entryF S fs e st.path (k, x)) (fun _ => Iff.rfl)]
        exact FSet.ext' HG
      subst hGeq
      iapply HΦ'
      iframe
      simp only [↓reduceIte]
      iunfold twCore at Hcore
      icases Hcore with ⟨%tr4, Hw, #Htr4, -, -⟩
      iexists ps4, sp', tr4, el'
      iunfold ownPath at Hps4
      iframe
      iframe #
      ipureintro
      intro h; have h1 := Hspj h; subst h1; exact Hspe h
    · iexists ps, sp, tr0, _
      iframe
      isplitr
      · iapply noErrs_nil
      iframe #
      isplitr
      · ipureintro; intro; rfl
      have h0 : kvs.filter (fun kv => decide (kv.1 ∈ ([] : List GoString))) = [] := by simp
      rw [h0]
      simp only [fieldsM, LawB.ps_union_empty]
      iframe
  iunfold mapIterPost at Hr
  cases r
  · simp only [Bool.false_eq_true, ↓reduceIte]
    iexfalso; iexact Hr
  · simp only [↓reduceIte]
    icases Hr with ⟨%done, %Hdone, %psj, %spj, %trj, %el, errs, Herrs, Hw, #Htrj, Hps, Hsp, %Hspj, Ha, Hs⟩
    have hall : kvs.filter (fun kv => decide (kv.1 ∈ done)) = kvs := by
      apply List.filter_eq_self.2
      intro kv hkv
      simp only [mapIterDone, Bool.false_eq_true, ↓reduceIte] at Hdone
      simp only [decide_eq_true_eq]
      exact Hdone.mem_iff.2 (List.mem_map.2 ⟨kv, hkv, rfl⟩)
    rw [hall]
    wp_auto
    iapply HΦ
    iframe
    iexists spj
    isplitl
    · unfold twOwn twCore
      iexists psj
      iframe
      iframe #
      ipureintro; exact Hwf
    ipureintro; exact Hspj

end proof

end smd
end EtcdGrove
end Perennial
