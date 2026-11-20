/-
`typed.validatingObjectWalker.visitMapItems`: a member of the recursion cluster `typed.validatingObjectWalkerRec` (`validatingObjectWalkerRec.lean`); its proof is the
projection of the cluster's (its body is `validatingObjectWalker__visitMapItemsBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.validatingObjectWalker__visitMapItemsBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.mapUnstructuredString__IterateUsing
public import Spec.sigs_k8s_io.structured_merge_diff.v7.schema.Map__FindField
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.ValidationErrors__WithPrefix
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.validatingObjectWalker__finishDescent
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.validatingObjectWalker__prepareDescent
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsA
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsA2
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

theorem typed.validatingObjectWalker.visitMapItems.wp_proofBody
    (h_mapUnstructuredString_IterateUsing : value.mapUnstructuredString.IterateUsing.spec (GF := GF))
    (h_Map_FindField : schema.Map.FindField.spec (GF := GF))
    (h_ValidationErrors_WithPrefix : typed.ValidationErrors.WithPrefix.spec (GF := GF))
    (h_validatingObjectWalker_finishDescent : typed.validatingObjectWalker.finishDescent.spec (GF := GF))
    (h_validatingObjectWalker_prepareDescent : typed.validatingObjectWalker.prepareDescent.spec (GF := GF)) :
    typed.validatingObjectWalker.visitMapItems.specBody (GF := GF) := by
  unfold typed.validatingObjectWalker.visitMapItems.specBody typed.validatingObjectWalkerRec.specI
    typed.validatingObjectWalker.validate.specI typed.validatingObjectWalker.doList.specI
    typed.validatingObjectWalker.doMap.specI typed.validatingObjectWalker.visitListItems.specI
    typed.validatingObjectWalker.visitMapItems.specI
  iintro #IH
  iintro %w %sc %S %st %tp %fs %e %rel %m %kvs %sp
  wp_start as ⟨Hown, #Hm, #Hmv, %Hpre⟩
  obtain ⟨Hfind, Hc⟩ := Hpre
  ihave %Hmc := isMapV_concrete_law_holds m kvs $$ Hmv
  obtain ⟨gm, rfl⟩ := Hmc
  iunfold vwOwn at Hown
  icases Hown with ⟨Hcore, Hsp, Ha⟩
  iunfold vwCore at Hcore
  icases Hcore with ⟨%tr0, Hw, #Htr0, #Hsc, %Hwf⟩
  icases isMapRep_elim_law_holds tp fs e rel $$ Hm with
    ⟨%fsl, %sfs, %etv, -, -, -, -, -, #Het, #Hetv, -⟩
  have Hnd : (fs.map (·.1)).Nodup := Schema.WF_fields_nodup_law_holds S _ fs e rel Hwf Hfind
  have Hent := conforms_entry_law_holds S st.t fs e rel kvs Hfind Hc
  icases IH with ⟨-, -, #HV, -, -⟩
  wp_auto
  ipersist v
  ipersist t
  wp_func_lits
  wp_apply h_mapUnstructuredString_IterateUsing gm kvs st.alloc _
    (fun _ => iprop(∃ (sp1 : Loc) (el : GoSlice), errs_ptr ↦ el ∗ noErrs el ∗
      vwCore w sc S st sp1 st.alloc ∗ spareWalkers typed.validatingObjectWalker sp1 ∗
      ⌜sp ≠ null → sp1 = sp⌝))
    iprop(False) $$ [Ha errs Hw Hsp] as %r ⟨Ha, Hr⟩
  · iframe Hmv Ha
    isplitr
    · iunfold iterUFnOk
      imodintro
      iintro %done %k %x %vv %Hst %Φ' !> ⟨Ha, ⟨%sp1, %el, errs, Herrs, Hcore, Hsp, %Hsp1⟩, Hvv⟩ HΦ'
      simp only [← recv_eq_func_mk]
      wp_call
      wp_auto
      obtain ⟨t', ht', hct⟩ := Hent k x (LawA2.lookupKV_mem k x kvs Hst.1)
      have hfs : (S.find t'.name).isSome := LawA.conforms_find S t' x hct
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
          icases isTypeRef_elim_law_holds etv t' $$ Hetv' with ⟨#Hnt, -⟩
          ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hnt
          wp_auto
          rw [decide_eq_false Hnn]
          wp_auto
          isplitr
          · ipureintro; rfl
          iexists etv
          iframe
          iexact Hetv'
      wp_apply h_validatingObjectWalker_prepareDescent w sc S st sp1 st.alloc trv t' $$ [Hcore Hsp]
        as %w2 ⟨%sp', Hcore, Hcore2, Hsp, %Hspn, %Hspe⟩
      · iframe; iframe #
      iunfold vwCore at Hcore2
      icases Hcore2 with ⟨%tr2, Hw2, #Htr2, -, -⟩
      wp_auto
      wp_func_lits
      wp_apply HV $$ %w2 %sc %S %(VWSt.mk vv t' st.alloc) %(DFrac.own 1) %x %_ %sp' [Hw2 Hsp Ha Hvv]
        as %errs2 ⟨Herrs2, Hvv, %sp'', Hown2, %Hsp''⟩
      · iframe Hvv
        isplitl [Hw2 Hsp Ha]
        · unfold vwOwn vwCore
          iframe Hsp Ha
          iexists tr2
          iframe Hw2
          iframe #
          ipureintro; exact Hwf
        ipureintro; exact ⟨hfs, hct⟩
      have hsp2 := (Hsp'' Hspn).symm
      subst hsp2
      wp_apply LawA2.wp_append_noErrs el errs2 $$ [Herrs Herrs2] as %el' Hel'
      · iframe
      unfold vwOwn
      icases Hown2 with ⟨Hcore2, Hsp, Ha⟩
      wp_apply h_validatingObjectWalker_finishDescent w w2 sc S st (VWSt.mk vv t' st.alloc) sp' st.alloc
        $$ [Hcore Hcore2 Hsp] as ⟨Hcore, Hsp⟩
      · iframe; ipureintro; exact Hspn
      try wp_auto
      iapply HΦ'
      iframe
      simp only [↓reduceIte]
      iexists sp', el'
      iframe
      ipureintro
      intro h; have h1 := Hsp1 h; subst h1; exact Hspe h
    · iexists sp, _
      iframe errs Hsp
      isplitr
      · iapply noErrs_nil
      isplitl
      · unfold vwCore; iexists tr0; iframe Hw; iframe #; ipureintro; exact Hwf
      ipureintro; intro; rfl
  iunfold mapIterPost at Hr
  cases r
  · simp only [Bool.false_eq_true, ↓reduceIte]
    iexfalso; iexact Hr
  · simp only [↓reduceIte]
    icases Hr with ⟨%done, -, %sp1, %el, errs, Herrs, Hcore, Hsp, %Hsp1⟩
    wp_auto
    iapply HΦ
    iframe Herrs
    iexists sp1
    unfold vwOwn
    iframe
    ipureintro; exact Hsp1

end proof

end smd
end EtcdGrove
end Perennial
