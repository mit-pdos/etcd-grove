/-
`typed.reconcileWithSchemaWalker.visitMapItems`: a member of the recursion cluster `typed.reconcileWithSchemaWalkerRec` (`reconcileWithSchemaWalkerRec.lean`); its proof is the
projection of the cluster's (its body is `reconcileWithSchemaWalker__visitMapItemsBody.lean`).

Proved (Prove phase 2026-11-21): the cluster's specs give the walker back as `rwOwnAt` with its
path slice unchanged (`LawProofsBRecon2Own.lean`), so the child's slice after `v2.reconcile()` is
the one `prepareDescent` gave it and `prepareDescent`'s wand gives the parent's path back.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.reconcileWithSchemaWalker__visitMapItemsBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElementSet__Has
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElementSet__Iterate
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.SetNodeMap__Get
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.SetNodeMap__Iterate
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.reconcileWithSchemaWalker__finishDescent
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.reconcileWithSchemaWalker__prepareDescent
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.typeRefAtPath
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsA2
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsBRecon2
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsBPers
public import Proof.sigs_k8s_io.structured_merge_diff.v7.schema.LawProofs
public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsSet

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option synthInstance.maxSize 1024

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

/-- `typeRefAtPath`'s result at a map type of the schema: the child's type (`reconChild`). -/
theorem typed.reconcileWithSchemaWalker.typeRefAtPath_reconChild
    (h_typeRefAtPath : typed.typeRefAtPath.spec (GF := GF)) (S : Schema) (t : TypeRef) (tp : Loc)
    (fl : List (GoString × TypeRef)) (em : Option TypeRef) (rel : ElemRel)
    (hfind : S.find t.name = some (.map fl em rel)) (pe : fieldpath.PathElement) (x : PE) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ isMapRep tp fl em rel ∗ isPE pe x ∗
        ⌜(fl.map (·.1)).Nodup⌝ }}
      (App (App (Val (@! _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.typeRefAtPath)) (Val #tp)) (Val #pe))
    {{ (tr : schema.TypeRef) (ok : Bool), RET (PairV #tr #ok);
        match reconChild S t x with
        | none => iprop(⌜ok = false⌝)
        | some t' => iprop(⌜ok = true⌝ ∗ isTypeRef tr t') }} := by
  iintro %Φ ⟨#Hpkg, #Hm, #Hpe, %Hnd⟩ HΦ
  wp_apply h_typeRefAtPath tp fl em rel pe x $$ [] as %tr %ok H
  · iframe #; ipureintro; exact Hnd
  iapply HΦ
  cases x <;> simp only [reconChild, hfind] <;> iexact H

theorem typed.reconcileWithSchemaWalker.visitMapItems.wp_proofBody
    (h_PathElementSet_Has : fieldpath.PathElementSet.Has.spec (GF := GF))
    (h_PathElementSet_Iterate : fieldpath.PathElementSet.Iterate.spec (GF := GF))
    (h_SetNodeMap_Get : fieldpath.SetNodeMap.Get.spec (GF := GF))
    (h_SetNodeMap_Iterate : fieldpath.SetNodeMap.Iterate.spec (GF := GF))
    (h_reconcileWithSchemaWalker_finishDescent : typed.reconcileWithSchemaWalker.finishDescent.spec (GF := GF))
    (h_reconcileWithSchemaWalker_prepareDescent : typed.reconcileWithSchemaWalker.prepareDescent.spec (GF := GF))
    (h_typeRefAtPath : typed.typeRefAtPath.spec (GF := GF)) :
    typed.reconcileWithSchemaWalker.visitMapItems.specBody (GF := GF) := by
  unfold typed.reconcileWithSchemaWalker.visitMapItems.specBody typed.reconcileWithSchemaWalkerRec.specI
    typed.reconcileWithSchemaWalker.reconcile.specI typed.reconcileWithSchemaWalker.doList.specI
    typed.reconcileWithSchemaWalker.doMap.specI typed.reconcileWithSchemaWalker.visitListItems.specI
    typed.reconcileWithSchemaWalker.visitMapItems.specI
  iintro #IH
  icases IH with ⟨-, -, #Hrec, -, -⟩
  iintro %w %sc %S %st %ps %R %A %tp %fl %em %rel %ep %F %sp
  wp_start as ⟨Hown, #Hm, #HF, %Hpre⟩
  obtain ⟨Hfind, Hrel, Hcard⟩ := Hpre
  iunfold rwOwnAt at Hown
  icases Hown with ⟨%fs, %tv, %rem, %add, Hcore, Hp, #Hfs, #Hrem, #Hadd, Hsp⟩
  iunfold rwCore at Hcore
  icases Hcore with ⟨%tr, Hw, #Htr, #Hsc, %Hwf⟩
  icases isSet_split_law_holds ep F $$ HF with ⟨#Hmem, #Hch⟩
  have hg : isGranularT S st.t = true := by simp [isGranularT, Hfind, Hrel]
  have Hnd := LawB.map_fields_nodup S Hwf _ fl em rel Hfind
  wp_auto
  ipersist v
  ipersist t
  ipersist element
  ipersist handleElement
  generalize hf : (func.mk BAnon (BNamed "pe") _ : GoFunc) = f at *
  -- `handleElement(pe, isMember)`: the child at `pe` visited, its contribution added
  ihave #Hhe : (□ ∀ (pe : fieldpath.PathElement) (x : PE) (b : Bool) (L : List PE),
      {{ isPE pe x ∗ LawBR.rwVisit errs_ptr w sc S st ps fs tv sp
           (optU R (LawBR.reconKids S st.t st.path F L)) (optU A (LawBR.reconKids S st.t st.path F L)) ∗
         ⌜b = false → x ∈ F.heads⌝ }}
        (App (App (Val #f) (Val #pe)) (Val #b))
      {{ RET #(); LawBR.rwVisit errs_ptr w sc S st ps fs tv sp
           (optU R (LawBR.reconKids S st.t st.path F (L ++ [x])))
           (optU A (LawBR.reconKids S st.t st.path F (L ++ [x]))) }} : IProp GF) $$ []
  · iintro !> %pe %x %b %L %Φ' !> ⟨#Hpe, Hst, %Hb⟩ HΦ'
    rw [← hf, ← recv_eq_func_mk]
    wp_auto
    wp_apply typed.reconcileWithSchemaWalker.typeRefAtPath_reconChild h_typeRefAtPath S st.t tp fl em rel Hfind
      pe x $$ [] as %trv %okt Htrp
    · iframe #; ipureintro; exact Hnd
    cases hcx : reconChild S st.t x with
    | none =>
      -- no type for `pe`: ignored
      icases Htrp with %Hokt
      subst Hokt
      wp_auto
      iapply HΦ'
      have hk : LawBR.reconKid S st.t st.path F x = none := by simp [LawBR.reconKid, hcx]
      simp only [LawBR.reconKids_snoc, hk, LawB.optU_none_r]
      iexact Hst
    | some e =>
      icases Htrp with ⟨%Hokt, #Htrv⟩
      subst Hokt
      have hres : (S.find e.name).isSome := LawBR.reconChild_resolves S Hwf st.t _ Hfind x e hcx
      iunfold LawBR.rwVisit at Hst
      icases Hst with ⟨%sp1, %rem1, %add1, %el, errs, Herrs, Hcore, Hp, #Hrem1, #Hadd1, Hsp, %Hsp1⟩
      wp_auto
      wp_apply h_reconcileWithSchemaWalker_prepareDescent w sc S st ps fs tv rem1 add1 sp1 pe x trv e
        $$ [Hcore Hp Hsp] as %w2 ⟨%sp', %ps2, Hcore, Hcore2, Hp2, Hundo, Hsp, %Hspn⟩
      · iframe; iframe #
      iunfold rwCore at Hcore2
      icases Hcore2 with ⟨%tr2, Hw2, #Htr2, -, -⟩
      wp_apply h_SetNodeMap_Get _ F.deep pe x $$ [] as %q %ok ⟨%Hok, Hq⟩
      · iframe #
      ihave #Hq : isSetO q (LawBR.childSet F x ok) $$ [Hq]
      · unfold LawBR.childSet isSetO
        cases ok
        · simp only [Bool.false_eq_true, ↓reduceIte]; iexact Hq
        · simp only [↓reduceIte]; iexact Hq
      have hX := LawBR.reconKid_eq S st.t st.path F x e hcx b ok Hok Hb
      have hat := LawBR.childSet_atomic F x b ok
      have hcd := LawBR.childSet_card F x ok (2 ^ 63) (by decide) Hcard
      cases hbv : b
      all_goals
        wp_auto
        wp_apply Hrec $$ %w2 %sc %S %(RWSt.mk e (st.path ++ [x]) (b && !ok)) %ps2 %(LawBR.childSet F x ok)
            %(optU R (LawBR.reconKids S st.t st.path F L)) %(optU A (LawBR.reconKids S st.t st.path F L)) %sp'
            [Hw2 Hp2 Hsp] as %errs2 ⟨Herrs2, %R', %A', ⟨%sp'', Hown2, %Hsp''⟩, %HRA⟩
        · iframe #
          isplitl
          · unfold rwOwnAt rwCore
            iexists q, tv, rem1, add1
            iframe
            isplitl [Hw2]
            · iexists tr2
              rw [hbv]
              simp only [Bool.true_and, Bool.false_and]
              iframe
              iframe #
              ipureintro; exact Hwf
            iframe #
          ipureintro
          exact ⟨hres, hat, hcd⟩
        have hsp2 : sp'' = sp' := Hsp'' Hspn.1
        subst sp''
        wp_apply LawA2.wp_append_noErrs el errs2 $$ [Herrs Herrs2] as %el' Hel'
        · iframe
        iunfold rwOwnAt at Hown2
        icases Hown2 with ⟨%fs3, %tv3, %rem2, %add2, Hcore2, Hp3, -, #Hrem2, #Hadd2, Hsp⟩
        ihave %Hcap : ⌜0 ≤ sint.Z ps2.cap⌝ $$ [Hp3]
        · iunfold ownPath at Hp3
          icases Hp3 with ⟨-, Hpc⟩
          ihave %Hw := ownSliceCap_wf _ _ $$ Hpc
          ipureintro; omega
        wp_apply h_reconcileWithSchemaWalker_finishDescent w w2 sc S st (RWSt.mk e (st.path ++ [x]) (b && !ok))
            ps ps2 fs tv rem1 add1 fs3 tv3 rem2 add2 sp' (optU R (LawBR.reconKids S st.t st.path F L))
            (optU A (LawBR.reconKids S st.t st.path F L)) R' A'
          $$ [Hcore Hcore2 Hsp] as ⟨%rem', %add', Hcore, #Hrem', #Hadd', Hsp⟩
        · iframe; iframe #; ipureintro; exact ⟨Hspn.1, Hcap⟩
        ihave Hp := Hundo $$ Hp3
        try wp_auto
        iapply HΦ'
        iunfold LawBR.rwVisit
        have hR := LawBR.kids_step S st.t st.path F L x R R' _ HRA.1 hX
        have hA := LawBR.kids_step S st.t st.path F L x A A' _ HRA.2 hX
        rw [← hR, ← hA]
        iexists sp', rem', add', el'
        iframe
        iframe #
        ipureintro
        intro h
        have h1 := Hsp1 h; subst h1; exact Hspn.2 h
  -- `element.Children.Iterate`: the children not members, each visited
  wp_apply h_SetNodeMap_Iterate _ F.deep _
    (fun done => iprop(∃ L : List PE, ⌜∀ y, y ∈ done → y ∈ L ∨ y ∈ F.tops⌝ ∗
      LawBR.rwVisit errs_ptr w sc S st ps fs tv sp
        (optU R (LawBR.reconKids S st.t st.path F L)) (optU A (LawBR.reconKids S st.t st.path F L))))
    $$ [errs Hw Hp Hsp] as ⟨%done1, %Hd1, %L1, %HL1, Hst⟩
  · iframe #
    isplitl
    · iexists []
      isplitr
      · ipureintro; intro y hy; simp at hy
      rw [LawBR.reconKids_nil, LawB.optU_none_r, LawB.optU_none_r]
      iunfold LawBR.rwVisit
      iexists sp, rem, add, slice.nil
      iframe
      iframe #
      isplitr
      · iapply noErrs_nil
      isplitl
      · unfold rwCore; iexists tr; iframe; iframe #; ipureintro; exact Hwf
      ipureintro; intro _; rfl
    iintro !> %done %pe %x %Hx %Φ' !> ⟨⟨%L, %HL, Hst⟩, #Hpe⟩ HΦ'
    simp only [← recv_eq_func_mk]
    wp_call
    wp_auto
    wp_apply h_PathElementSet_Has _ DFrac.discard F.tops pe x $$ [] as %r ⟨-, %Hr⟩
    · iframe #
    wp_if_destruct
    · try wp_auto
      wp_apply Hhe $$ %pe %x %false %L [Hst] as Hst
      · iframe; iframe #
        ipureintro; intro _; rw [← LawBR.deep_heads]; exact Hx.1
      iapply HΦ'
      iexists (L ++ [x])
      iframe
      ipureintro
      intro y hy
      rcases List.mem_append.1 hy with hy | hy
      · rcases HL y hy with h | h
        · exact Or.inl (List.mem_append_left _ h)
        · exact Or.inr h
      · exact Or.inl (List.mem_append_right _ hy)
    · skip
      iapply HΦ'
      iexists L
      iframe
      ipureintro
      intro y hy
      rcases List.mem_append.1 hy with hy | hy
      · exact HL y hy
      · simp at hy; subst hy; exact Or.inr (Hr.1 rfl)
  have Hc1 : ∀ y, y ∈ F.heads → y ∈ L1 ∨ y ∈ F.tops := by
    intro y hy
    apply HL1
    rw [← FSet.mem_ofList', Hd1.2, LawBR.deep_heads]; exact hy
  -- `element.Members.Iterate`: the members, each visited
  wp_apply h_PathElementSet_Iterate _ DFrac.discard F.tops _
    (fun done => iprop(∃ L : List PE, ⌜(∀ y, y ∈ F.heads → y ∈ L ∨ y ∈ F.tops) ∧ ∀ y, y ∈ done → y ∈ L⌝ ∗
      LawBR.rwVisit errs_ptr w sc S st ps fs tv sp
        (optU R (LawBR.reconKids S st.t st.path F L)) (optU A (LawBR.reconKids S st.t st.path F L))))
    $$ [Hst] as ⟨-, %done2, %Hd2, %L2, %HL2, Hst⟩
  · iframe #
    isplitl
    · iexists L1
      iframe
      ipureintro
      exact ⟨Hc1, fun y hy => by simp at hy⟩
    iintro !> %done %pe %x %Hx %Φ' !> ⟨⟨%L, %HL, Hst⟩, #Hpe⟩ HΦ'
    simp only [← recv_eq_func_mk]
    wp_call
    wp_auto
    wp_apply Hhe $$ %pe %x %true %L [Hst] as Hst
    · iframe; iframe #
      ipureintro; intro h; cases h
    iapply HΦ'
    iexists (L ++ [x])
    iframe
    ipureintro
    refine ⟨fun y hy => ?_, fun y hy => ?_⟩
    · rcases HL.1 y hy with h | h
      · exact Or.inl (List.mem_append_left _ h)
      · exact Or.inr h
    · rcases List.mem_append.1 hy with hy | hy
      · exact List.mem_append_left _ (HL.2 y hy)
      · exact List.mem_append_right _ hy
  have Hc2 : ∀ y, y ∈ F.heads → y ∈ L2 := by
    intro y hy
    rcases HL2.1 y hy with h | h
    · exact h
    · apply HL2.2
      rw [← FSet.mem_ofList', Hd2.2]; exact h
  iunfold LawBR.rwVisit at Hst
  icases Hst with ⟨%sp1, %rem1, %add1, %el, errs, Herrs, Hcore, Hp, #Hrem1, #Hadd1, Hsp, %Hsp1⟩
  wp_auto
  iapply HΦ
  iframe Herrs
  iexists (optU R (LawBR.reconKids S st.t st.path F L2)), (optU A (LawBR.reconKids S st.t st.path F L2))
  isplitl
  · iexists sp1
    isplitl; rotate_left
    · ipureintro; exact Hsp1
    unfold rwOwnAt
    iexists fs, tv, rem1, add1
    iframe
    iframe #
  ipureintro
  exact ⟨LawBR.kids_final S st.t st.path F L2 R hg Hc2, LawBR.kids_final S st.t st.path F L2 A hg Hc2⟩

end proof

end smd
end EtcdGrove
end Perennial
