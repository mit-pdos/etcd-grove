/-
`typed.validatingObjectWalker.visitListItems`: a member of the recursion cluster `typed.validatingObjectWalkerRec` (`validatingObjectWalkerRec.lean`); its proof is the
projection of the cluster's (its body is `validatingObjectWalker__visitListItemsBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.validatingObjectWalker__visitListItemsBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.MakePathElementSet
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElementSet__Has
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElementSet__Insert
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.heapAllocator__Free
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.freelistAllocator__Free
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__AtUsing
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__AtUsing_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__Length
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__Length_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.listItemToPathElement
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.validatingObjectWalker__finishDescent
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.validatingObjectWalker__prepareDescent
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__At
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__At_ptr
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsA
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsA2
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsAPure
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsBPers
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsB2
public import Proof.sigs_k8s_io.structured_merge_diff.v7.schema.LawProofs
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.LawProofsDispatch
public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsRep

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

theorem typed.validatingObjectWalker.visitListItems.wp_proofBody
    (h_MakePathElementSet : fieldpath.MakePathElementSet.spec (GF := GF))
    (h_PathElementSet_Has : fieldpath.PathElementSet.Has.spec (GF := GF))
    (h_PathElementSet_Insert : fieldpath.PathElementSet.Insert.spec (GF := GF))
    (h_heapAllocator_Free : value.heapAllocator.Free.spec (GF := GF))
    (h_freelistAllocator_Free : value.freelistAllocator.Free.spec (GF := GF))
    (h_listUnstructured_AtUsing : value.listUnstructured.AtUsing.spec (GF := GF))
    (h_listUnstructured_AtUsing_ptr : value.listUnstructured.AtUsing_ptr.spec (GF := GF))
    (h_listUnstructured_Length : value.listUnstructured.Length.spec (GF := GF))
    (h_listUnstructured_Length_ptr : value.listUnstructured.Length_ptr.spec (GF := GF))
    (h_listItemToPathElement : typed.listItemToPathElement.spec (GF := GF))
    (h_validatingObjectWalker_finishDescent : typed.validatingObjectWalker.finishDescent.spec (GF := GF))
    (h_validatingObjectWalker_prepareDescent : typed.validatingObjectWalker.prepareDescent.spec (GF := GF))
    (h_listUnstructured_At : value.listUnstructured.At.spec (GF := GF))
    (h_listUnstructured_At_ptr : value.listUnstructured.At_ptr.spec (GF := GF)) :
    typed.validatingObjectWalker.visitListItems.specBody (GF := GF) := by
  unfold typed.validatingObjectWalker.visitListItems.specBody typed.validatingObjectWalkerRec.specI
    typed.validatingObjectWalker.validate.specI typed.validatingObjectWalker.doList.specI
    typed.validatingObjectWalker.doMap.specI typed.validatingObjectWalker.visitListItems.specI
    typed.validatingObjectWalker.visitMapItems.specI
  iintro #IH
  icases IH with ⟨-, -, #HV, -, -⟩
  iintro %w %sc %S %st %tp %e %rel %ks %ll %vs %sp
  wp_start as ⟨Hown, #Hl, Hlv, %Hpre⟩
  obtain ⟨Hfind, Hc⟩ := Hpre
  ihave #Hlv := isListV_persistent_law_holds ll vs $$ Hlv
  icases LawA2.isListV_dispatchA h_listUnstructured_Length h_listUnstructured_Length_ptr
    h_listUnstructured_AtUsing h_listUnstructured_AtUsing_ptr h_listUnstructured_At
    h_listUnstructured_At_ptr ll vs $$ [] with ⟨%li, %Hli, #HLen, #HAtU, -⟩
  · iframe #; iPkgInit
  subst Hli
  iunfold vwOwn at Hown
  icases Hown with ⟨Hcore, Hsp, Ha⟩
  iunfold vwCore at Hcore
  icases Hcore with ⟨%tr0, Hw, #Htr0, #Hsc, %Hwf⟩
  icases isListRep_elim_law_holds tp e rel ks $$ Hl with ⟨%lv, %ksl, #Hlv0, %Hlv', #Hks, #Het⟩
  ihave ⟨Hlv2, %Hnn⟩ := typedPointsto_not_null_dup _ _ _ $$ Hlv0
  iStructNamed Hlv2
  ihave ⟨Ha, %ia, %Hia, #Hfree⟩ := isAlloc_Free h_heapAllocator_Free h_freelistAllocator_Free st.alloc $$ [Ha]
  · iframe Ha; iPkgInit
  wp_auto
  wp_bind (App (Val wrapDefer) _)
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  wp_apply HLen as %n %Hn
  wp_apply h_MakePathElementSet n $$ [] as %ov Hov
  · ipureintro; show 0 ≤ n.toInt; omega
  try wp_auto
  ipersist v
  ipersist t
  ipersist list
  have hlen63 : vs.length < 2 ^ 63 := by have := n.toInt_lt; omega
  ihave Hw : vwCore w sc S st sp st.alloc $$ [Hw]
  · unfold vwCore; iexists tr0; iframe; iframe #; ipureintro; exact Hwf
  ihave HI : (∃ (ip : Loc) (j : w64) (el : GoSlice) (fk : GoFunc) (cs : List GoInterface)
      (ovv : fieldpath.PathElementSet) (O : FSet PE) (sp1 : Loc),
      "iter" ∷ «$iter_i_ptr» ↦ ip ∗ "i" ∷ ip ↦ j ∗
      "errs" ∷ errs_ptr ↦ el ∗ "Herrs" ∷ noErrs el ∗
      "defer" ∷ defer ↦ fk ∗ "Hfs" ∷ ([∗list] c ∈ cs, freeable c) ∗
      "#HD" ∷ □ (∀ Ψ : val → IProp GF, isAlloc (GoInterface.ok ia) -∗ ([∗list] c ∈ cs, freeable c) -∗
        (isAlloc (GoInterface.ok ia) -∗ Ψ #()) -∗ WP (App (Val #fk) (Val #())) {{ Ψ }}) ∗
      "obs" ∷ observedKeys_ptr ↦ ovv ∗ "Hov" ∷ ownPESetV ovv O ∗
      "%HO" ∷ ⌜∀ p, p ∈ O → p ∈ keysOf ks (vs.take (sint.nat j))⌝ ∗
      "Hw" ∷ vwCore w sc S st sp1 st.alloc ∗
      "Hsp" ∷ spareWalkers typed.validatingObjectWalker sp1 ∗ "%Hsp1" ∷ ⌜sp ≠ null → sp1 = sp⌝ ∗
      "Ha" ∷ isAlloc st.alloc ∗ "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ vs.length⌝ : IProp GF)
    $$ [«$iter_i» i errs defer Hov observedKeys Hw Hsp Ha]
  · iexists _, _, _, _, [], _, _, sp
    iframe
    isplitr
    · iapply noErrs_nil
    isplitr
    · iapply BigSepL.bigSepL_nil.2; itrivial
    isplitr
    · imodintro
      iintro %Ψ Ha - HΨ
      simp only [← recv_eq_func_mk]
      wp_call
      iapply HΨ; iexact Ha
    ipureintro
    refine ⟨?_, fun _ => rfl, by decide, by simp⟩
    intro p hp
    exact absurd ((FSet.mem_ofList' _ _).1 hp) (by simp)
  wp_for HI
  iunfold vwCore at Hw
  icases Hw with ⟨%tr1, Hw, #Htr1, -, -⟩
  wp_apply HLen as %n2 %Hn2
  try wp_auto
  wp_if_destruct
  · have hjl : sint.nat j < vs.length := by
      have : sint.Z j < sint.Z n2 := by simpa using intoVal_eq_iff.1 Hif
      show (sint.Z j).toNat < vs.length
      have h2 : sint.Z n2 = vs.length := Hn2
      omega
    have hjZ : sint.Z j < vs.length := by
      have : sint.Z j < sint.Z n2 := by simpa using intoVal_eq_iff.1 Hif
      have h2 : sint.Z n2 = vs.length := Hn2
      omega
    have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
    obtain ⟨x, hx⟩ : ∃ x, vs[sint.nat j]? = some x := ⟨vs[sint.nat j], List.getElem?_eq_getElem hjl⟩
    wp_apply HAtU $$ %st.alloc %j %x [Ha] as %child ⟨Ha, Hch⟩
    · iframe; ipureintro; exact ⟨Hj.1, hx⟩
    rw [Hia]
    wp_auto
    rw [Hlv'.1]
    obtain ⟨hall, hassoc⟩ := conforms_item_law_holds S st.t e rel ks vs Hfind Hc
    have hxin : x ∈ vs := List.mem_of_getElem? hx
    have hcx : conforms S e x := hall x hxin
    have hsubj : ∀ p, p ∈ keysOf ks (vs.take (sint.nat j)) →
        p ∈ keysOf ks (vs.take (sint.nat j + 1)) := by
      intro p hp; rw [LawA2.keysOf_take_succ ks vs _ x hx]; exact List.mem_append_left _ hp
    wp_join iprop(∃ (pev : fieldpath.PathElement) (ovv' : fieldpath.PathElementSet) (O' : FSet PE),
        pe_ptr ↦ pev ∗ observedKeys_ptr ↦ ovv' ∗ ownPESetV ovv' O' ∗
        ⌜∀ p, p ∈ O' → p ∈ keysOf ks (vs.take (sint.nat j + 1))⌝ ∗ isAlloc st.alloc ∗
        isValF child (DFrac.own 1) x ∗ child_ptr ↦ child ∗
        w ↦ (typed.validatingObjectWalker.mk st.value sc tr1 false sp1 st.alloc))
      with [pe obs Hov Ha Hch Hw child] as ⟨%pev, %ovv', %O', pe, obs, Hov, %HO', Ha, Hch, child, Hw⟩
    all_goals first
      | (iexists _, _, O; rw [Hia]; iframe; ipureintro; exact fun p hp => hsubj p (HO p hp))
      | skip
    · have hr : rel = .associative := by
        cases rel <;> simp_all [ElemRel.goName] <;> exact absurd Hif (by decide)
      subst hr
      obtain ⟨hks, hnd⟩ := hassoc rfl
      obtain ⟨-, hksnd, fs, em, rel', hfe, -⟩ := LawB.list_wf S Hwf st.t e .associative ks Hfind (by decide)
      obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 (show (keyOf ks x).isSome from hks x hxin)
      have hkne : ks ≠ [] := by rintro rfl; simp [keyOf] at hk; split at hk <;> simp_all
      try wp_auto
      wp_apply h_listItemToPathElement (GoInterface.ok ia) sc S tp e ks fs em rel' child (DFrac.own 1) x st.t.name
        $$ [Ha Hch] as %pe1 %err Hpost
      · iframe; iframe #; ipureintro; exact ⟨Hwf, hkne, hfe, Hfind, hcx, by rw [hk]; rfl⟩
      rw [hk]
      icases Hpost with ⟨Ha, Hch, %herr, #Hpe1⟩
      subst herr
      wp_auto
      have hkO : k ∉ O := fun h => LawA2.keyOf_fresh ks vs _ x k hnd hx hk (HO k h)
      ihave ⟨Hset, Hback⟩ := LawA2.ownPESet_lend observedKeys_ptr ovv O $$ [obs Hov]
      · iframe
      wp_apply h_PathElementSet_Has observedKeys_ptr _ O pe1 k $$ [Hset] as %r ⟨Hset, %hr⟩
      · iframe; iframe #
      have hrf : r = false := by cases r <;> simp_all
      subst hrf
      icases Hback $$ Hset with ⟨%ovv1, obs, Hov⟩
      wp_auto
      wp_apply h_PathElementSet_Insert observedKeys_ptr O pe1 k $$ [obs Hov] as Hset
      · iframe #
        isplitl
        · unfold ownPESet; iexists ovv1; iframe
        ipureintro
        apply LawA2.cardLt_of_sub O (keysOf ks (vs.take (sint.nat j))) _ HO
        have := LawA2.keysOf_take_length ks vs (sint.nat j); omega
      unfold ownPESet
      icases Hset with ⟨%ovv2, obs, Hov⟩
      isplitr
      · ipureintro; rfl
      iexists pe1, ovv2, _
      rw [Hia]
      iframe
      ipureintro
      intro p hp
      rw [LawA2.keysOf_take_succ ks vs _ x hx, hk]
      rcases (FSet.mem_union' _ _ _).1 hp with h | h
      · exact List.mem_append_left _ (HO p h)
      · have := (FSet.mem_ofList' _ _).1 h
        simp at this; subst this; simp
    have hfe : (S.find e.name).isSome := LawA.conforms_find S e x hcx
    wp_apply h_validatingObjectWalker_prepareDescent w sc S st sp1 st.alloc lv.ElementType' e $$ [Hw Hsp]
      as %w2 ⟨%sp', Hcore, Hcore2, Hsp, %Hspn, %Hspe⟩
    · iframe #; iframe; unfold vwCore; iexists tr1; iframe; iframe #; ipureintro; exact Hwf
    iunfold vwCore at Hcore2
    icases Hcore2 with ⟨%tr2, Hw2, #Htr2, -, -⟩
    wp_auto
    wp_apply HV $$ %w2 %sc %S %(VWSt.mk child e st.alloc) %(DFrac.own 1) %x %_ %sp' [Hw2 Hsp Ha Hch]
      as %errs2 ⟨Herrs2, Hch, %sp'', Hown2, %Hsp''⟩
    · iframe Hch
      isplitl [Hw2 Hsp Ha]
      · unfold vwOwn vwCore
        iframe Hsp Ha
        iexists tr2
        iframe Hw2
        iframe #
        ipureintro; exact Hwf
      ipureintro; exact ⟨hfe, hcx⟩
    have hsp2 := (Hsp'' Hspn).symm
    subst hsp2
    wp_apply LawA2.wp_append_noErrs el errs2 $$ [Herrs Herrs2] as %el' Hel'
    · iframe
    unfold vwOwn
    icases Hown2 with ⟨Hcore2, Hsp, Ha⟩
    wp_apply h_validatingObjectWalker_finishDescent w w2 sc S st (VWSt.mk child e st.alloc) sp' st.alloc
      $$ [Hcore Hcore2 Hsp] as ⟨Hcore, Hsp⟩
    · iframe; ipureintro; exact Hspn
    try wp_auto
    wp_for_post
    simp only [Hia]
    ihave Hfr := isValF_freeable_law_holds _ _ $$ Hch
    iframe
    iexists _, _, el', _, (child :: cs), ovv', O', sp'
    iframe
    isplitr
    · imodintro
      iintro %Ψ Ha ⟨Hc, Hcs⟩ HΨ
      simp only [← recv_eq_func_mk]
      wp_call
      wp_apply Hfree $$ %_ [Ha Hc] as Ha
      · iframe
      try wp_auto
      iapply HD $$ Ha Hcs HΨ
    ipureintro
    refine ⟨?_, fun h => (Hspe (by have := Hsp1 h; subst this; exact h)).trans (Hsp1 h), ?_⟩
    · intro p hp
      rw [hj1]; exact HO' p hp
    · constructor <;> word
  · have hd : decide (sint.Z j < sint.Z n2) = false := by
      cases h : decide (sint.Z j < sint.Z n2) <;> simp_all
    rw [hd]
    simp only [Bool.false_eq_true, ↓reduceIte]
    wp_auto
    rw [Hia]
    wp_bind (App (Val #fk) _)
    iapply HD $$ Ha Hfs
    iintro Ha
    wp_auto
    iapply HΦ
    iframe
    iexists sp1
    unfold vwOwn vwCore
    rw [Hia]
    iframe
    isplitl
    · iframe #; ipureintro; exact Hwf
    ipureintro; exact Hsp1

end proof

end smd
end EtcdGrove
end Perennial
