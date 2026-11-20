/-
`typed.toFieldSetWalker.visitListItems`: a member of the recursion cluster `typed.toFieldSetWalkerRec` (`toFieldSetWalkerRec.lean`); its proof is the
projection of the cluster's (its body is `toFieldSetWalker__visitListItemsBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.toFieldSetWalker__visitListItemsBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.MakePathElementSet
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElementSet__Has
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElementSet__Insert
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__Insert
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__At
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__At_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__Length
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__Length_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.listItemToPathElement
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

set_option synthInstance.maxHeartbeats 200000 in
set_option synthInstance.maxSize 4096 in
theorem typed.toFieldSetWalker.visitListItems.wp_proofBody
    (h_MakePathElementSet : fieldpath.MakePathElementSet.spec (GF := GF))
    (h_PathElementSet_Has : fieldpath.PathElementSet.Has.spec (GF := GF))
    (h_PathElementSet_Insert : fieldpath.PathElementSet.Insert.spec (GF := GF))
    (h_Set_Insert : fieldpath.Set.Insert.spec (GF := GF))
    (h_listUnstructured_At : value.listUnstructured.At.spec (GF := GF))
    (h_listUnstructured_At_ptr : value.listUnstructured.At_ptr.spec (GF := GF))
    (h_listUnstructured_Length : value.listUnstructured.Length.spec (GF := GF))
    (h_listUnstructured_Length_ptr : value.listUnstructured.Length_ptr.spec (GF := GF))
    (h_listItemToPathElement : typed.listItemToPathElement.spec (GF := GF))
    (h_toFieldSetWalker_finishDescent : typed.toFieldSetWalker.finishDescent.spec (GF := GF))
    (h_toFieldSetWalker_prepareDescent : typed.toFieldSetWalker.prepareDescent.spec (GF := GF)) :
    typed.toFieldSetWalker.visitListItems.specBody (GF := GF) := by
  unfold typed.toFieldSetWalker.visitListItems.specBody typed.toFieldSetWalkerRec.specI
    typed.toFieldSetWalker.toFieldSet.specI typed.toFieldSetWalker.doList.specI
    typed.toFieldSetWalker.doMap.specI typed.toFieldSetWalker.visitListItems.specI
    typed.toFieldSetWalker.visitMapItems.specI
  iintro #IH
  icases IH with ⟨-, -, #HT, -, -⟩
  iintro %w %sc %S %st %s %F %tp %e %ks %ll %vs %sp
  wp_start as ⟨Hown, #Hl, Hlv, %Hpre⟩
  obtain ⟨Hfind, Hc, Hcard⟩ := Hpre
  ihave #Hlv := isListV_persistent_law_holds ll vs $$ Hlv
  icases LawA3.isListV_dispatchL h_listUnstructured_Length h_listUnstructured_Length_ptr
    h_listUnstructured_At h_listUnstructured_At_ptr ll vs $$ [] with ⟨%li, %Hli, #HLen, #HAt⟩
  · iframe #; iPkgInit
  subst Hli
  iunfold twOwn at Hown
  icases Hown with ⟨%ps, Hcore, Hps, Hsp, Ha, Hs⟩
  iunfold twCore at Hcore
  icases Hcore with ⟨%tr0, Hw, #Htr0, #Hsc, %Hwf⟩
  icases isListRep_elim_law_holds tp e .associative ks $$ Hl with ⟨%lv, %ksl, #Hlv0, %Hlv', #Hks, #Het⟩
  ihave ⟨Hlv2, %Hnn⟩ := typedPointsto_not_null_dup _ _ _ $$ Hlv0
  iStructNamed Hlv2
  obtain ⟨hall, hassoc⟩ := conforms_item_law_holds S st.t e .associative ks vs Hfind Hc
  obtain ⟨hks, hnd⟩ := hassoc rfl
  obtain ⟨-, hksnd, fs, em, rel', hfe, -⟩ := LawB.list_wf S Hwf st.t e .associative ks Hfind (by decide)
  have hkne : ks ≠ [] := by
    rintro rfl
    have := LawB.list_wf S Hwf st.t e .associative [] Hfind (by decide)
    have hw := LawB.find_wf S Hwf _ _ Hfind
    simp [Atom.wf] at hw
  wp_auto
  wp_apply HLen as %n %Hn
  wp_apply h_MakePathElementSet n $$ [] as %ov1 Hov1
  · ipureintro; show 0 ≤ n.toInt; omega
  wp_apply HLen as %n' %Hn'
  wp_apply h_MakePathElementSet n' $$ [] as %ov2 Hov2
  · ipureintro; show 0 ≤ n'.toInt; omega
  try wp_auto
  ipersist v
  ipersist t
  ipersist list
  have hlen63 : vs.length < 2 ^ 63 := by have := n.toInt_lt; omega
  -- the first loop: the keys seen (all distinct: no duplicates)
  ihave HI1 : (∃ (j : w64) (ovv : fieldpath.PathElementSet) (O : FSet PE),
      "i" ∷ i_ptr ↦ j ∗ "seen" ∷ seen_ptr ↦ ovv ∗ "Hov1" ∷ ownPESetV ovv O ∗
      "%HO" ∷ ⌜∀ p, p ∈ O → p ∈ keysOf ks (vs.take (sint.nat j))⌝ ∗
      "Hw" ∷ w ↦ (typed.toFieldSetWalker.mk st.value sc tr0 s ps sp st.alloc) ∗
      "Ha" ∷ isAlloc st.alloc ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ vs.length⌝ : IProp GF)
    $$ [i seen Hov1 Hw Ha]
  · iexists _, _, _
    iframe
    ipureintro
    refine ⟨?_, by decide, by simp⟩
    intro p hp; exact absurd hp (FSet.mem_empty _)
  wp_for HI1
  wp_apply HLen as %n2 %Hn2
  try wp_auto
  wp_if_destruct
  · have hjZ : sint.Z j < vs.length := by
      have : sint.Z j < sint.Z n2 := by simpa using intoVal_eq_iff.1 Hif
      have h2 : sint.Z n2 = vs.length := Hn2
      omega
    have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
    have hjl : sint.nat j < vs.length := by have := Hj.1; word
    obtain ⟨x, hx⟩ : ∃ x, vs[sint.nat j]? = some x := ⟨vs[sint.nat j], List.getElem?_eq_getElem hjl⟩
    have hxin : x ∈ vs := List.mem_of_getElem? hx
    have hcx : conforms S e x := hall x hxin
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 (show (keyOf ks x).isSome from hks x hxin)
    wp_apply HAt $$ %j %x as %child Hch
    · ipureintro; exact ⟨Hj.1, hx⟩
    try wp_auto
    wp_apply h_listItemToPathElement st.alloc sc S tp e ks fs em rel' child (DFrac.own 1) x st.t.name
      $$ [Ha Hch] as %pe1 %err Hpost
    · iframe; iframe #; ipureintro; exact ⟨Hwf, hkne, hfe, Hfind, hcx, by rw [hk]; rfl⟩
    rw [hk]
    icases Hpost with ⟨Ha, -, %herr, #Hpe1⟩
    subst herr
    try wp_auto
    have hkO : k ∉ O := fun h => LawA2.keyOf_fresh ks vs _ x k hnd hx hk (HO k h)
    ihave ⟨Hset, Hback⟩ := LawA2.ownPESet_lend seen_ptr ovv O $$ [seen Hov1]
    · iframe
    wp_apply h_PathElementSet_Has seen_ptr _ O pe1 k $$ [Hset] as %r ⟨Hset, %hr⟩
    · iframe; iframe #
    have hrf : r = false := by cases r <;> simp_all
    subst hrf
    icases Hback $$ Hset with ⟨%ovv1, seen, Hov1⟩
    wp_auto
    wp_apply h_PathElementSet_Insert seen_ptr O pe1 k $$ [seen Hov1] as Hset
    · iframe #
      isplitl
      · unfold ownPESet; iexists ovv1; iframe
      ipureintro
      apply LawA2.cardLt_of_sub O (keysOf ks (vs.take (sint.nat j))) _ HO
      have := LawA2.keysOf_take_length ks vs (sint.nat j); omega
    unfold ownPESet
    icases Hset with ⟨%ovv2, seen, Hov1⟩
    try wp_auto
    wp_for_post
    iframe
    iexists _, ovv2, _
    iframe
    ipureintro
    refine ⟨?_, ?_, ?_⟩
    · intro p hp
      rw [hj1, LawA2.keysOf_take_succ ks vs _ x hx, hk]
      rcases (FSet.mem_union' _ _ _).1 hp with h | h
      · exact List.mem_append_left _ (HO p h)
      · have := (FSet.mem_ofList' _ _).1 h
        simp at this; subst this; simp
    · word
    · word
  · have hd : decide (sint.Z j < sint.Z n2) = false := by
      cases h : decide (sint.Z j < sint.Z n2) <;> simp_all
    rw [hd]
    simp only [Bool.false_eq_true, ↓reduceIte]
    wp_auto
    -- the second loop: each item's fields and path (no duplicates)
    ihave HI2 : (∃ (j : w64) (psj : fieldpath.Path) (spj : Loc) (trj : schema.TypeRef) (el : GoSlice)
        (ovd : fieldpath.PathElementSet),
        "i" ∷ i_ptr ↦ j ∗ "errs" ∷ errs_ptr ↦ el ∗ "Herrs" ∷ noErrs el ∗
        "Hw" ∷ w ↦ (typed.toFieldSetWalker.mk st.value sc trj s psj spj st.alloc) ∗
        "#Htrj" ∷ isTypeRef trj st.t ∗
        "Hps" ∷ ownPath psj st.path ∗ "Hsp" ∷ spareWalkers typed.toFieldSetWalker spj ∗
        "%Hspj" ∷ ⌜sp ≠ null → spj = sp⌝ ∗ "Ha" ∷ isAlloc st.alloc ∗
        "Hs" ∷ ownSet s (PathSet.union F (fieldsL S e ks st.path (vs.take (sint.nat j)))) ∗
        "dup" ∷ duplicates_ptr ↦ ovd ∗ "Hov2" ∷ ownPESetV ovd FSet.empty ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ vs.length⌝ : IProp GF)
      $$ [i errs Hw Hps Hsp Ha Hs duplicates Hov2]
    · iexists _, _, _, _, _, _
      iframe
      isplitr
      · iapply noErrs_nil
      have h0 : vs.take (sint.nat (W64 0)) = [] := by simp
      rw [h0]
      simp only [fieldsL, LawB.ps_union_empty]
      iframe; iframe #
      ipureintro; refine ⟨by simp, by decide, by simp⟩
    wp_for HI2
    wp_apply HLen as %n3 %Hn3
    try wp_auto
    wp_if_destruct
    · have hjZ : sint.Z j < vs.length := by
        have : sint.Z j < sint.Z n3 := by simpa using intoVal_eq_iff.1 Hif
        have h2 : sint.Z n3 = vs.length := Hn3
        omega
      have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
      have hjl : sint.nat j < vs.length := by have := Hj.1; word
      obtain ⟨x, hx⟩ : ∃ x, vs[sint.nat j]? = some x := ⟨vs[sint.nat j], List.getElem?_eq_getElem hjl⟩
      have hxin : x ∈ vs := List.mem_of_getElem? hx
      have hcx : conforms S e x := hall x hxin
      obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 (show (keyOf ks x).isSome from hks x hxin)
      have hstep := LawA3.fieldsL_step F S e ks st.path vs (sint.nat j) x k hx hk
      have hsubF : ∀ q, q ∈ PathSet.union F (fieldsL S e ks st.path (vs.take (sint.nat j + 1))) →
          q ∈ PathSet.union F (fieldsL S e ks st.path vs) := by
        intro q hq
        rcases (LawA3.mem_pu _ _ _).1 hq with h | h
        · exact (LawA3.mem_pu _ _ _).2 (Or.inl h)
        · exact (LawA3.mem_pu _ _ _).2 (Or.inr (LawA3.fieldsL_take_sub _ _ _ _ _ _ _ h))
      rw [← hstep] at hsubF
      have hcard2 : (PathSet.union (PathSet.union F (fieldsL S e ks st.path (vs.take (sint.nat j))))
          (fieldsAt S e (st.path ++ [k]) x)).CardLt (2 ^ 63 - 1) :=
        LawA3.cardLt_sub _ _ _ (fun q hq => hsubF q ((LawA3.mem_pu _ _ _).2 (Or.inl hq))) Hcard
      wp_apply HAt $$ %j %x as %child Hch
      · ipureintro; exact ⟨Hj.1, hx⟩
      try wp_auto
      wp_apply h_listItemToPathElement st.alloc sc S tp e ks fs em rel' child (DFrac.own 1) x st.t.name
        $$ [Ha Hch] as %pe1 %err Hpost
      · iframe; iframe #; ipureintro; exact ⟨Hwf, hkne, hfe, Hfind, hcx, by rw [hk]; rfl⟩
      rw [hk]
      icases Hpost with ⟨Ha, Hch, %herr, #Hpe1⟩
      subst herr
      try wp_auto
      ihave ⟨Hset, Hback⟩ := LawA2.ownPESet_lend duplicates_ptr ovd FSet.empty $$ [dup Hov2]
      · iframe
      wp_apply h_PathElementSet_Has duplicates_ptr _ FSet.empty pe1 k $$ [Hset] as %r ⟨Hset, %hr⟩
      · iframe; iframe #
      have hrf : r = false := by
        cases r
        · rfl
        · exact absurd (hr.1 rfl) (FSet.mem_empty _)
      subst hrf
      icases Hback $$ Hset with ⟨%ovd1, dup, Hov2⟩
      try wp_auto
      wp_apply h_toFieldSetWalker_prepareDescent w sc S st psj s spj st.alloc pe1 k lv.ElementType' e
        $$ [Hw Hps Hsp] as %w2 ⟨%sp', %ps2, Hcore, Hcore2, Hps2, Hsp, %Hspn, %Hspe⟩
      · iframe; iframe #; unfold twCore; iexists trj; iframe; iframe #; ipureintro; exact Hwf
      iunfold twCore at Hcore2
      icases Hcore2 with ⟨%tr2, Hw2, #Htr2, -, -⟩
      try wp_auto
      wp_apply HT $$ %w2 %sc %S %(TWSt.mk child e (st.path ++ [k]) st.alloc) %s
        %(PathSet.union F (fieldsL S e ks st.path (vs.take (sint.nat j)))) %(DFrac.own 1) %x %sp'
        [Hw2 Hps2 Hsp Ha Hs Hch] as %errs2 ⟨Herrs2, Hch, %sp'', Hown2, %Hsp''⟩
      · iframe Hch
        isplitl [Hw2 Hps2 Hsp Ha Hs]
        · unfold twOwn twCore
          iexists ps2
          iframe
          iframe #
          ipureintro; exact Hwf
        ipureintro; exact ⟨hcx, hcard2⟩
      have hsp2 := (Hsp'' Hspn).symm
      subst hsp2
      wp_apply LawA2.wp_append_noErrs el errs2 $$ [Herrs Herrs2] as %el' Hel'
      · iframe
      unfold twOwn
      icases Hown2 with ⟨%ps3, Hcore2, Hps3, Hsp, Ha, Hs⟩
      iunfold twCore at Hcore2
      icases Hcore2 with ⟨%tr3, Hw2, #Htr3, -, -⟩
      try wp_auto
      unfold ownPath
      icases Hps3 with ⟨Hpf, Hpc⟩
      wp_apply h_Set_Insert s _ ps3 (DFrac.own 1) (st.path ++ [k]) $$ [Hs Hpf] as ⟨Hs, Hpf⟩
      · iframe; ipureintro; exact hcard2
      try wp_auto
      wp_apply h_toFieldSetWalker_finishDescent w w2 sc S st (TWSt.mk child e (st.path ++ [k]) st.alloc)
        psj ps3 s sp' st.alloc k $$ [Hcore Hw2 Hpf Hpc Hsp] as ⟨%ps4, Hcore, Hps4, Hsp⟩
      · iframe
        isplitl [Hw2]
        · unfold twCore; iexists tr3; iframe; iframe #; ipureintro; exact Hwf
        isplitl [Hpf Hpc]
        · unfold ownPath; iframe
        ipureintro; exact Hspn
      try wp_auto
      wp_for_post
      iunfold twCore at Hcore
      icases Hcore with ⟨%tr4, Hw, #Htr4, -, -⟩
      iframe
      iexists (j + W64 1), ps4, sp', tr4, el', ovd1
      rw [hj1, ← hstep]
      unfold ownPath
      iframe
      iframe #
      ipureintro
      refine ⟨fun h => ?_, ?_, ?_⟩
      · have h1 := Hspj h; subst h1; exact Hspe h
      · word
      · word
    · have hd : decide (sint.Z j < sint.Z n3) = false := by
        cases h : decide (sint.Z j < sint.Z n3) <;> simp_all
      rw [hd]
      simp only [Bool.false_eq_true, ↓reduceIte]
      wp_auto
      have hjk : sint.nat j = vs.length := by
        have : ¬ sint.Z j < sint.Z n3 := by simpa using hd
        have h2 : sint.Z n3 = vs.length := Hn3
        have := Hj.2
        word
      rw [hjk, List.take_length]
      iapply HΦ
      iframe
      iexists spj
      unfold ownPath
      iframe
      isplitl
      · unfold twOwn twCore ownPath
        iexists psj
        iframe
        iframe #
        ipureintro; exact Hwf
      ipureintro; exact Hspj

end proof

end smd
end EtcdGrove
end Perennial
