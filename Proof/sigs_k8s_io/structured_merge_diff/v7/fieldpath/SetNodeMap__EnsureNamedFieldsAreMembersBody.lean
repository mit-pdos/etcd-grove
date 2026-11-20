/-
`fieldpath.SetNodeMap.EnsureNamedFieldsAreMembers`' body (the recursion cluster
`fieldpath.EnsureNamedFieldsAreMembersRec`, `EnsureNamedFieldsAreMembersRec.lean`). A field element
has a nil `Key` (`fpE.isPE_field_key`), which Go's `else if pe.Key != nil && atom.List != nil` reads. Each child at
the type Go computes (`childType`: `fpE.childType_map`/`_list`/`_other`), its set by the cluster's
`Set.EnsureNamedFieldsAreMembers`; the node list `nl.map (fpE.ensF S ty)` (`fpE.ens_nlPaths`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.SetNodeMap__EnsureNamedFieldsAreMembersBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.SetNodeMap__Size
public import Spec.sigs_k8s_io.structured_merge_diff.v7.schema.Map__FindField
public import Spec.sigs_k8s_io.structured_merge_diff.v7.schema.Schema__Resolve
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Defs
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Vocab
import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsEnsure
import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsCard

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
variable [package_sem : fieldpath.Assumptions]

theorem fieldpath.SetNodeMap.EnsureNamedFieldsAreMembers.wp_proofBody
    (h_SetNodeMap_Size : fieldpath.SetNodeMap.Size.spec (GF := GF))
    (h_Map_FindField : schema.Map.FindField.spec (GF := GF))
    (h_Schema_Resolve : schema.Schema.Resolve.spec (GF := GF)) :
    fieldpath.SetNodeMap.EnsureNamedFieldsAreMembers.specBody (GF := GF) := by
  unfold fieldpath.SetNodeMap.EnsureNamedFieldsAreMembers.specBody fieldpath.EnsureNamedFieldsAreMembersRec.specI
    fieldpath.Set.EnsureNamedFieldsAreMembers.specI fieldpath.SetNodeMap.EnsureNamedFieldsAreMembers.specI
  iintro #IH
  iintro %l %D %sc %S %tr %ty
  wp_start as ⟨#Hl, #Hsc, #Htr, %hpre⟩
  wp_auto
  wp_apply (h_SetNodeMap_Size l D) $$ [$Hl] as %sz %hsz
  have hszD : sint.Z sz = D.card := hsz _ (FSet.hasCard_card' D) hpre.2
  wp_apply wp_slice_make3 (V := fieldpath.setNode) (W64 0) sz ⟨by word, by word⟩
    as %o0 ⟨Ho, Hocap, -⟩
  rw [List.replicate_zero]
  have Hnd := Schema.WF_types_nodup_law_holds S hpre.1
  wp_apply h_Schema_Resolve sc S tr ty $$ [] as %a %ok ⟨%Hok, #Ha⟩
  · iframe #; ipureintro; exact Hnd
  unfold isNodes
  icases Hl with ⟨%m, #Hm, Hv⟩
  icases (fpC.isNodesV_view m D).1 $$ Hv with ⟨%ns, %nl, #Hns, #Hnl, %hok⟩
  iStructNamed Hm
  wp_auto
  ihave %hlen := fpC.nodesL_length ns nl $$ Hnl
  ihave %hsl := ownSlice_len $$ Hns
  ihave HL : iprop(∃ (k : w64) (osl : GoSlice) (outs : List fieldpath.setNode),
      "i" ∷ i_ptr ↦ k ∗ "member" ∷ (∃ nv : fieldpath.setNode, member_ptr ↦ nv) ∗
      "out" ∷ out_ptr ↦ osl ∗ "Hos" ∷ osl ↦* outs ∗
      "Hocap" ∷ ownSliceCap fieldpath.setNode osl (DFrac.own 1) ∗
      "#Hlo" ∷ fpC.nodesL outs ((nl.take (sint.nat k)).map (fpE.ensF S ty)) ∗
      "%hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z m.members'.len⌝) $$ [i member out Ho Hocap]
  · iexists W64 0, o0, []; iframe; isplitl [member]
    · iexists _; iexact member
    rw [show sint.nat (W64 0) = 0 by rfl, List.take_zero, List.map_nil, fpC.nodesL_nil_eq]
    isplit
    · itrivial
    ipureintro
    exact ⟨by word, by word⟩
  iapply wp_fupd
  wp_for HL
  wp_if_destruct
  · have Hif' : sint.Z k < sint.Z m.members'.len := by simpa [intoVal_eq_iff] using Hif
    rw [if_pos ⟨hk.1, Hif'⟩]
    have hkn : sint.nat k < ns.length := by word
    list_elem ns (sint.nat k) as n0
    icases member with ⟨%nv, member⟩
    wp_apply (wp_load_slice_index m.members' (sint.Z k) ns DFrac.discard n0 hk.1) $$ [$Hns] as _
    · ipureintro; exact Hn0_lookup
    icases fpC.node_at m.members' ns nl (sint.Z k) n0 hk.1 Hn0_lookup $$ [$Hns $Hnl] with
      ⟨%pe, %S1, %h1, -, -, #Hpe, #HS⟩
    ihave %hpp := fpE.isPE_ptrs _ _ $$ Hpe
    ihave ⟨%hSc, %hLi, %hMa⟩ := LawProofs.isAtomOpt_ptrs _ _ $$ Ha
    wp_bind (If _ _ _)
    iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ atom_ptr ↦ a ∗ member_ptr ↦ n0 ∗
      ∃ tr' : schema.TypeRef, tr_ptr ↦ tr' ∗ isTypeRefOpt tr' (childType S ty pe)))) $$ [tr atom member]
    · by_cases hA : ∃ n fs e rel, pe = .field n ∧ S.resolveRef ty = some (.map fs e rel)
      · obtain ⟨n, fs, e, rel, rfl, hA⟩ := hA
        have hfn : n0.pathElement'.FieldName' ≠ null := fun h => hpp.1.1 h n rfl
        have hmn : a.Map' ≠ null := fun h => hMa.1 h fs e rel hA
        ihave #Ham : isAtomOpt a (some (.map fs e rel)) $$ [Ha]
        · rw [← hA]; iexact Ha
        icases (isAtomOpt_map_law_holds a fs e rel).1 $$ Ham with ⟨-, #Hmr⟩
        icases isMapRep_elim_law_holds _ fs e rel $$ Hmr with
          ⟨%fsl, %sfs, %etv, -, -, -, -, -, #Het, #Hetv, -⟩
        ihave #Hfn := fpE.isPE_field _ _ $$ Hpe
        simp only [decide_eq_false hfn]
        wp_auto
        simp only [decide_eq_false hmn]
        wp_auto
        have hfnd : (fs.map (·.1)).Nodup := by
          cases ty with
          | none => simp [Schema.resolveRef] at hA
          | some t => exact Schema.WF_fields_nodup_law_holds S t.name fs e rel hpre.1 hA
        wp_apply h_Map_FindField _ fs e rel n $$ [] as %sf %ok Hsf
        · iframe #; ipureintro; exact hfnd
        rw [fpE.childType_map hA n]
        unfold fieldType
        rcases hl : lookupKV n fs with _ | t
        · simp only
          icases Hsf with %Hsf
          obtain ⟨rfl, rfl⟩ := Hsf
          wp_auto
          iframe
          isplitr
          · ipureintro; rfl
          iexact Hetv
        · simp only
          icases Hsf with ⟨%Hok, Hsf⟩
          subst Hok
          icases (isStructField_elim_law_holds sf (n, t)).1 $$ Hsf with ⟨%-, #Ht⟩
          wp_auto
          iframe
          isplitr
          · ipureintro; rfl
          iapply (isTypeRefOpt_some_law_holds _ _).2
          iexact Ht
      · wp_if_destruct
        all_goals try (
          have hF : n0.pathElement'.FieldName' ≠ null := Hif
          have hM : a.Map' = null := by
            refine Classical.byContradiction fun hm => hA ?_
            obtain ⟨n, hn⟩ : ∃ n, pe = .field n :=
              Classical.byContradiction fun h => hF (hpp.1.2 fun n hn => h ⟨n, hn⟩)
            obtain ⟨fs, e, rel, he⟩ : ∃ fs e rel, S.resolveRef ty = some (.map fs e rel) :=
              Classical.byContradiction fun h => hm (hMa.2 fun fs e rel he => h ⟨fs, e, rel, he⟩)
            exact ⟨n, fs, e, rel, hn, he⟩
          simp only [decide_eq_true hM]
          wp_auto)
        all_goals
          have h1 : ∀ n fs e rel, ¬ (pe = .field n ∧ S.resolveRef ty = some (.map fs e rel)) :=
            fun n fs e rel h => hA ⟨n, fs, e, rel, h⟩
          wp_if_destruct
          · have hK : n0.pathElement'.Key' = null := Hif
            have h2 : ∀ fl e rel ks, ¬ (pe = .key fl ∧ S.resolveRef ty = some (.list e rel ks)) :=
              fun fl e rel ks h => hpp.2.1 hK fl h.1
            (try wp_auto)
            iframe
            (try isplitr)
            rw [fpE.childType_other h1 h2]
            iapply (isTypeRefOpt_none_law_holds _).2
            ipureintro; rfl
          · have hK : n0.pathElement'.Key' ≠ null := Hif
            wp_if_destruct
            · have hL : a.List' = null := Hif
              have h2 : ∀ fl e rel ks, ¬ (pe = .key fl ∧ S.resolveRef ty = some (.list e rel ks)) :=
                fun fl e rel ks h => hLi.1 hL e rel ks h.2
              (try wp_auto)
              iframe
              (try isplitr)
              rw [fpE.childType_other h1 h2]
              iapply (isTypeRefOpt_none_law_holds _).2
              ipureintro; rfl
            · have hL : a.List' ≠ null := Hif
              obtain ⟨fl, hfl⟩ : ∃ fl, pe = .key fl :=
                Classical.byContradiction fun h => hK (hpp.2.2 fun fl hn => h ⟨fl, hn⟩)
              obtain ⟨e, rel, ks, hAl⟩ : ∃ e rel ks, S.resolveRef ty = some (.list e rel ks) :=
                Classical.byContradiction fun h => hL (hLi.2 fun e rel ks he => h ⟨e, rel, ks, he⟩)
              subst hfl
              ihave #Hal : isAtomOpt a (some (.list e rel ks)) $$ [Ha]
              · rw [← hAl]; iexact Ha
              icases (isAtomOpt_list_law_holds a e rel ks).1 $$ Hal with ⟨-, #Hlr⟩
              icases isListRep_elim_law_holds _ e rel ks $$ Hlr with ⟨%lv, %ksl, #Hlv, -, -, #Het⟩
              iStructNamed Hlv
              (try wp_auto)
              iframe
              (try isplitr); (try (ipureintro; rfl))
              rw [fpE.childType_list hAl]
              iapply (isTypeRefOpt_some_law_holds _ _).2
              iexact Het
    iintro %v ⟨%hv, atom, member, %tr', tr, Htr'⟩
    ihave #Htr' := isTypeRefOpt_persistent_law_holds _ _ $$ Htr'
    subst hv
    wp_auto
    have hD : D = fpC.nlPaths nl := FSet.ext' hok.2
    have hnd : (fpC.keys nl).Nodup := fpC.sorted_nodup _ (fpC.nlok_wf hok.1) hok.1.1
    have hkl : sint.nat k < nl.length := by omega
    have hnlk : nl[sint.nat k] = (pe, S1) := by
      have := h1; simp only [sint.nat] at hkl ⊢; rw [List.getElem?_eq_getElem hkl] at this
      exact Option.some.inj this
    have hS1 : FSet.CardLt S1 (2 ^ 63) := by
      have h2 := fpK.nl_card_take nl _ hkl hnd
      have h3 := fpK.nl_card_take_le nl (sint.nat k + 1)
      have h4 := hpre.2
      rw [hnlk] at h2
      unfold FSet.CardLt at h4 ⊢
      rw [hD] at h4
      simp only at h2
      omega
    icases IH with ⟨#HSet, -⟩
    wp_apply HSet $$ %n0.set' %S1 %sc %S %tr' %(childType S ty pe) [] as %p #Hp
    · iframe #; ipureintro; exact ⟨hpre.1, hS1⟩
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %nsl ⟨Hnsl, -⟩
    wp_apply wp_slice_append $$ [$Hos $Hocap $Hnsl] as %osl' ⟨Hos, Hocap, -⟩
    wp_for_post
    ihave #Hlo' := fpC.nodesL_snoc outs _ ⟨n0.pathElement', p⟩ pe (ensureNamedOpt S (childType S ty pe) S1)
      $$ [$Hlo $Hpe $Hp]
    iframe
    iexists k + W64 1, osl', outs ++ [⟨n0.pathElement', p⟩]
    iframe
    isplitl [member]
    · iexists _; iexact member
    rw [show sint.nat (k + W64 1) = sint.nat k + 1 by word, fpC.take_succ' nl _ hkl, List.map_append,
      hnlk]
    simp only [List.map_cons, List.map_nil, fpE.ensF]
    isplit
    · iexact Hlo'
    ipureintro
    exact ⟨by word, by word⟩
  · have hkl : sint.nat k = nl.length := by
      have : ¬ sint.Z k < sint.Z m.members'.len := by simpa [intoVal_eq_iff] using Hif
      word
    rw [hkl, List.take_length]
    ipersist «$r0»
    ipersist Hos
    imodintro
    iapply HΦ
    iexists _
    isplit
    · iexact «$r0»
    iapply (fpC.isNodesV_view _ _).2
    iexists outs, nl.map (fpE.ensF S ty)
    isplit
    · iexact Hos
    isplit
    · iexact Hlo
    ipureintro
    exact ⟨fpE.ens_nlok S ty hok.1, fpE.ens_nlPaths S ty hok.1 D hok.2⟩

end proof

end smd
end EtcdGrove
end Perennial
