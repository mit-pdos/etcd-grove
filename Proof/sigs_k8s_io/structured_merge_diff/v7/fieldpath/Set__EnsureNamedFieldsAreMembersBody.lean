/-
`fieldpath.Set.EnsureNamedFieldsAreMembers`' body (the recursion cluster
`fieldpath.EnsureNamedFieldsAreMembersRec`, `EnsureNamedFieldsAreMembersRec.lean`): proved. The
members are copied into a fresh slice (its capacity `s.Members.Size()+len(s.Children.members)`
bounded by the set's count, `fpE.nl_length_le`), each child key that is a declared field of the
map type made a member (`fpE.namedB`, `fpE.ens_tops`), the children by the cluster's
`SetNodeMap.EnsureNamedFieldsAreMembers` (`fpE.ens_deep`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__EnsureNamedFieldsAreMembersBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElementSet__Insert
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElementSet__Size
public import Spec.sigs_k8s_io.structured_merge_diff.v7.schema.Map__FindField
public import Spec.sigs_k8s_io.structured_merge_diff.v7.schema.Schema__Resolve
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Defs
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Vocab
import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsEnsure

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

theorem fieldpath.Set.EnsureNamedFieldsAreMembers.wp_proofBody
    (h_PathElementSet_Insert : fieldpath.PathElementSet.Insert.spec (GF := GF))
    (h_PathElementSet_Size : fieldpath.PathElementSet.Size.spec (GF := GF))
    (h_Map_FindField : schema.Map.FindField.spec (GF := GF))
    (h_Schema_Resolve : schema.Schema.Resolve.spec (GF := GF)) :
    fieldpath.Set.EnsureNamedFieldsAreMembers.specBody (GF := GF) := by
  unfold fieldpath.Set.EnsureNamedFieldsAreMembers.specBody fieldpath.EnsureNamedFieldsAreMembersRec.specI
    fieldpath.Set.EnsureNamedFieldsAreMembers.specI fieldpath.SetNodeMap.EnsureNamedFieldsAreMembers.specI
  iintro #IH
  iintro %p %s %sc %S %tr %ty
  wp_start as ⟨#Hs, #Hsc, #Htr, %hpre⟩
  icases (fpC.isSet_view p s).1 $$ Hs with ⟨%v, #Hp, #Hm, #Hc, %hne⟩
  icases (fpC.isNodesV_view v.Children' s.deep).1 $$ Hc with ⟨%ns, %nl, #Hns, #Hnl, %hok⟩
  iStructNamed Hp
  ihave #HMs : isPESet (p.[fieldpath.Set', go!"Members"]) DFrac.discard s.tops $$ [Members Hm]
  · unfold isPESet; iexists v.Members'; iframe #
  wp_auto
  wp_apply (h_PathElementSet_Size _ DFrac.discard s.tops) $$ [$HMs] as %sz ⟨-, %hsz⟩
  ihave %hlen := fpC.nodesL_length ns nl $$ Hnl
  ihave %hsl := ownSlice_len $$ Hns
  have hD : s.deep = fpC.nlPaths nl := FSet.ext' hok.2
  have htc : s.tops.card = (sint.Z sz).toNat :=
    (FSet.hasCard_iff _ _).1 hsz.2
  have hsc := fpK.set_card s hne
  have hnll := fpE.nl_length_le nl hok.1 nl.length (Nat.le_refl _)
  rw [List.take_length, ← hD] at hnll
  have hcs := hpre.2
  unfold FSet.CardLt at hcs
  have hsum : sint.Z sz + sint.Z v.Children'.members'.len < 2 ^ 63 := by
    have h2 : sint.Z v.Children'.members'.len = (nl.length : Int) := by
      rw [← hlen, hsl.1]; word
    have h0 := hsz.1
    omega
  iStructNamedSuffix Children "c"
  wp_auto
  wp_apply wp_slice_make3 (V := fieldpath.PathElement) (W64 0) (sz + v.Children'.members'.len)
    ⟨by word, by word⟩ as %o0 ⟨Ho, Hocap, -⟩
  have Hnd := Schema.WF_types_nodup_law_holds S hpre.1
  wp_apply h_Schema_Resolve sc S tr ty $$ [] as %a %ok ⟨%Hok, #Ha⟩
  · iframe #; ipureintro; exact Hnd
  icases fpE.isPESetV_copy _ _ $$ Hm with ⟨%es, #Hes, #Hcopy⟩
  iStructNamedSuffix Members "m"
  wp_auto
  rw [List.replicate_zero]
  wp_apply wp_slice_append $$ [$Ho $Hocap $Hes] as %o1 ⟨Ho, Hocap, -⟩
  rw [List.nil_append]
  ihave Hmv := Hcopy $$ %o1 Ho Hocap
  ihave HL : iprop(∃ (k : w64),
      "i" ∷ i_ptr ↦ k ∗ "node" ∷ (∃ nv : fieldpath.setNode, node_ptr ↦ nv) ∗
      "Hmem" ∷ ownPESet members_ptr
        (FSet.union s.tops (FSet.ofList (((fpC.keys nl).take (sint.nat k)).filter (fpE.namedB S ty)))) ∗
      "%hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z v.Children'.members'.len⌝) $$ [i node members Hmv]
  · iexists W64 0
    iframe
    isplitl [node]
    · iexists _; iexact node
    rw [show sint.nat (W64 0) = 0 by rfl, List.take_zero, List.filter_nil]
    have e0 : FSet.union s.tops (FSet.ofList ([] : List PE)) = s.tops :=
      FSet.ext' (fun x => by rw [FSet.mem_union', FSet.mem_ofList']; simp)
    rw [e0]
    isplitl
    · unfold ownPESet; iexists _; iframe
    ipureintro; exact ⟨by word, by word⟩
  have hD' : ∀ q, q ∈ s.deep ↔ q ∈ fpC.nlPaths nl := hok.2
  have hkeys : (fpC.keys nl).length = nl.length := by simp [fpC.keys]
  have h2 : sint.Z v.Children'.members'.len = (nl.length : Int) := by
    rw [← hlen, hsl.1]; word
  ihave %hpa := LawProofs.isAtomOpt_ptrs _ _ $$ Ha
  obtain ⟨-, -, hMa⟩ := hpa
  iapply wp_fupd
  wp_for HL
  wp_if_destruct
  · have Hif' : sint.Z k < sint.Z v.Children'.members'.len := by simpa [intoVal_eq_iff] using Hif
    rw [if_pos ⟨hk.1, Hif'⟩]
    have hkn : sint.nat k < ns.length := by word
    have hkl : sint.nat k < nl.length := by omega
    list_elem ns (sint.nat k) as n0
    icases node with ⟨%nv, node⟩
    wp_apply (wp_load_slice_index v.Children'.members' (sint.Z k) ns DFrac.discard n0 hk.1) $$ [$Hns] as _
    · ipureintro; exact Hn0_lookup
    icases fpC.node_at v.Children'.members' ns nl (sint.Z k) n0 hk.1 Hn0_lookup $$ [$Hns $Hnl] with
      ⟨%pe, %S1, %h1, -, -, #Hpe, -⟩
    have hnlk : nl[sint.nat k] = (pe, S1) := by
      have := h1; simp only [sint.nat] at hkl ⊢; rw [List.getElem?_eq_getElem hkl] at this
      exact Option.some.inj this
    have htk : (fpC.keys nl).take (sint.nat k + 1) = (fpC.keys nl).take (sint.nat k) ++ [pe] := by
      rw [fpC.take_succ' _ _ (by omega)]
      simp [fpC.keys, hnlk]
    have hs1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
    ihave %hpp := fpE.isPE_fieldName_ptr _ _ $$ Hpe
    by_cases hA : ∃ n fs e rel, pe = .field n ∧ S.resolveRef ty = some (.map fs e rel)
    · obtain ⟨n, fs, e, rel, rfl, hA⟩ := hA
      have hfn : n0.pathElement'.FieldName' ≠ null := fun h => hpp.1 h n rfl
      have hmn : a.Map' ≠ null := fun h => hMa.1 h fs e rel hA
      ihave #Ham : isAtomOpt a (some (.map fs e rel)) $$ [Ha]
      · rw [← hA]; iexact Ha
      icases (isAtomOpt_map_law_holds a fs e rel).1 $$ Ham with ⟨-, #Hmr⟩
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
      rcases hl : lookupKV n fs with _ | t
      · simp only
        icases Hsf with %Hsf
        obtain ⟨rfl, rfl⟩ := Hsf
        have hnb : fpE.namedB S ty (.field n) = false := by rw [fpE.namedB_map hA n, hl]; rfl
        wp_auto
        wp_for_post
        iframe
        iexists k + W64 1
        iframe
        isplitl [node]
        · iexists _; iexact node
        rw [hs1, htk, ← fpE.members_step_out S ty _ _ _ hnb]
        iframe
        ipureintro; exact ⟨by word, by word⟩
      · simp only
        icases Hsf with ⟨%Hok, -⟩
        subst Hok
        have hnb : fpE.namedB S ty (.field n) = true := by rw [fpE.namedB_map hA n, hl]; rfl
        wp_auto
        have hcard : FSet.CardLt (FSet.union s.tops (FSet.ofList (((fpC.keys nl).take (sint.nat k)).filter
            (fpE.namedB S ty)))) (2 ^ 63 - 1) := by
          unfold FSet.CardLt
          have c1 := FSet_card_union_law_holds s.tops (FSet.ofList (((fpC.keys nl).take (sint.nat k)).filter
            (fpE.namedB S ty)))
          have c2 := fpE.card_ofList_le (((fpC.keys nl).take (sint.nat k)).filter (fpE.namedB S ty))
          have c3 := List.length_filter_le (fpE.namedB S ty) ((fpC.keys nl).take (sint.nat k))
          have c4 : ((fpC.keys nl).take (sint.nat k)).length = sint.nat k := by
            rw [List.length_take]; omega
          omega
        wp_apply h_PathElementSet_Insert members_ptr _ n0.pathElement' (.field n) $$ [$Hmem $Hpe] as Hmem
        · ipureintro; exact hcard
        wp_for_post
        iframe
        iexists k + W64 1
        iframe
        isplitl [node]
        · iexists _; iexact node
        rw [hs1, htk, ← fpE.members_step_in S ty _ _ _ hnb]
        iframe
        ipureintro; exact ⟨by word, by word⟩
    · have h1 : ∀ n fs e rel, ¬ (pe = .field n ∧ S.resolveRef ty = some (.map fs e rel)) :=
        fun n fs e rel h => hA ⟨n, fs, e, rel, h⟩
      have hnb : fpE.namedB S ty pe = false := fpE.namedB_other h1
      wp_if_destruct
      all_goals try (
        have hF : n0.pathElement'.FieldName' ≠ null := Hif
        have hM : a.Map' = null := by
          refine Classical.byContradiction fun hm => hA ?_
          obtain ⟨n, hn⟩ : ∃ n, pe = .field n :=
            Classical.byContradiction fun h => hF (hpp.2 fun n hn => h ⟨n, hn⟩)
          obtain ⟨fs, e, rel, he⟩ : ∃ fs e rel, S.resolveRef ty = some (.map fs e rel) :=
            Classical.byContradiction fun h => hm (hMa.2 fun fs e rel he => h ⟨fs, e, rel, he⟩)
          exact ⟨n, fs, e, rel, hn, he⟩
        simp only [decide_eq_true hM]
        wp_auto)
      all_goals
        wp_for_post
        iframe
        iexists k + W64 1
        iframe
        isplitl [node]
        · iexists _; iexact node
        rw [hs1, htk, ← fpE.members_step_out S ty _ _ _ hnb]
        iframe
        ipureintro; exact ⟨by word, by word⟩
  · have hkl : sint.nat k = nl.length := by
      have : ¬ sint.Z k < sint.Z v.Children'.members'.len := by simpa [intoVal_eq_iff] using Hif
      word
    rw [hkl, ← hkeys, List.take_length, ← fpE.ens_tops S ty s hok.1 hD']
    have hdc : FSet.CardLt s.deep (2 ^ 63) :=
      FSet_cardLt_mono_law_holds s.deep s _ _ (fun q hq => ((fpE.mem_deep' s q).1 hq).1) (Nat.le_refl _)
        hpre.2
    unfold ownPESet
    icases Hmem with ⟨%mv, Hmp, Hmv⟩
    wp_auto
    icases IH with ⟨-, #HN⟩
    wp_apply HN $$ %(p.[fieldpath.Set', go!"Children"]) %s.deep %sc %S %tr %ty [] as %rc Hrc
    · iframe #
      isplit
      · unfold isNodes; iexists v.Children'; iframe #
      ipureintro; exact ⟨hpre.1, hdc⟩
    unfold isNodes
    icases Hrc with ⟨%cv, #Hrcp, #Hcv⟩
    wp_auto
    ipersist «$r0»
    imod ownPESetV_persist_law_holds _ _ $$ Hmv with #Hmv'
    imodintro
    iapply HΦ
    rw [← fpE.ens_deep] at *
    iapply (fpS.isSet_of_parts _ ⟨mv, cv⟩ (ensureNamedOpt S ty s) _ _ rfl rfl
      (fpE.ens_nil S ty s hne))
    iframe #


end proof

end smd
end EtcdGrove
end Perennial
