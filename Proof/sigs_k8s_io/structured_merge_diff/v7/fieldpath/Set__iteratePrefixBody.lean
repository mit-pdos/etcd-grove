/-
`fieldpath.Set.iteratePrefix`: a member of the recursion cluster `fieldpath.iteratePrefixRec` (`iteratePrefixRec.lean`); its proof is the
projection of the cluster's (its body is `Set__iteratePrefixBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__iteratePrefixBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElementSet__Iterate
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Defs
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Vocab
import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsIter
import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsRep

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

theorem fieldpath.Set.iteratePrefix.wp_proofBody
    (h_PathElementSet_Iterate : fieldpath.PathElementSet.Iterate.spec (GF := GF)) :
    fieldpath.Set.iteratePrefix.specBody (GF := GF) := by
  unfold fieldpath.Set.iteratePrefix.specBody fieldpath.iteratePrefixRec.specI
    fieldpath.Set.iteratePrefix.specI fieldpath.SetNodeMap.iteratePrefix.specI
  iintro #IH
  iintro %p %S %ps %es %pre %f %T %I %done0
  wp_start as ⟨#Hs, Hps, Hcap, #Hes, HI, %hpre, #Hf⟩
  unfold isSet
  icases Hs with ⟨%t, %ht, #Ht⟩
  rcases t with ⟨ms, cs⟩
  rw [fpD.trieRep_mk_eq]
  icases Ht with ⟨%v, %mes, %ns, #Hp, #Hmes, #Hml, #Hns, #Hcs⟩
  iStructNamed Hp
  wp_auto
  irename «prefix» => Hpc
  irename f => Hfc
  ipersist Hpc
  ipersist Hfc
  have hcan := ht.1
  simp only [Trie.Canonical] at hcan
  ihave #Hmset : iprop(isPESet (p.[fieldpath.Set', go!"Members"]) DFrac.discard (FSet.ofList ms)) $$ []
  · unfold isPESet isPESetV
    iexists v.Members'; iframe Members; iexists mes, ms; iframe Hmes Hml; ipureintro; exact ⟨hcan.1, rfl⟩
  ihave %hesl := isPEs_length_law_holds es pre $$ Hes
  wp_apply (h_PathElementSet_Iterate _ DFrac.discard (FSet.ofList ms) _
    (fun done => iprop(ps ↦* es ∗ ownSliceCap fieldpath.PathElement ps (DFrac.own 1) ∗
      I (done0 ++ done.map (fun x => pre ++ [x]))))) $$ [Hps Hcap HI]
    as ⟨-, %mdone, %hmd, Hps, Hcap, HI⟩
  · iframe Hmset
    isplitl [Hps Hcap HI]
    · iframe; simp only [List.map_nil, List.append_nil]; iexact HI
    iintro !> %done %e %x %hx !> %Φ' ⟨⟨Hps, Hcap, HI⟩, #He⟩ HΦ'
    wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    (try wp_auto)
    wp_apply (wp_slice_append_undo ps es _ [e] (DFrac.own 1)) $$ [$Hps $Hcap $Hsl]
      as %ps' ⟨Hps', Hcap', -, Hback⟩
    icases (ownSlice_dfractional (GF := GF) ps' (es ++ [e])).dfractional
      (DFrac.own (1 : Qp).half) (DFrac.own (1 : Qp).half) |>.1 $$ [Hps'] with ⟨H1, H2⟩
    · rw [DFrac.op_own, Qp.half_add_half]; iexact Hps'
    have hxm : x ∈ ms := (FSet.mem_ofList' ms x).1 hx.1
    have hxS : [x] ∈ S := (ht.2 [x]).1 (by simp only [Trie.paths]; exact Or.inl ⟨x, rfl, hxm⟩)
    have hpx := hpre [x] hxS
    have hnot : pre ++ [x] ∉ done0 ++ done.map (fun y => pre ++ [y]) := by
      rw [List.mem_append, not_or]
      refine ⟨hpx.2, fun hm => ?_⟩
      obtain ⟨y, hy, he⟩ := List.mem_map.1 hm
      simp at he; subst he; exact hx.2 hy
    ihave #Hfx := Hf $$ %(done0 ++ done.map (fun y => pre ++ [y])) %(pre ++ [x]) %ps'
      %(DFrac.own (1 : Qp).half) %(And.intro hpx.1 hnot)
    wp_apply Hfx $$ [HI H1] as ⟨HI, HP⟩
    · iframe HI
      unfold isPathF
      iexists (es ++ [e]); iframe H1
      iapply (isPEs_app_law_holds es [e] pre [x] hesl).2
      iframe Hes
      iapply (isPEs_cons_law_holds e [] x []).2
      iframe He
      unfold isPEs; rw [fpL.isPEL_nil_eq]; itrivial
    unfold isPathF
    icases HP with ⟨%es'', H1, #Hes''⟩
    ihave %hag := ownSlice_agree $$ H1 H2
    subst hag
    ihave Hps' := (ownSlice_dfractional (GF := GF) ps' (es ++ [e])).dfractional
      (DFrac.own (1 : Qp).half) (DFrac.own (1 : Qp).half) |>.2 $$ [H1 H2]
    · iframe
    rw [DFrac.op_own, Qp.half_add_half]
    ihave ⟨Hps, Hcap⟩ := Hback $$ [Hps' Hcap']
    · iframe
    iapply HΦ'
    iframe
    simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc]
    iexact HI
  ihave #Hnodes : iprop(isNodes (p.[fieldpath.Set', go!"Children"]) S.deep) $$ []
  · unfold isNodes isNodesV
    iexists v.Children'; iframe Children; iexists ns, cs; iframe Hns Hcs; ipureintro
    exact ⟨hcan.2.1, hcan.2.2, fpD.deep_iff ms cs S ht.2⟩
  icases IH with ⟨-, #HN⟩
  wp_apply HN $$ %(p.[fieldpath.Set', go!"Children"]) %S.deep %ps %es %pre %f %T %I
    %(done0 ++ mdone.map (fun y => pre ++ [y])) [Hps Hcap HI] as ⟨Hps, Hcap, %dsc, %hdsc, HI⟩
  · iframe
    isplit; · iexact Hnodes
    isplit; · iexact Hes
    isplit
    · ipureintro
      intro q hq
      have hq' := (PathSet_mem_deep_law_holds S q).1 hq
      refine ⟨(hpre q hq'.1).1, ?_⟩
      rw [List.mem_append, not_or]
      refine ⟨(hpre q hq'.1).2, fun hm => ?_⟩
      obtain ⟨y, -, he⟩ := List.mem_map.1 hm
      have := List.append_cancel_left he
      subst this; simp at hq'
    · iexact Hf
  iapply HΦ
  iframe Hps Hcap
  iexists (mdone.map (fun y => pre ++ [y]) ++ dsc)
  isplitr
  · ipureintro; exact fpD.iterate_final pre ms cs S ht.2 mdone dsc
      ⟨hmd.1, hmd.2⟩ hdsc
  · rw [← List.append_assoc]; iexact HI

end proof

end smd
end EtcdGrove
end Perennial
