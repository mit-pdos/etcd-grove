/-
`fieldpath.PathElementSet.Insert`: proved over its callees' specs (the hypotheses).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElementSet__Insert
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElement__Compare
public import Spec.slices.BinarySearchFunc
public import Spec.slices.Insert
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Defs
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Vocab
import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsRep
import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsPESet

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

theorem fieldpath.PathElementSet.Insert.wp_proof
    (h_PathElement_Compare : fieldpath.PathElement.Compare.spec (GF := GF))
    (h_slices_BinarySearchFunc : EtcdGrove.slices.BinarySearchFunc.spec (GF := GF))
    (h_slices_Insert : EtcdGrove.slices.Insert.spec (GF := GF)) :
    fieldpath.PathElementSet.Insert.spec (GF := GF) := fun l S e pe => by
  wp_start as ⟨Hs, #He, %hc⟩
  unfold ownPESet ownPESetV
  icases Hs with ⟨%v, Hl, %es, %xs, Hm, Hcap, #Hx, %h⟩
  icases fpA.peset_members_upd l v (DFrac.own 1) $$ Hl with ⟨Hf, Hback⟩
  ihave %hmd := fpA.isPEL_mdl es xs pe $$ Hx
  ihave %hw := fpL.isPEL_wf es xs $$ Hx
  ihave %hlen := fpL.isPEL_length es xs $$ Hx
  ihave %hp := fpL.isPE_wf' e pe $$ He
  wp_auto
  wp_apply (h_slices_BinarySearchFunc (E := fieldpath.PathElement) fieldpath.PathElement.ty v.members' es (DFrac.own 1) e _
    (fun a => PE.compare (fpA.mdl es xs pe a) pe) iprop(True)) $$ [$Hm] as %i %found ⟨Hm, -, %hi1, %hi2, %hi3⟩
  · isplitr
    · itrivial
    isplit
    · imodintro
      iintro %a %ha
      imodintro
      iintro %Φ' - HΦ'
      have hk := fpA.peIdx_get es a ha
      ihave ⟨%x, %hx, Ha⟩ := fpL.isPEL_lookup es xs _ a hk $$ Hx
      have hx' : x = fpA.mdl es xs pe a := by
        have := hmd _ a hk; rw [hx] at this; exact Option.some.inj this
      subst hx'
      wp_auto
      wp_method_call; wp_call; wp_auto
      wp_apply (h_PathElement_Compare a e (fpA.mdl es xs pe a) pe) $$ [$Ha $He] as %r %hr
      iapply HΦ'
      iframe
      ipureintro; exact ⟨trivial, hr⟩
    · ipureintro
      intro k j ek ej hk hj hkj
      exact fpA.sorted_signum hw hp h.1 k j _ _ (hmd k ek hk) (hmd j ej hj) hkj
  obtain ⟨hbs, hf⟩ := fpA.bs_transfer es xs pe (fpA.mdl es xs pe) hmd hlen _ found hi1 hi2 hi3
  rw [fpA.bs_found hw hp h.1 hbs] at hf
  cases found
  case true =>
    wp_auto
    have hm : pe ∈ xs := hf.1 rfl
    iapply HΦ
    iexists _
    isplitl [Hf Hback]
    · iapply Hback; iexact Hf
    iexists es, xs; iframe; isplit; iexact Hx; ipureintro
    refine ⟨h.1, ?_⟩
    rw [← h.2]
    apply FSet.ext'; intro x
    rw [FSet.mem_union', FSet.mem_ofList', FSet.mem_ofList']
    constructor
    · intro hx; exact Or.inl hx
    · rintro (hx | hx)
      · exact hx
      · simp at hx; subst hx; exact hm
  case false =>
  have hn : pe ∉ xs := fun hm => by simpa using hf.2 hm
  wp_auto
  have hcard : xs.length < 2 ^ 63 - 1 := by
    have h1 := (FSet.hasCard_iff _ _).1 (fpA.hasCard_of_sorted xs hw h.1)
    unfold FSet.CardLt at hc; rw [← h.2, h1] at hc; exact hc
  wp_apply (wp_slice_literal (V := fieldpath.PathElement) [e])
  isplitr
  · ipureintro; rfl
  iintro %osl ⟨Hosl, -⟩
  wp_auto
  wp_apply (h_slices_Insert v.members' es i _ [e] (DFrac.own 1)) $$ [$Hm $Hcap $Hosl] as %s' ⟨Hm, Hcap, -⟩
  · ipureintro; refine ⟨hi1.1, hi1.2, ?_⟩; simp; omega
  iapply HΦ
  iexists _
  isplitl [Hback Hf]
  · iapply Hback; iexact Hf
  iexists _, (xs.take (sint.Z i).toNat ++ [pe] ++ xs.drop (sint.Z i).toNat)
  iframe Hm Hcap
  isplit
  · iapply fpA.isPEL_insert; iframe Hx He
  ipureintro
  refine ⟨?_, ?_⟩
  · have := fpA.bs_insert_sorted hw hp h.1 hbs hn
    simpa only [List.append_assoc, List.singleton_append] using this
  · rw [fpA.ofList_insert, h.2]

end proof

end smd
end EtcdGrove
end Perennial
