/-
`fieldpath.PathElementValueMap.Insert`: proved over its callees' specs (the hypotheses).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElementValueMap__Insert
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElementMap__Insert
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

theorem fieldpath.PathElementValueMap.Insert.wp_proof
    (h_PathElementMap_Insert : fieldpath.PathElementMap.Insert.spec (GF := GF)) :
    fieldpath.PathElementValueMap.Insert.spec (GF := GF) := fun l M e pe x => by
  wp_start as ⟨Hs, #He, %hx⟩
  unfold ownPEVMap ownPEVMapV
  icases Hs with ⟨%v, Hl, Hmap, %hptr⟩
  icases fpA.pevmap_valueMap_upd l v (DFrac.own 1) $$ Hl with ⟨Hf, Hback⟩
  wp_auto
  wp_apply (h_PathElementMap_Insert _ M e pe x) $$ [Hf Hmap] as Hmap
  · isplitl [Hf Hmap]
    · unfold ownPEMap; iexists _; iframe
    isplit
    · iexact He
    · ipureintro; exact hx.2
  iapply HΦ
  unfold ownPEMap
  icases Hmap with ⟨%w, Hw, Hmv⟩
  iexists _
  isplitl [Hback Hw]
  · iapply Hback; iexact Hw
  iframe
  ipureintro
  intro k y hk
  unfold PEMap.insert at hk
  by_cases h : k = pe
  · simp [h] at hk; rw [← hk]; exact hx.1
  · simp only [h, ↓reduceIte] at hk; exact hptr k y hk

end proof

end smd
end EtcdGrove
end Perennial
