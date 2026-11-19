/-
`fieldpath.PathElementSet.Size`: proved over its callees' specs (the hypotheses).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElementSet__Size
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

theorem fieldpath.PathElementSet.Size.wp_proof :
    fieldpath.PathElementSet.Size.spec (GF := GF) := fun l dq S => by
  wp_start as Hs
  unfold isPESet isPESetV
  icases Hs with ⟨%v, Hl, %es, %xs, Hm, #Hx, %h⟩
  icases fpA.peset_members_acc l v dq $$ Hl with ⟨Hf, Hback⟩
  wp_auto
  ihave %hl := ownSlice_len $$ Hm
  ihave %hlen := fpL.isPEL_length es xs $$ Hx
  ihave %hw := fpL.isPEL_wf es xs $$ Hx
  iapply HΦ
  isplitl [Hf Hback Hm]
  · iexists v; isplitl [Hf Hback]
    · iapply Hback; iexact Hf
    iexists es, xs; iframe; isplit; iexact Hx; ipureintro; exact h
  ipureintro
  refine ⟨by word, ?_⟩
  rw [← h.2]
  have := fpA.hasCard_of_sorted xs hw h.1
  rw [show (sint.Z v.members'.len).toNat = xs.length by
    have := hl.1; simp only [sint.nat, sint.Z] at this ⊢; omega]
  exact this

end proof

end smd
end EtcdGrove
end Perennial
