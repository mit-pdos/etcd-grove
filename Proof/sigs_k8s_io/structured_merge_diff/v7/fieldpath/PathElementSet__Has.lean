/-
`fieldpath.PathElementSet.Has`: proved over its callees' specs (the hypotheses).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElementSet__Has
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElement__Compare
public import Spec.slices.BinarySearchFunc
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

theorem fieldpath.PathElementSet.Has.wp_proof
    (h_PathElement_Compare : fieldpath.PathElement.Compare.spec (GF := GF))
    (h_slices_BinarySearchFunc : EtcdGrove.slices.BinarySearchFunc.spec (GF := GF)) :
    fieldpath.PathElementSet.Has.spec (GF := GF) := fun l dq S e pe => by
  wp_start as ⟨Hs, #He⟩
  unfold isPESet isPESetV
  icases Hs with ⟨%v, Hl, %es, %xs, Hm, #Hx, %h⟩
  icases fpA.peset_members_acc l v dq $$ Hl with ⟨Hf, Hback⟩
  ihave %hmd := fpA.isPEL_mdl es xs pe $$ Hx
  ihave %hw := fpL.isPEL_wf es xs $$ Hx
  ihave %hlen := fpL.isPEL_length es xs $$ Hx
  ihave %hp := fpL.isPE_wf' e pe $$ He
  wp_auto
  wp_apply (h_slices_BinarySearchFunc (E := fieldpath.PathElement) fieldpath.PathElement.ty v.members' es dq e _
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
  iapply HΦ
  isplitl [Hf Hback Hm]
  · iexists v; isplitl [Hf Hback]
    · iapply Hback; iexact Hf
    iexists es, xs; iframe; isplit; iexact Hx; ipureintro; exact h
  ipureintro
  rw [hf, fpA.bs_found hw hp h.1 hbs, ← h.2, FSet.mem_ofList']

end proof

end smd
end EtcdGrove
end Perennial
