/-
`typed.resolveSchema`: not proved yet (`sorry`): the stage's Prove step, after the freeze
(notes/smd-plan.md). Draft (2026-11-19).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.resolveSchema
public import Spec.sigs_k8s_io.structured_merge_diff.v7.schema.Schema__Resolve
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.deduceAtom
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.handleAtom
public import Proof.sigs_k8s_io.structured_merge_diff.v7.schema.LawProofs

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

theorem typed.resolveSchema.wp_proof
    (h_Schema_Resolve : schema.Schema.Resolve.spec (GF := GF))
    (h_deduceAtom : typed.deduceAtom.spec (GF := GF))
    (h_handleAtom : typed.handleAtom.spec (GF := GF)) :
    typed.resolveSchema.spec (GF := GF) := fun sc S tr t A v dq o T hv Pre Q => by
  wp_start as ⟨#HS, #Htr, %HWF, Hv, HP, Hh⟩
  have Hnd := Schema.WF_types_nodup_law_holds S HWF.1
  ihave #Htr' := (isTypeRefOpt_some_law_holds tr t).2 $$ Htr
  wp_auto
  wp_apply h_Schema_Resolve sc S tr (some t) $$ [] as %a %ok ⟨%Hok, #Ha⟩
  · iframe #; ipureintro; exact Hnd
  simp only [Schema.resolveRef, Schema.resolvesRef, Schema.resolves, HWF.2, Option.isSome_some] at Hok ⊢
  subst Hok
  wp_auto
  wp_apply h_deduceAtom a A v dq o $$ [Hv] as Hv
  · iframe #; iframe Hv
  wp_apply h_handleAtom a A tr T hv iprop(isValO v dq o ∗ Pre) Q $$ [Hv HP Hh] as %errs HQ
  · iframe #; iframe Hv HP; iapply Hh $$ Ha
  iapply HΦ $$ HQ

end proof

end smd
end EtcdGrove
end Perennial
