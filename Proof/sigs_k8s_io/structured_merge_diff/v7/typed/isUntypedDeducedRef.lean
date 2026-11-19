/-
`typed.isUntypedDeducedRef`: not proved yet (`sorry`): the stage's Prove step, after the freeze
(notes/smd-plan.md). Draft (2026-11-19).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.isUntypedDeducedRef
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

theorem typed.isUntypedDeducedRef.wp_proof :
    typed.isUntypedDeducedRef.spec (GF := GF) := fun tr ot => by
  rcases ot with _ | t
  · simp only [Option.map_none, reduceCtorEq, decide_false]
    wp_start as Hot
    ihave %Htr := (isTypeRefOpt_none_law_holds tr).1 $$ Hot
    subst Htr
    wp_auto
    iapply HΦ
    itrivial
  · simp only [Option.map_some, Option.some.injEq]
    wp_start as Hot
    ihave Ht := (isTypeRefOpt_some_law_holds tr t).1 $$ Hot
    icases isTypeRef_elim_law_holds tr t $$ Ht with ⟨Hn, %Hz⟩
    ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hn
    wp_auto
    wp_if_destruct
    · exact absurd Hif Hnn
    · iapply HΦ
      itrivial

end proof

end smd
end EtcdGrove
end Perennial
