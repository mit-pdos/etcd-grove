/-
`schema.Schema.resolveNoOverrides`:
not proved yet (`sorry`): Draft of the `schema` package's per-function specs (notes/smd-plan.md,
"The call DAG"); proved in the stage's Prove step, after the freeze.

Lean-first (2026-11-19).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.schema.Schema__resolveNoOverrides
public import Spec.sigs_k8s_io.structured_merge_diff.v7.schema.Schema__FindNamedType
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
variable [package_sem : schema.Assumptions]

theorem schema.Schema.resolveNoOverrides.wp_proof
    (h_Schema_FindNamedType : schema.Schema.FindNamedType.spec (GF := GF)) :
    schema.Schema.resolveNoOverrides.spec (GF := GF) := by
  intro sc S tr ot
  wp_start as ⟨#HS, #Htr, %Hnd⟩
  wp_auto
  cases ot with
  | none =>
    ihave %Hz := (isTypeRefOpt_none_law_holds tr).1 $$ Htr
    subst Hz
    wp_auto
    iapply HΦ
    isplitr
    · ipureintro; rfl
    · rw [show S.resolveRef none = none from rfl]
      iapply (isAtomOpt_none_law_holds _).2; ipureintro; rfl
  | some t =>
    ihave Ht := (isTypeRefOpt_some_law_holds tr t).1 $$ Htr
    ihave ⟨#Hn, %Htz⟩ := isTypeRef_elim_law_holds tr t $$ Ht
    ihave %Hnn := typedPointsto_not_null $$ Hn
    wp_if_destruct
    all_goals try (exfalso; exact Hnn Hif)
    wp_apply h_Schema_FindNamedType sc S t.name $$ [] as %td %ok Hr
    · iframe #; ipureintro; exact Hnd
    cases hf : S.find t.name with
    | none =>
      icases Hr with %Hr
      obtain ⟨rfl, rfl⟩ := Hr
      wp_auto
      iapply HΦ
      simp only [Schema.resolvesRef, Schema.resolves, Schema.resolveRef, hf]
      isplitr
      · ipureintro; rfl
      · iapply (isAtomOpt_none_law_holds _).2; ipureintro; rfl
    | some A =>
      icases Hr with ⟨%Hr, #Ha⟩
      obtain ⟨rfl, -⟩ := Hr
      wp_auto
      iapply HΦ
      simp only [Schema.resolvesRef, Schema.resolves, Schema.resolveRef, hf, Option.isSome_some]
      isplitr
      · ipureintro; trivial
      · iexact Ha

end proof

end smd
end EtcdGrove
end Perennial
