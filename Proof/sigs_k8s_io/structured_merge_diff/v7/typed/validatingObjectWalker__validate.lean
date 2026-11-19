/-
`typed.validatingObjectWalker.validate`: not proved yet (`sorry`): the stage's Prove step, after the freeze
(notes/smd-plan.md). Draft (2026-11-19).

Recursive (`validate` → `resolveSchema` → `doList`/`doMap` → `visit*` → `validate`): the link needs a form for a cycle of specs (open question in the report).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.validatingObjectWalker__validate
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.resolveSchema
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.ValidationErrors__WithLazyPrefix
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.validatingObjectWalker__doScalar
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.validatingObjectWalker__doList
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.validatingObjectWalker__doMap

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

theorem typed.validatingObjectWalker.validate.wp_proof
    (hresolveSchema : typed.resolveSchema.spec (GF := GF))
    (hValidationErrors_WithLazyPrefix : typed.ValidationErrors.WithLazyPrefix.spec (GF := GF))
    (hvalidatingObjectWalker_doScalar : typed.validatingObjectWalker.doScalar.spec (GF := GF))
    (hvalidatingObjectWalker_doList : typed.validatingObjectWalker.doList.spec (GF := GF))
    (hvalidatingObjectWalker_doMap : typed.validatingObjectWalker.doMap.spec (GF := GF)) :
    typed.validatingObjectWalker.validate.spec (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
