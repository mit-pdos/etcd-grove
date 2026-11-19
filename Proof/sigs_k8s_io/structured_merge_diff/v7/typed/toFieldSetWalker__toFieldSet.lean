/-
`typed.toFieldSetWalker.toFieldSet`: not proved yet (`sorry`): the stage's Prove step, after the freeze
(notes/smd-plan.md). Draft (2026-11-19).

Recursive (`toFieldSet` → `resolveSchema` → `doList`/`doMap` → `visit*` → `toFieldSet`): the link needs a form for a cycle of specs (open question in the report).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.toFieldSetWalker__toFieldSet
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.resolveSchema
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.toFieldSetWalker__doScalar
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.toFieldSetWalker__doList
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.toFieldSetWalker__doMap

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

theorem typed.toFieldSetWalker.toFieldSet.wp_proof
    (hresolveSchema : typed.resolveSchema.spec (GF := GF))
    (htoFieldSetWalker_doScalar : typed.toFieldSetWalker.doScalar.spec (GF := GF))
    (htoFieldSetWalker_doList : typed.toFieldSetWalker.doList.spec (GF := GF))
    (htoFieldSetWalker_doMap : typed.toFieldSetWalker.doMap.spec (GF := GF)) :
    typed.toFieldSetWalker.toFieldSet.spec (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
