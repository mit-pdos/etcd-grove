/-
`typed.getAssociativeKeyDefault`: not proved yet (`sorry`): the stage's Prove step, after the freeze
(notes/smd-plan.md). Draft (2026-11-19).

Callees without a spec file here (other packages', the standard library's, or the
walker's own interface calls through a bundle): `errors.New`.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.getAssociativeKeyDefault
public import Spec.sigs_k8s_io.structured_merge_diff.v7.schema.Schema__Resolve
public import Spec.sigs_k8s_io.structured_merge_diff.v7.schema.Map__FindField

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

theorem typed.getAssociativeKeyDefault.wp_proof
    (hSchema_Resolve : schema.Schema.Resolve.spec (GF := GF))
    (hMap_FindField : schema.Map.FindField.spec (GF := GF)) :
    typed.getAssociativeKeyDefault.spec (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
