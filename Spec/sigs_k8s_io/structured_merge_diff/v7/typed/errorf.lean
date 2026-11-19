/-
`typed.errorf(format, args...)` (internal): one validation error, its message formatted.

Margin: the arguments include values `fmt.Sprintf`'s trust-boundary spec does not cover today
(`ArgsWf`: a `value.Value`, a `schema.TypeRef`): its proof needs a `fmt` spec for any arguments
(that `Sprintf` returns some string).

Draft (2026-11-19, notes/smd-plan.md, "The call DAG": the `typed` rows).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.Base
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.Walkers

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI
open sigs_k8s_io.structured_merge_diff.v7

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : typed.Assumptions]

/-- See the file header. -/
abbrev typed.errorf.spec : Prop :=
  ∀ (format : GoString) (args : GoSlice) (xs : List GoInterface) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ args ↦*{dq} xs }}
    (App (App (Val (@! _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.errorf)) (Val #format)) (Val #args))
  {{ (errs : GoSlice), RET #errs; args ↦*{dq} xs ∗ ∃ e, ownErrs errs [e] }}

end spec

end smd
end EtcdGrove
end Perennial
