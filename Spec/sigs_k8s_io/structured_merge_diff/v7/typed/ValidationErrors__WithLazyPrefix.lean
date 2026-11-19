/-
`ValidationErrors.WithLazyPrefix(fn)`: when there are errors, prefixes each one's path with
`fn()` (`""` for a nil `fn`), in place; returns the slice. `fn` is called only when there are
errors, so a walker with none passes any `fn` (`prefixOk` is needed only for errors).

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
abbrev typed.ValidationErrors.WithLazyPrefix.spec : Prop :=
  ∀ (errs : GoSlice) (es : List _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.ValidationError) (f : GoFunc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ errs ↦* es ∗ (⌜es = []⌝ ∨ prefixOk f) }}
    (App (Val (errs @!! _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.ValidationErrors.ty @!! go!"WithLazyPrefix")) (Val #f))
  {{ RET #errs; ∃ es' : List _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.ValidationError, errs ↦* es' ∗ ⌜es'.length = es.length⌝ }}

end spec

end smd
end EtcdGrove
end Perennial
