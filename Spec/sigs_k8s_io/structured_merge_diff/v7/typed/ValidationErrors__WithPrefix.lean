/-
`ValidationErrors.WithPrefix(prefix)`: prefixes each error's path, in place, and returns the
slice.

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
abbrev typed.ValidationErrors.WithPrefix.spec : Prop :=
  ∀ (errs : GoSlice) (es : List _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.ValidationError) (pfx : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ errs ↦* es }}
    (App (Val (errs @!! _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.ValidationErrors.ty @!! go!"WithPrefix")) (Val #pfx))
  {{ RET #errs; errs ↦* (es.map (fun e => { e with Path' := pfx ++ e.Path' })) }}

end spec

end smd
end EtcdGrove
end Perennial
