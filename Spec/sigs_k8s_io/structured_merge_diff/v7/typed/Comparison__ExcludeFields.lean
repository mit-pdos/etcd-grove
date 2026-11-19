/-
`(*Comparison).ExcludeFields(fields)` with no fields (nil): the comparison itself, unchanged.
Out of the scope otherwise: `Updater.update` calls it only when `IgnoredFields` is not nil, which
the scope excludes (`issues/smd-ignoredfields-missing-version-panic.md`).

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
abbrev typed.Comparison.ExcludeFields.spec : Prop :=
  ∀ (c : Loc) (C : Cmp) (fields : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ isComparison c C ∗ ⌜fields = null⌝ }}
    (App (Val (c @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.Comparison.ty @!! go!"ExcludeFields")) (Val #fields))
  {{ RET #c; isComparison c C }}

end spec

end smd
end EtcdGrove
end Perennial
