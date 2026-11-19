/-
`toFieldSetWalker.finished()` (internal): resets the walker (schema, type, path, set) and puts it
back in `tPool` (`twPooled`). The set stays with the caller (it was read before).

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
abbrev typed.toFieldSetWalker.finished.spec : Prop :=
  ∀ (w sc : Loc) (S : Schema) (st : TWSt) (ps : fieldpath.Path) (s sp : Loc) (a : value.Allocator),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ twCore w sc S st ps s sp a ∗ spareWalkers _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.toFieldSetWalker sp }}
    (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.toFieldSetWalker.ty @!! go!"finished")) (Val #()))
  {{ RET #(); True }}

end spec

end smd
end EtcdGrove
end Perennial
