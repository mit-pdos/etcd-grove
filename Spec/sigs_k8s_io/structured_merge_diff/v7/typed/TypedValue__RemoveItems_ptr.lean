/-
`TypedValue.RemoveItems` called through a `*TypedValue` (`Updater.prune`'s
`convertedMerged.RemoveItems(...)`): see `TypedValue.RemoveItems`.

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
abbrev typed.TypedValue.RemoveItems_ptr.spec : Prop :=
  ∀ (tp ip sc : Loc) (S : Schema) (t : TypeRef) (x : UVal) (R : PathSet),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ isTV tp sc S t x ∗ isSet ip R ∗ ⌜conforms S t (removeItems S t x R)⌝ }}
    (App (Val (tp @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.TypedValue.ty @!! go!"RemoveItems")) (Val #ip))
  {{ (p : Loc), RET #p; isTV p sc S t (removeItems S t x R) }}

end spec

end smd
end EtcdGrove
end Perennial
