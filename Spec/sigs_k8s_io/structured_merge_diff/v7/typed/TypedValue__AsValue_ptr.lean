/-
`TypedValue.AsValue()` called through a `*TypedValue` (as the driver's `s.live.AsValue()`): the
value it holds.

Lean-first (2026-11-19, notes/smd-plan.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.merge.Base
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.Defs

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
variable [package_sem : merge.Assumptions]

/-- See the file header. -/
abbrev typed.TypedValue.AsValue_ptr.spec : Prop :=
  ∀ (p sc : Loc) (S : Schema) (t : TypeRef) (x : UVal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ isTV p sc S t x }}
    (App (Val (p @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.TypedValue.ty @!! go!"AsValue")) (Val #()))
  {{ (v : value.Value), RET #v; isVal v x }}

end spec

end smd
end EtcdGrove
end Perennial
