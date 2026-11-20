/-
`(*listUnstructuredRange).Next()`: advances the cursor; whether it is on an item (internal).

Internal to `value` (PRINCIPLES, "Scope": may mirror its code).

Lean-first (2026-11-19, notes/smd-plan.md): Draft, the stage's per-package specs of `value`.
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.Base
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.Defs
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.Objects

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
variable [package_sem : value.Assumptions]

/-- See the file header. The premise `n < vs.length` (post-freeze change B2c, 2026-11-20): `Next` is
called only while the cursor is before the end, so the cursor's increment does not overflow. -/
abbrev value.listUnstructuredRange.Next.spec : Prop :=
  ∀ (q : Loc) (vs : List UVal) (n : Int),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.value ∗ ownRange (interface.mkOk (go.GoType.PointerType value.listUnstructuredRange.ty) #q) vs n ∗ ⌜n < vs.length⌝ }}
    (App (Val (q @!! (go.GoType.PointerType value.listUnstructuredRange.ty) @!! go!"Next")) (Val #()))
  {{ (b : Bool), RET #b; ownRange (interface.mkOk (go.GoType.PointerType value.listUnstructuredRange.ty) #q) vs (n + 1) ∗ ⌜b = decide (n + 1 < vs.length)⌝ }}

end spec

end smd
end EtcdGrove
end Perennial
