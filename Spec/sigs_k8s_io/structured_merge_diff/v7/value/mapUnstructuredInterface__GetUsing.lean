/-
`mapUnstructuredInterface.GetUsing`. Out of scope: a `map[interface{}]interface{}` is not admitted by `isIface` (no value of the
scope has this view); the precondition is `False`, so no client can call it.

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

/-- See the file header. -/
abbrev value.mapUnstructuredInterface.GetUsing.spec : Prop :=
  ∀ (m : GoMap) (al : value.Allocator) (k : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.value ∗ ⌜False⌝ }}
    (App (App (Val (m @!! value.mapUnstructuredInterface.ty @!! go!"GetUsing")) (Val #al)) (Val #k))
  {{ (v : value.Value) (ok : Bool), RET (PairV #v #ok); True }}

end spec

end smd
end EtcdGrove
end Perennial
