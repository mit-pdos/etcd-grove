/-
`(*freelistAllocator).allocValueUnstructured()`: a spare wrapper or a fresh one, owned whole
(internal).

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
abbrev value.freelistAllocator.allocValueUnstructured.spec : Prop :=
  ∀ (p : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.value ∗ isAlloc (interface.mkOk (go.GoType.PointerType value.freelistAllocator.ty) #p) }}
    (App (Val (p @!! (go.GoType.PointerType value.freelistAllocator.ty) @!! go!"allocValueUnstructured")) (Val #()))
  {{ (q : Loc), RET #q; isAlloc (interface.mkOk (go.GoType.PointerType value.freelistAllocator.ty) #p) ∗ wrapperOwn q }}

end spec

end smd
end EtcdGrove
end Perennial
