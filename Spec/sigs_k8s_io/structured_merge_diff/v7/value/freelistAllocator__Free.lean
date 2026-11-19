/-
`(*freelistAllocator).Free(x)`: takes back a wrapper or a range owned whole (cleared, kept
for reuse if the freelist has room); a no-op on anything else in scope (`freeable`).

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
abbrev value.freelistAllocator.Free.spec : Prop :=
  ∀ (p : Loc) (x : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.value ∗ isAlloc (interface.mkOk (go.GoType.PointerType value.freelistAllocator.ty) #p) ∗ freeable x }}
    (App (Val (p @!! (go.GoType.PointerType value.freelistAllocator.ty) @!! go!"Free")) (Val #x))
  {{ RET #(); isAlloc (interface.mkOk (go.GoType.PointerType value.freelistAllocator.ty) #p) }}

end spec

end smd
end EtcdGrove
end Perennial
