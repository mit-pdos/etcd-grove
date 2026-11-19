/-
`(*heapAllocator).Free(x)`: a no-op (takes nothing; the `Allocator` bundle's `Free` triple,
which consumes `freeable x`, is an instance).

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
abbrev value.heapAllocator.Free.spec : Prop :=
  ∀ (p : Loc) (x : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.value }}
    (App (Val (p @!! (go.GoType.PointerType value.heapAllocator.ty) @!! go!"Free")) (Val #x))
  {{ RET #(); True }}

end spec

end smd
end EtcdGrove
end Perennial
