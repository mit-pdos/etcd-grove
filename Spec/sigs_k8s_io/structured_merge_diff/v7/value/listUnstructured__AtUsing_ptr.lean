/-
`listUnstructured.AtUsing(a, i)` through a `*listUnstructured` (the pointer view `ListEqualsUsing` gets): item `i` in a wrapper from `a`, owned whole
(the caller may free it, or keep it). Called by `typed` (`validatingObjectWalker`,
`mergingWalker`).

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
abbrev value.listUnstructured.AtUsing_ptr.spec : Prop :=
  ∀ (p : Loc) (vs : List UVal) (al : value.Allocator) (n : w64) (x : UVal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.value ∗ isListV (interface.mkOk (go.GoType.PointerType value.listUnstructured.ty) #p) vs ∗ isAlloc al ∗ ⌜0 ≤ n.toInt ∧ vs[n.toInt.toNat]? = some x⌝ }}
    (App (App (Val (p @!! (go.GoType.PointerType value.listUnstructured.ty) @!! go!"AtUsing")) (Val #al)) (Val #n))
  {{ (v : value.Value), RET #v; isAlloc al ∗ isValF v (DFrac.own 1) x }}

end spec

end smd
end EtcdGrove
end Perennial
