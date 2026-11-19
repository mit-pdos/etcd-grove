/-
`(*listUnstructuredRange).Item()`: the cursor's index and item, in the range's own wrapper,
lent whole (rewritten at the next `Item`): giving it back gives the range back (internal).

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
abbrev value.listUnstructuredRange.Item.spec : Prop :=
  ∀ (q : Loc) (vs : List UVal) (n : Int) (x : UVal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.value ∗ ownRange (interface.mkOk (go.GoType.PointerType value.listUnstructuredRange.ty) #q) vs n ∗ ⌜0 ≤ n ∧ vs[n.toNat]? = some x⌝ }}
    (App (Val (q @!! (go.GoType.PointerType value.listUnstructuredRange.ty) @!! go!"Item")) (Val #()))
  {{ (j : w64) (v : value.Value), RET (PairV #j #v); ⌜j.toInt = n⌝ ∗
      isValF v (DFrac.own 1) x ∗ (isValF v (DFrac.own 1) x -∗ ownRange (interface.mkOk (go.GoType.PointerType value.listUnstructuredRange.ty) #q) vs n) }}

end spec

end smd
end EtcdGrove
end Perennial
