/-
`value.Equals(lhs, rhs)`: whether the two values are equal (maps by their entries, lists in
order; no floats in scope, so equality is exact). It only reads the two wrappers: any shares
`dq1`, `dq2` are given back (so SMD's own recursion, which lends wrappers it rewrites, and a client
with the persistent `isVal` are both instances).

Lean-first (2026-11-19, notes/smd-plan.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.Base
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.Defs

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
abbrev value.Equals.spec : Prop :=
  ∀ (a b : value.Value) (dq1 dq2 : DFrac) (x y : UVal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.value ∗
      isValF a dq1 x ∗ isValF b dq2 y }}
    (App (App (Val (@! _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.value.Equals)) (Val #a)) (Val #b))
  {{ (r : Bool), RET #r; isValF a dq1 x ∗ isValF b dq2 y ∗ ⌜r = true ↔ x = y⌝ }}

end spec

end smd
end EtcdGrove
end Perennial
