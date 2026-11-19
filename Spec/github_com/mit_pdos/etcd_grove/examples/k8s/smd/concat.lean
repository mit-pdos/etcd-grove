/-
`concat(a, b)`: a new slice of `a`'s paths then `b`'s.

Lean-first (2026-11-19, notes/smd-robustness.md).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.smd.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_smd

open Iris Iris.BI
open smd

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.smd.Assumptions]

/-- See the file header. -/
abbrev concat.spec : Prop :=
  ∀ (a b : GoSlice) (dqa dqb : DFrac) (xs ys : List GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.smd ∗ a ↦*{dqa} xs ∗ b ↦*{dqb} ys }}
    (App (App (Val (@! _root_.Perennial.github_com.mit_pdos.etcd_grove.examples.k8s.smd.concat)) (Val #a)) (Val #b))
  {{ (r : GoSlice), RET #r; a ↦*{dqa} xs ∗ b ↦*{dqb} ys ∗ r ↦* (xs ++ ys) }}

end spec

end k8s_smd
end EtcdGrove
end Perennial
