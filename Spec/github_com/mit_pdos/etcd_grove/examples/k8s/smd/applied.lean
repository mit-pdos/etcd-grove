/-
`applied(paths...)`: the applied versioned set of the paths at the scenario's version.

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
abbrev applied.spec : Prop :=
  ∀ (s : GoSlice) (dq : DFrac) (ss : List GoSlice) (ps : List Path),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.smd ∗ s ↦*{dq} ss ∗ ownPaths ss ps }}
    (App (Val (@! _root_.Perennial.github_com.mit_pdos.etcd_grove.examples.k8s.smd.applied)) (Val #s))
  {{ (v : GoInterface), RET #v; s ↦*{dq} ss ∗ ownVSet v (applied ps) }}

end spec

end k8s_smd
end EtcdGrove
end Perennial
