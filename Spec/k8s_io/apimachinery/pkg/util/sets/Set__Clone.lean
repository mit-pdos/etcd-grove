/-
`Set[T].Clone()` (`set.go`): a copy. Lean-first; for the union builder's `ToDecision`. Lean-first
(no Rocq counterpart).
-/
module

public import Proof.k8s_io.apimachinery.pkg.util.sets.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace sets

open Iris Iris.BI k8s_io.apimachinery.pkg.util.sets

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.util.sets.Assumptions]

/-- See the file header. -/
abbrev Set.Clone.spec : Prop :=
  ∀ {K : Type} [ZeroVal K] [DecidableEq K] [go.IntoValInj K] [TypedPointsto (GF := GF) K]
    {T : go.GoType} [IntoValTyped (GF := GF) K T] [∀ k : K, SafeMapKey (GF := GF) T k]
    (m : Loc) (dq : DFrac) (s : GMap K Elem),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.sets ∗ m ↦${dq} s }}
    (App (Val (m @!! Set''.ty T @!! go!"Clone")) (Val #()))
  {{ (r : Loc), RET #r; m ↦${dq} s ∗ r ↦$ s }}

end spec

end sets
end EtcdGrove
end Perennial
