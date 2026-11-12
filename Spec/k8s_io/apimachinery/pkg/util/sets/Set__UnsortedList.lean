/-
`Set[T].UnsortedList()` (`set.go:202`): the items, in some order. Lean-first; for `sets.List`.
-/
module

public import Proof.k8s_io.apimachinery.pkg.util.sets.Defs

@[expose] public section

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

/-- `s.UnsortedList()`: a new slice of the set's items, each once, in some order. -/
abbrev Set.UnsortedList.spec : Prop :=
  ∀ {K : Type} [ZeroVal K] [DecidableEq K] [go.IntoValInj K] [TypedPointsto (GF := GF) K]
    {T : go.GoType} [IntoValTyped (GF := GF) K T] (m : Loc) (dq : DFrac) (s : GMap K Elem),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.sets ∗ m ↦${dq} s }}
    (App (Val (m @!! Set'.ty T @!! go!"UnsortedList")) (Val #()))
  {{ (sl : GoSlice) (ks : List K), RET #sl; m ↦${dq} s ∗ sl ↦* ks ∗
      ⌜(∀ k, k ∈ ks ↔ (s !! k).isSome) ∧ ks.Nodup ∧ ks.length = GMap.size s⌝ }}

end spec

end sets
end EtcdGrove
end Perennial
