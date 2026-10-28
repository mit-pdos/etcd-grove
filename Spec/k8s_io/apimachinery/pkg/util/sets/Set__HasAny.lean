/-
`Set[T].HasAny(items...)` (`set.go:93`): whether any of the items is in the set. Lean-first; for
client-go's thread-safe store (`storeIndex.addIndexers`).
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

/-- `s.HasAny(ks...)`: whether some item of `ks` is in the set. -/
abbrev Set.HasAny.spec : Prop :=
  ∀ {K : Type} [ZeroVal K] [DecidableEq K] [go.IntoValInj K] [TypedPointsto (GF := GF) K]
    {T : go.GoType} [IntoValTyped (GF := GF) K T] [∀ k : K, SafeMapKey (GF := GF) T k]
    (m : Loc) (dq : DFrac) (s : GMap K Elem) (sl : GoSlice) (dl : DFrac) (ks : List K),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.sets ∗ m ↦${dq} s ∗
      sl ↦*{dl} ks }}
    (App (Val (m @!! Set'.ty T @!! go!"HasAny")) (Val #sl))
  {{ RET #(decide (∃ k ∈ ks, (s !! k).isSome)); m ↦${dq} s ∗ sl ↦*{dl} ks }}

end spec

end sets
end EtcdGrove
end Perennial
