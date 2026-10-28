/-
`KeySet[T, V](theMap)` (`set.go:40`): the set of a map's keys. Lean-first; for client-go's
thread-safe store (`storeIndex.addIndexers`).
-/
module

public import Proof.k8s_io.apimachinery.pkg.util.sets.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace sets

open Iris Iris.BI k8s_io.apimachinery.pkg.util.sets

/-- The set of a map's keys. -/
def keysOf {K V : Type} [GooseExts] [DecidableEq K] (m : GMap K V) : GMap K Elem :=
  GMap.fmap (fun _ => present) m

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.util.sets.Assumptions]

/-- `KeySet(m)`: a new set of `m`'s keys; `m` read only. -/
abbrev KeySet.spec : Prop :=
  ∀ {K V : Type} [ZeroVal K] [DecidableEq K] [go.IntoValInj K] [TypedPointsto (GF := GF) K]
    {T : go.GoType} [IntoValTyped (GF := GF) K T] [∀ k : K, SafeMapKey (GF := GF) T k]
    [ZeroVal V] [TypedPointsto (GF := GF) V] {Vt : go.GoType} [IntoValTyped (GF := GF) V Vt]
    (mref : Loc) (dq : DFrac) (m : GMap K V),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.sets ∗ mref ↦${dq} m }}
    (App (Val #(functions KeySet [T, Vt])) (Val #mref))
  {{ (r : Loc), RET #r; mref ↦${dq} m ∗ r ↦$ keysOf m }}

end spec

end sets
end EtcdGrove
end Perennial
