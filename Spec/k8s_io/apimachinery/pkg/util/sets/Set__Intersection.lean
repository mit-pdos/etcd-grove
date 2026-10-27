/-
`Set[T].Intersection(s2)` (`set.go:156`): a new set. Lean-first; for `storeIndex.addIndexers`'s
error message, which needs only that it returns a set.
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.util.sets.Assumptions]

/-- `s1.Intersection(s2)`: a new set (its contents unspecified); both sets read only. -/
abbrev Set.Intersection.spec : Prop :=
  ∀ {K : Type} [ZeroVal K] [DecidableEq K] [go.IntoValInj K] [TypedPointsto (GF := GF) K]
    {T : go.GoType} [IntoValTyped (GF := GF) K T] [∀ k : K, SafeMapKey (GF := GF) T k]
    (m1 m2 : Loc) (d1 d2 : DFrac) (s1 s2 : GMap K Elem),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.sets ∗ m1 ↦${d1} s1 ∗
      m2 ↦${d2} s2 }}
    (App (Val (m1 @!! Set'.ty T @!! go!"Intersection")) (Val #m2))
  {{ (r : Loc), RET #r; m1 ↦${d1} s1 ∗ m2 ↦${d2} s2 ∗ ∃ s : GMap K Elem, r ↦$ s }}

end spec

end sets
end EtcdGrove
end Perennial
