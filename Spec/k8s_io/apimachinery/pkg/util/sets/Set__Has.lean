/-
`Set[T].Has(item)` (`set.go`): membership. Lean-first; for client-go's work queue.
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

/-- `s.Has(item)`: whether `item` is in the set. -/
abbrev Set.Has.spec : Prop :=
  ∀ {K : Type} [ZeroVal K] [DecidableEq K] [go.IntoValInj K] [TypedPointsto (GF := GF) K]
    {T : go.GoType} [IntoValTyped (GF := GF) K T] (m : Loc) (dq : DFrac) (s : GMap K Elem) (k : K)
    [SafeMapKey (GF := GF) T k],
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.sets ∗ m ↦${dq} s }}
    (App (Val (m @!! Set'.ty T @!! go!"Has")) (Val #k))
  {{ RET #(decide ((s !! k).isSome)); m ↦${dq} s }}

end spec

end sets
end EtcdGrove
end Perennial
