/-
`New[T](items...)` (`set.go:31`): a new set of the items. Lean-first; for `Set.Intersection`.
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

/-- `New(ks...)`: a new set of the items `ks`. -/
abbrev New.spec : Prop :=
  ∀ {K : Type} [ZeroVal K] [DecidableEq K] [go.IntoValInj K] [TypedPointsto (GF := GF) K]
    {T : go.GoType} [IntoValTyped (GF := GF) K T] [∀ k : K, SafeMapKey (GF := GF) T k]
    (sl : GoSlice) (dq : DFrac) (ks : List K),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.sets ∗ sl ↦*{dq} ks }}
    (App (Val #(functions New [T])) (Val #sl))
  {{ (r : Loc), RET #r; r ↦$ insertAll ∅ ks ∗ sl ↦*{dq} ks }}

end spec

end sets
end EtcdGrove
end Perennial
