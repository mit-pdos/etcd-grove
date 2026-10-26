/-
`Set[T].Insert(items...)` (`set.go`): adds the items, returns the set. Lean-first; for client-go's work queue.
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

/-- `s.Insert(items...)`: the items in the set (`insertAll`). -/
abbrev Set.Insert.spec : Prop :=
  ∀ {K : Type} [ZeroVal K] [DecidableEq K] [go.IntoValInj K] [TypedPointsto (GF := GF) K]
    {T : go.GoType} [IntoValTyped (GF := GF) K T] [∀ k : K, SafeMapKey (GF := GF) T k]
    (m : Loc) (s : GMap K Elem) (sl : GoSlice) (dq : DFrac) (ks : List K),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.sets ∗ m ↦$ s ∗ sl ↦*{dq} ks }}
    (App (Val (m @!! Set'.ty T @!! go!"Insert")) (Val #sl))
  {{ RET #m; m ↦$ insertAll s ks ∗ sl ↦*{dq} ks }}

end spec

end sets
end EtcdGrove
end Perennial
