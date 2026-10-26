/-
`Set[T].Delete(items...)` (`set.go`): removes the items, returns the set. Lean-first; for client-go's work queue.
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

/-- `s.Delete(items...)`: none of the items in the set (`deleteAll`). -/
abbrev Set.Delete.spec : Prop :=
  ∀ {K : Type} [ZeroVal K] [DecidableEq K] [go.IntoValInj K] [TypedPointsto (GF := GF) K]
    {T : go.GoType} [IntoValTyped (GF := GF) K T] [∀ k : K, SafeMapKey (GF := GF) T k]
    (m : Loc) (s : GMap K Elem) (sl : GoSlice) (dq : DFrac) (ks : List K),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.sets ∗ m ↦$ s ∗ sl ↦*{dq} ks }}
    (App (Val (m @!! Set'.ty T @!! go!"Delete")) (Val #sl))
  {{ RET #m; m ↦$ deleteAll s ks ∗ sl ↦*{dq} ks }}

end spec

end sets
end EtcdGrove
end Perennial
