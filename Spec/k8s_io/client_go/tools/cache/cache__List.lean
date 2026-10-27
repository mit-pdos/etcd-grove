/-
`(*cache).List()` (`store.go`): the thread-safe store's `List`. Lean-first; phase 4 of `notes/k8s-daemonset-plan.md` (the `cache` wrapper, `store.go`).
-/
module

public import Proof.k8s_io.client_go.tools.cache.CacheDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI k8s_io.client_go.tools.cache

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- **`c.List()`**, logically atomic (a reader): every item once. -/
abbrev cache.List.spec : Prop :=
  ∀ (ca ts : Loc) (γ : TsNames) (OK : GoInterface → IProp GF) (Fam : Nat → Fn)
    (KF : GoInterface → GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ isCache ca ts γ OK Fam KF ∗ tsReader ts γ OK Fam }}
  <<{ ∀∀ σ, storeSt γ σ }>>
    (App (Val (ca @!! go.GoType.PointerType k8s_io.client_go.tools.cache.cache.ty @!! go!"List")) (Val #()))
    @@ ∅
  <<{ storeSt γ σ }>>
  {{ (sl : GoSlice), RET #sl; ∃ ks : List GoString,
      ⌜ks.Nodup ∧ ∀ k, k ∈ ks ↔ k ∈ σ.items⌝ ∗ sl ↦* (ks.map (objAt σ.items)) ∗
      ([∗list] o ∈ ks.map (objAt σ.items), okNil OK o) ∗ tsReader ts γ OK Fam }}

end spec

end cache
end EtcdGrove
end Perennial
