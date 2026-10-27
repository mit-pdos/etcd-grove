/-
`(*cache).Replace(list, rv)` (`store.go`): the items keyed by the key function, then the thread-safe store's `Replace`. Lean-first; phase 4 of `notes/k8s-daemonset-plan.md` (the `cache` wrapper, `store.go`).
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

/-- **`c.Replace(list, rv)`**, logically atomic: the items become the list's objects by their
keys (`keyedItems KF xs`: a later object at a key wins), the resource version `rv`. -/
abbrev cache.Replace.spec : Prop :=
  ∀ (ca ts : Loc) (γ : TsNames) (OK : GoInterface → IProp GF) (Fam : Nat → Fn)
    (KF : GoInterface → GoString) (sl : GoSlice) (xs : List GoInterface) (rv : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ isCache ca ts γ OK Fam KF ∗
      sl ↦* xs ∗ □ ([∗list] x ∈ xs, OK x) }}
  <<{ ∀∀ σ, storeSt γ σ }>>
    (App (App (Val (ca @!! go.GoType.PointerType k8s_io.client_go.tools.cache.cache.ty @!! go!"Replace")) (Val #sl)) (Val #rv))
    @@ ∅
  <<{ storeSt γ (σ.replace (keyedItems KF xs) rv) }>>
  {{ RET #interface.nil; sl ↦* xs }}

end spec

end cache
end EtcdGrove
end Perennial
