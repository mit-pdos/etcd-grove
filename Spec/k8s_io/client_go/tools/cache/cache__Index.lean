/-
`(*cache).Index(n, obj)` (`store.go`): the thread-safe store's `Index`. Lean-first; phase 4 of `notes/k8s-daemonset-plan.md` (the `cache` wrapper, `store.go`).
-/
module

public import Proof.k8s_io.client_go.tools.cache.CacheDefs
public import Spec.k8s_io.client_go.tools.cache.threadSafeMap__Index

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI k8s_io.client_go.tools.cache

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- **`c.Index(n, obj)`**, logically atomic (a reader): `threadSafeMap.Index`'s result. -/
abbrev cache.Index.spec : Prop :=
  ∀ (ca ts : Loc) (γ : TsNames) (OK : GoInterface → IProp GF) (Fam : Nat → Fn GF)
    (kf : GoFunc) (n : GoString) (obj : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ isCache ca ts γ OK Fam kf ∗ tsReader ts γ OK Fam ∗
      □ OK obj }}
  <<{ ∀∀ σ, storeSt γ σ }>>
    (App (App (Val (ca @!! go.GoType.PointerType k8s_io.client_go.tools.cache.cache.ty @!! go!"Index")) (Val #n)) (Val #obj))
    @@ ∅
  <<{ storeSt γ σ }>>
  {{ (sl : GoSlice) (err : GoInterface), RET (PairV #sl #err);
      indexPost OK Fam σ n obj sl err ∗ tsReader ts γ OK Fam }}

end spec

end cache
end EtcdGrove
end Perennial
