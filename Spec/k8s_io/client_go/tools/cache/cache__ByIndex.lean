/-
`(*cache).ByIndex(n, v)` (`store.go`): the thread-safe store's `ByIndex`. Lean-first; phase 4 of `notes/k8s-daemonset-plan.md` (the `cache` wrapper, `store.go`).
-/
module

public import Proof.k8s_io.client_go.tools.cache.CacheDefs
public import Spec.k8s_io.client_go.tools.cache.threadSafeMap__ByIndex

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

/-- **`c.ByIndex(n, v)`**, logically atomic (a reader): `threadSafeMap.ByIndex`'s result. -/
abbrev cache.ByIndex.spec : Prop :=
  ∀ (ca ts : Loc) (γ : TsNames) (OK : GoInterface → IProp GF) (Fam : Nat → Fn)
    (kf : GoFunc) (n v : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ isCache ca ts γ OK Fam kf ∗ tsReader ts γ OK Fam }}
  <<{ ∀∀ σ, storeSt γ σ }>>
    (App (App (Val (ca @!! go.GoType.PointerType k8s_io.client_go.tools.cache.cache.ty @!! go!"ByIndex")) (Val #n)) (Val #v))
    @@ ∅
  <<{ storeSt γ σ }>>
  {{ (sl : GoSlice) (err : GoInterface), RET (PairV #sl #err);
      byIndexPost OK Fam σ n v sl err ∗ tsReader ts γ OK Fam }}

end spec

end cache
end EtcdGrove
end Perennial
