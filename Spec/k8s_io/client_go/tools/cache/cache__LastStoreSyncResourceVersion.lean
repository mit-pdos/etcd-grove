/-
`(*cache).LastStoreSyncResourceVersion()` (`store.go`): the thread-safe store's. Lean-first; phase 4 of `notes/k8s-daemonset-plan.md` (the `cache` wrapper, `store.go`).
-/
module

public import Proof.k8s_io.client_go.tools.cache.CacheDefs
public import Proof.k8s_io.client_go.features.GateDefs

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

/-- **`c.LastStoreSyncResourceVersion()`**, logically atomic (a reader), with the `AtomicFIFO` gate
on: the resource version. -/
abbrev cache.LastStoreSyncResourceVersion.spec : Prop :=
  ∀ (ca ts : Loc) (γ : TsNames) (OK : GoInterface → IProp GF) (Fam : Nat → Fn)
    (kf : GoFunc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ isCache ca ts γ OK Fam kf ∗ tsReader ts γ OK Fam ∗
      features.gateIs k8s_io.client_go.features.AtomicFIFO true }}
  <<{ ∀∀ σ, storeSt γ σ }>>
    (App (Val (ca @!! go.GoType.PointerType k8s_io.client_go.tools.cache.cache.ty @!! go!"LastStoreSyncResourceVersion")) (Val #()))
    @@ ∅
  <<{ storeSt γ σ }>>
  {{ RET #σ.rv; tsReader ts γ OK Fam }}

end spec

end cache
end EtcdGrove
end Perennial
