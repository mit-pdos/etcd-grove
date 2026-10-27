/-
`(*threadSafeMap).LastStoreSyncResourceVersion()` (`thread_safe_store.go:439`): the store's
resource version, under the read lock, when the `AtomicFIFO` gate is on. Lean-first; phase 4 of
`notes/k8s-daemonset-plan.md` (the consistency store reads it through the informers' stores).
-/
module

public import Proof.k8s_io.client_go.tools.cache.TSDefs
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

/-- **`c.LastStoreSyncResourceVersion()`**, logically atomic (a reader), with the `AtomicFIFO`
gate on (`features.gateIs`, a premise: `Main` sets it): the resource version at the
linearization point. Needs one of the lock's reader slots. -/
abbrev threadSafeMap.LastStoreSyncResourceVersion.spec : Prop :=
  ∀ (c : Loc) (γ : TsNames) (OK : GoInterface → IProp GF) (Fam : Nat → Fn),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ isTS c γ OK Fam ∗
      tsReader c γ OK Fam ∗ features.gateIs k8s_io.client_go.features.AtomicFIFO true }}
  <<{ ∀∀ σ, storeSt γ σ }>>
    (App (Val (c @!! go.GoType.PointerType threadSafeMap.ty @!! go!"LastStoreSyncResourceVersion"))
      (Val #()))
    @@ ∅
  <<{ storeSt γ σ }>>
  {{ RET #σ.rv; tsReader c γ OK Fam }}

end spec

end cache
end EtcdGrove
end Perennial
