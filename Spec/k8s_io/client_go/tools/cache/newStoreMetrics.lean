/-
`newStoreMetrics(id, metricsProvider)` (`informer_metrics.go:97`): the store's metrics, a no-op
gauge unless the identity is reserved. Lean-first.
-/
module

public import Proof.k8s_io.client_go.tools.cache.TSDefs

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

/-- `newStoreMetrics(id, p)` for an identity without a reservation and a provider (as
`NewThreadSafeStore`'s, the zero identity and the no-op provider): metrics whose gauge meets its
contract (the no-op gauge). -/
abbrev newStoreMetrics.spec : Prop :=
  ∀ (id : InformerNameAndResource) (p : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗
      ⌜id.reserved' = null ∧ p ≠ interface.nil⌝ }}
    (App (App (Val (@! newStoreMetrics)) (Val #id)) (Val #p))
  {{ (mp : Loc), RET #mp; ∃ g : GaugeMetric,
      structFieldRef storeMetrics go!"storeResourceVersion" mp ↦□ g ∗ gaugeOk g }}

end spec

end cache
end EtcdGrove
end Perennial
