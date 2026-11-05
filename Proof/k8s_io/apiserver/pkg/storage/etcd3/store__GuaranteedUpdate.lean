/-
Lean-first (no Rocq counterpart).

The proof of `(*store).GuaranteedUpdate`: the prepared key, tracing (no-ops), the destination's
`reflect.Value`, the initial read (`getCurrentState`, through `rwInv` as `conditionalDelete`'s,
D30n), then the loop, whose invariant is the store's reading `s` of the key's key-value at a state
`σ` the read fired at (`rdFacts`), with the caller's result if `σ` hands (the model's step is the
identity there), else the token `W` (as `conditionalDelete`'s). Each iteration runs `tryUpdate`
(`updateState`): an error is the model's answer at `σ` (`update_err`, so `σ` hands); otherwise the
result's encoding is either the stored data, not stale, and the store skips the write (the model's
no-op at `σ`, `update_skip`), or `updateOnce` either answers (an error, or the write) or, on a
conflict, gives the next iteration's reading.
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__GuaranteedUpdate
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__prepareKey
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__getCurrentState
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__getStateFromObject
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__updateState
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__updateOnce
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.refreshOnError
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.getTypeName
public import Spec.k8s_io.apiserver.pkg.storage.Preconditions__Check
public import Spec.k8s_io.apimachinery.pkg.conversion.EnforcePtr
public import Spec.k8s_io.component_base.tracing.Start
public import Spec.k8s_io.component_base.tracing.Span__AddEvent
public import Spec.k8s_io.component_base.tracing.Span__End
public import Spec.go_opentelemetry_io.otel.attribute.String
public import Spec.go_opentelemetry_io.otel.attribute.Int
public import Spec.k8s_io.apiserver.pkg.audit.GetAuditIDTruncated
public import Perennial.Proof.bytes.Link

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 16384

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

theorem store.GuaranteedUpdate.wp_proof
    (wp_prepareKey : store.prepareKey.spec (GF := GF) (hG := hG))
    (wp_getTypeName : getTypeName.spec (GF := GF) (hG := hG))
    (wp_EnforcePtr : conversion.EnforcePtr.spec (GF := GF) (hG := hG))
    (wp_getCur : store.getCurrentState.spec (GF := GF) (hG := hG))
    (wp_getStateFromObject : store.getStateFromObject.spec (GF := GF) (hG := hG))
    (wp_Check : storage.Preconditions.Check.spec (GF := GF) (hG := hG))
    (wp_updateState : store.updateState.spec (GF := GF) (hG := hG))
    (wp_updateOnce : store.updateOnce.spec (GF := GF) (hG := hG))
    (wp_refresh : refreshOnError.spec (GF := GF) (hG := hG))
    (wp_Start : tracing.Start.spec (GF := GF) (hG := hG))
    (wp_AddEvent : tracing.Span.AddEvent.spec (GF := GF) (hG := hG))
    (wp_End : tracing.Span.End.spec (GF := GF) (hG := hG))
    (wp_String : «attribute».String.spec (GF := GF) (hG := hG))
    (wp_Int : «attribute».Int.spec (GF := GF) (hG := hG))
    (wp_GetAuditIDTruncated : audit.GetAuditIDTruncated.spec (GF := GF) (hG := hG)) :
    store.GuaranteedUpdate.spec (GF := GF) (hG := hG) := by
  -- Stage 7b: restated at the Draft; the proof (at a93fbf6a24, before the restatement) is
  -- adapted in the Prove phase, after the Freeze: the cached object (`getStateFromObject`, `cachedOk`, the D1 premise), `Preconditions.Check`, `ignoreNotFound`, and `refreshOnError`'s generalized spec.
  sorry

end proof

end k8s
end EtcdGrove
end Perennial
