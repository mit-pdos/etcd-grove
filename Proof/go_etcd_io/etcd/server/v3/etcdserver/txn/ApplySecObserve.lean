/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/txn/ApplySecObserve.lean` (`metrics.go`): `applySec.WithLabelValues(version, op, strconv.FormatBool(success)).Observe(float64(latency.Microseconds()) / 1e6)`,
over `WithLabelValues`' spec with the vector's label names from the package's fact (`txnInit`).
Until prove-etcdserver (2026-11-20) a names-only trust-boundary axiom.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.ApplySecObserve
public import Spec.strconv.FormatBool
public import Spec.github_com.prometheus.client_golang.prometheus.HistogramVec__WithLabelValues

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

theorem txn.ApplySecObserve.wp_proof
    (hFB : strconv.FormatBool.spec (GF := GF) (hG := hG))
    (hWL : prometheus.HistogramVec.WithLabelValues.spec (GF := GF) (hG := hG)) :
    txn.ApplySecObserve.spec (GF := GF) (hG := hG) := by
  intro ver op success latency
  wp_start as %Hu
  ihave Hti : (txn.txnInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hti with ⟨-, -, -, ⟨%hv, #Hhv, %Hhl⟩, -⟩
  wp_auto
  -- `latency.Microseconds()` (Perennial's `time`, translated), then the float division
  wp_method_call
  wp_call
  (try wp_auto)
  wp_method_call
  wp_call
  (try wp_auto)
  wp_apply wp_float64_div as %_ -
  (try wp_auto)
  wp_apply hFB as %fb %Hfb
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %lsl ⟨Hlsl, -⟩
  (try wp_auto)
  wp_apply hWL hv _ [go!"version", go!"op", go!"success"] _ _ $$ [Hlsl] as %_ ⟨%oi, %Hoi, #Hobs, -⟩
  · iframe #; iframe Hlsl; ipureintro
    refine ⟨Hhl, rfl, ?_⟩
    intro v hv'
    change v ∈ [ver, op, fb] at hv'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv'
    rcases hv' with rfl | rfl | rfl
    · exact Hu.1
    · exact Hu.2
    · rw [Hfb]; split <;> decide
  subst Hoi
  iunfold prometheus.observerSpec at Hobs
  (try wp_auto)
  wp_apply Hobs
  (try wp_auto)
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
