/-
Proof of `Spec/github_com/grpc_ecosystem/go_grpc_middleware/providers/prometheus/WithServerHandlingTimeHistogram.lean`
over the real code (providers/prometheus v1.1.0, `server_options.go:42-47`; prove-metrics3,
2026-11-21: until then a trust-boundary axiom): the closure over the (nil) options slice, which it
reads and never writes (its variable made read-only), sets the two histogram fields of the config.
-/
module

public import Spec.github_com.grpc_ecosystem.go_grpc_middleware.providers.prometheus.WithServerHandlingTimeHistogram

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.grpc_ecosystem.go_grpc_middleware.providers.prometheus.Assumptions]

theorem grpc_prometheus.WithServerHandlingTimeHistogram.wp_proof :
    grpc_prometheus.WithServerHandlingTimeHistogram.spec (GF := GF) (hG := hG) := by
  wp_start as -
  repeat (first | wp_pure | wp_alloc_auto)
  ipersist opts
  wp_auto
  iapply HΦ
  unfold promSrvMetricsOpt
  imodintro
  iintro %c %ho %eh
  wp_start as ⟨Hho, Heh⟩
  wp_auto
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
