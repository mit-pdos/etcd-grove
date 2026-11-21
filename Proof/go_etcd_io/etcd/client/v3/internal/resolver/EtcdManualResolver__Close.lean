/-
Proof of `Spec/go_etcd_io/etcd/client/v3/internal/resolver/EtcdManualResolver__Close.lean`, over the
translated code (prove-grpc3, 2026-11-21; until then a trust-boundary axiom, item 5, client
construction). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.internal.resolver.EtcdManualResolver__Close

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.internal.resolver.Assumptions]
variable [manual_sem : google_golang_org.grpc.resolver.manual.Assumptions]

/-- (prove-grpc3, 2026-11-21: until then a trust-boundary axiom) `Close` is promoted from the
embedded `*manual.Resolver`, whose `Close` calls `CloseCallback`, `func() {}`. -/
theorem resolver.EtcdManualResolver.Close.wp_proof :
    resolver.EtcdManualResolver.Close.spec (GF := GF) (hG := hG) := by
  intro r
  wp_start as Hc
  iunfold etcdResolverCloser at Hc
  icases Hc with ⟨%mr, %f, HR, Hcb, #Hf⟩
  wp_auto
  wp_method_call
  wp_auto
  wp_apply Hf
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
