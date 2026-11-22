/-
Proof of `Spec/go_etcd_io/etcd/client/v3/internal/resolver/EtcdManualResolver__SetEndpoints.lean`,
over the translated code (prove-grpc3, 2026-11-21; until then a trust-boundary axiom, item 5, client
construction). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.internal.resolver.EtcdManualResolver__SetEndpoints

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

/-- (prove-grpc3, 2026-11-21: until then a trust-boundary axiom) `SetEndpoints(eps)` sets
`r.endpoints = eps` and calls `updateState` on a copy of `*r`, which pushes no state: `getCC` calls
the manual resolver's `CC()`, which panics on a resolver not built (`mr.cc` is `nil`: half of it is
`etcdResolverOwn`'s, the other half the lock invariant's), after its deferred `Unlock`, and `getCC`'s
deferred `recover()` makes it return `nil`. -/
theorem resolver.EtcdManualResolver.SetEndpoints.wp_proof :
    resolver.EtcdManualResolver.SetEndpoints.spec (GF := GF) (hG := hG) := by
  intro r eps0 sl eps
  wp_start as ⟨Hown, #Hsl⟩
  iunfold etcdResolverOwn at Hown
  icases Hown with ⟨%mr, %sl0, %Hrnn, HR, Hend, -, Hsc, #Hmu, Hcc⟩
  wp_auto
  icases (typedPointsto_half_split _ _ 1).1 $$ Hend with ⟨Hend1, Hend2⟩
  icases (typedPointsto_half_split _ _ 1).1 $$ Hsc with ⟨Hsc1, Hsc2⟩
  ihave Hst : r ↦{DFrac.own (Qp.half 1)}
      ({ Resolver' := mr, endpoints' := sl, serviceConfig' := null } :
        go_etcd_io.etcd.client.v3.internal.resolver.EtcdManualResolver) $$ [HR Hend1 Hsc1]
  · iapply typedPointsto_combine _ _ _ Hrnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  wp_method_call
  wp_auto
  iStructNamed Hst
  ihave Hend := (typedPointsto_half_split _ _ 1).2 $$ [endpoints Hend2]
  · iframe
  ihave Hsc := (typedPointsto_half_split _ _ 1).2 $$ [serviceConfig Hsc2]
  · iframe
  wp_method_call
  wp_auto
  wp_func_call
  wp_auto
  wp_apply wp_with_defer_recover as %defer %pnc defer pnc
  wp_method_call
  wp_auto
  dsimp only
  wp_method_call
  wp_auto
  wp_apply wp_with_defer as %defer2 defer2
  wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hmu] as ⟨Hlocked, HR⟩
  iunfold manualResolverLockInv at HR
  icases HR with ⟨%cc0, %ls, Hcc', Hls⟩
  icombine Hcc Hcc' gives %Hcceq
  subst Hcceq
  wp_apply wp_panic
  wp_apply sync.Mutex.wp_Unlock _ _ $$ [Hlocked Hcc' Hls]
  · iframe Hmu Hlocked
    iunfold manualResolverLockInv
    iexists _, _
    iframe
  wp_apply wp_recoverPanic $$ [$pnc] as pnc
  iapply HΦ
  iunfold etcdResolverOwn
  iexists mr, sl
  iframe Resolver Hend Hsc Hsl Hmu Hcc
  ipureintro; exact Hrnn

end proof

end EtcdGrove
end Perennial
