/-
Proof of `Spec/go_etcd_io/etcd/client/v3/internal/resolver/New.lean`, over the translated code
(prove-grpc3, 2026-11-21; until then a trust-boundary axiom, item 5, client construction).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.internal.resolver.New

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

/-- (prove-grpc3, 2026-11-21: until then a trust-boundary axiom) `New(eps...)` is
`&EtcdManualResolver{Resolver: manual.NewBuilderWithScheme(Schema), endpoints: eps}`: the manual
resolver's fields are fresh, its mutex gets the lock invariant, its `cc` (`nil`) is split between the
invariant and `etcdResolverOwn`, its `CloseCallback` persisted for `etcdResolverCloser`. -/
theorem resolver.New.wp_proof : resolver.New.spec (GF := GF) (hG := hG) := by
  intro sl eps
  wp_start as #Hsl
  wp_auto
  wp_func_call
  simp only [go_etcd_io.etcd.client.v3.internal.resolver.Schema]
  wp_auto
  simp only [recv_eq_func_mk]
  iapply wp_fupd
  wp_auto
  rename_i res0 mr
  irename : (mr ↦ (_ : google_golang_org.grpc.resolver.manual.Resolver) : IProp GF) => Hm
  icases typedPointsto_not_null_dup _ _ _ $$ «$r0» with ⟨«$r0», %Hrnn⟩
  iStructNamed Hm
  iStructNamed «$r0»
  icases (typedPointsto_half_split _ _ 1).1 $$ cc with ⟨cc1, cc2⟩
  icases (typedPointsto_half_split _ _ 1).1 $$ Resolver with ⟨R1, R2⟩
  imod sync.init_Mutex (manualResolverLockInv mr) ⊤
    (mr.[google_golang_org.grpc.resolver.manual.Resolver, go!"mu"]) $$ mu [cc2 lastSeenState] with #Hmu
  · inext
    iunfold manualResolverLockInv
    iexists _, _
    iframe cc2 lastSeenState
  imodintro
  iapply HΦ
  isplitr
  · ipureintro; exact Hrnn
  isplitl [R1 endpoints serviceConfig cc1]
  · iunfold etcdResolverOwn
    iexists mr, sl
    iframe R1 endpoints serviceConfig cc1 Hsl Hmu
    ipureintro; exact Hrnn
  iunfold etcdResolverCloser
  iexists mr, _
  iframe R2 CloseCallback
  iintro !> %Φ' HΦ'
  wp_auto
  iexact HΦ'

end proof

end EtcdGrove
end Perennial
