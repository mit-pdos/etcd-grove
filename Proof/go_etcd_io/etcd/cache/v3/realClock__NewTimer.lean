/-
Proof of `Spec/go_etcd_io/etcd/cache/v3/realClock__NewTimer.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.realClock__NewTimer
public import Spec.go_etcd_io.etcd.cache.v3.realTimer__Chan
public import Spec.go_etcd_io.etcd.cache.v3.realTimer__Stop
public import Spec.go_etcd_io.etcd.cache.v3.realTimer__Reset

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem realClock.NewTimer.wp_proof (hChan : realTimer.Chan.spec (GF := GF) (hG := hG))
    (hStop : realTimer.Stop.spec (GF := GF) (hG := hG))
    (hReset : realTimer.Reset.spec (GF := GF) (hG := hG)) :
    realClock.NewTimer.spec (GF := GF) (hG := hG) := by
  intro rc d
  wp_start
  wp_auto
  wp_apply time.wp_NewTimer d as %t %ch %γ #HT
  wp_alloc r as Hr
  iStructNamed Hr
  ipersist timer
  wp_auto
  ihave #HR : isRealTimer r $$ []
  · unfold isRealTimer
    iexists t, ch, γ
    iframe #
  iapply HΦ
  unfold isTimer
  isplitl
  · imodintro
    iintro %Φ' _ HΦ'
    wp_apply hChan r $$ [$Hpkg $HR] as %ch' %γ' #Hb
    iapply HΦ' $$ Hb
  isplitl
  · iintro %d'
    imodintro
    iintro %Φ' _ HΦ'
    wp_apply hReset r d' $$ [$Hpkg $HR] as %b -
    iapply HΦ'
    itrivial
  · imodintro
    iintro %Φ' _ HΦ'
    wp_apply hStop r $$ [$Hpkg $HR] as %b -
    iapply HΦ'
    itrivial

end proof

end EtcdGrove
end Perennial
