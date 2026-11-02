/-
`(*clientv3.lessor).TimeToLive(ctx, id, opts...)` (`client/v3/lease.go`; the closed lease example, `notes/lease-ex-plan.md`). Lean-first (no
Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.lessor__TimeToLive
public import Spec.go_etcd_io.etcd.client.v3.toLeaseTimeToLiveRequest
public import Spec.go_etcd_io.etcd.client.v3.retryLeaseClient__LeaseTimeToLive
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.LeaseTimeToLiveResponse__GetHeader
public import Spec.go_etcd_io.etcd.client.v3.ContextError

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

set_option maxHeartbeats 0 in
theorem lessor.TimeToLive.wp_proof
    (wp_toReq : toLeaseTimeToLiveRequest.spec (GF := GF) (hG := hG))
    (wp_retry : retryLeaseClient.LeaseTimeToLive.spec (GF := GF) (hG := hG))
    (wp_GetHeader : LeaseTimeToLiveResponse.GetHeader.spec (GF := GF) (hG := hG))
    (wp_ContextError : ContextError.spec (GF := GF) (hG := hG)) :
    lessor.TimeToLive.spec (GF := GF) (hG := hG) := by
  intro l addr Spec Q ctx cd id osl gs
  wp_start as ⟨#Hrem, #Hrpc, #Hpre, #Hopts, #Hctx, #Hce⟩
  iunfold lessorRemoteAt at Hrem
  icases Hrem with ⟨%rlc, %conn, %sl, #Hremote, #Hrlc, #Hconn, #Hcopts, #Hco⟩
  iunfold callOptsAt at Hco
  icases Hco with ⟨%vs, #Hsl, %Hcap, #Hok, -⟩
  wp_auto
  wp_apply wp_toReq id osl gs $$ [] as %r Hr
  · iframe #
  wp_apply wp_retry rlc conn addr Spec Q ctx cd _ _ sl vs $$ [Hr] as %resp %err ⟨-, Hres⟩
  · iframe #
    iframe
    simp only
    iframe #
    isplitl []
    · ipureintro; exact Hcap
    ipureintro; trivial
  iunfold leaseTTLCallOut at Hres
  icases Hres with (⟨%Herr, %m, #Hm, HQ⟩ | ⟨%Herr, #Hse⟩)
  · subst Herr
    wp_auto
    iunfold leaseTTLRespMsg at Hm
    icases Hm with ⟨%Hnn, %h, %ks, #Hh, #Hhdr, #Hid, #Httl, #Hgttl, #Hks⟩
    ihave #Hpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
    · iPkgInit
    iapply wp_fupd
    wp_apply wp_GetHeader resp h DFrac.discard $$ [] as -
    · iframe #
      ipureintro; exact Hnn
    try wp_auto
    iStructNamed «$r0»
    ipersist ResponseHeader
    ipersist ID
    ipersist TTL
    ipersist GrantedTTL
    ipersist Keys
    imodintro
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    iexists m, h, ks
    iframe #
    iframe
  · obtain ⟨Hne, Hce', Hnull⟩ := Herr
    cases err with
    | nil => exact absurd rfl Hne
    | ok ei =>
      wp_auto
      wp_apply wp_ContextError ctx cd (GoInterface.ok ei) $$ [$Hse] as %err' ⟨%Herr', #Hse', -⟩
      · iframe #; ipureintro; exact fun _ => Hce'
      iapply HΦ
      iright
      iframe #
      ipureintro
      exact ⟨(Herr'.2 Hne).1, (Herr'.2 Hne).2, rfl⟩

end proof

end EtcdGrove
end Perennial
