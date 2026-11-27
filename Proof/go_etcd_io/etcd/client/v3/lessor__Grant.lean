/-
Proof of `Spec/go_etcd_io/etcd/client/v3/lessor__Grant.lean` (item 1, the client lease).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.lessor__Grant
public import Spec.go_etcd_io.etcd.client.v3.retryLeaseClient__LeaseGrant
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.LeaseGrantResponse__GetHeader
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
theorem lessor.Grant.wp_proof
    (wp_retry : retryLeaseClient.LeaseGrant.spec (GF := GF) (hG := hG))
    (wp_GetHeader : LeaseGrantResponse.GetHeader.spec (GF := GF) (hG := hG))
    (wp_ContextError : ContextError.spec (GF := GF) (hG := hG)) :
    lessor.Grant.spec (GF := GF) (hG := hG) := by
  intro l conn addr Spec Q ctx om cd ttl
  wp_start as ⟨Hlt, #Hrem, #Hrpc, #Hom, #Hpre, #Hctx, #Hce⟩
  iunfold lessorRemoteAtC at Hrem
  icases Hrem with ⟨%rlc, %sl, #Hremote, #Hrlc, #Hconn, #Hcopts, #Hco⟩
  iunfold callOptsAt at Hco
  icases Hco with ⟨%vs, #Hsl, %Hcap, #Hok, -⟩
  wp_auto
  wp_apply wp_retry rlc conn addr Spec Q ctx om cd _ _ sl vs $$ [Hlt «$r0»] as %resp %err ⟨Hlt, -, Hres⟩
  · iframe #
    iframe
    simp only
    rw [show (0 : w64) = W64 0 from rfl]
    iframe #
    isplitl []
    · ipureintro; exact Hcap
    ipureintro; trivial
  iunfold leaseGrantCallOut at Hres
  icases Hres with (⟨%Herr, %m, #Hm, HQ⟩ | ⟨%Herr, #Hse⟩)
  · subst Herr
    wp_auto
    iunfold leaseGrantRespMsg at Hm
    icases Hm with ⟨%Hnn, %h, #Hh, #Hhdr, #Hid, #Httl, #Herrs⟩
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
    imodintro
    iapply HΦ
    iframe Hlt
    ileft
    isplitr
    · ipureintro; rfl
    iexists m, h
    iframe #
    iframe
  · obtain ⟨Hne, Hce', Hnull⟩ := Herr
    cases err with
    | nil => exact absurd rfl Hne
    | ok ei =>
      wp_auto
      ihave ⟨%mC, #HmC⟩ := go_etcd_io.etcd.cache.v3.statusErrOk_descIs _ $$ Hse
      wp_apply wp_ContextError ctx cd (GoInterface.ok ei) mC $$ [$Hse $HmC] as %err' ⟨%Herr', #Hse', -, -⟩
      · iframe #; ipureintro; exact fun _ => Hce'
      iapply HΦ
      iframe Hlt
      iright
      iframe #
      ipureintro
      exact ⟨(Herr'.2 Hne).1, (Herr'.2 Hne).2, rfl⟩

end proof

end EtcdGrove
end Perennial
