/-
Proof of `Spec/Cache__WaitForRevision.lean`. Lean-first (no Rocq counterpart).

A polling loop: the store's `LatestRev`, then a blocking select on `time.After`'s channel and
the context's Done channel.
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.Cache__WaitForRevision
public import Spec.go_etcd_io.etcd.cache.v3.store__LatestRev

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem Cache.WaitForRevision.wp_proof
    (wp_LatestRev : store.LatestRev.spec (GF := GF) (hG := hG)) :
    Cache.WaitForRevision.spec (GF := GF) (hG := hG) := by
  intro c cf γr γd cap ctx s rev
  wp_start as ⟨#Hc, #Hctx, Hrd⟩
  unfold isCacheFields
  iNamed Hc
  ihave #Hctx' := Hctx
  iNamed Hctx'
  imod monoNatLbOwn_0 (GF := GF) cf.γs.rev with #Hlb0
  wp_auto
  unfold cacheReader
  wp_for
  wp_apply wp_LatestRev cf.store cf.γs cf.scap (etcdCert cf.pfx) (W64 0) $$ [$HisStore $Hrd]
    as %lr ⟨Hrd, %st, #Hseen, %Hlr⟩
  · unfold storeRevLb; rw [show sint.nat (W64 0) = 0 from rfl]; iexact Hlb0
  iunfold storeSeen at Hseen
  icases Hseen with ⟨%Hst, #Hlbst⟩
  subst Hlr
  wp_if_destruct
  · -- the store has caught up
    wp_for_post
    iapply HΦ
    iframe Hrd
    ileft
    isplitr
    · ipureintro; rfl
    unfold storeRevLb
    iapply monoNatLbOwn_le (sint.nat rev) (by first | exact Int.toNat_le_toNat Hif | word) $$ Hlbst
  wp_apply time.wp_After as %tch %γt #Htch
  wp_apply +noauto HDone as %ch1 %γ1 #Hdone
  wp_auto_lc 2
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, tch, γt
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Htch
    iapply bag_recv_au $$ [$Hlc1 $Hlc2] Htch
    inext
    iintro %t -
    wp_auto
    wp_for_post
    iframe
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch1, γ1
    isplit
    · ipureintro; rfl
    isplit
    · iapply context.isContextDone_is_chan $$ Hdone
    iapply context.isContextDone_receive _ _ _ _ $$ Hdone
    iintro ⟨#HPD, #Hcl⟩
    wp_auto
    ihave #HErrD := HErr $$ %Broadcast.Done
    wp_apply HErrD $$ [] as %err' %herr'
    · iexact Hcl
    wp_for_post
    iapply HΦ
    iframe Hrd
    iright
    iframe HPD Hcl
    ipureintro; exact herr'
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end EtcdGrove
end Perennial
