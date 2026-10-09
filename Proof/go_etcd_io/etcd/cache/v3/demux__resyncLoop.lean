/-
Proof of `Spec/go_etcd_io/etcd/cache/v3/demux__resyncLoop.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.demux__resyncLoop
public import Spec.go_etcd_io.etcd.cache.v3.demux__resyncLaggingWatchers
public import Spec.go_etcd_io.etcd.cache.v3.notifier__notify

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

theorem demux.resyncLoop.wp_proof
    (wp_resyncLaggingWatchers : demux.resyncLaggingWatchers.spec (GF := GF) (hG := hG))
    (wp_notify : notifier.notify.spec (GF := GF) (hG := hG)) :
    demux.resyncLoop.spec (GF := GF) (hG := hG) := by
  intro d γd cap C γn ctx s
  wp_start as ⟨#Hd, Hh, Hrh, #Hctx⟩
  ihave #Hd' := Hd
  iunfold isDemux at Hd'
  icases Hd' with ⟨%ri, %n, #Hri, #Hres, #Hslots, %Hcap⟩
  iunfold demuxResyncHandle at Hrh
  icases Hrh with ⟨%n', #Hres', Hnh⟩
  icombine Hres Hres' gives %Hnn
  ihave #Hctx' := Hctx
  iNamed Hctx'
  subst Hnn
  imod monoNatLbOwn_0 (GF := GF) γn.count with #Hlb0
  wp_apply wp_with_defer as %defer defer
  wp_apply time.wp_NewTimer ri as %t %tch %γt #Ht
  ipersist d
  ipersist ctx
  ipersist timer
  ihave #Ht' := Ht
  iunfold time.isTimer at Ht'
  icases Ht' with ⟨#HC, #Hbag⟩
  try wp_auto
  wp_for
  wp_apply +noauto HDone as %ch1 %γ1 #Hdone
  wp_auto_lc 2
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `<-ctx.Done()`: return
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch1, γ1
    isplit
    · ipureintro; rfl
    isplit
    · iapply context.isContextDone_is_chan $$ Hdone
    iapply context.isContextDone_receive _ _ _ _ $$ Hdone
    iintro -
    wp_auto
    wp_for_post
    wp_apply time.Timer.wp_Stop t tch γt $$ [$Ht] as %b -
    iapply HΦ
    iframe
    unfold demuxResyncHandle
    iexists n
    iframe
    iframe #
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- the timer fired: resync, notify, reset
    simp only [chan.blockingClausePre]
    iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, tch, γt
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Hbag
    iapply bag_recv_au $$ [$Hlc1 $Hlc2] Hbag
    inext
    iintro %tm -
    wp_auto
    wp_apply wp_resyncLaggingWatchers d γd cap C $$ [$Hpkg $Hd $Hh] as ⟨Hh, -⟩
    wp_apply wp_notify n γn 0 $$ [$Hpkg $Hnh] as ⟨Hnh, -⟩
    · unfold notifierLb; iexact Hlb0
    wp_apply time.Timer.wp_Reset t tch γt ri $$ [$Ht] as %b -
    wp_for_post
    iframe
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end EtcdGrove
end Perennial
