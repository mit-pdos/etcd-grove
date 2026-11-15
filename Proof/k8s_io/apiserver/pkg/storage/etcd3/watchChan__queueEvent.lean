/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/etcd3/watchChan__queueEvent.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.watchChan__queueEvent
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.blockLogger__recordWait
public import Perennial.Proof.time.Link

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

theorem watchChan.queueEvent.wp_proof
    (wp_recordWait : blockLogger.recordWait.spec (GF := GF) (hG := hG)) :
    watchChan.queueEvent.spec (GF := GF) (hG := hG) := by
  intro wc ch lg ctx cdw γc P R sent e
  wp_start as ⟨#Hch, #Hctxf, #Hlg, #Hbl, #Hctx, #Hspsc, Hprod, HP⟩
  ihave #Pti : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  wp_apply wp_with_defer as %defer defer
  wp_apply_core time.wp_Now
  iintro %t -
  wp_auto_lc 3
  wp_apply context.isContext_Done ctx cdw $$ Hctx as %dch %γd #Hdone
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance, ch, γc.chanName, e
    isplit
    · ipureintro; exact ⟨rfl, rfl⟩
    isplit
    · ihave #H := Hspsc
      unfold isSpsc
      icases H with ⟨$, -⟩
    iapply spsc_send_au γc ch P R sent e _ $$ Hspsc [$Hlc1 $Hlc2 $Hlc3] [Hprod HP]
    · iframe
    inext
    iintro Hprod
    wp_auto
    wp_apply time.wp_Since as %d -
    (try wp_auto)
    wp_apply wp_recordWait $$ [$Hbl]
    (try wp_auto)
    iapply HΦ
    ileft
    iexact Hprod
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, dch, γd
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply context.isContextDone_is_chan $$ Hdone
    iapply context.isContextDone_receive _ _ _ _ $$ Hdone
    iintro ⟨#Hpd, -⟩
    wp_auto
    wp_apply time.wp_Since as %d -
    (try wp_auto)
    wp_apply wp_recordWait $$ [$Hbl]
    (try wp_auto)
    iapply HΦ
    iright
    iframe
    imodintro
    iexact Hpd
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end k8s
end EtcdGrove
end Perennial
