/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/etcd3/watchChan__sendError.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.watchChan__sendError
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.isCancelError
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.transformErrorToEvent

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

theorem watchChan.sendError.wp_proof
    (wp_isCancelError : isCancelError.spec (GF := GF) (hG := hG))
    (wp_transformErrorToEvent : transformErrorToEvent.spec (GF := GF) (hG := hG)) :
    watchChan.sendError.spec (GF := GF) (hG := hG) := by
  intro wc ch ctx cdw γch cf γc Pc err Q
  wp_start as ⟨#Hch, #Hctxf, #Hcf, #Hcancel, #HPc, #Hctx, #Hok, #Hchan, Hsend⟩
  iunfold context.cancelSpec at Hcancel
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply wp_isCancelError $$ [$Hok] as %b -
  cases b
  case true =>
    wp_auto
    wp_bind (App (Val #cf) (Val #()))
    iapply Hcancel $$ HPc
    inext
    iintro -
    wp_auto
    iapply HΦ
    iright
    iexact Hsend
  wp_auto
  wp_apply wp_transformErrorToEvent $$ [$Hok] as %p ⟨%ev, %sp, %st, Hp, Hsp, %Hevf⟩
  ipersist Hsp
  ihave %Hpnn := typedPointsto_not_null $$ Hp
  ihave Hsf : statusFailureAt (GF := GF) ev.Object' $$ []
  · unfold statusFailureAt
    iexists sp, st
    isplitr
    · ipureintro; exact ⟨Hevf.2.1, Hevf.2.2⟩
    iexact Hsp
  simp only [Hpnn, decide_false, Bool.not_false]
  wp_auto_lc 3
  wp_apply context.isContext_Done ctx cdw $$ Hctx as %dch %γd #Hdone
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists k8s_io.apimachinery.pkg.watch.Event, inferInstance, inferInstance, inferInstance,
      inferInstance, ch, γch, ev
    isplit
    · ipureintro; exact ⟨rfl, rfl⟩
    isplit
    · iexact Hchan
    iapply Hsend $$ %ev %Hevf.1 Hsf [$Hlc1 $Hlc2 $Hlc3]
    inext
    iintro HQ
    wp_auto
    wp_bind (App (Val #cf) (Val #()))
    iapply Hcancel $$ HPc
    inext
    iintro -
    wp_auto
    iapply HΦ
    ileft
    iexact HQ
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, dch, γd
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply context.isContextDone_is_chan $$ Hdone
    iapply context.isContextDone_receive _ _ _ _ $$ Hdone
    iintro -
    wp_auto
    wp_bind (App (Val #cf) (Val #()))
    iapply Hcancel $$ HPc
    inext
    iintro -
    wp_auto
    iapply HΦ
    iright
    iexact Hsend
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end k8s
end EtcdGrove
end Perennial
