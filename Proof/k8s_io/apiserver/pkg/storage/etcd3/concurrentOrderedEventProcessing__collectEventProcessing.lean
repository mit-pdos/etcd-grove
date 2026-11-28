/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/etcd3/concurrentOrderedEventProcessing__collectEventProcessing.lean`
(k8s 7f-5b). The loop's state: the queue's consumer half with the response channels received `recv`,
`procd`'s half at `recv.length`, `procEx` at `false`, the alive fraction. Each queue element is the
incoming channel's element at the same index (`kQElem`), whose `kProcExited` disjunct is refuted
(`kProcExited_refute`), with the consumer half of its response channel, whose element is `transform`'s
result (`kRcElem`, no error: the `sendError` arm is dead); then the serial goroutine's step. Lean-first
(no Rocq counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.concurrentOrderedEventProcessing__collectEventProcessing
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.watchChan__sendEvent

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

set_option maxHeartbeats 1600000 in
theorem concurrentOrderedEventProcessing.collectEventProcessing.wp_proof
    (wp_sendEvent : watchChan.sendEvent.spec (GF := GF) (hG := hG)) :
    concurrentOrderedEventProcessing.collectEventProcessing.spec (GF := GF) (hG := hG) := by
  intro _ Obj _ _ pp chQ γq wc sp c W γk γ cd sel emp inS m Q procd alive ctx kp recur q Hhist
  wp_start as ⟨#Fwc, #FQ, #Hcons, #HQs, Hcq, Hpd, Hpe, Hal⟩
  ihave #Hh : □ (∀ (l l' : Nat) (s s' : KVState), Q l s -∗ Q l' s' -∗ ⌜kvSameHist s s'⌝) $$ []
  · imodintro
    iintro %l %l' %s %s' H1 H2
    iapply (Hhist l l' s s')
    iframe
  iunfold kWcCons at Hcons
  icases Hcons with ⟨#Hprod, %p, %lg, -, -, #Hrl, #Hbl, -, -, -, -⟩
  ihave #Hprod' := Hprod
  iunfold kWcProd at Hprod'
  icases Hprod' with ⟨%wp, %chI, %chR, %lgI, %cf, %rse, %γc, -, -, -, -, -, -,
    #Hfctx, -, -, -, -, -, -, -, -, #HfR, #Hrc, #Hctx, -, -, -⟩
  ihave #Hrc' := Hrc
  iunfold kResChan at Hrc'
  icases Hrc' with ⟨#HchanR, -⟩
  wp_auto
  ihave HI : (∃ (recv : List Loc) (pr rr : Loc), "processingResponse" ∷ processingResponse_ptr ↦ pr ∗
      "r" ∷ r_ptr ↦ rr ∗ "Hcq" ∷ spscConsumer γq recv ∗
      "Hpd" ∷ dghostVar procd (DFrac.own (1 : Qp).half) recv.length ∗
      "Hpe" ∷ dghostVar γ.procEx (DFrac.own 1) false ∗ "Hal" ∷ kResAlive alive q : IProp GF)
      $$ [processingResponse r Hcq Hpd Hpe Hal]
  · iexists [], _, _
    simp only [named]
    iframe
  wp_for HI
  wp_apply (lc := 3) context.isContext_Done ctx (kCdw γ cd) $$ Hctx as %dch %γd #Hcdone
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, dch, γd
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply context.isContextDone_is_chan $$ Hcdone
    iapply context.isContextDone_receive _ _ _ _ $$ Hcdone
    iintro -
    (try wp_auto)
    wp_for_post
    (try wp_auto)
    iapply HΦ $$ Hal
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance, chQ, γq.chanName
    isplitr
    · ipureintro; rfl
    isplitr
    · iunfold isSpsc at HQs
      icases HQs with ⟨#Hc, -⟩
      iexact Hc
    iapply spsc_rcv_au γq chQ _ _ recv _ $$ HQs [$Hlc1 $Hlc2] Hcq
    inext
    iintro %rc %ok Hv
    cases ok
    · simp only [Bool.false_eq_true, ↓reduceIte]
      icases Hv with ⟨⟨⟩, -⟩
    simp only [↓reduceIte]
    icases Hv with ⟨Hel, Hcq⟩
    iunfold kQElem at Hel
    icases Hel with ⟨%ep, %r, %raws, %lb, %lb0, %st, %σ, %σ0, %γrc, -, %Hlen, #Hbig, #HQ, #HQ0,
      %Hst, %Hsub, Hok, #Hrcs, Hrcc⟩
    ihave ⟨Hpe, Hok⟩ := kProcExited_refute γ cd 1 _ $$ Hpe Hok
    have hlen : raws.length = recv.length := by simp at Hlen; omega
    (try wp_auto)
    wp_apply (lc := 3) context.isContext_Done ctx (kCdw γ cd) $$ Hctx as %dch2 %γd2 #Hcdone2
    wp_apply_core chan.wp_select_blocking
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, dch2, γd2
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply context.isContextDone_is_chan $$ Hcdone2
      iapply context.isContextDone_receive _ _ _ _ $$ Hcdone2
      iintro -
      (try wp_auto)
      wp_for_post
      (try wp_auto)
      iapply HΦ $$ Hal
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance, rc, γrc.chanName
      isplitr
      · ipureintro; rfl
      isplitr
      · iunfold isSpsc at Hrcs
        icases Hrcs with ⟨#Hc, -⟩
        iexact Hc
      iapply spsc_rcv_au γrc rc _ _ [] _ $$ Hrcs [$Hlc1 $Hlc2] Hrcc
      inext
      iintro %rv %ok2 Hv2
      cases ok2
      · simp only [Bool.false_eq_true, ↓reduceIte]
        icases Hv2 with ⟨⟨⟩, -⟩
      simp only [↓reduceIte]
      icases Hv2 with ⟨Hel2, -⟩
      iunfold kRcElem at Hel2
      icases Hel2 with ⟨%res, Hr, Hres⟩
      (try wp_auto)
      iunfold kResOf at Hres
      cases he : kRawToEv c.S.dec sel emp c.S.zero σ r with
      | none =>
        icases Hres with %Hres
        subst Hres
        iapply fupd_wp
        imod kRes_filterStep c W γ cd sel emp inS m Q procd alive chR q recv.length r raws lb lb0 st
          σ σ0 hlen Hst Hsub he $$ Hrc Hh Hpd Hbig HQ HQ0 Hok Hal Hlc3 with ⟨Hal, Hpd⟩
        imodintro
        (try wp_auto)
        wp_for_post
        iframe
        iexists recv ++ [rc], _, _
        simp only [named]
        iframe
        simp only [List.length_append, List.length_singleton]
        iframe
      | some e =>
        icases Hres with ⟨%ev, Hres, Hw⟩
        ihave %Hrnn := typedPointsto_not_null $$ Hres
        ihave Hcm := kRes_evCommit c W γ cd sel emp inS m Q procd alive chR q recv.length r raws lb
          lb0 st σ σ0 e ev hlen Hst Hsub he $$ Hrc Hh Hpd Hbig HQ HQ0 Hok Hw Hal
        (try wp_auto)
        simp only [Hrnn, decide_false]
        (try wp_auto)
        wp_apply (wp_sendEvent wc chR lg res ctx (kCdw γ cd) γ.res.chanName ev (DFrac.own 1)
          iprop(kResAlive alive q ∗ dghostVar procd (DFrac.own (1 : Qp).half) recv.length)
          iprop(kResAlive alive q ∗ dghostVar procd (DFrac.own (1 : Qp).half) (recv.length + 1)))
          $$ [$Hres $Hcm] as %b ⟨Hres, Hb⟩
        · iframe #
        icases Hb with (⟨%Hb, Hal, Hpd⟩ | ⟨%Hb, -, Hal, Hpd⟩)
        · subst Hb
          (try wp_auto)
          wp_for_post
          iframe
          iexists recv ++ [rc], _, _
          simp only [named]
          iframe
          simp only [List.length_append, List.length_singleton]
          iframe
        · subst Hb
          (try wp_auto)
          wp_for_post
          (try wp_auto)
          iapply HΦ $$ Hal
    iapply BigAndL.bigAndL_nil.2
    itrivial
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end k8s
end EtcdGrove
end Perennial
