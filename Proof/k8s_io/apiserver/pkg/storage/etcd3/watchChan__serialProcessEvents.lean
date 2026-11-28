/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/etcd3/watchChan__serialProcessEvents.lean` (k8s 7f-5b). The
loop's state: the incoming channel's consumer half with the raw events received `recv`, `procd`'s half at
`recv.length`, `procEx` at `false`, the alive fraction. Each receipt's `kProcExited` disjunct is refuted
(`kProcExited_refute`); `transform` returns no error, so the `sendError` arm is dead. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.watchChan__serialProcessEvents
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.watchChan__transform
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.watchChan__sendEvent
public import Perennial.Spec.sync.WaitGroup__Done
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

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
theorem watchChan.serialProcessEvents.wp_proof
    (wp_transform : watchChan.transform.spec (GF := GF) (hG := hG))
    (wp_sendEvent : watchChan.sendEvent.spec (GF := GF) (hG := hG))
    (wp_Done : sync.WaitGroup.Done.spec (GF := GF) (hG := hG)) :
    watchChan.serialProcessEvents.spec (GF := GF) (hG := hG) := by
  intro _ Obj _ _ wc sp c W γk γ cd sel emp inS m Q procd alive ctx kp recur q wg HQok Hhist
  wp_start as ⟨#Hcons, Hproc, Hdone, Htok⟩
  ihave #Hh : □ (∀ (l l' : Nat) (s s' : KVState), Q l s -∗ Q l' s' -∗ ⌜kvSameHist s s'⌝) $$ []
  · imodintro
    iintro %l %l' %s %s' H1 H2
    iapply (Hhist l l' s s')
    iframe
  ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold kWcCons at Hcons
  icases Hcons with ⟨#Hprod, %p, %lg, #Hpred, #Hsel, #Hrl, #Hbl, #Hsw, #Htr, #Hver, %Hpfx⟩
  ihave #Hprod' := Hprod
  iunfold kWcProd at Hprod'
  icases Hprod' with ⟨%wp, %chI, %chR, %lgI, %cf, %rse, %γc, #Hfw, #Hsw1, -, -, -, #Hfrt,
    #Hfctx, -, -, -, -, #HfI, -, -, #Hinc, #HfR, #Hrc, #Hctx, -, -, %Hp⟩
  obtain ⟨hinS, -, -⟩ := Hp
  ihave #Hsw' := Hsw
  iunfold storeWatchOk at Hsw'
  icases Hsw' with ⟨%wp', %nf, %crv, %rse', #Hsw2, -, #Hwcodec, #Hwnf, -, #Hwvi, #Hwti, -, -,
    #Hnio, -, -, -, #Hwco, -⟩
  ihave %Hwp := typedPointsto_agree_wand _ _ _ _ _ $$ Hsw1 Hsw2
  subst Hwp
  ihave #Hrc' := Hrc
  iunfold kResChan at Hrc'
  icases Hrc' with ⟨#HchanR, -⟩
  iunfold kProcSt at Hproc
  icases Hproc with ⟨Hci, Hpd, Hpe, Hal⟩
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  ihave HI : ∃ recv : List Loc, spscConsumer γ.inc recv ∗
      dghostVar procd (DFrac.own (1 : Qp).half) recv.length ∗
      dghostVar γ.procEx (DFrac.own 1) false ∗ kResAlive alive q $$ [Hci Hpd Hpe Hal]
  · iexists []
    iframe
  wp_for HI
  icases HI with ⟨Hci, Hpd, Hpe, Hal⟩
  wp_apply (lc := 3) context.isContext_Done ctx (kCdw γ cd) $$ Hctx as %dch %γd #Hcdone
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance, chI, γ.inc.chanName
    isplitr
    · ipureintro; rfl
    isplitr
    · iunfold isSpsc at Hinc
      icases Hinc with ⟨#Hc, -⟩
      iexact Hc
    iapply spsc_rcv_au γ.inc chI _ _ recv _ $$ Hinc [$Hlc1 $Hlc2] Hci
    inext
    iintro %v %ok Hv
    cases ok
    · simp only [Bool.false_eq_true, ↓reduceIte]
      icases Hv with ⟨⟨⟩, -⟩
    simp only [↓reduceIte]
    icases Hv with ⟨Hel, Hci⟩
    iunfold kInElem at Hel
    icases Hel with ⟨%r, %raws, %lb, %lb0, %st, %σ, %σ0, Hev, %Hlen, #Hbig, #HQ, #HQ0, %Hst,
      %Hsub, Hok⟩
    iunfold eventAt at Hev
    icases Hev with ⟨%x, #Hx, #Hxr⟩
    ihave %HQp := HQok lb σ $$ HQ
    obtain ⟨hdec, hkv, hev⟩ := kRaw_transformOk c HQp.1 HQp.2.1 HQp.2.2 Hpfx hinS Hsub
      (List.mem_append_right _ (List.mem_singleton_self r))
    ihave ⟨Hpe, Hok⟩ := kProcExited_refute γ cd 1 _ $$ Hpe Hok
    have hlen : raws.length = recv.length := by simp at Hlen; omega
    (try wp_auto)
    wp_apply (wp_transform Obj c.S W c.codec c.vi c.ti wc wp (GoInterface.ok ctx) nf p sel emp v x
      σ r hdec hkv hev) $$ [] as %res %err ⟨%Herr, Hres⟩
    · iframe #
    subst Herr
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
      iexists recv ++ [v]
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
        iexists recv ++ [v]
        iframe
        simp only [List.length_append, List.length_singleton]
        iframe
      · subst Hb
        (try wp_auto)
        wp_for_post
        (try wp_auto)
        wp_apply (rwg.wp_Done_top wp_Done rwgN 3 wg (kResAlive alive q)) $$ [$Hdone $Hal]
        (try wp_auto)
        iapply HΦ $$ Htok
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
    wp_apply (rwg.wp_Done_top wp_Done rwgN 3 wg (kResAlive alive q)) $$ [$Hdone $Hal]
    (try wp_auto)
    iapply HΦ $$ Htok
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end k8s
end EtcdGrove
end Perennial
