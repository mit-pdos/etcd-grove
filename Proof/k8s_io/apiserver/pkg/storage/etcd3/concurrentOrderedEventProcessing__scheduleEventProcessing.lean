/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/etcd3/concurrentOrderedEventProcessing__scheduleEventProcessing.lean`
(k8s 7f-5b). The loop's state: the incoming channel's consumer half and the queue's producer half, at equal
counts (the `i`-th response channel queued is for the `i`-th raw event received), the scheduler's slot of
`run`'s wait group and its level-`1` thread token. Each raw event `r` (at `σ`) gets a response channel
(`start_spsc` with `kRcElem` for `r` at `σ`); the queue element (`kQElem`) takes the event's facts and the
channel's consumer half; the per-event goroutine (a member of the wait group: `rwg.wp_Add_member`,
`rwg.wp_fork_member`) `transform`s it (`kRaw_transformOk` from the read laws) and sends the result with
the producer half, then exits through `rwg.wp_Done_member`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.concurrentOrderedEventProcessing__scheduleEventProcessing
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.watchChan__transform
public import Perennial.Spec.sync.WaitGroup__Add
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

set_option maxHeartbeats 3200000 in
theorem concurrentOrderedEventProcessing.scheduleEventProcessing.wp_proof
    (wp_transform : watchChan.transform.spec (GF := GF) (hG := hG))
    (wp_Add : sync.WaitGroup.Add.spec (GF := GF) (hG := hG))
    (wp_Done : sync.WaitGroup.Done.spec (GF := GF) (hG := hG)) :
    concurrentOrderedEventProcessing.scheduleEventProcessing.spec (GF := GF) (hG := hG) := by
  intro _ Obj _ _ pp chQ γq wc sp c W γk γ cd sel emp inS m Q procd alive ctx kp recur wg P HQok
  wp_start as ⟨#Fwc, #FQ, #Hcons, Hci, #HQs, Hqp, Hdone, Hl1⟩
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
  wp_auto
  ipersist p
  ipersist wg
  ipersist ctx
  ihave HI : (∃ (recvI sentQ : List Loc) (e0 : Loc), "e" ∷ e_ptr ↦ e0 ∗
      "Hci" ∷ spscConsumer γ.inc recvI ∗ "Hqp" ∷ spscProducer γq sentQ ∗
      "%Hrs" ∷ ⌜recvI.length = sentQ.length⌝ ∗ "Hdone" ∷ rwg.rwgDone rwgN 3 wg P ∗
      "Hl1" ∷ levelTok 1 : IProp GF) $$ [e Hci Hqp Hdone Hl1]
  · iexists [], [], _
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
    iapply HΦ
    iframe
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
    iapply spsc_rcv_au γ.inc chI _ _ recvI _ $$ Hinc [$Hlc1 $Hlc2] Hci
    inext
    iintro %v %ok Hv
    cases ok
    · simp only [Bool.false_eq_true, ↓reduceIte]
      icases Hv with ⟨⟨⟩, -⟩
    simp only [↓reduceIte]
    icases Hv with ⟨Hel, Hci⟩
    iunfold kInElem at Hel
    icases Hel with ⟨%r, %raws, %lb, %lb0, %st, %σ, %σ0, #Hev, %Hlen, #Hbig, #HQ, #HQ0, %Hst,
      %Hsub, Hok⟩
    (try wp_auto)
    wp_apply chan.wp_make2 (V := Loc) (W64 1) as %rc %γch ⟨#Hrch, -, Hrco⟩
    · ipureintro; decide
    imod start_spsc rc (kRcElem c W sel emp σ r) (fun _ => iprop(False)) γch $$ Hrch [Hrco]
      with ⟨%γrc, #Hrcs, Hrcp, Hrcc⟩
    · iright; iexact Hrco
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
      iapply HΦ
      iframe
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance, chQ, γq.chanName, rc
      isplitr
      · ipureintro; exact ⟨rfl, rfl⟩
      isplitr
      · iunfold isSpsc at HQs
        icases HQs with ⟨#Hc, -⟩
        iexact Hc
      ihave HQe : kQElem c W γ cd sel emp inS m Q (sentQ.length : Int) rc $$ [Hok Hrcc]
      · iunfold kQElem
        iexists v, r, raws, lb, lb0, st, σ, σ0, γrc
        iframe #
        iframe
        ipureintro; rw [← Hrs]; exact ⟨Hlen, Hst, Hsub⟩
      iapply spsc_send_au γq chQ _ _ sentQ rc _ $$ HQs [$Hlc1 $Hlc2 $Hlc3] [$Hqp $HQe]
      inext
      iintro Hqp
      (try wp_auto)
      wp_apply (rwg.wp_Add_member wp_Add rwgN 3 wg P) $$ [$Hdone $Hl1] as ⟨Hdone, Hpend⟩
      (try wp_auto)
      iunfold eventAt at Hev
      icases Hev with ⟨%x, #Hx, #Hxr⟩
      ihave %HQp := HQok lb σ $$ HQ
      obtain ⟨hdec, hkv, hev⟩ := kRaw_transformOk c HQp.1 HQp.2.1 HQp.2.2 Hpfx hinS Hsub
        (List.mem_append_right _ (List.mem_singleton_self r))
      wp_bind (Fork _)
      iapply (rwg.wp_fork_member rwgN 3 wg _ ⊤ (by simp) _ _) $$ Hpend [Hrcp] [-]
      · inext
        iintro Hmd Htf
        wp_auto
        wp_apply wp_with_defer as %defer defer
        (try wp_auto)
        wp_apply (wp_transform Obj c.S W c.codec c.vi c.ti wc wp (GoInterface.ok ctx) nf p sel emp v
          x σ r hdec hkv hev) $$ [] as %res %err ⟨%Herr, Hres⟩
        · iframe #
        subst Herr
        (try wp_auto)
        wp_apply (lc := 3) context.isContext_Done ctx (kCdw γ cd) $$ Hctx as %dch3 %γd3 #Hcdone3
        wp_apply_core chan.wp_select_blocking
        iapply BigAndL.bigAndL_cons.2
        isplit
        · simp only [chan.blockingClausePre]
          iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, dch3, γd3
          isplitr
          · ipureintro; rfl
          isplitr
          · iapply context.isContextDone_is_chan $$ Hcdone3
          iapply context.isContextDone_receive _ _ _ _ $$ Hcdone3
          iintro -
          (try wp_auto)
          wp_apply (rwg.wp_Done_member wp_Done rwgN 3 wg) $$ [$Hmd $Htf] as Htok
          (try wp_auto)
          iframe Htok
        iapply BigAndL.bigAndL_cons.2
        isplit
        · simp only [chan.blockingClausePre]
          iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance, rc, γrc.chanName, _
          isplitr
          · ipureintro; exact ⟨rfl, rfl⟩
          isplitr
          · iunfold isSpsc at Hrcs
            icases Hrcs with ⟨#Hc, -⟩
            iexact Hc
          iapply spsc_send_au γrc rc _ _ [] _ _ $$ Hrcs [$Hlc1 $Hlc2 $Hlc3] [Hrcp Hres «$v1»]
          · iframe Hrcp
            iunfold kRcElem
            iexists res
            iunfold kResOf
            iframe
          inext
          iintro -
          (try wp_auto)
          wp_apply (rwg.wp_Done_member wp_Done rwgN 3 wg) $$ [$Hmd $Htf] as Htok
          (try wp_auto)
          iframe Htok
        iapply BigAndL.bigAndL_nil.2
        itrivial
      · inext
        iintro Hl1
        (try wp_auto)
        wp_for_post
        iframe
        iexists recvI ++ [v], sentQ ++ [rc], _
        simp only [named]
        iframe
        ipureintro; simp [Hrs]
    iapply BigAndL.bigAndL_nil.2
    itrivial
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end k8s
end EtcdGrove
end Perennial
