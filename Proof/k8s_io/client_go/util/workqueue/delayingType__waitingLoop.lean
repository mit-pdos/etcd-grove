/-
Proof of `Spec/k8s_io/client_go/util/workqueue/delayingType__waitingLoop.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.util.workqueue.delayingType__waitingLoop
public import Spec.k8s_io.client_go.util.workqueue.delayingType__Add
public import Spec.k8s_io.client_go.util.workqueue.Typed__ShuttingDown
public import Spec.k8s_io.client_go.util.workqueue.insert
public import Spec.k8s_io.client_go.util.workqueue.waitForPriorityQueue__Peek
public import Spec.container.heap.Init_
public import Spec.k8s_io.apimachinery.pkg.util.runtime.HandleCrashWithLogger
public import Proof.k8s_io.client_go.util.workqueue.DelayingLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace workqueue

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.util.workqueue

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.util.workqueue.Assumptions]

theorem delayingType.waitingLoop.wp_proof
    (wp_Add : delayingType.Add.spec (GF := GF) (hG := hG))
    (wp_ShuttingDown : Typed.ShuttingDown.spec (GF := GF) (hG := hG))
    (wp_insert : insert.spec (GF := GF) (hG := hG))
    (wp_Init : heap.Init_.spec (GF := GF) (hG := hG))
    (wp_Pop : heap.Pop.spec (GF := GF) (hG := hG))
    (wp_HandleCrash : utilruntime.HandleCrashWithLogger.spec (GF := GF) (hG := hG))
    (hLen : waitForPriorityQueue.Len.spec (GF := GF) (hG := hG))
    (hLess : waitForPriorityQueue.Less.spec (GF := GF) (hG := hG))
    (hSwap : waitForPriorityQueue.Swap.spec (GF := GF) (hG := hG))
    (hPush : waitForPriorityQueue.Push.spec (GF := GF) (hG := hG))
    (hPop : waitForPriorityQueue.Pop.spec (GF := GF) (hG := hG))
    (hPeek : waitForPriorityQueue.Peek.spec (GF := GF) (hG := hG)) :
    delayingType.waitingLoop.spec (GF := GF) (hG := hG) := by
  intro K T _ q γ logger
  wp_start as #Hdq
  ihave #Hq' := Hdq
  iNamed Hq'
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply chan.wp_make1 (V := time.Time) as %nev %γn ⟨#Hnevc, %_, Hnoc⟩
  imod start_bag (fun _ : time.Time => iprop(True)) ChanState.Idle nev γn trivial $$ Hnevc Hnoc
    with #Hnev
  (try wp_auto)
  wp_apply wp_slice_literal (V := Loc) []
  isplitr
  · ipureintro; rfl
  iintro %s0 ⟨Hs0, Hcap0⟩
  simp only [go.arrayLiteralSize, List.foldl]
  (try wp_auto)
  generalize «$r0_ptr» = pq
  have hhi := wq_heapIface (K := K) (T := T) @hLen @hLess @hSwap @hPush pq
  have hhp := wq_heapPopIface (K := K) (T := T) @hPop pq
  ihave #Hheap := hhi $$ Hpkg
  ihave #HheapPop := hhp $$ Hpkg
  wp_apply (wp_Init (Loc × K) (interface.mk (go.GoType.PointerType (waitForPriorityQueue.ty T)) #pq)
    (wqHeap (K := K) pq) (wqElem (K := K) (T := T)) [])
    $$ [$Hheap «$r0» Hs0 Hcap0] as ⟨%ys, Hq, %Hys⟩
  · iunfold wqHeap; iexists _; iframe; iunfold wqAt; iframe
    try simp only [List.map_nil]
    iframe
    iapply BigSepL.bigSepL_nil.2; itrivial
  have hys : ys = [] := List.Perm.eq_nil Hys
  subst hys
  wp_apply wp_map_make1 (K := K) (V := Loc) T (go.GoType.PointerType (waitFor.ty T)) as %m Hm
  (try wp_auto)
  iunfold isClock at Hc
  icases Hc with ⟨%ci, %Hci, #HNow, #HNewTimer, -⟩
  subst Hci
  iunfold isTickerI at Htk
  icases Htk with ⟨%hi, %Hhi, #HhbC, -⟩
  subst Hhi
  ihave HI : iprop(∃ (ws : List (Loc × K)) (mm : GMap K Loc) (tm : k8s_io.utils.clock.Timer),
      "Hq" ∷ wqHeap (K := K) pq ws ∗ "Hm" ∷ m ↦$ mm ∗ "%Hok" ∷ ⌜byDataOk mm ws⌝ ∗
      "nextReadyAtTimer" ∷ nextReadyAtTimer_ptr ↦ tm ∗
      "#Htm" ∷ (⌜tm = GoInterface.nil⌝ ∨ isTimerI tm)) $$ [Hq Hm nextReadyAtTimer]
  · iexists [], ∅, GoInterface.nil
    iframe
    isplitr
    · ipureintro; exact ⟨List.nodup_nil, fun k w => by simp⟩
    ileft; ipureintro; rfl
  wp_for HI
  wp_apply wp_ShuttingDown $$ [$Htyped] as %b Hb
  cases b
  · -- not shutting down
    iclear Hb
    wp_auto
    wp_apply HNow as %now -
    -- add the entries whose time has come
    wp_join iprop(∃ (ws : List (Loc × K)) (mm : GMap K Loc),
        "Hq" ∷ wqHeap (K := K) pq ws ∗ "Hm" ∷ m ↦$ mm ∗ "%Hok" ∷ ⌜byDataOk mm ws⌝ ∗
        "now" ∷ now_ptr ↦ now ∗ "waitingForQueue" ∷ waitingForQueue_ptr ↦ pq ∗
        "waitingEntryByData" ∷ waitingEntryByData_ptr ↦ m ∗ "q" ∷ q_ptr ↦ q) at next
        with [Hq Hm now waitingForQueue waitingEntryByData q]
        as ⟨%ws, %mm, Hq, Hm, %Hok, now, waitingForQueue, waitingEntryByData, q⟩
    · ihave HJ : iprop(∃ (ws : List (Loc × K)) (mm : GMap K Loc),
          "Hq" ∷ wqHeap (K := K) pq ws ∗ "Hm" ∷ m ↦$ mm ∗ "%Hok" ∷ ⌜byDataOk mm ws⌝) $$ [Hq Hm]
      · iexists ws, mm; iframe; ipureintro; exact Hok
      wp_for HJ
      wp_apply (wqHeap_Len_of (K := K) (T := T) @hLen pq ws) $$ [$Hq] as ⟨Hq, %Hwl⟩
      rcases hws : ws with _ | ⟨a, ws'⟩
      · -- empty: the loop ends
        subst hws
        have h0 : ¬ (sint.Z (W64 0) < sint.Z (W64 (([] : List (Loc × K)).length : Int))) := by
          simp only [List.length_nil]; word
        simp only [h0, val_false_ne_true, decide_false, _root_.decide_true, Bool.false_eq_true,
          ↓reduceIte]
        wp_join_done
        iexists [], mm
        iframe
        try (ipureintro; exact Hok)
      · subst hws
        have hlt : sint.Z (W64 0) < sint.Z (W64 ((a :: ws').length : Int)) := by
          simp only [List.length_cons] at Hwl ⊢; word
        simp only [hlt, _root_.decide_true, eq_self_iff_true, ↓reduceIte]
        wp_auto
        wp_apply (wqHeap_Peek_of (K := K) (T := T) @hPeek pq a ws') $$ [$Hq] as Hq
        (try wp_auto)
        icases wqHeap_first_readyAt (K := K) pq a ws' $$ Hq with ⟨%t, Ht, Hq⟩
        wp_apply Time.wp_ptr_After_dq $$ [$Ht] as %b Ht
        ihave Hq := Hq $$ Ht
        cases b
        · -- due: popped and added
          wp_auto
          wp_apply (wp_Pop (Loc × K) (interface.mk (go.GoType.PointerType (waitForPriorityQueue.ty T)) #pq)
            (wqHeap (K := K) pq) (wqElem (K := K) (T := T)) (a :: ws') (List.cons_ne_nil _ _))
            $$ [$Hheap $HheapPop $Hq] as %x ⟨%ys, %b0, Hq, Hx, %Hys⟩
          iunfold wqElem at Hx
          icases Hx with ⟨%Hx, %i, Hb0⟩
          subst Hx
          iunfold wfAt at Hb0
          icases Hb0 with ⟨#Hbd, Hbr, Hbi⟩
          wp_auto
          wp_apply wp_Add $$ [$Hdq]
          wp_apply wp_mapDelete $$ Hm as Hm
          wp_for_post
          iframe
          iexists ys, _
          iframe
          ipureintro
          exact byDataOk_delete b0 Hok Hys
        · -- not due yet: the loop ends
          wp_auto
          wp_for_post
          wp_join_done
          iexists (a :: ws'), mm
          iframe
          try (ipureintro; exact Hok)
    -- the next entry's timer
    wp_join iprop(∃ (nch : Loc) (γc : ChanNames) (tm' : k8s_io.utils.clock.Timer),
        "nextReadyAt" ∷ nextReadyAt_ptr ↦ nch ∗
        "#Hnch" ∷ □ isChanBag γc nch (V := time.Time) (fun _ => iprop(True)) ∗
        "nextReadyAtTimer" ∷ nextReadyAtTimer_ptr ↦ tm' ∗
        "#Htm" ∷ □ (⌜tm' = GoInterface.nil⌝ ∨ isTimerI tm') ∗
        "Hq" ∷ wqHeap (K := K) pq ws ∗
        "now" ∷ now_ptr ↦ now ∗ "waitingForQueue" ∷ waitingForQueue_ptr ↦ pq ∗ "q" ∷ q_ptr ↦ q) at next
        with [nextReadyAt nextReadyAtTimer Hq now waitingForQueue q]
        as ⟨%nch, %γc, %tm', nextReadyAt, #Hnch, nextReadyAtTimer, #Htm', Hq, now, waitingForQueue, q⟩
    · wp_apply (wqHeap_Len_of (K := K) (T := T) @hLen pq ws) $$ [$Hq] as ⟨Hq, %Hwl⟩
      rcases hws : ws with _ | ⟨a, ws'⟩
      · subst hws
        have h0 : ¬ (sint.Z (W64 0) < sint.Z (W64 (([] : List (Loc × K)).length : Int))) := by
          simp only [List.length_nil]; word
        simp only [h0, val_false_ne_true, decide_false, _root_.decide_true, Bool.false_eq_true,
          ↓reduceIte]
        wp_auto
        wp_join_done
        iexists nev, γn, tm
        iframe
        isplitr
        · imodintro; iexact Hnev
        imodintro; iexact Htm
      · subst hws
        have hlt : sint.Z (W64 0) < sint.Z (W64 ((a :: ws').length : Int)) := by
          simp only [List.length_cons] at Hwl ⊢; word
        simp only [hlt, _root_.decide_true, eq_self_iff_true, ↓reduceIte]
        wp_auto
        wp_join at next with [nextReadyAtTimer]
        · icases Htm with (%Hnil | #Htmi)
          · subst Hnil
            (try wp_auto)
            wp_join_done
          · iunfold isTimerI at Htmi
            icases Htmi with ⟨%i, %Hi, #HC0, #HStop0⟩
            subst Hi
            wp_auto
            wp_apply HStop0 as %_ -
            wp_join_done
        wp_apply (wqHeap_Peek_of (K := K) (T := T) @hPeek pq a ws') $$ [$Hq] as Hq
        (try wp_auto)
        icases wqHeap_first_readyAt (K := K) pq a ws' $$ Hq with ⟨%t, Ht, Hq⟩
        wp_apply Time.wp_ptr_Sub_dq $$ [$Ht] as %d Ht
        ihave Hq := Hq $$ Ht
        (try wp_auto)
        wp_apply HNewTimer as %tm2 #Htm2
        ihave #Htm2' := Htm2
        iunfold isTimerI at Htm2'
        icases Htm2' with ⟨%i2, %Hi2, #HC2, -⟩
        subst Hi2
        (try wp_auto)
        wp_apply HC2 as %nch %γc #Hnch
        (try wp_auto)
        wp_join_done
        iexists nch, γc, (GoInterface.ok i2)
        iframe
        isplitr
        · imodintro; iexact Hnch
        imodintro; iright; iexact Htm2
    -- the select
    wp_apply (lc := 2) HhbC as %hch %γh #Hhch
    wp_apply_core chan.wp_select_blocking
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- `<-q.stopCh`: return
      simp only [chan.blockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch, γ.stop
      isplit
      · ipureintro; rfl
      isplit
      · iapply ownBroadcastChan_is_chan $$ Hstop
      iapply broadcast_chan_receive $$ Hstop
      iintro -
      wp_auto
      wp_for_post
      -- the deferred `utilruntime.HandleCrashWithLogger(logger)`
      wp_apply wp_HandleCrash
      iapply HΦ; itrivial
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- `<-q.heartbeat.C()`: again
      simp only [chan.blockingClausePre]
      iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, hch, γh
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply is_bag_is_chan $$ Hhch
      iapply bag_recv_au $$ [$Hlc1 $Hlc2] Hhch
      inext
      iintro %_ -
      wp_auto
      wp_for_post
      iframe
      iexists ws, mm, tm'
      iframe
      isplitr
      · ipureintro; exact Hok
      iexact Htm'
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- `<-nextReadyAt`: again
      simp only [chan.blockingClausePre]
      iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, nch, γc
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply is_bag_is_chan $$ Hnch
      iapply bag_recv_au $$ [$Hlc1 $Hlc2] Hnch
      inext
      iintro %_ -
      wp_auto
      wp_for_post
      iframe
      iexists ws, mm, tm'
      iframe
      isplitr
      · ipureintro; exact Hok
      iexact Htm'
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- `<-q.waitingForAddCh`: the entry inserted or added, then the channel drained
      simp only [chan.blockingClausePre]
      iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance, wch, γ.wch
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply is_bag_is_chan $$ Hbag
      iapply bag_recv_au $$ [$Hlc1 $Hlc2] Hbag
      inext
      iintro %w Hw
      wp_auto
      iunfold entryOk at Hw
      icases Hw with ⟨%wf, Hw⟩
      ihave Hw := wfFields_of (K := K) w wf $$ Hw
      iunfold wfFields at Hw
      icases Hw with ⟨Hd, Hr, Hi⟩
      wp_join iprop(∃ (ws : List (Loc × K)) (mm : GMap K Loc),
          "Hq" ∷ wqHeap (K := K) pq ws ∗ "Hm" ∷ m ↦$ mm ∗ "%Hok" ∷ ⌜byDataOk mm ws⌝ ∗
          "waitingForQueue" ∷ waitingForQueue_ptr ↦ pq ∗
          "waitingEntryByData" ∷ waitingEntryByData_ptr ↦ m ∗ "q" ∷ q_ptr ↦ q) at next
          with [Hq Hm waitingForQueue waitingEntryByData q waitEntry Hd Hr Hi]
          as ⟨%ws, %mm, Hq, Hm, %Hok, waitingForQueue, waitingEntryByData, q⟩
      · wp_apply HNow as %now2 -
        (try wp_auto)
        wp_apply Time.wp_ptr_After_dq $$ [$Hr] as %b Hr
        cases b
        · -- due: added
          (try wp_auto)
          wp_apply wp_Add $$ [$Hdq]
          wp_join_done
          iexists ws, mm
          iframe
          try (ipureintro; exact Hok)
        · -- later: inserted
          (try wp_auto)
          wp_apply (wp_insert pq ws m mm w wf Hok) $$ [$Hq $Hm Hd Hr Hi] as ⟨%ws2, %mm2, Hq, Hm, %Hok2⟩
          · iunfold wfFields; iframe
          wp_join_done
          iexists ws2, mm2
          iframe
          try (ipureintro; exact Hok2)
      -- drain `waitingForAddCh`
      ihave HD : iprop(∃ (ws : List (Loc × K)) (mm : GMap K Loc) (d : Bool),
          "Hq" ∷ wqHeap (K := K) pq ws ∗ "Hm" ∷ m ↦$ mm ∗ "%Hok" ∷ ⌜byDataOk mm ws⌝ ∗
          "drained" ∷ drained_ptr ↦ d) $$ [Hq Hm drained]
      · iexists ws, mm, false; iframe; ipureintro; exact Hok
      wp_for HD
      cases d
      · -- not drained: a non-blocking receive
        simp only [Bool.not_false, _root_.decide_true, ↓reduceIte]
        wp_auto_lc 2
        wp_apply_core chan.wp_select_nonblocking
        isplit
        · iapply BigAndL.bigAndL_cons.2
          isplit
          · simp only [chan.nonblockingClausePre]
            iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance, wch, γ.wch
            isplitr
            · ipureintro; rfl
            isplitr
            · iapply is_bag_is_chan $$ Hbag
            iapply blocking_rcv_implies_nonblocking
            iapply bag_recv_au $$ [$Hlc1 $Hlc2] Hbag
            inext
            iintro %w Hw
            wp_auto
            iunfold entryOk at Hw
            icases Hw with ⟨%wf, Hw⟩
            ihave Hw := wfFields_of (K := K) w wf $$ Hw
            iunfold wfFields at Hw
            icases Hw with ⟨Hd, Hr, Hi⟩
            wp_apply HNow as %now2 -
            (try wp_auto)
            wp_apply Time.wp_ptr_After_dq $$ [$Hr] as %b Hr
            cases b
            · (try wp_auto)
              wp_apply wp_Add $$ [$Hdq]
              wp_for_post
              iframe
              iexists ws, mm, false
              iframe
              try (ipureintro; exact Hok)
            · (try wp_auto)
              wp_apply (wp_insert pq ws m mm w wf Hok) $$ [$Hq $Hm Hd Hr Hi]
                as ⟨%ws2, %mm2, Hq, Hm, %Hok2⟩
              · iunfold wfFields; iframe
              wp_for_post
              iframe
              iexists ws2, mm2, false
              iframe
              try (ipureintro; exact Hok2)
          iapply BigAndL.bigAndL_nil.2
          itrivial
        · -- `default`: drained
          wp_auto
          wp_for_post
          iframe
          iexists ws, mm, true
          iframe
          try (ipureintro; exact Hok)
      · -- drained: the outer loop again
        simp only [Bool.not_true, val_false_ne_true, decide_false, _root_.decide_true,
          Bool.false_eq_true, ↓reduceIte]
        wp_for_post
        iframe
        iexists ws, mm, tm'
        iframe
        isplitr
        · ipureintro; exact Hok
        iexact Htm'
    iapply BigAndL.bigAndL_nil.2
    itrivial
  · -- shutting down: return (the deferred `HandleCrashWithLogger` runs)
    wp_auto
    wp_for_post
    wp_apply wp_HandleCrash
    iapply HΦ; itrivial

end proof

end workqueue
end EtcdGrove
end Perennial
