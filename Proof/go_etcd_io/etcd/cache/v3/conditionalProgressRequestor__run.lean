/-
Proof of `Spec/go_etcd_io/etcd/cache/v3/conditionalProgressRequestor__run.lean`. Lean-first (no
Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.conditionalProgressRequestor__run

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

/-- A blocking receive on a context's Done channel returns once the context is done. -/
theorem wp_contextDone_receive (s : context.ContextDesc (IProp GF)) (ch : Loc) (γ : ChanNames) :
    ⊢ ∀ Φ : val → IProp GF, context.isContextDone s ch γ -∗
      (□ s.PDone ∗ context.ContextClosed s.Done_gn -∗ Φ (PairV #() #false)) -∗
      WP (App (Val (chan.receive (go.GoType.StructType []))) (Val #ch)) {{ Φ }} := by
  iintro %Φ #Hd HΦ
  ihave #Hch := context.isContextDone_is_chan _ _ _ $$ Hd
  iapply chan.wp_receive (V := Unit) ch γ $$ Hch
  iintro _
  iapply context.isContextDone_receive _ _ _ _ $$ Hd
  iintro H
  iapply HΦ $$ H

theorem val_false_ne_true : (#false : val) ≠ #true :=
  fun h => absurd (GoGlobalContext.intoVal_inj_bool h) (by decide)

theorem conditionalProgressRequestor.run.wp_proof :
    conditionalProgressRequestor.run.spec (GF := GF) (hG := hG) := by
  intro p n clk ri ctx s
  wp_start as ⟨#Hp, #Hrun, #Hclk, #Hn, #Hctx⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  ihave #Hp' := Hp
  unfold isProgressRequestor
  icases Hp' with ⟨%cp, #Hcp, #Hcond, #Hmu⟩
  unfold isPrRun
  icases Hrun with ⟨#Hnf, #Hri, #Hcl⟩
  ihave #Hctx' := Hctx
  iNamed Hctx'
  wp_apply wp_with_defer as %defer defer
  ipersist p
  ipersist ctx
  wp_apply wp_fork $$ []
  · -- the goroutine: once `ctx` is done, set `stopped` and signal
    wp_apply wp_with_defer as %defer2 defer2
    wp_apply +noauto HDone as %ch1 %γ1 #Hdone
    wp_apply wp_contextDone_receive s ch1 γ1 $$ [$Hdone] as -
    wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
    unfold prLockInv
    icases Hinv with ⟨%w, %b, Hw, Hb⟩
    wp_auto
    wp_apply sync.Cond.wp_Signal $$ [$Hcond]
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hw Hb]
    · inext; iexists w, _; iframe
    itrivial
  -- the timer
  unfold isClock
  wp_apply Hclk $$ %ri as %t #Ht
  ipersist timer
  ihave #Ht' := Ht
  unfold isTimer
  icases Ht' with ⟨#HChan, #HReset, #HStop⟩
  ihave #Hlocker := sync.Mutex_is_Locker (prMuxAddr p) (prLockInv p) $$ Hsync Hmu
  wp_for
  -- `stopped := func() bool { ... }()`: wait on `cond` while there is no waiter and not stopped
  wp_apply wp_with_defer as %d2 d2
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
  try wp_auto
  ihave HI : (sync.ownMutex (prMuxAddr p) ∗ prLockInv p : IProp GF) $$ [Hlocked Hinv]
  · iframe
  wp_for HI
  icases HI with ⟨Hlocked, Hinv⟩
  iunfold prLockInv at Hinv
  icases Hinv with ⟨%w, %b, Hw, Hb⟩
  try wp_auto
  wp_if_destruct
  · try wp_auto
    cases b
    · -- no waiter, not stopped: `p.cond.Wait()`
      simp only [Bool.not_false, _root_.decide_true, ↓reduceIte]
      try wp_auto
      wp_apply sync.Cond.wp_Wait cp (interface.mk (go.GoType.PointerType sync.Mutex.ty)
          #(prMuxAddr p)) (iprop(sync.ownMutex (prMuxAddr p) ∗ prLockInv p))
        $$ [Hlocked Hw Hb] as HI
      · isplitr
        · iexact Hcond
        isplitr
        · iexact Hlocker
        iframe; iunfold prLockInv; iexists _, _; iframe
      wp_for_post
      iframe
    · simp only [Bool.not_true, ↓reduceIte, val_false_ne_true, decide_false, _root_.decide_true,
        Bool.false_eq_true]
      try wp_auto
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hw Hb]
      · inext; iunfold prLockInv; iexists _, _; iframe
      wp_for_post
      wp_apply HStop as %b' -
      iapply HΦ
      itrivial
  · try wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hw Hb]
    · inext; iunfold prLockInv; iexists _, _; iframe
    cases b
    · try wp_auto
      -- `select` on the timer and `ctx.Done()`
      wp_apply HChan as %tch %γt #Htch
      wp_apply +noauto HDone as %ch1 %γ1 #Hdone
      wp_auto_lc 2
      wp_apply_core chan.wp_select_blocking
      iapply BigAndL.bigAndL_cons.2
      isplit
      · -- the timer fired
        simp only [chan.blockingClausePre]
        iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, tch, γt
        isplitr
        · ipureintro; rfl
        isplitr
        · iapply is_bag_is_chan $$ Htch
        iapply bag_recv_au $$ [$Hlc1 $Hlc2] Htch
        inext
        iintro %tm -
        wp_auto
        wp_apply wp_with_defer as %d3 d3
        wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
        iunfold prLockInv at Hinv
        icases Hinv with ⟨%w', %b', Hw, Hb⟩
        try wp_auto
        wp_if_destruct
        · try wp_auto
          wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hw Hb]
          · inext; iunfold prLockInv; iexists _, _; iframe
          cases b'
          · -- waiters and not stopped: `RequestProgress`
            try wp_auto
            wp_apply HReset as %rb -
            iunfold isEtcdProgressNotifier at Hn
            wp_apply Hn $$ [$Hctx] as %err -
            cases err with
            | nil =>
              wp_auto
              wp_for_post
              iframe
            | ok e =>
              wp_auto
              wp_apply wp_slice_literal
              isplitr
              · ipureintro; rfl
              iintro %sl -
              wp_apply fmt.wp_Printf $$ [$Hfmt] as %nb %e2 -
              wp_for_post
              iframe
          · try wp_auto
            wp_apply HReset as %rb -
            wp_for_post
            iframe
        · try wp_auto
          wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hw Hb]
          · inext; iunfold prLockInv; iexists _, _; iframe
          wp_apply HReset as %rb -
          wp_for_post
          iframe
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
        wp_apply HStop as %b' -
        iapply HΦ
        itrivial
      iapply BigAndL.bigAndL_nil.2
      itrivial
    · try wp_auto
      wp_for_post
      wp_apply HStop as %b' -
      iapply HΦ
      itrivial

end proof

end EtcdGrove
end Perennial
