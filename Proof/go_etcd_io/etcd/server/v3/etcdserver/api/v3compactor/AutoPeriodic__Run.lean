/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3compactor/AutoPeriodic__Run.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.AutoPeriodic__Run
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.AutoPeriodic__shouldCompact
public import Spec.time.Duration__Seconds
public import Spec.time.Time__IsZero
public import Spec.errors.Is
public import Spec.go_uber_org.zap.Int64
public import Spec.go_uber_org.zap.Float64
public import Spec.go_uber_org.zap.Duration
public import Spec.go_uber_org.zap.Error
public import Spec.go_uber_org.zap.Logger__Info
public import Spec.go_uber_org.zap.Logger__Warn
public import Perennial.Proof.time.Results

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Assumptions]
variable [package_sem_time : _root_.Perennial.time.Assumptions]
variable [package_sem_err : _root_.Perennial.errors.Assumptions]
variable [f2i : Float64ToInt64] [f2i_sem : Float64ToInt64Semantics]

set_option hygiene false in
/-- The end of an iteration: the loop invariant `HI` again. -/
local macro "close_inv" : tactic => `(tactic| (
  iexists _, _, _, _, _
  iframe))

set_option hygiene false in
/-- `lg.Info(msg, fields...)` / `lg.Warn(...)`: the fields' slice literal, then the call
(`wp_Info`/`wp_Warn`, the logger non-nil: `Hlg`). -/
local macro "ap_log" : tactic => `(tactic| (
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %fsl ⟨-, -⟩
  (try wp_auto)
  first
    | (wp_apply wp_Info _ _ _ $$ []
       · iframe #; ipureintro; exact Hlg)
    | (wp_apply wp_Warn _ _ _ $$ []
       · iframe #; ipureintro; exact Hlg)
  (try wp_auto)))

/-- `errors.Is(err, target)` of an error `errors.Is` can classify (`apErrIs`) and a pointer-leaf
target: some boolean. -/
theorem v3compactor.wp_Is_apErr (hIs : errors.Is.spec (GF := GF) (hG := hG)) (err : GoInterface)
    (e : GoInterfaceOk) (he : errLeaf e) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.errors ∗ apErrIs err }}
      (App (App (Val (@! _root_.Perennial.errors.Is)) (Val #err)) (Val #(GoInterface.ok e)))
    {{ (b : Bool), RET #b; True }} := by
  iintro %Φ ⟨#Hpkg, #Herr⟩ HΦ
  iunfold apErrIs at Herr
  ihave ⟨%S, %M, #Ht, %HS⟩ := Herr $$ %(GoInterface.ok e)
  iapply hIs S M err (GoInterface.ok e) (fun tii h => by cases h; exact he.1)
    (HS.2 (fun tii h => by cases h; exact he.1))
  · iframe #; ipureintro; exact HS.1
  iintro !> %b -
  iapply HΦ
  itrivial

set_option maxHeartbeats 0 in
theorem v3compactor.AutoPeriodic.Run.wp_proof
    (wp_shouldCompact : v3compactor.AutoPeriodic.shouldCompact.spec (GF := GF) (hG := hG))
    (wp_Seconds : time.Duration.Seconds.spec (GF := GF) (hG := hG))
    (wp_IsZero : time.Time.IsZero.spec (GF := GF) (hG := hG))
    (wp_Is : errors.Is.spec (GF := GF) (hG := hG))
    (wp_Int64 : zap.Int64.spec (GF := GF) (hG := hG))
    (wp_Float64 : zap.Float64.spec (GF := GF) (hG := hG))
    (wp_Duration : zap.Duration.spec (GF := GF) (hG := hG))
    (wp_Error : zap.Error.spec (GF := GF) (hG := hG))
    (wp_Info : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (wp_Warn : zap.Logger.Warn.spec (GF := GF) (hG := hG)) :
    v3compactor.AutoPeriodic.Run.spec (GF := GF) (hG := hG) := by
  intro ac P tv R T
  -- `Duration`'s value methods resolve through its underlying `int64` (Perennial gives
  -- `NotInterface` per type constructor, and `go.int64` is a `def`)
  haveI : go.NotInterface go.int64 := ⟨by unfold go.int64; trivial⟩
  wp_start as ⟨#Hac, #Htv, #HEC, #Hclk, #Hsg, #Hrg, #Hc, HT, %Hlg, %Hret⟩
  ihave #Hac' := Hac
  iunfold isAutoPeriodic at Hac'
  icases Hac' with ⟨#Flg, #Fclock, #Fret, #Fmb, #Frg, #Fc, #Fsg, ⟨%ctx, %γ, %cancel, #Fctx, #Fcancel, #Hctx, -⟩, #Hmu⟩
  ihave #Hctx' := Hctx
  iNamed Hctx'
  ihave #Hclk' := Hclk
  iunfold apClockOk at Hclk'
  iunfold clockwork.isClock at Hclk'
  icases Hclk' with ⟨%clki, %Hclki, #HNow, #HAfter⟩
  ihave #Hsg' := Hsg
  iunfold apSizeOk at Hsg'
  icases Hsg' with ⟨%sgi, %Hsgi, #HSize⟩
  ihave #Hrg' := Hrg
  iunfold apRevOk at Hrg'
  icases Hrg' with ⟨%rgi, %Hrgi, #HRev⟩
  ihave #Hc' := Hc
  iunfold apCompactOk at Hc'
  icases Hc' with ⟨%ci, %Hci, #HCompact⟩
  ihave #HEC' := HEC
  iunfold apErrCompacted at HEC'
  icases HEC' with ⟨%ece, #GEC, %Hece⟩
  rw [Hclki, Hsgi, Hrgi, Hci]
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Htime : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Herrors : isPkgInit (PROP := IProp GF) pkg_id.errors $$ []
  · iPkgInit
  ihave #Htv' := Htv
  iunfold apTuning at Htv'
  icases Htv' with ⟨#Ghw, #Gsi, #Glt, #Gcd, #Galpha⟩
  wp_auto
  ipersist ac
  ipersist highWater
  wp_apply wp_fork $$ [HT cooldownUntil prev rate lastTime lastSize]
  · -- the goroutine
    ihave HI : iprop(∃ (cu lt : time.Time) (pv rt ls : w64),
        "cooldownUntil" ∷ cooldownUntil_ptr ↦ cu ∗ "prev" ∷ prev_ptr ↦ pv ∗ "HT" ∷ T pv ∗
        "rate" ∷ rate_ptr ↦ rt ∗ "lastTime" ∷ lastTime_ptr ↦ lt ∗ "lastSize" ∷ lastSize_ptr ↦ ls)
      $$ [HT cooldownUntil prev rate lastTime lastSize]
    · iexists _, _, _, _, _
      rw [show (zero_val w64 : w64) = W64 0 from rfl]
      iframe
    wp_auto
    wp_for HI
    -- the `select` on `ac.ctx.Done()` and `ac.clock.After(AutoPeriodicSampleInterval)`
    wp_apply +noauto HDone as %ch1 %γ1 #Hdone
    wp_auto
    wp_apply +noauto HAfter as %tch %γt #Htch
    wp_auto_lc 2
    wp_apply_core chan.wp_select_blocking
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- `<-ac.ctx.Done()`: return
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
      itrivial
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- the sample tick
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
      -- `paused`, under the mutex
      wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HR⟩
      iunfold apLockInv at HR
      icases HR with ⟨%b, Hp⟩
      wp_auto
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hp]
      · inext; iunfold apLockInv; iexists _; iframe
      wp_if_destruct
      rotate_left
      · -- paused: the next sample
        wp_for_post
        close_inv
      -- the sample: the time and the size
      wp_apply HNow as %now -
      wp_apply HSize as %size -
      -- the growth rate's update (only `rate` changes)
      wp_join iprop(∃ rt' : w64, rate_ptr ↦ rt' ∗ lastTime_ptr ↦ lt ∗ lastSize_ptr ↦ ls ∗
          now_ptr ↦ now ∗ size_ptr ↦ size) at next
        with [rate lastTime lastSize now size] as ⟨%rt', rate, lastTime, lastSize, now, size⟩
      · wp_apply wp_IsZero $$ [$lastTime] as %bz lastTime
        cases bz <;> simp only [Bool.not_false, Bool.not_true]
        · -- not the first sample: `dt`
          wp_auto
          wp_apply _root_.Perennial.time.Time.wp_ptr_Sub $$ [$now] as %d now
          wp_apply wp_Seconds d as %dt -
          generalize (float64Leb (W64 0) dt && !decide (dt = W64 0)) = bgt
          cases bgt <;> wp_auto
          · -- `dt <= 0`: no update
            wp_join_done
          -- `dt > 0`: the instantaneous rate, clamped at `0`, smoothed
          generalize (float64Leb _ (W64 0) && !decide (_ = W64 0)) = blt
          wp_join iprop(∃ inst : w64, inst_ptr ↦ inst) at next with [inst] as ⟨%inst, inst⟩
          · cases blt <;> wp_auto <;> wp_join_done
          wp_if_destruct <;> wp_join_done
        · -- the first sample: no rate yet
          wp_auto
          wp_join_done
      -- the cooldown
      wp_apply _root_.Perennial.time.Time.wp_ptr_Before $$ [$now] as %bb now
      cases bb
      rotate_left
      · wp_auto
        wp_for_post
        close_inv
      wp_auto
      -- the projection
      wp_apply wp_shouldCompact ac P tv size rt' $$ [] as %bs %Hbs
      · iframe #
      cases bs
      · wp_auto
        wp_for_post
        close_inv
      wp_auto
      -- the revision to compact at
      wp_apply HRev as %v ⟨%Hv0, #HRv⟩
      wp_if_destruct
      · -- `rev <= 0`
        wp_for_post
        close_inv
      wp_if_destruct
      · -- `rev <= prev`
        wp_for_post
        close_inv
      -- the projected time to the high-water mark (for the log only)
      generalize (float64Leb (W64 0) rt' && !decide (rt' = W64 0)) = bpos
      wp_join iprop(∃ e : time.Duration, eta_ptr ↦ e ∗ size_ptr ↦ size ∗ rate_ptr ↦ rt') at next
        with [eta size rate] as ⟨%e, eta, size, rate⟩
      · cases bpos <;> wp_auto <;> wp_join_done
      wp_apply _root_.Perennial.time.wp_Now as %start -
      repeat (first
        | wp_apply wp_Int64 as %_ -
        | wp_apply wp_Float64 as %_ -
        | wp_apply wp_Duration as %_ -)
      ap_log
      -- the compaction
      ihave #HC := HCompact $$ %(GoInterface.ok ctx) %«$a1_ptr» %_ %pv %(v - P.retention) %v
      wp_apply HC $$ [«$a1» HT] as %resp %err ⟨#Herr, HTT⟩
      · iframe
        iframe #
        have h0 : ¬ sint.Z (v - P.retention) ≤ sint.Z (W64 0) := by assumption
        have h1 : ¬ sint.Z (v - P.retention) ≤ sint.Z pv := by assumption
        isplitr
        · ipureintro; exact ⟨rfl, rfl⟩
        ipureintro
        refine ⟨by word, by word, by word⟩
      -- `err != nil && !errors.Is(err, mvcc.ErrCompacted)`: a failure, retried at a later sample
      rcases err with _ | ei <;> wp_auto
      focus
        wp_apply v3compactor.wp_Is_apErr wp_Is _ ece Hece $$ [$Herrors $Herr] as %bis -
        cases bis
        · -- a failure: log, and the next sample (`prev` unchanged)
          wp_auto
          repeat (first
            | wp_apply wp_Int64 as %_ -
            | wp_apply wp_Error as %_ -)
          ap_log
          wp_for_post
          icases HTT with ⟨HT, -⟩
          close_inv
        wp_auto
      -- compacted (or already compacted): `prev = rev`, `T rev`, the cooldown, the log
      all_goals
        icases HTT with ⟨-, HT⟩
        imod HT
        wp_apply HNow as %t2 -
        wp_apply _root_.Perennial.time.Time.wp_Add as %t3 -
        repeat (first
          | wp_apply wp_Int64 as %_ -
          | wp_apply HSize as %_ -
          | wp_apply _root_.Perennial.time.wp_Since as %_ -
          | wp_apply wp_Duration as %_ -)
        ap_log
        wp_for_post
        close_inv
    iapply BigAndL.bigAndL_nil.2
    itrivial
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
