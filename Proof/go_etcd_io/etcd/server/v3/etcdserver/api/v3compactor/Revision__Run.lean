/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3compactor/Revision__Run.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Revision__Run
public import Spec.errors.Is
public import Spec.go_uber_org.zap.Int64
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
set_option hygiene false in
/-- `lg.Info(msg, fields...)` / `lg.Warn(...)`: the fields' slice literal, then the call
(`wp_Info`/`wp_Warn`, the logger non-nil: `Hlg`). -/
local macro "v3c_log" : tactic => `(tactic| (
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

set_option hygiene false in
/-- The end of an iteration: the loop invariant `HI` again. -/
local macro "close_inv" : tactic => `(tactic| (
  iexists _
  iframe))

set_option maxHeartbeats 0 in
theorem v3compactor.Revision.Run.wp_proof
    (wp_Is : errors.Is.spec (GF := GF) (hG := hG))
    (wp_Int64 : zap.Int64.spec (GF := GF) (hG := hG))
    (wp_Duration : zap.Duration.spec (GF := GF) (hG := hG))
    (wp_Error : zap.Error.spec (GF := GF) (hG := hG))
    (wp_Info : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (wp_Warn : zap.Logger.Warn.spec (GF := GF) (hG := hG)) :
    v3compactor.Revision.Run.spec (GF := GF) (hG := hG) := by
  intro rc P R T
  haveI : go.NotInterface go.int64 := ⟨by unfold go.int64; trivial⟩
  wp_start as ⟨#Hrc, #HEC, #Hclk, #Hrg, #Hc, HT, %Hlg, %Hret⟩
  ihave #Hrc' := Hrc
  iunfold isRevision at Hrc'
  icases Hrc' with ⟨#Flg, #Fclock, #Fret, #Fitv, #Frg, #Fc, #Hctxat, #Hmu⟩
  iunfold cancellableCtxAt at Hctxat
  icases Hctxat with ⟨%ctx, %γ, %cancel, #Fctx, #Fcancel, #Hctx, -⟩
  ihave #Hctx' := Hctx
  iNamed Hctx'
  ihave #Hclk' := Hclk
  iunfold clockwork.isClockFor at Hclk'
  icases Hclk' with ⟨%clki, %Hclki, #HNow, #HAfter⟩
  ihave #HAfterI := HAfter $$ %P.interval []
  · ipureintro; rfl
  ihave #Hrg' := Hrg
  iunfold v3cRevOk at Hrg'
  icases Hrg' with ⟨%rgi, %Hrgi, #HRev⟩
  ihave #Hc' := Hc
  iunfold rvCompactOk at Hc'
  icases Hc' with ⟨%ci, %Hci, #HCompact⟩
  ihave #HEC' := HEC
  iunfold v3cErrCompacted at HEC'
  icases HEC' with ⟨%ece, #GEC, %Hece⟩
  rw [Hclki, Hrgi, Hci]
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Htime : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Herrors : isPkgInit (PROP := IProp GF) pkg_id.errors $$ []
  · iPkgInit
  wp_auto
  ipersist rc
  wp_apply wp_fork $$ [HT prev]
  · -- the goroutine
    ihave HI : iprop(∃ pv : w64, "prev" ∷ prev_ptr ↦ pv ∗ "HT" ∷ T pv) $$ [HT prev]
    · iexists _
      try rw [show (zero_val w64 : w64) = W64 0 from rfl]
      iframe
    wp_auto
    wp_for HI
    try simp only [decide_true, ↓reduceIte]
    -- the `select` on `rc.ctx.Done()` and `rc.clock.After(rc.interval)`
    wp_apply +noauto HDone as %ch1 %γ1 #Hdone
    wp_auto
    wp_apply +noauto HAfterI as %tch %γt #Htch
    wp_auto_lc 2
    wp_apply_core chan.wp_select_blocking
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- `<-rc.ctx.Done()`: return
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
    · -- the tick
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
      iunfold rvLockInv at HR
      icases HR with ⟨%b, Hp⟩
      wp_auto
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hp]
      · inext; iunfold rvLockInv; iexists _; iframe
      wp_if_destruct
      rotate_left
      · -- paused: the next round
        wp_for_post
        close_inv
      -- the revision to compact at
      wp_apply HRev as %v ⟨%Hv0, #HRv⟩
      wp_if_destruct
      · -- `rev <= 0`
        wp_for_post
        close_inv
      wp_if_destruct
      · -- `rev == prev`
        wp_for_post
        close_inv
      wp_apply _root_.Perennial.time.wp_Now as %start -
      repeat (wp_apply wp_Int64 as %_ -)
      v3c_log
      -- the compaction
      ihave #HC := HCompact $$ %(GoInterface.ok ctx) %«$a1_ptr» %_ %pv %(v - P.retention) %v
      wp_apply HC $$ [«$a1» HT] as %resp %err ⟨#Herr, HTT⟩
      · iframe
        iframe #
        isplitr
        · ipureintro; exact ⟨rfl, rfl⟩
        ipureintro
        refine ⟨by word, by assumption, by word⟩
      -- `err != nil && !errors.Is(err, mvcc.ErrCompacted)`: a failure, retried at a later round
      rcases err with _ | ei <;> wp_auto
      focus
        wp_apply v3compactor.wp_Is_v3cErr wp_Is _ ece Hece $$ [$Herrors $Herr] as %bis -
        cases bis
        · -- a failure: log, and the next round (`prev` unchanged)
          wp_auto
          repeat (first
            | wp_apply wp_Int64 as %_ -
            | wp_apply wp_Duration as %_ -
            | wp_apply wp_Error as %_ -)
          v3c_log
          wp_for_post
          icases HTT with ⟨HT, -⟩
          close_inv
        wp_auto
      -- compacted (or already compacted): `prev = rev`, `T rev`, the log
      all_goals
        icases HTT with ⟨-, HT⟩
        imod HT
        repeat (first
          | wp_apply wp_Int64 as %_ -
          | wp_apply _root_.Perennial.time.wp_Since as %_ -
          | wp_apply wp_Duration as %_ -)
        v3c_log
        wp_for_post
        close_inv
    iapply BigAndL.bigAndL_nil.2
    itrivial
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
