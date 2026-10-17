/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3compactor/Periodic__Run.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Periodic__Run
public import Spec.errors.Is
public import Spec.go_uber_org.zap.Int64
public import Spec.go_uber_org.zap.Duration
public import Spec.go_uber_org.zap.Error
public import Spec.go_uber_org.zap.Logger__Info
public import Spec.go_uber_org.zap.Logger__Warn
public import Perennial.Proof.time.Results
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Periodic__getCompactInterval
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Periodic__getRetryInterval
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Periodic__getRetentions

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
  iexists _, _, _, _, _
  iframe
  iframe #))

set_option maxHeartbeats 0 in
theorem v3compactor.Periodic.Run.wp_proof
    (wp_getCompactInterval : v3compactor.Periodic.getCompactInterval.spec (GF := GF) (hG := hG))
    (wp_getRetryInterval : v3compactor.Periodic.getRetryInterval.spec (GF := GF) (hG := hG))
    (wp_getRetentions : v3compactor.Periodic.getRetentions.spec (GF := GF) (hG := hG))
    (wp_Is : errors.Is.spec (GF := GF) (hG := hG))
    (wp_Int64 : zap.Int64.spec (GF := GF) (hG := hG))
    (wp_Duration : zap.Duration.spec (GF := GF) (hG := hG))
    (wp_Error : zap.Error.spec (GF := GF) (hG := hG))
    (wp_Info : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (wp_Warn : zap.Logger.Warn.spec (GF := GF) (hG := hG)) :
    v3compactor.Periodic.Run.spec (GF := GF) (hG := hG) := by
  intro pc P R T
  haveI : go.NotInterface go.int64 := ⟨by unfold go.int64; trivial⟩
  wp_start as ⟨#Hpc, Hrd, Hrevs0, #HEC, #Hclk, #Hrg, #Hc, HT, %Hlg, %Hper⟩
  ihave #Hpc' := Hpc
  iunfold isPeriodic at Hpc'
  icases Hpc' with ⟨#Flg, #Fclock, #Fperiod, #Fitv, #Frg, #Fc, #Hctxat, #Hguard⟩
  iunfold cancellableCtxAt at Hctxat
  icases Hctxat with ⟨%ctx, %γ, %cancel, #Fctx, #Fcancel, #Hctx, -⟩
  ihave #Hctx' := Hctx
  iNamed Hctx'
  ihave #Hclk' := Hclk
  iunfold clockwork.isClockFor at Hclk'
  icases Hclk' with ⟨%clki, %Hclki, #HNow, #HAfter⟩
  ihave #HAfterI := HAfter $$ %(pdRetry P.period) []
  · ipureintro; rfl
  ihave #Hrg' := Hrg
  iunfold v3cRevOk at Hrg'
  icases Hrg' with ⟨%rgi, %Hrgi, #HRev⟩
  ihave #Hc' := Hc
  iunfold pdCompactOk at Hc'
  icases Hc' with ⟨%ci, %Hci, #HCompact⟩
  ihave #HEC' := HEC
  iunfold v3cErrCompacted at HEC'
  icases HEC' with ⟨%ece, #GEC, %Hece⟩
  iunfold pdRevs at Hrevs0
  icases Hrevs0 with ⟨%s0, Hrevs, #Hs0, Hcap0⟩
  rw [Hclki, Hrgi, Hci]
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Htime : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Herrors : isPkgInit (PROP := IProp GF) pkg_id.errors $$ []
  · iPkgInit
  have hret := pdRetentions_pos P.period Hper
  wp_auto
  wp_apply wp_getCompactInterval pc P.period P.interval DFrac.discard DFrac.discard $$ [] as -
  · iframe #
  wp_apply wp_getRetryInterval pc P.period DFrac.discard $$ [] as -
  · iframe #
  wp_apply wp_getRetentions pc P.period DFrac.discard $$ [] as -
  · iframe #; ipureintro; exact Hper
  try wp_auto
  ipersist pc
  ipersist compactInterval
  ipersist retryInterval
  ipersist retentions
  wp_apply wp_fork $$ [HT Hrd Hrevs Hcap0]
  · -- the goroutine
    try wp_auto
    wp_apply HNow as %now0 -
    try wp_auto
    ihave HI : iprop(∃ (lr : w64) (ls : time.Time) (bi : w64) (s : GoSlice) (xs : List w64),
        "lastRevision" ∷ lastRevision_ptr ↦ lr ∗ "HT" ∷ T lr ∗ "lastSuccess" ∷ lastSuccess_ptr ↦ ls ∗
        "baseInterval" ∷ baseInterval_ptr ↦ bi ∗ "Hrevs" ∷ pdRevsAddr pc ↦ s ∗
        "#Hs" ∷ s ↦*□ xs ∗ "Hcap" ∷ ownSliceCap w64 s (DFrac.own 1) ∗
        "#HR" ∷ □ (∀ x : w64, ⌜x ∈ xs⌝ → □ R x) ∗ "Hrd" ∷ pdReader pc)
      $$ [HT Hrd Hrevs Hcap0 lastRevision lastSuccess baseInterval]
    · iexists _, _, _, s0, []
      try rw [show (zero_val w64 : w64) = W64 0 from rfl]
      iframe
      iframe #
      imodintro
      iintro %x %Hx
      simp at Hx
    try wp_auto
    wp_for HI
    try simp only [decide_true, ↓reduceIte]
    -- `pc.revs = append(pc.revs, pc.rg.Rev())`
    wp_apply HRev as %v ⟨%Hv0, #HRv⟩
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_apply wp_slice_append_persistent $$ [Hs Hcap Hsl1] as %s1 ⟨#Hs1, Hcap1, -⟩
    · iframe; iframe #
    try wp_auto
    ihave %Hlen1 := ownSlice_len _ _ _ $$ Hs1
    ihave %Hwf1 := ownSlice_wf _ _ _ $$ Hs1
    -- `if len(pc.revs) > retentions { pc.revs = pc.revs[1:] }`
    wp_join iprop(∃ (s2 : GoSlice) (xs2 : List w64), pdRevsAddr pc ↦ s2 ∗ s2 ↦*□ xs2 ∗
        ownSliceCap w64 s2 (DFrac.own 1) ∗ □ (∀ x : w64, ⌜x ∈ xs2⌝ → □ R x) ∗ ⌜1 ≤ xs2.length⌝)
      with [Hrevs Hcap1] as ⟨%s2, %xs2, Hrevs, #Hs2, Hcap, #HR2, %Hl2⟩
    · -- the window is full: drop its oldest revision
      have Hb : 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) ≤ sint.Z s1.len ∧ sint.Z s1.len ≤ sint.Z s1.cap :=
        ⟨by word, by word, Hwf1.2⟩
      simp only [Hb, _root_.and_self, ↓reduceIte]
      wp_auto
      icases (ownSlice_slice (W64 1) s1.len s1 DFrac.discard _ ⟨Hb.1, Hb.2.1, Int.le_refl _⟩).1 $$ Hs1
        with ⟨-, #Hmid, -⟩
      ihave Hcap2 := (ownSliceCap_slice s1 (W64 1) _ Hb).1 $$ Hcap1
      wp_join_done
      iexists _, _
      iframe
      iframe #
      isplitl
      · imodintro
        iintro %x %Hx
        unfold subslice at Hx
        have Hx' : x ∈ xs ++ [v] := List.mem_of_mem_take (List.mem_of_mem_drop Hx)
        rcases List.mem_append.1 Hx' with h | h
        · iapply HR $$ %x %h
        · simp at h; subst h; iexact HRv
      ipureintro
      rw [subslice_length _ _ _ (by rw [Hlen1.1]; exact Nat.le_refl _)]
      word
    · -- the window is not full
      iexists _, _
      iframe
      iframe #
      isplitl
      · imodintro
        iintro %x %Hx
        rcases List.mem_append.1 Hx with h | h
        · iapply HR $$ %x %h
        · simp at h; subst h; iexact HRv
      ipureintro
      simp
    -- the `select` on `pc.ctx.Done()` and `pc.clock.After(retryInterval)`
    wp_apply +noauto HDone as %ch1 %γ1 #Hdone
    wp_auto
    wp_apply +noauto HAfterI as %tch %γt #Htch
    wp_auto_lc 2
    wp_apply_core chan.wp_select_blocking
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- `<-pc.ctx.Done()`: return
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
      -- `paused`, under the read lock
      iunfold pdReader at Hrd
      wp_apply sync.RWMutex.wp_RLock $$ [$Hrd] as ⟨Hrl, HP⟩
      iunfold pdLockInv at HP
      icases HP with ⟨%b, Hp⟩
      wp_auto
      wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl Hp] as Hrd
      · inext; iunfold pdLockInv; iexists _; iframe
      wp_if_destruct
      rotate_left
      · -- paused: the next sample
        wp_for_post
        iunfold pdReader
        close_inv
      -- `rev := pc.revs[0]`
      ihave %Hlen2 := ownSlice_len _ _ _ $$ Hs2
      obtain ⟨r0, rest, hxs⟩ : ∃ r0 rest, xs2 = r0 :: rest := by
        cases xs2 with
        | nil => simp at Hl2
        | cons a l => exact ⟨a, l, rfl⟩
      have Hb0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z s2.len := by
        rw [hxs] at Hlen2; simp at Hlen2; constructor <;> word
      simp only [Hb0, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index s2 (sint.Z (W64 0)) xs2 DFrac.discard r0 Hb0.1 $$ [] as -
      · iframe #; ipureintro; rw [hxs]; rfl
      ihave #HRr := HR2 $$ %r0 %(by rw [hxs]; simp)
      try wp_auto
      -- `pc.clock.Now().Sub(lastSuccess) < baseInterval || rev == lastRevision`: the next sample
      wp_apply HNow as %now -
      wp_apply _root_.Perennial.time.Time.wp_Sub as %d -
      wp_if_destruct
      · wp_for_post
        iunfold pdReader
        close_inv
      wp_if_destruct
      · wp_for_post
        iunfold pdReader
        close_inv
      -- `if baseInterval == pc.period { baseInterval = compactInterval }`
      wp_join iprop(∃ bi' : w64, baseInterval_ptr ↦ bi') with [baseInterval] as ⟨%bi', baseInterval⟩
      all_goals try (iexists _; iframe; done)
      repeat (first
        | wp_apply wp_Int64 as %_ -
        | wp_apply wp_Duration as %_ -)
      v3c_log
      wp_apply HNow as %st -
      try wp_auto
      -- the compaction
      ihave #HC := HCompact $$ %(GoInterface.ok ctx) %«$a1_ptr» %_ %lr %r0
      wp_apply HC $$ [«$a1» HT] as %resp %err ⟨#Herr, HTT⟩
      · iframe
        iframe #
        isplitr
        · ipureintro; exact ⟨rfl, rfl⟩
        ipureintro
        assumption
      rcases err with _ | ei <;> wp_auto
      focus
        wp_apply v3compactor.wp_Is_v3cErr wp_Is _ ece Hece $$ [$Herrors $Herr] as %bis -
        cases bis
        · -- a failure: log, and the next sample (`lastRevision` unchanged)
          try wp_auto
          repeat (first
            | wp_apply wp_Int64 as %_ -
            | wp_apply wp_Duration as %_ -
            | wp_apply wp_Error as %_ -)
          v3c_log
          wp_for_post
          icases HTT with ⟨HT, -⟩
          iunfold pdReader
          close_inv
        try wp_auto
      -- compacted (or already compacted): `lastRevision = rev`, `T rev`, the log
      all_goals
        icases HTT with ⟨-, HT⟩
        imod HT
        repeat (first
          | wp_apply wp_Int64 as %_ -
          | wp_apply wp_Duration as %_ -
          | wp_apply HNow as %_ -
          | wp_apply _root_.Perennial.time.Time.wp_Sub as %_ -)
        v3c_log
        wp_apply HNow as %_ -
        try wp_auto
        wp_for_post
        iunfold pdReader
        close_inv
    iapply BigAndL.bigAndL_nil.2
    itrivial
  iapply HΦ
  itrivial


end proof

end EtcdGrove
end Perennial
