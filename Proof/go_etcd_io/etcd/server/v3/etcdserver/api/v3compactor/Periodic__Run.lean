/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3compactor/Periodic__Run.lean`. Lean-first (no Rocq
counterpart). The spec-first pilot's phase 1 (`notes/compactor-pilot-plan.md`): the spec is written,
the proof is phase 3's hard full proof.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Periodic__Run
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Periodic__getCompactInterval
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Periodic__getRetryInterval
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Periodic__getRetentions
public import Spec.go_uber_org.zap.Int64
public import Spec.go_uber_org.zap.Duration
public import Spec.go_uber_org.zap.Logger__Info
public import Spec.go_uber_org.zap.Logger__Warn
public import Spec.go_uber_org.zap.Error
public import Spec.errors.Is
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.ErrLaws

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api v3compactor

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Assumptions]

set_option hygiene false in
/-- A compaction that succeeded (or found the revision compacted already): the log line,
`lastRevision = rev`, `lastSuccess = pc.clock.Now()`, the next round. -/
local macro "per_ok" : tactic => `(tactic| (
  (try wp_auto)
  wp_apply hInt64 as %g1 -
  wp_apply hDuration as %g2 -
  wp_apply +noauto HNow as %t3 -
  (try wp_auto)
  wp_apply _root_.Perennial.time.Time.wp_Sub as %dur -
  wp_apply hDuration as %g3 -
  wp_apply wp_slice_literal
  try (isplitr; (ipureintro; rfl))
  try iintro %_ ⟨_, -⟩
  try wp_auto
  wp_apply hLogger_Info $$ []
  · ipureintro; exact Hlgnn
  (try wp_auto)
  wp_apply +noauto HNow as %t4 -
  (try wp_auto)
  wp_for_post
  iframe
  iexists (y0 :: rest), s2, y0, _, _, T + sint.Z ri, sint.Z v
  simp only [named]
  iframe
  iframe #
  ipureintro; exact hw2))

set_option hygiene false in
/-- A compaction that failed: the warning, the next round (`lastRevision` unchanged). -/
local macro "per_fail" : tactic => `(tactic| (
  (try wp_auto)
  wp_apply hInt64 as %g1 -
  wp_apply hDuration as %g2 -
  wp_apply hDuration as %g3 -
  wp_apply hError as %g4 -
  wp_apply wp_slice_literal
  try (isplitr; (ipureintro; rfl))
  try iintro %_ ⟨_, -⟩
  try wp_auto
  wp_apply hLogger_Warn $$ []
  · ipureintro; exact Hlgnn
  (try wp_auto)
  wp_for_post
  iframe
  iexists (y0 :: rest), s2, lr, _, _, T + sint.Z ri, sint.Z v
  simp only [named]
  iframe
  iframe #
  ipureintro; exact hw'))

theorem v3compactor.Periodic.Run.wp_proof
    (hPeriodic_getCompactInterval : v3compactor.Periodic.getCompactInterval.spec (GF := GF) (hG := hG))
    (hPeriodic_getRetryInterval : v3compactor.Periodic.getRetryInterval.spec (GF := GF) (hG := hG))
    (hPeriodic_getRetentions : v3compactor.Periodic.getRetentions.spec (GF := GF) (hG := hG))
    (hInt64 : zap.Int64.spec (GF := GF) (hG := hG))
    (hDuration : zap.Duration.spec (GF := GF) (hG := hG))
    (hLogger_Info : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (hLogger_Warn : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (hError : zap.Error.spec (GF := GF) (hG := hG))
    (hIs : errors.Is.spec (GF := GF) (hG := hG)) :
    v3compactor.Periodic.Run.spec (GF := GF) (hG := hG) := by
  intro pc E period γf
  wp_start as ⟨#Hpc, Htok, Hpre⟩
  iunfold isPeriodic at Hpc
  icases Hpc with ⟨%lg, %clk, %pd, %ctx, %cd, %γctx, %cancel, #Hlg, %Hlgnn, #Hclkf, #Hclk, #Hpdf,
    %Hpd, #Hrg, #Hc, #Hctxf, #Hctx, #Hcancelf, #Hcs, #Hguard⟩
  obtain ⟨Hpd, H10⟩ := Hpd
  -- (one `word` in this declaration: several shared a cached proof the kernel rejected,
  -- `notes/perennial-changes.md`, "`word`'s caches")
  have hpd63 : sint.Z pd < 2 ^ 63 := by word
  have h0 : sint.Z (W64 0) = 0 := rfl
  have h1 : sint.Z (W64 1) = 1 := rfl
  iunfold periodicRunTok at Htok
  icases Htok with ⟨⟨%s0, Hrevs, Hs0, Hcap0⟩, Hslot, Hfirst⟩
  iunfold runPre at Hpre
  icases Hpre with ⟨#HRev, #HCompact, HR, #HLb0⟩
  (try wp_auto)
  wp_apply (hPeriodic_getCompactInterval pc pd DFrac.discard) $$ [$Hpdf] as %ci0 ⟨%Hci0, -⟩
  wp_apply (hPeriodic_getRetryInterval pc pd DFrac.discard (by omega)) $$ [$Hpdf] as %ri ⟨%Hri, -⟩
  wp_apply (hPeriodic_getRetentions pc pd DFrac.discard (by omega)) $$ [$Hpdf] as %rn ⟨%Hrn, -⟩
  (try wp_auto)
  ipersist pc
  ipersist compactInterval
  ipersist retryInterval
  ipersist retentions
  icases clockwork.clockOk_ok _ _ $$ Hclk with %Hcki
  obtain ⟨cki, Hcki⟩ := Hcki
  subst Hcki
  ihave #HNow := clockwork.clockOk_Now _ _ $$ Hclk
  ihave #HRev' := HRev
  iunfold revGetterOk at HRev'
  icases HRev' with ⟨%ri0, %Hri0, #HRevT⟩
  wp_apply wp_fork $$ [HR Hrevs Hs0 Hcap0 Hslot Hfirst]
  · -- the goroutine
    wp_auto
    wp_apply +noauto HNow as %t0 -
    (try wp_auto)
    icases clockwork.clockLb_init (GF := GF) clockwork.realClock with ⟨%n0, #Hn0⟩
    ihave Hinv : iprop(∃ (xs : List w64) (sl : GoSlice) (lr : w64) (ls : time.Time) (bi : time.Duration)
        (n m : Int),
      "Hrevs" ∷ structFieldRef v3compactor.Periodic go!"revs" pc ↦ sl ∗ "Hs" ∷ sl ↦* xs ∗
      "Hcap" ∷ ownSliceCap w64 sl (DFrac.own 1) ∗
      "lastRevision" ∷ lastRevision_ptr ↦ lr ∗ "lastSuccess" ∷ lastSuccess_ptr ↦ ls ∗
      "baseInterval" ∷ baseInterval_ptr ↦ bi ∗
      "#Hn" ∷ clockwork.clockLb clockwork.realClock n ∗ "#Hst" ∷ stampsOk E.RevLb (sint.Z ri) n xs ∗
      "#Hm" ∷ □ E.RevLb m ∗ "Hfirst" ∷ firstOk γf (sint.Z rn) xs ∗
      "%Hw" ∷ ⌜windowOk xs m (sint.Z rn) (sint.Z lr)⌝)
        $$ [Hrevs Hs0 Hcap0 lastRevision lastSuccess baseInterval Hfirst]
    · iexists [], s0, _, _, _, n0, 0
      simp only [named]
      iframe
      iframe #
      isplitr
      · unfold stampsOk; simp only [List.length_nil]; iapply BigSepL.bigSepL_nil.2; itrivial
      isplitl [Hfirst]
      · simp only [firstOk]; iexact Hfirst
      ipureintro
      refine ⟨List.Pairwise.nil, by simp, by omega, ?_, by omega, by simp, fun _ => h0⟩
      simp only [List.length_nil]; rw [Hrn]; unfold retentionsOf
      have := retentions_bound (sint.Z pd) (by omega) hpd63
      omega
    wp_for Hinv
    (try wp_auto)
    -- `pc.revs = append(pc.revs, pc.rg.Rev())`
    rw [Hri0]
    ihave #HRevm := HRevT $$ %m
    wp_apply +noauto HRevm $$ [HR] as %v ⟨HR, #Hv, %Hvb⟩
    · iframe; iframe #
    (try wp_auto)
    wp_apply wp_slice_literal (V := w64)
    isplitr
    · ipureintro; rfl
    iintro %sl2p ⟨Hsl2, -⟩
    wp_apply (wp_slice_append (V := w64) sl xs _ [v] (DFrac.own 1)) $$ [$Hs $Hcap $Hsl2]
      as %s1 ⟨Hs1, Hcap1, -⟩
    (try wp_auto)
    ihave %Hlen1 := ownSlice_len _ _ _ $$ Hs1
    -- `if len(pc.revs) > retentions { pc.revs = pc.revs[1:] }`
    wp_join iprop(∃ (s2 : GoSlice) (ys : List w64),
        "Hrevs" ∷ structFieldRef v3compactor.Periodic go!"revs" pc ↦ s2 ∗ "Hs" ∷ s2 ↦* ys ∗
        "Hcap" ∷ ownSliceCap w64 s2 (DFrac.own 1) ∗
        ⌜(ys = xs ++ [v] ∧ ((xs.length : Int) + 1 ≤ sint.Z rn)) ∨
          (sint.Z rn < (xs.length : Int) + 1 ∧ ys = (xs ++ [v]).tail)⌝) at next
        with [Hrevs Hs1 Hcap1] as ⟨%s2, %ys, Hrevs, Hs, Hcap, %Hys⟩
    · wp_if_destruct
      · -- trimmed
        ihave %Hwf := ownSliceCap_wf _ _ $$ Hcap1
        have hl1 : (xs.length : Int) + 1 = sint.Z s1.len := by
          have := Hlen1.1
          rw [List.length_append, List.length_singleton] at this
          change xs.length + 1 = (sint.Z s1.len).toNat at this
          omega
        rw [if_pos ⟨by omega, by omega, by omega⟩]
        (try wp_auto)
        icases (ownSlice_slice (V := w64) (W64 1) s1.len s1 (DFrac.own 1) (xs ++ [v])
          ⟨by omega, by omega, by omega⟩).1 $$ Hs1 with ⟨-, Hmid, -⟩
        icases (ownSliceCap_slice (V := w64) s1 (W64 1) (DFrac.own 1) ⟨by omega, by omega, by omega⟩).1
          $$ Hcap1 with Hcap2
        wp_join_done
        iexists _, _
        iframe
        ipureintro
        right
        refine ⟨by omega, ?_⟩
        rw [subslice_def, List.take_of_length_le (by omega), show sint.nat (W64 1) = 1 from rfl,
          List.drop_one]
      · wp_join_done
        iexists s1, xs ++ [v]
        iframe
        ipureintro
        left
        refine ⟨rfl, ?_⟩
        have := Hlen1.1
        rw [List.length_append, List.length_singleton] at this
        change xs.length + 1 = (sint.Z s1.len).toNat at this
        omega
    have hrn1 : 1 ≤ sint.Z rn := by
      rw [Hrn]; unfold retentionsOf
      have := retentions_bound (sint.Z pd) (by omega) hpd63
      omega
    have hw' := windowOk_step xs ys v m (sint.Z rn) (sint.Z lr) Hw Hvb hrn1 Hys
    imod firstOk_step γf (sint.Z rn) xs ys v hrn1 Hw.2.2.2.1 Hys $$ Hfirst with Hfirst
    -- `select { case <-pc.ctx.Done(): return; case <-pc.clock.After(retryInterval): ... }`
    ihave #Hctx2 : iprop(context.isContextDef ctx cd) $$ [Hctx]
    · iexact Hctx
    iunfold context.isContextDef at Hctx2
    icases Hctx2 with ⟨-, #HDone, -⟩
    wp_apply +noauto HDone as %dch %γd #Hdone
    (try wp_auto)
    ihave #HA := clockwork.clockOk_After _ _ ri (E.RevLb (sint.Z v)) n $$ Hclk Hv Hn
    wp_apply +noauto HA as %tch %γt ⟨%T, %HnT, #HstT, #Htch⟩
    wp_auto_lc 2
    wp_apply_core chan.wp_select_blocking
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- `<-pc.ctx.Done()`: the goroutine returns
      simp only [chan.blockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, dch, γd
      isplit
      · ipureintro; rfl
      isplit
      · iapply context.isContextDone_is_chan $$ Hdone
      iapply context.isContextDone_receive _ _ _ _ $$ Hdone
      iintro -
      (try wp_auto)
      wp_for_post
      itrivial
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- `<-pc.clock.After(retryInterval)`: the clock is `retry` past the new sample's stamp
      simp only [chan.blockingClausePre]
      iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, tch, γt
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply is_bag_is_chan $$ Htch
      iapply bag_recv_au $$ [$Hlc1 $Hlc2] Htch
      inext
      iintro %tm #Hn'
      (try wp_auto)
      -- the window's stamps, one more wait old: at the clock bound `T + retry`
      ihave #Hst1 : stampsOk E.RevLb (sint.Z ri) (T + sint.Z ri) (xs ++ [v]) $$ []
      · iapply stampsOk_snoc E.RevLb (sint.Z ri) n T xs v HnT
        isplit
        · iexact Hst
        · iexact HstT
      ihave #Hst' : stampsOk E.RevLb (sint.Z ri) (T + sint.Z ri) ys $$ []
      · rcases Hys with ⟨rfl, -⟩ | ⟨hl, rfl⟩
        · iexact Hst1
        · cases xs with
          | nil => simp at hl; omega
          | cons x0 rest =>
            simp only [List.cons_append, List.tail_cons]
            iapply stampsOk_tail E.RevLb (sint.Z ri) (T + sint.Z ri) x0 (rest ++ [v])
            iexact Hst1
      -- `paused`, under the read lock
      wp_apply sync.RWMutex.wp_RLock $$ [$Hslot] as ⟨Hrl, HP⟩
      iunfold perPausedInv at HP
      icases HP with ⟨%pz, Hpz⟩
      (try wp_auto)
      wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl Hpz] as Hslot
      · inext; iunfold perPausedInv; iexists pz; iframe
      (try wp_auto)
      cases pz
      rotate_left
      · -- paused: the next round
        (try wp_auto)
        wp_for_post
        iframe
        iexists ys, s2, lr, ls, bi, T + sint.Z ri, sint.Z v
        simp only [named]
        iframe
        iframe #
        ipureintro; exact hw'
      (try wp_auto)
      -- `rev := pc.revs[0]`: the window is not empty
      obtain ⟨y0, rest, hys0⟩ : ∃ y0 rest, ys = y0 :: rest := by
        rcases Hys with ⟨rfl, -⟩ | ⟨hl, rfl⟩
        · cases xs with
          | nil => exact ⟨v, [], rfl⟩
          | cons x0 r => exact ⟨x0, r ++ [v], rfl⟩
        · cases xs with
          | nil => simp at hl; omega
          | cons x0 r =>
            cases r with
            | nil => exact ⟨v, [], rfl⟩
            | cons x1 r' => exact ⟨x1, r' ++ [v], rfl⟩
      subst hys0
      ihave %Hlen2 := ownSlice_len _ _ _ $$ Hs
      rw [if_pos ⟨by omega, by
        have := Hlen2.1
        change (y0 :: rest).length = (sint.Z s2.len).toNat at this
        simp at this; omega⟩]
      wp_apply (wp_load_slice_index (V := w64) s2 (sint.Z (W64 0)) (y0 :: rest) (DFrac.own 1) y0
        (by omega)) $$ [$Hs] as Hs
      · ipureintro; rfl
      (try wp_auto)
      -- `if pc.clock.Now().Sub(lastSuccess) < baseInterval || rev == lastRevision { continue }`
      wp_apply +noauto HNow as %t1 -
      wp_apply _root_.Perennial.time.Time.wp_Sub as %dd -
      (try wp_auto)
      wp_if_destruct
      · -- too soon: the next round
        (try wp_auto)
        wp_for_post
        iframe
        iexists (y0 :: rest), s2, lr, ls, bi, T + sint.Z ri, sint.Z v
        simp only [named]
        iframe
        iframe #
        ipureintro; exact hw'
      (try wp_auto)
      wp_if_destruct
      · -- `rev == lastRevision`: the next round
        (try wp_auto)
        wp_for_post
        iframe
        iexists (y0 :: rest), s2, _, ls, bi, T + sint.Z ri, sint.Z v
        simp only [named]
        iframe
        iframe #
        ipureintro; exact hw'
      (try wp_auto)
      have hy0 : 0 < sint.Z y0 := by
        obtain ⟨-, hall, -, -, hlr, hhd, -⟩ := hw'
        have h1 : sint.Z lr ≤ sint.Z y0 := hhd y0 (by simp)
        have h2 : sint.Z y0 ≠ sint.Z lr := fun h => Hif (BitVec.eq_of_toInt_eq h)
        omega
      -- `if baseInterval == pc.period { baseInterval = compactInterval }`
      wp_if_destruct
      all_goals (try wp_auto)
      all_goals (
        -- the log line before the compaction
        wp_apply hInt64 as %f1 -
        wp_apply hDuration as %f2 -
        wp_apply wp_slice_literal
        try (isplitr; (ipureintro; rfl))
        try iintro %_ ⟨_, -⟩
        try wp_auto
        wp_apply hLogger_Info $$ []
        · ipureintro; exact Hlgnn
        (try wp_auto)
        wp_apply +noauto HNow as %t2 -
        (try wp_auto)
        -- `pc.c.Compact(pc.ctx, &pb.CompactionRequest{Revision: rev})`, at C1's periodic permit
        icases perPermit_of_window E.RevLb period (sint.Z ri) (sint.Z rn) (T + sint.Z ri) γf y0 rest
          H10 (by rw [Hri, Hpd]) (by rw [Hrn, Hpd]) hy0 $$ [Hst' Hfirst Hn'] with ⟨#Hperm, Hfirst⟩
        · iframe Hfirst; iframe #
        ihave #HCompact' := HCompact
        iunfold compactableOk at HCompact'
        icases HCompact' with ⟨%cci, %Hcci, #HCT⟩
        rw [Hcci]
        (try wp_auto)
        ihave #HC1 := HCT $$ %(sint.Z y0) %ctx %cd %«$a1_ptr»
        wp_apply +noauto HC1 $$ [HR «$a1»] as %resp %err ⟨HR, #Herr⟩
        · iframe HR #
          unfold compactReqIs
          iexists _; iframe; ipureintro; exact ⟨rfl, rfl⟩
        (try wp_auto)
        -- `err == nil || errors.Is(err, mvcc.ErrCompacted)`: `ErrCompacted` is an `errors.New` error
        ihave #Pmvcc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc $$ []
        · iPkgInit
        icases mvcc.ErrCompacted_target $$ Pmvcc with ⟨%ec, #Hec, %Hecp⟩
        have hw2 : windowOk (y0 :: rest) (sint.Z v) (sint.Z rn) (sint.Z y0) := by
          obtain ⟨a, b, c, d, -, -, -⟩ := hw'
          exact ⟨a, b, c, d, (b y0 (by simp)).1, by simp, by simp⟩
        cases err with
        | nil =>
          (try wp_auto)
          per_ok
        | ok ei =>
          iunfold errTreeOk at Herr
          ihave ⟨%S, %M, #Htree, %HS⟩ := Herr $$
            %(GoInterface.ok ec)
          have Hptr : ∀ tii, GoInterface.ok ec = GoInterface.ok tii →
              _root_.Perennial.errors.IsPointerError tii := fun tii h => by
            cases h; exact Hecp
          (try wp_auto)
          wp_apply (hIs S M (GoInterface.ok ei) _ Hptr (HS.2 Hptr)) $$ [] as %b -
          · iframe Htree; ipureintro; exact HS.1
          cases b
          · (try wp_auto)
            per_fail
          · (try wp_auto)
            per_ok)
    iapply BigAndL.bigAndL_nil.2
    itrivial
  (try wp_auto)
  iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial
