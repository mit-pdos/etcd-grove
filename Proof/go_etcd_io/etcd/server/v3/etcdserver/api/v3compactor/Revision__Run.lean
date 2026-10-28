/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3compactor/Revision__Run.lean`. Lean-first (no Rocq
counterpart). The spec-first pilot's phase 1 (`notes/compactor-pilot-plan.md`): the spec is written,
the proof is phase 3's easy full proof.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Revision__Run
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
/-- A compaction that succeeded (or found the revision compacted already): `prev = rev`, the log
line, the next round. -/
local macro "rev_ok" : tactic => `(tactic| (
  (try wp_auto)
  wp_apply hInt64 as %g1 -
  wp_apply hInt64 as %g2 -
  wp_apply _root_.Perennial.time.wp_Since as %dur -
  wp_apply hDuration as %g3 -
  wp_apply wp_slice_literal
  try (isplitr; (ipureintro; rfl))
  try iintro %_ ⟨_, -⟩
  try wp_auto
  wp_apply hLogger_Info $$ []
  · ipureintro; exact Hlgnn
  (try wp_auto)
  wp_for_post
  iframe
  iexists _; iframe))

set_option hygiene false in
/-- A compaction that failed: the warning, the next round (`prev` unchanged). -/
local macro "rev_fail" : tactic => `(tactic| (
  (try wp_auto)
  wp_apply hInt64 as %g1 -
  wp_apply hInt64 as %g2 -
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
  iexists _; iframe))

theorem v3compactor.Revision.Run.wp_proof
    (hInt64 : zap.Int64.spec (GF := GF) (hG := hG))
    (hDuration : zap.Duration.spec (GF := GF) (hG := hG))
    (hLogger_Info : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (hLogger_Warn : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (hError : zap.Error.spec (GF := GF) (hG := hG))
    (hIs : errors.Is.spec (GF := GF) (hG := hG)) :
    v3compactor.Revision.Run.spec (GF := GF) (hG := hG) := by
  intro rc E ret
  wp_start as ⟨#Hrc, Hpre⟩
  iunfold isRevision at Hrc
  icases Hrc with ⟨%lg, %clk, %rt, %ctx, %cd, %γctx, %cancel, #Hlg, %Hlgnn, #Hclkf, #Hclk, #Hrt, %Hrt,
    #Hrg, #Hc, #Hctxf, #Hctx, #Htrc, #Hcancelf, #Hcs, #Hmu⟩
  iunfold runPre at Hpre
  icases Hpre with ⟨#HRev, #HCompact, HR, #HLb0⟩
  wp_auto
  ipersist rc
  wp_apply wp_fork $$ [HR prev]
  · -- the goroutine
    wp_auto
    ihave Hinv : iprop(∃ p : w64, "prev" ∷ prev_ptr ↦ p) $$ [prev]
    · iexists _; iframe
    wp_for Hinv
    ihave #Hctx2 : iprop(context.isContextDef ctx cd) $$ [Hctx]
    · iexact Hctx
    iunfold context.isContextDef at Hctx2
    icases Hctx2 with ⟨-, #HDone, -⟩
    wp_apply +noauto HDone as %dch %γd #Hdone
    (try wp_auto)
    icases clockwork.clockOk_ok _ _ $$ Hclk with %Hci
    obtain ⟨ci, Hci⟩ := Hci
    subst Hci
    icases clockwork.clockLb_init (GF := GF) clockwork.realClock with ⟨%n0, #Hn0⟩
    simp only [go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.revInterval]
    (try wp_auto)
    ihave #HA := clockwork.clockOk_After _ _ (W64 300000000000) (iprop(True) : IProp GF) n0 $$ Hclk [] Hn0
    · iintro !>; itrivial
    wp_apply +noauto HA as %tch %γt ⟨%T, %HnT, -, #Htch⟩
    wp_auto_lc 2
    wp_apply_core chan.wp_select_blocking
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- `<-rc.ctx.Done()`: the goroutine returns
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
    · -- `<-rc.clock.After(revInterval)`
      simp only [chan.blockingClausePre]
      iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, tch, γt
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply is_bag_is_chan $$ Htch
      iapply bag_recv_au $$ [$Hlc1 $Hlc2] Htch
      inext
      iintro %tm -
      (try wp_auto)
      -- `paused`, under the lock
      wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
      iunfold revPausedInv at Hinv
      icases Hinv with ⟨%pz, Hpz⟩
      (try wp_auto)
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hpz]
      · inext; iunfold revPausedInv; iexists pz; iframe
      (try wp_auto)
      cases pz
      rotate_left
      · -- paused: the next round
        (try wp_auto)
        wp_for_post
        iframe
        iexists p; iframe
      (try wp_auto)
      -- `rc.rg.Rev() - rc.retention`
      ihave #HRev' := HRev
      iunfold revGetterOk at HRev'
      icases HRev' with ⟨%ri, %Hri, #HRevT⟩
      rw [Hri]
      ihave #HRev0 := HRevT $$ %(0 : Int)
      wp_apply +noauto HRev0 $$ [HR] as %v ⟨HR, #Hv, %Hvb⟩
      · iframe; iframe #
      (try wp_auto)
      -- `if rev <= 0 || rev == prev { continue }`
      wp_if_destruct
      · -- `rev <= 0`: the next round
        (try wp_auto)
        wp_for_post
        iframe
        iexists p; iframe
      (try wp_auto)
      have Hpos : ¬sint.Z (v - rt) ≤ sint.Z (W64 0) := Hif
      wp_if_destruct
      · -- `rev == prev`: the next round
        (try wp_auto)
        wp_for_post
        iframe
        iexists _; iframe
      (try wp_auto)
      -- the log line before the compaction
      wp_apply _root_.Perennial.time.wp_Now as %now -
      (try wp_auto)
      wp_apply hInt64 as %f1 -
      wp_apply hInt64 as %f2 -
      wp_apply wp_slice_literal
      try (isplitr; (ipureintro; rfl))
      try iintro %_ ⟨_, -⟩
      try wp_auto
      wp_apply hLogger_Info $$ []
      · ipureintro; exact Hlgnn
      (try wp_auto)
      -- `rc.c.Compact(rc.ctx, &pb.CompactionRequest{Revision: rev})`, at C1's revision permit
      ihave #HCompact' := HCompact
      iunfold compactableOk at HCompact'
      icases HCompact' with ⟨%cci, %Hcci, #HCT⟩
      rw [Hcci]
      (try wp_auto)
      ihave #HC1 := HCT $$ %(sint.Z (v - rt)) %ctx %cd %«$a1_ptr»
      have hsum : sint.Z (v - rt) + ret = sint.Z v := by
        rw [← Hrt]
        have h0 : ¬ sint.Z (v - rt) ≤ 0 := by simpa using Hpos
        word
      wp_apply +noauto HC1 $$ [HR «$a1»] as %resp %err ⟨HR, #Herr⟩
      · iframe HR #
        unfold revPermit
        isplitr
        · isplitr
          · ipureintro; have h0 : ¬ sint.Z (v - rt) ≤ 0 := by simpa using Hpos
            omega
          rw [hsum]; iexact Hv
        iapply compactReqIs_of _ _ _ ⟨rfl, rfl⟩ $$ «$a1»
      (try wp_auto)
      -- `err == nil || errors.Is(err, mvcc.ErrCompacted)`: `ErrCompacted` is an `errors.New` error
      ihave #Pmvcc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc $$ []
      · iPkgInit
      icases mvcc.ErrCompacted_target $$ Pmvcc with ⟨%ec, #Hec, %Hecp⟩
      cases err with
      | nil =>
        (try wp_auto)
        rev_ok
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
          rev_fail
        · (try wp_auto)
          rev_ok
    iapply BigAndL.bigAndL_nil.2
    itrivial
  (try wp_auto)
  iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial
