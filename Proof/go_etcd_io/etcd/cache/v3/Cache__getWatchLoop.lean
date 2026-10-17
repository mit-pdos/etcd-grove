/-
Proof of `Spec/Cache__getWatchLoop.lean`. Lean-first (no Rocq counterpart).

The loop's invariant: the demux's writer, in any state, with the revision bound's authority, the
wait-group token, and (etcd#22408) the backoff after `k` failed attempts, `backoffAt cfg k` (the
retry timer comes from the cache's `Clock`; the schedule itself is the pure model below). Each `get` gets etcd's linearizability for the revision bound from the
client (`isEtcdKVE`), knowing etcd has reached it (`cacheBound`).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.Cache__getWatchLoop
public import Spec.go_etcd_io.etcd.cache.v3.Cache__getWatch
public import Spec.fmt.Printf
public import Spec.time.Duration__String
public import Proof.go_etcd_io.etcd.cache.v3.InvConfig

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

/-! ## The backoff schedule (etcd#22408)

`backoff *= 2; if backoff > c.cfg.MaxBackoff { backoff = c.cfg.MaxBackoff }` on `time.Duration`
(`int64`, wrapping multiplication, signed comparison). -/

theorem one_le_two_pow_int : ∀ k : Nat, (1 : Int) ≤ 2 ^ k
  | 0 => by decide
  | k + 1 => by rw [Int.pow_succ]; have := one_le_two_pow_int k; omega

section backoff
variable [FfiSyntax]

/-- One step of the schedule: double, capped at `mx`. -/
def backoffNext (mx b : w64) : w64 :=
  if sint.Z mx < sint.Z (b * W64 2) then mx else b * W64 2

/-- The backoff after `k` failed attempts, from `InitialBackoff`. -/
def backoffAt (cfg : Config) : Nat → w64
  | 0 => cfg.InitialBackoff'
  | k + 1 => backoffNext cfg.MaxBackoff' (backoffAt cfg k)

/-- With `0 < InitialBackoff ≤ MaxBackoff < 2^62`, the schedule is `min(InitialBackoff·2^k,
MaxBackoff)`: it starts at `InitialBackoff`, doubles, and flattens at `MaxBackoff`. -/
theorem backoffAt_eq_min (cfg : Config) (h0 : 0 < sint.Z cfg.InitialBackoff')
    (h1 : sint.Z cfg.InitialBackoff' ≤ sint.Z cfg.MaxBackoff')
    (h2 : sint.Z cfg.MaxBackoff' < 2 ^ 62) :
    ∀ k : Nat, sint.Z (backoffAt cfg k) = min (sint.Z cfg.InitialBackoff' * 2 ^ k)
      (sint.Z cfg.MaxBackoff') := by
  intro k
  induction k with
  | zero => simp only [backoffAt, Int.pow_zero, Int.mul_one]; omega
  | succ k ih =>
    have hP : (0 : Int) < 2 ^ k := by have := one_le_two_pow_int k; omega
    have hIP : 0 < sint.Z cfg.InitialBackoff' * 2 ^ k := Int.mul_pos h0 hP
    have hsucc : sint.Z cfg.InitialBackoff' * 2 ^ (k + 1) =
        2 * (sint.Z cfg.InitialBackoff' * 2 ^ k) := by
      rw [Int.pow_succ, ← Int.mul_assoc, Int.mul_comm _ 2]
    generalize hX : sint.Z cfg.InitialBackoff' * 2 ^ k = X at ih hIP hsucc
    rw [hsucc]
    have hb0 : 0 < sint.Z (backoffAt cfg k) := by omega
    have hbm : sint.Z (backoffAt cfg k) ≤ sint.Z cfg.MaxBackoff' := by omega
    have hmul : sint.Z (backoffAt cfg k * W64 2) = 2 * sint.Z (backoffAt cfg k) := by
      word
    simp only [backoffAt, backoffNext]
    split
    · rename_i h
      rw [hmul] at h
      omega
    · rename_i h
      rw [hmul] at h ⊢
      omega

/-- Under the same bounds every backoff is in `[InitialBackoff, MaxBackoff]`: positive, so the
loop never retries without waiting. -/
theorem backoffAt_bounds (cfg : Config) (h0 : 0 < sint.Z cfg.InitialBackoff')
    (h1 : sint.Z cfg.InitialBackoff' ≤ sint.Z cfg.MaxBackoff')
    (h2 : sint.Z cfg.MaxBackoff' < 2 ^ 62) (k : Nat) :
    sint.Z cfg.InitialBackoff' ≤ sint.Z (backoffAt cfg k) ∧
      sint.Z (backoffAt cfg k) ≤ sint.Z cfg.MaxBackoff' := by
  rw [backoffAt_eq_min cfg h0 h1 h2 k]
  have hP : (1 : Int) ≤ 2 ^ k := one_le_two_pow_int k
  have : sint.Z cfg.InitialBackoff' * 1 ≤ sint.Z cfg.InitialBackoff' * 2 ^ k :=
    Int.mul_le_mul_of_nonneg_left hP (by omega)
  omega

/-- A configuration `newCache` accepts whose schedule wraps: `InitialBackoff = MaxBackoff =
2^62` ns (about 146 years). -/
def wrapCfg : Config :=
  { defaultConfigVal with InitialBackoff' := W64 (2 ^ 62), MaxBackoff' := W64 (2 ^ 62) }

/-- The bound `MaxBackoff < 2^62` is needed: for `wrapCfg`, which `newCache` accepts, the
doubling wraps to `-2^63`, which is not above `MaxBackoff`, so the backoff becomes negative and
then `0` for good: the loop then retries without waiting. -/
theorem backoffAt_wraps :
    CfgValid wrapCfg ∧ sint.Z (backoffAt wrapCfg 1) < 0 ∧
      ∀ k, 2 ≤ k → backoffAt wrapCfg k = W64 0 := by
  have e1 : backoffAt wrapCfg 1 = backoffNext (W64 (2 ^ 62)) (W64 (2 ^ 62)) := rfl
  have e2 : backoffAt wrapCfg 2 = backoffNext (W64 (2 ^ 62)) (backoffAt wrapCfg 1) := rfl
  have n1 : backoffNext (W64 (2 ^ 62)) (W64 (2 ^ 62)) = W64 (2 ^ 63) := by decide
  have n2 : backoffNext (W64 (2 ^ 62)) (W64 (2 ^ 63)) = W64 0 := by decide
  have n0 : backoffNext (W64 (2 ^ 62)) (W64 0) = W64 0 := by decide
  have hmx : wrapCfg.MaxBackoff' = W64 (2 ^ 62) := rfl
  have h2 : backoffAt wrapCfg 2 = W64 0 := by rw [e2, e1, n1, n2]
  refine ⟨?_, ?_, ?_⟩
  · unfold CfgValid
    show 0 < sint.Z (W64 2048) ∧ 2 ≤ sint.Z (W64 32) ∧ 0 < sint.Z (W64 (2 ^ 62)) ∧
      sint.Z (W64 (2 ^ 62)) ≤ sint.Z (W64 (2 ^ 62)) ∧ 0 < sint.Z (W64 5000000000)
    decide
  · rw [e1, n1]; decide
  · intro k hk
    induction k with
    | zero => omega
    | succ k ih =>
      rcases Nat.lt_or_ge k 2 with h | h
      · have : k = 1 := by omega
        subst this; exact h2
      · show backoffNext wrapCfg.MaxBackoff' (backoffAt wrapCfg k) = W64 0
        rw [ih h, hmx, n0]

end backoff

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

-- `wp_load` from a persistent struct points-to (see `Cache__waitTillRevision.lean`).
attribute [-instance] Config.Config_access_store_InitialBackoff
  Config.Config_access_store_MaxBackoff

theorem Cache.getWatchLoop.wp_proof
    (wp_getWatch : Cache.getWatch.spec (GF := GF) (hG := hG))
    (wp_Printf : EtcdGrove.fmt.Printf.spec (GF := GF) (hG := hG))
    (wp_DurStr : EtcdGrove.time.Duration.String.spec (GF := GF) (hG := hG)) :
    Cache.getWatchLoop.spec (GF := GF) (hG := hG) := by
  intro c cf γr γd cap c0
  wp_start as ⟨#Hc, Hw, Hrun⟩
  ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  ihave #Hc' := Hc
  iunfold isCacheFields at Hc'
  iNamed Hc'
  icases HisICtx with ⟨%ics, #Hctxi, -⟩
  ihave #Hctxi' := Hctxi
  iNamed Hctxi'
  ihave #Hcfg' := Hcfg
  iStructNamedPrefix Hcfg' "Cfg"
  ihave #Hclk := HisClock
  iunfold isClockFor at Hclk
  try wp_auto
  try ipersist c
  try ipersist ctx
  ihave HI : (∃ (c1 : DemuxCore) (k : Nat), "Hw" ∷ cacheWriter cf γd cap c1 ∗
      "Hrun" ∷ cacheWgLoopRunning cf ∗ "backoff" ∷ backoff_ptr ↦ backoffAt cf.cfg k : IProp GF)
      $$ [Hw Hrun backoff]
  · iexists c0, 0; simp only [named, backoffAt]; iframe
  wp_for HI
  -- `ctx.Err()`
  ihave #HErrU := HErr $$ %Broadcast.Unknown
  wp_apply HErrU as %err -
  cases err with
  | ok e =>
    wp_auto
    wp_for_post
    iapply HΦ
    iframe Hrun
    iexists c1
    iframe
  | nil =>
  wp_auto
  -- `c.getWatch()`
  wp_apply wp_getWatch c cf γr γd cap c1 $$ [$Hpkg $Hc $Hw $Hrun]
    as %err ⟨%Hne, #HeS, Hrun, %c2, Hw⟩
  obtain ⟨e, rfl⟩ : ∃ e, err = GoInterface.ok e := by
    cases err with
    | nil => exact absurd rfl Hne
    | ok e => exact ⟨e, rfl⟩
  wp_auto
  -- `fmt.Printf(...)`
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  ihave #HeS' : EtcdGrove.fmt.stringMethodSpec e go!"Error" $$ []
  · rw [show EtcdGrove.fmt.stringMethodSpec e go!"Error" = errorStringSpec e from rfl]
    iapply errStrOk_elim; iexact HeS
  wp_apply wp_Printf $$ [$Hfmt $Hsl] as %n %e2 -
  · try rw [show sint.nat (W64 (0 + 1)) = 1 by rfl]
    try simp only [List.set_cons_succ, List.set_cons_zero]
    simp only [EtcdGrove.fmt.argsOk]
    isplitr
    · iapply EtcdGrove.time.Duration.String.argOk wp_DurStr
    isplitr
    · simp only [EtcdGrove.fmt.argOk]; iright; ileft; iexact HeS'
    itrivial
  -- `timer := c.clock.NewTimer(backoff)`
  try wp_auto
  wp_apply Hclk as %t #Ht
  · -- the backoff is in `[InitialBackoff, MaxBackoff]` (`BackoffOk`, `backoffAt_bounds`)
    ipureintro
    left
    exact backoffAt_bounds cf.cfg Hbackoff.1 Hbackoff.2.1 Hbackoff.2.2 k
  ihave #Ht' := Ht
  iunfold isTimer at Ht'
  icases Ht' with ⟨#HtChan, -, #HtStop⟩
  try wp_auto
  -- the backoff: `select` on `ctx.Done()` and `timer.Chan()`
  wp_apply +noauto HDone as %ch1 %γ1 #Hdone
  wp_auto
  wp_apply +noauto HtChan as %tch %γt #Htch
  wp_auto_lc 2
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `<-ctx.Done()`: `timer.Stop()`, return
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch1, γ1
    isplit
    · ipureintro; rfl
    isplit
    · iapply context.isContextDone_is_chan $$ Hdone
    iapply context.isContextDone_receive _ _ _ _ $$ Hdone
    iintro -
    wp_auto
    wp_apply HtStop as %b -
    wp_for_post
    iapply HΦ
    iframe Hrun
    iexists c2
    iframe
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `<-timer.Chan()`: double the backoff, capped at `MaxBackoff`; loop
    simp only [chan.blockingClausePre]
    iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, tch, γt
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Htch
    iapply bag_recv_au $$ [$Hlc1 $Hlc2] Htch
    inext
    iintro %t' -
    wp_auto
    wp_if_destruct
    · wp_for_post
      iframe HΦ
      iexists c2, (k + 1)
      simp only [named, backoffAt, backoffNext]
      rw [if_pos (by assumption)]
      iframe
    · wp_for_post
      iframe HΦ
      iexists c2, (k + 1)
      simp only [named, backoffAt, backoffNext]
      rw [if_neg (by assumption)]
      iframe
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end EtcdGrove
end Perennial
