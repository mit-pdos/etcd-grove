/-
# remote's counter instance: its porcupine model (`notes/remote-port-plan.md`, R4)

`Model()` (counter.go) is the counter with pending increments: linkv's pending-writes model
`pSeq cB` (`Proof/.../etcd/txnlin/PendModel.lean`) of the counter `cB` (`Defs.lean`), on
porcupine's operations through `cDec`. Its state `State{Lo, K}` stands for a set of
configurations, which `Equal` compares as values.

- `stepG`: `step`, transcribed on Go's `int64`s (`step`'s spec, `Net/Spec/.../counter/step.lean`).
- `cSet lo K`: the configurations `State{lo, K}` stands for, `(lo + j, K - j)` for `j ≤ K`: the
  counter's value and its pending increments (a list of `K - j` `true`s). Closed under late
  effects (`cSet_closed`), each reached from `(lo, K)` (`cSet_reach`).
- `ppost_errT`, `ppost_errF`, `ppost_okT`, `ppost_okF`: the model's next set from `cSet lo K`,
  one per kind of operation (an unknown increment, an unknown read, an answered increment, an
  answered read), by extensionality.
- **`stepG_pSeq`**: `step` on `State{lo, K}` (with `lo + K < 2^60`: no overflow) is the model's
  step on `cSet lo K`: `false` exactly when the model has no next state, else a
  `State{lo', K'}` of the next set, `lo' + K' ≤ lo + K + 1`.
- `cS`: the model spec. Its `rep k v s` (`cRep`): `v` is the boxed `State{lo, K}` and `s` is
  `cSet lo K`, with `lo + K ≤ k` (a step adds at most one) and `lo + K ≤ 2^60` (`Step` runs below
  index `2^60`; and equal `State`s are then the same `(lo, K)`, so the same set: `stV_inj`).
- `cS_pendDec`: `cS` decodes as `remote`'s far-side store `cR γ` (`PendDec`): `cDec` on a boxed
  `bool` and a boxed `Out` (`cDec_box`, by the injectivity of the boxes: an `Out`'s fields are
  read off its value by deterministic steps, `out_intoVal_inj`).
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.Defs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

namespace github_com.mit_pdos.etcd_grove.examples.lib.remote.counter

open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote

section go
variable [GooseExts]

/-- `step` (counter.go), on Go's `int64`s (wrapping; comparisons signed). -/
def stepG (s : State) (incr : Bool) (o : Out) : Bool × State :=
  if o.Unknown' then
    if incr then (true, ⟨s.Lo', s.K' + W64 1⟩) else (true, s)
  else if incr then
    if sint.Z o.N' < sint.Z (s.Lo' + W64 1) ∨ sint.Z (s.Lo' + s.K' + W64 1) < sint.Z o.N' then
      (false, s)
    else (true, ⟨o.N', s.K' - (o.N' - W64 1 - s.Lo')⟩)
  else if sint.Z o.N' < sint.Z s.Lo' ∨ sint.Z (s.Lo' + s.K') < sint.Z o.N' then (false, s)
  else (true, ⟨o.N', s.K' - (o.N' - s.Lo')⟩)

/-- The state `State{lo, K}`. -/
def stV (lo K : Nat) : State := ⟨W64 lo, W64 K⟩

end go

/-! ## The configurations a state stands for -/

section pure

/-- **The configurations `State{lo, K}` stands for**: `(lo + j, K - j)` for `j ≤ K`, the
counter's value and its `K - j` pending increments (a list of `true`s). -/
def cSet (lo K : Nat) : linkv.PSet w64 Bool :=
  fun c => ∃ j, j ≤ K ∧ c.st = W64 (lo + j : Nat) ∧ c.pend = List.replicate (K - j) true

theorem w64_succ (x : Nat) : W64 (x : Nat) + W64 1 = W64 (x + 1 : Nat) := by
  word

theorem w64_add (a b : Nat) : W64 (a : Nat) + W64 (b : Nat) = W64 (a + b : Nat) := by
  word

theorem w64_sub (a b : Nat) (h : b ≤ a) : W64 (a : Nat) - W64 (b : Nat) = W64 (a - b : Nat) := by
  word

theorem sZ_w64 (x : Nat) (h : x < 2 ^ 63) : sint.Z (W64 (x : Nat)) = x := by
  word

theorem w64_sZ (n : w64) : W64 (sint.Z n) = n := by
  word

theorem cB_true (x : w64) : cB.step true x = (x + W64 1, x + W64 1) := rfl
theorem cB_false (x : w64) : cB.step false x = (x, x) := rfl

/-- A late effect keeps a configuration in the set. -/
theorem cSet_silent {lo K : Nat} {c c' : linkv.PCfg w64 Bool} (hc : cSet lo K c)
    (h : linkv.PSilent cB c c') : cSet lo K c' := by
  obtain ⟨j, hj, hst, hp⟩ := hc
  cases h with
  | apply i hi =>
    rw [hp] at hi ⊢
    have hi' := List.eq_of_mem_replicate hi
    subst hi'
    have hpos : 0 < K - j := by
      rcases Nat.eq_zero_or_pos (K - j) with h0 | h0
      · rw [h0] at hi; simp at hi
      · exact h0
    refine ⟨j + 1, by omega, ?_, ?_⟩
    · show (cB.step true c.st).1 = _
      rw [cB_true, hst, w64_succ]; rfl
    · simp only [List.erase_replicate_self]; congr 1
  | perm p hpp =>
    refine ⟨j, hj, hst, ?_⟩
    simp only at hpp ⊢
    rw [hp] at hpp
    exact List.perm_replicate.1 hpp

theorem cSet_closed (lo K : Nat) : linkv.PSet.Closed cB (cSet lo K) := by
  intro c c' hc hr
  induction hr with
  | refl => exact hc
  | step hs _ ih => exact ih (cSet_silent hc hs)

/-- One late effect from `(x, K + 1)`. -/
theorem silent_one (x K : Nat) :
    linkv.PSilent cB ⟨W64 (x : Nat), List.replicate (K + 1) true⟩
      ⟨W64 (x + 1 : Nat), List.replicate K true⟩ := by
  have := linkv.PSilent.apply (P := cB) ⟨W64 (x : Nat), List.replicate (K + 1) true⟩ true
    List.mem_cons_self
  simp only [cB_true, w64_succ, List.erase_replicate_self, Nat.add_sub_cancel] at this
  exact this

/-- Every configuration of the set is reached from its least, `(lo, K)`. -/
theorem cSet_reach {lo K : Nat} {c' : linkv.PCfg w64 Bool} (h : cSet lo K c') :
    linkv.PReach cB ⟨W64 (lo : Nat), List.replicate K true⟩ c' := by
  obtain ⟨j, hj, hst, hp⟩ := h
  induction j generalizing lo K with
  | zero =>
    cases c'
    simp only at hst hp
    subst hst hp
    exact linkv.PReach.refl _
  | succ j ih =>
    obtain ⟨K, rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
    refine .step (silent_one lo K) (ih (lo := lo + 1) (K := K) (by omega) ?_ ?_)
    · rw [hst]; congr 2; omega
    · rw [hp]; congr 1; omega

/-- The least configuration of a set is in it. -/
theorem cSet_base (lo K : Nat) : cSet lo K ⟨W64 (lo : Nat), List.replicate K true⟩ :=
  ⟨0, Nat.zero_le _, rfl, rfl⟩

/-- `ppost` from a closed set: no late effects needed before the step. -/
theorem ppost_closed_iff {S : linkv.PSet w64 Bool} (hS : linkv.PSet.Closed cB S) (i : Bool)
    (o : linkv.Ans w64) (c' : linkv.PCfg w64 Bool) :
    linkv.ppost cB S i o c' ↔
      ∃ c c₁, S c ∧ linkv.PStep cB c i o c₁ ∧ linkv.PReach cB c₁ c' := by
  constructor
  · rintro ⟨c₀, c, c₁, h0, hr, hs, hr1⟩
    exact ⟨c, c₁, hS _ _ h0 hr, hs, hr1⟩
  · rintro ⟨c, c₁, h, hs, hr1⟩
    exact ⟨c, c, c₁, h, .refl _, hs, hr1⟩

/-- An increment of unknown outcome: one more pending. -/
theorem ppost_errT (lo K : Nat) : linkv.ppost cB (cSet lo K) true .err = cSet lo (K + 1) := by
  funext c'
  apply propext
  rw [ppost_closed_iff (cSet_closed lo K)]
  constructor
  · rintro ⟨c, c₁, ⟨j, hj, hst, hp⟩, hs, hr⟩
    cases hs with
    | errW =>
      refine cSet_closed lo (K + 1) ⟨c.st, true :: c.pend⟩ _ ⟨j, by omega, hst, ?_⟩ hr
      show true :: c.pend = _
      rw [hp, show K + 1 - j = (K - j) + 1 by omega]; rfl
    | errR h _ => simp [cB] at h
  · intro h
    obtain ⟨j, hj, hst, hp⟩ := h
    rcases Nat.lt_or_ge j (K + 1) with hlt | hge
    · refine ⟨⟨W64 (lo + j : Nat), List.replicate (K - j) true⟩, _,
        ⟨j, by omega, rfl, rfl⟩, .errW _ true rfl rfl, ?_⟩
      cases c'
      simp only at hst hp
      subst hst hp
      rw [show K + 1 - j = (K - j) + 1 by omega]
      exact .refl _
    · have hj' : j = K + 1 := by omega
      subst hj'
      refine ⟨⟨W64 (lo + K : Nat), []⟩, _, ⟨K, Nat.le_refl _, rfl, by simp⟩,
        .errW _ true rfl rfl, .single ?_⟩
      cases c'
      simp only [Nat.sub_self, List.replicate_zero] at hst hp
      subst hst hp
      rw [show lo + (K + 1) = lo + K + 1 by omega]
      exact silent_one (lo + K) 0

/-- A read of unknown outcome: nothing changes. -/
theorem ppost_errF (lo K : Nat) : linkv.ppost cB (cSet lo K) false .err = cSet lo K := by
  funext c'
  apply propext
  rw [ppost_closed_iff (cSet_closed lo K)]
  constructor
  · rintro ⟨c, c₁, hc, hs, hr⟩
    cases hs with
    | errW h _ => simp [cB] at h
    | errR => exact cSet_closed lo K _ _ hc hr
  · intro h
    exact ⟨c', c', h, .errR _ false rfl rfl, .refl _⟩

/-- An answered increment of `n`: from `(lo + j, K - j)` with `n = lo + j + 1`. -/
theorem ppost_okT (lo K : Nat) (n : w64) (c' : linkv.PCfg w64 Bool) :
    linkv.ppost cB (cSet lo K) true (.ok n) c' ↔
      ∃ j, j ≤ K ∧ n = W64 (lo + j + 1 : Nat) ∧ cSet (lo + j + 1) (K - j) c' := by
  rw [ppost_closed_iff (cSet_closed lo K)]
  constructor
  · rintro ⟨c, c₁, ⟨j, hj, hst, hp⟩, hs, hr⟩
    generalize ha : (linkv.Ans.ok n : linkv.Ans w64) = a at hs
    cases hs with
    | ok =>
      injection ha with ha
      rw [cB_true, hst, w64_succ] at ha hr
      refine ⟨j, hj, ha, cSet_closed _ _ _ _ ⟨0, Nat.zero_le _, rfl, ?_⟩ hr⟩
      show c.pend = _
      rw [hp, Nat.sub_zero]
    | errW => cases ha
    | errR => cases ha
    | obs => simp_all [cB]
  · rintro ⟨j, hj, hn, hc'⟩
    refine ⟨⟨W64 (lo + j : Nat), List.replicate (K - j) true⟩, _, ⟨j, hj, rfl, rfl⟩, ?_,
      cSet_reach hc'⟩
    have := linkv.PStep.ok (P := cB) ⟨W64 (lo + j : Nat), List.replicate (K - j) true⟩ true rfl
    simp only [cB_true, w64_succ] at this
    rw [hn]; exact this

/-- An answered read of `n`: at `(lo + j, K - j)` with `n = lo + j`. -/
theorem ppost_okF (lo K : Nat) (n : w64) (c' : linkv.PCfg w64 Bool) :
    linkv.ppost cB (cSet lo K) false (.ok n) c' ↔
      ∃ j, j ≤ K ∧ n = W64 (lo + j : Nat) ∧ cSet (lo + j) (K - j) c' := by
  rw [ppost_closed_iff (cSet_closed lo K)]
  constructor
  · rintro ⟨c, c₁, ⟨j, hj, hst, hp⟩, hs, hr⟩
    generalize ha : (linkv.Ans.ok n : linkv.Ans w64) = a at hs
    cases hs with
    | ok =>
      injection ha with ha
      rw [cB_false, hst] at ha hr
      refine ⟨j, hj, ha, cSet_closed _ _ _ _ ⟨0, Nat.zero_le _, rfl, ?_⟩ hr⟩
      show c.pend = _
      rw [hp, Nat.sub_zero]
    | errW => cases ha
    | errR => cases ha
    | obs => simp_all [cB]
  · rintro ⟨j, hj, hn, hc'⟩
    refine ⟨⟨W64 (lo + j : Nat), List.replicate (K - j) true⟩, _, ⟨j, hj, rfl, rfl⟩, ?_,
      cSet_reach hc'⟩
    have := linkv.PStep.ok (P := cB) ⟨W64 (lo + j : Nat), List.replicate (K - j) true⟩ false rfl
    simp only [cB_false] at this
    rw [hn]; exact this

variable [GooseExts]

theorem pSeq_some {S T : linkv.PSet w64 Bool} {i : Bool} {o : linkv.Ans w64}
    (h : linkv.ppost cB S i o = T) (c : linkv.PCfg w64 Bool) (hc : T c) :
    (linkv.pSeq cB).step S (i, o) = some T := by
  simp only [linkv.pSeq]
  split
  · rw [h]
  · next hn => exact absurd ⟨c, h ▸ hc⟩ hn

theorem pSeq_none {S : linkv.PSet w64 Bool} {i : Bool} {o : linkv.Ans w64}
    (h : ∀ c, ¬ linkv.ppost cB S i o c) : (linkv.pSeq cB).step S (i, o) = none := by
  simp only [linkv.pSeq]
  split
  · next hn => exact absurd hn (fun ⟨c, hc⟩ => h c hc)
  · rfl

/-- What `step` returns, as a verdict and a next state: the model's (see `stepG_pSeq`). -/
def StepOk (lo K : Nat) (r : Bool × State) (m : Option (linkv.PSet w64 Bool)) : Prop :=
  r.1 = m.isSome ∧ ∀ S', m = some S' →
    ∃ lo' K', r.2 = stV lo' K' ∧ lo' + K' ≤ lo + K + 1 ∧ S' = cSet lo' K'

theorem stepOk_some {lo K lo' K' : Nat} {r : Bool × State} {m : Option (linkv.PSet w64 Bool)}
    (h1 : r = (true, stV lo' K')) (hb : lo' + K' ≤ lo + K + 1) (hm : m = some (cSet lo' K')) :
    StepOk lo K r m := by
  subst h1 hm
  refine ⟨rfl, ?_⟩
  rintro S' ⟨⟩
  exact ⟨lo', K', rfl, hb, rfl⟩

theorem stepOk_none {lo K : Nat} {r : Bool × State} {m : Option (linkv.PSet w64 Bool)}
    (h1 : r.1 = false) (hm : m = none) : StepOk lo K r m := by
  subst hm
  exact ⟨h1, by rintro _ ⟨⟩⟩

/-- **`step` is the model's step** on the set `State{lo, K}` stands for, with no `int64`
overflow (`lo + K < 2^60`): it returns `false` exactly when the model has no next state, and
otherwise a `State{lo', K'}` of the model's next state, with `lo' + K' ≤ lo + K + 1`. -/
theorem stepG_pSeq (lo K : Nat) (hb : lo + K < 2 ^ 60) (b u : Bool) (n : w64) :
    StepOk lo K (stepG (stV lo K) b ⟨u, n⟩)
      ((linkv.pSeq cB).step (cSet lo K) (b, if u then .err else .ok n)) := by
  have h1 : sint.Z (W64 (lo : Nat) + W64 1) = lo + 1 := by
    rw [w64_succ, sZ_w64 _ (by omega)]; push_cast; rfl
  have h2 : sint.Z (W64 (lo : Nat) + W64 (K : Nat) + W64 1) = lo + K + 1 := by
    rw [w64_add, w64_succ, sZ_w64 _ (by omega)]; push_cast; rfl
  have h3 : sint.Z (W64 (lo : Nat)) = lo := sZ_w64 _ (by omega)
  have h4 : sint.Z (W64 (lo : Nat) + W64 (K : Nat)) = lo + K := by
    rw [w64_add, sZ_w64 _ (by omega)]; push_cast; rfl
  cases u with
  | true =>
    cases b with
    | true =>
      refine stepOk_some (lo' := lo) (K' := K + 1) ?_ (by omega)
        (pSeq_some (ppost_errT lo K) _ (cSet_base lo (K + 1)))
      simp only [stepG, stV, ite_true, w64_succ]
    | false =>
      refine stepOk_some (lo' := lo) (K' := K) ?_ (by omega)
        (pSeq_some (ppost_errF lo K) _ (cSet_base lo K))
      simp only [stepG, stV, ite_true, Bool.false_eq_true, ite_false]
  | false =>
    cases b with
    | true =>
      simp only [stepG, stV, Bool.false_eq_true, ite_false, ite_true, h1, h2]
      split
      · next hc =>
        refine stepOk_none rfl (pSeq_none ?_)
        intro c hp
        obtain ⟨j, hj, hn, -⟩ := (ppost_okT lo K n c).1 hp
        rw [hn, sZ_w64 _ (by omega)] at hc
        omega
      · next hc =>
        obtain ⟨j, hj⟩ : ∃ j : Nat, sint.Z n = lo + j + 1 := ⟨(sint.Z n - lo - 1).toNat, by omega⟩
        have hjK : j ≤ K := by omega
        have hn : n = W64 (lo + j + 1 : Nat) := by
          rw [← w64_sZ n, hj]; push_cast; rfl
        have hpost : linkv.ppost cB (cSet lo K) true (.ok n) = cSet (lo + j + 1) (K - j) := by
          funext c'
          apply propext
          rw [ppost_okT]
          constructor
          · rintro ⟨j', hj', hn', hc'⟩
            have : j' = j := by
              have := congrArg sint.Z (hn.symm.trans hn')
              rw [sZ_w64 _ (by omega), sZ_w64 _ (by omega)] at this
              omega
            subst this
            exact hc'
          · intro hc'
            exact ⟨j, hjK, hn, hc'⟩
        refine stepOk_some (lo' := lo + j + 1) (K' := K - j) ?_ (by omega)
          (pSeq_some hpost _ (cSet_base _ _))
        simp only [stV, Prod.mk.injEq, _root_.true_and, State.mk.injEq]
        refine ⟨hn, ?_⟩
        rw [hn]
        word
    | false =>
      simp only [stepG, stV, Bool.false_eq_true, ite_false, h3, h4]
      split
      · next hc =>
        refine stepOk_none rfl (pSeq_none ?_)
        intro c hp
        obtain ⟨j, hj, hn, -⟩ := (ppost_okF lo K n c).1 hp
        rw [hn, sZ_w64 _ (by omega)] at hc
        omega
      · next hc =>
        obtain ⟨j, hj⟩ : ∃ j : Nat, sint.Z n = lo + j := ⟨(sint.Z n - lo).toNat, by omega⟩
        have hjK : j ≤ K := by omega
        have hn : n = W64 (lo + j : Nat) := by
          rw [← w64_sZ n, hj]; push_cast; rfl
        have hpost : linkv.ppost cB (cSet lo K) false (.ok n) = cSet (lo + j) (K - j) := by
          funext c'
          apply propext
          rw [ppost_okF]
          constructor
          · rintro ⟨j', hj', hn', hc'⟩
            have : j' = j := by
              have := congrArg sint.Z (hn.symm.trans hn')
              rw [sZ_w64 _ (by omega), sZ_w64 _ (by omega)] at this
              omega
            subst this
            exact hc'
          · intro hc'
            exact ⟨j, hjK, hn, hc'⟩
        refine stepOk_some (lo' := lo + j) (K' := K - j) ?_ (by omega)
          (pSeq_some hpost _ (cSet_base _ _))
        simp only [stV, Prod.mk.injEq, _root_.true_and, State.mk.injEq]
        refine ⟨hn, ?_⟩
        rw [hn]
        word

end pure

/-! ## The model spec -/

section spec
variable [GooseExts] [GoGlobalContext] {GF : BundledGFunctors}

/-- A state value, boxed (`any` holding a `State`). -/
abbrev boxS (s : State) : GoInterface := interface.mkOk State.ty #s

/-- **The representation**: a value of index `k` is the boxed `State{lo, K}` of the set
`cSet lo K`, with `lo + K ≤ k` (each step adds at most one to `lo + K`) and `lo + K ≤ 2^60` (so
`step`'s `int64` arithmetic does not overflow, and equal `State`s are equal sets). -/
def cRep (k : Nat) (v : GoInterface) (s : linkv.PSet w64 Bool) : Prop :=
  ∃ lo K : Nat, lo + K ≤ k ∧ lo + K ≤ 2 ^ 60 ∧ v = boxS (stV lo K) ∧ s = cSet lo K

/-- **The counter's porcupine model** (pending increments): `pSeq cB` through `cDec`; inputs
boxed `bool`s, outputs boxed `Out`s. -/
def cS : ModelSpec GF (linkv.PSet w64 Bool) where
  M := linkv.pM cB cDec
  rep k v s := iprop(⌜cRep k v s⌝)
  ioOk i o := iprop(⌜(∃ b, i = boxB b) ∧ ∃ u n, o = outV u n⌝)
  ioOk_pers _ _ := by infer_instance

/-- The initial set: `State{0, 0}`'s. -/
theorem cSet_init : cSet 0 0 = linkv.pInit cB := by
  funext c
  apply propext
  constructor
  · rintro ⟨j, hj, hst, hp⟩
    have : j = 0 := by omega
    subst this
    cases c
    simp only at hst hp
    subst hst hp
    rfl
  · intro h
    subst h
    exact ⟨0, Nat.le_refl _, rfl, rfl⟩

/-- Equal states of bounded `lo + K` are equal sets. -/
theorem stV_inj {lo K lo' K' : Nat} (hb : lo + K ≤ 2 ^ 60) (hb' : lo' + K' ≤ 2 ^ 60)
    (h : stV lo K = stV lo' K') : lo = lo' ∧ K = K' := by
  simp only [stV, State.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have e1 := congrArg sint.Z h1
  have e2 := congrArg sint.Z h2
  rw [sZ_w64 _ (by omega), sZ_w64 _ (by omega)] at e1 e2
  omega

end spec

section dec
variable [GooseExts] [go_gctx : GoGlobalContext] [lctx : GoLocalContext]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.Assumptions]

/-- `Out`'s values are injective (`N` and `Unknown` are read off by deterministic steps). -/
theorem out_intoVal_inj {x y : Out} (h : (#x : val) = #y) : x = y := by
  have hN := (Out.TypeAssumptions.get'N x).isGoStep_det_internal.isGoStep_pure_det
  have hN' := (Out.TypeAssumptions.get'N y).isGoStep_det_internal.isGoStep_pure_det
  have hU := (Out.TypeAssumptions.get'Unknown x).isGoStep_det_internal.isGoStep_pure_det
  have hU' := (Out.TypeAssumptions.get'Unknown y).isGoStep_det_internal.isGoStep_pure_det
  rw [h, hN'] at hN
  rw [h, hU'] at hU
  have eN : Val #x.N' = Val #y.N' := (congrFun hN (Val #y.N')) ▸ rfl
  have eU : Val #x.Unknown' = Val #y.Unknown' := (congrFun hU (Val #y.Unknown')) ▸ rfl
  injection eN with eN
  injection eU with eU
  have eN' := GoGlobalContext.intoVal_inj_w64 eN
  have eU' := GoGlobalContext.intoVal_inj_bool eU
  cases x; cases y
  simp only at eN' eU'
  subst eN' eU'
  rfl

theorem boxB_inj' (a b : Bool) (h : boxB a = boxB b) : a = b := by
  simp only [boxB, interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq,
    _root_.true_and] at h
  exact GoGlobalContext.intoVal_inj_bool h

theorem outV_inj {u n u' n'} (h : outV u n = outV u' n') : u = u' ∧ n = n' := by
  simp only [outV, interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq,
    _root_.true_and] at h
  have := out_intoVal_inj h
  simp only [Out.mk.injEq] at this
  exact this

/-- `cDec` on a boxed `bool` and a boxed `Out`. -/
theorem cDec_box (b u : Bool) (n : w64) :
    cDec (boxB b, outV u n) = some (b, if u then .err else .ok n) := by
  unfold cDec
  split
  · next h =>
    have hs := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec h))
    obtain ⟨h1, h2⟩ := Prod.mk.inj hs
    have e1 := boxB_inj' _ _ h1
    obtain ⟨e2, e3⟩ := outV_inj h2
    have e1' : Classical.choose h = b := e1.symm
    have e2' : Classical.choose (Classical.choose_spec h) = u := e2.symm
    have e3' : Classical.choose (Classical.choose_spec (Classical.choose_spec h)) = n := e3.symm
    dsimp only
    rw [e3', e2', e1']
  · next hn => exact absurd ⟨b, u, n, rfl⟩ hn

/-- The model's step on porcupine's operation `(boxB b, outV u n)`. -/
theorem pM_box (S : linkv.PSet w64 Bool) (b u : Bool) (n : w64) :
    (linkv.pM cB cDec).step S (boxB b, outV u n) =
      (linkv.pSeq cB).step S (b, if u then .err else .ok n) :=
  linkv.pM_step cB cDec S _ b _ (cDec_box b u n)

/-- The model's step on porcupine's operation `(boxB b, outV u n)`. -/
theorem cS_step {GF : BundledGFunctors} (S : linkv.PSet w64 Bool) (b u : Bool) (n : w64) :
    (cS (GF := GF)).M.step S (boxB b, outV u n) =
      (linkv.pSeq cB).step S (b, if u then .err else .ok n) :=
  linkv.pM_step cB cDec S _ b _ (cDec_box b u n)

/-- **porcupine's model is the pending-writes model** of the far side's store `cR γ`. -/
theorem cS_pendDec {GF : BundledGFunctors} [AllG GF] (γ : GName) :
    PendDec (cR (GF := GF) γ) (cS (GF := GF)) where
  init := rfl
  ok s i o := cS_step s i false o
  err s i := cS_step s i true (W64 0)
  ioOk_ok i o := BI.pure_intro ⟨⟨i, rfl⟩, false, o, rfl⟩
  ioOk_err i := BI.pure_intro ⟨⟨i, rfl⟩, true, W64 0, rfl⟩
  noObs _ := rfl

end dec

end github_com.mit_pdos.etcd_grove.examples.lib.remote.counter
end Perennial
