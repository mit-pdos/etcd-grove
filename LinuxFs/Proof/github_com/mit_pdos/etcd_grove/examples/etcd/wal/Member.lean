/-
Lean-first (no Rocq counterpart).

# The running member's WAL side (W4c U5)

While an incarnation's WAL is open (between `Create` or a checked restart and `Close`), the WAL's
state `d` (the program's `tWalOwn γ (some d)`) is exactly candidate `c`'s history (no crash has cut it):
`tMemOk o c d`. From it a syncing call's return re-establishes `tRelI` for the oracle with its mark moved
(`tMemOk_synced`). The pending `Open`s are none (`checkRestart` clears them; only `restartRead` adds
them, before the next `checkRestart`), so the unlock bound is the candidate's own.
-/
module

public import LinuxFs.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.Inv

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI

section pure
variable [GooseExts]

theorem uint_nat_W64_of_lt' (n : Nat) (h : n < 2 ^ 64) : uint.nat (W64 n) = n := by word

/-- **The open WAL's state `d` is candidate `c`'s history** of the created oracle `o`, with `c`'s
bounds, no pending `Open`, the synced mark within `since`. -/
def tMemOk (o : TOracle) (c : TCand) (d : WalDur) : Prop :=
  o.created = true ∧ c ∈ o.cands ∧ o.opens = [] ∧
  d.H.map WalOpG.toM = (tCandHist o c).map absOp ∧
  d.pur ≤ uint.nat c.pur ∧ d.cut ≤ uint.nat c.pur ∧ d.unl ≤ uint.nat c.unl ∧ d.sized = true ∧
  tHistWf (tCandHist o c) ∧ uint.nat o.synced ≤ o.since.length

/-- The oracle with every operation since the last restart synced (`m.o.synced = len(m.o.since)`). -/
def tSynced (o : TOracle) : TOracle := { o with synced := W64 o.since.length }

theorem tSynced_hist (o : TOracle) (c : TCand) : tCandHist (tSynced o) c = tCandHist o c := rfl

/-- The synced oracle's candidate mark is the whole history. -/
theorem tSynced_mark (o : TOracle) (c : TCand) (hl : o.since.length < 2 ^ 64) :
    tCandMark (tSynced o) c = (tCandHist o c).length := by
  unfold tCandMark tSynced tCandHist
  simp only [List.length_append]
  rw [uint_nat_W64_of_lt' _ hl]

theorem tMemOk_synced {o : TOracle} {c : TCand} {d : WalDur} (h : tMemOk o c d)
    (hl : o.since.length < 2 ^ 64) : tMemOk (tSynced o) c d := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, -⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, ?_⟩
  show uint.nat (W64 o.since.length) ≤ o.since.length
  rw [uint_nat_W64_of_lt' _ hl]; exact Nat.le_refl _

/-- The WAL's history length is the candidate's. -/
theorem tMemOk_len {o : TOracle} {c : TCand} {d : WalDur} (h : tMemOk o c d) :
    d.H.length = (tCandHist o c).length := by
  have := congrArg List.length h.2.2.2.1
  simpa using this

/-- **A fully synced running WAL is accounted for by its candidate**: `tCandOk` at the whole
history. -/
theorem tMemOk_candOk {o : TOracle} {c : TCand} {d : WalDur} (h : tMemOk o c d)
    (hl : o.since.length < 2 ^ 64) : tCandOk (tSynced o) c d := by
  obtain ⟨-, -, -, h4, h5, h6, h7, h8, h9, -⟩ := h
  refine ⟨?_, h5, h6, Nat.le_trans h7 (Nat.le_max_left _ _), h8, h9⟩
  rw [tSynced_hist, tSynced_mark o c hl, h4]
  refine ⟨(tCandHist o c).length, Nat.le_refl _, by rw [List.length_map]; exact Nat.le_refl _, Or.inl ?_⟩
  rw [← List.length_map (f := absOp), List.take_length]

end pure

end etcd_wal
end EtcdGrove
end Perennial
