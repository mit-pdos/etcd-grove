/-
What a crash keeps of the tree's history, with a lower bound: `TreeCrashedLb V V' n`, a crash of
`V` (`TreeCrashed`) that kept at least the first `n` entries of its log. A machine crash keeps every
committed entry (`MachineCrash`), so a crash of a state whose first `c` entries are committed is
one (`osCrash_lb`). Untrusted.
-/
module

public import GooseLang.Ext.Fs.CrashFiles

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

/-- A crash of the history `V` that kept at least its first `n` entries: some prefix of `k ≥ n`
entries replayed, nothing logged since. -/
def TreeCrashedLb (V V' : Hist) (n : Nat) : Prop :=
  ∃ k, n ≤ k ∧ k ≤ V.2.length ∧ V' = (replay ((V.2.take k).map (·.op)) V.1, [])

/-- It is a crash. -/
theorem TreeCrashedLb.crashed {V V' : Hist} {n : Nat} (h : TreeCrashedLb V V' n) :
    TreeCrashed V V' := by
  obtain ⟨k, -, hk, rfl⟩ := h
  exact ⟨k, hk, rfl⟩

/-- Every crash keeps at least nothing. -/
theorem TreeCrashed.lb_zero {V V' : Hist} (h : TreeCrashed V V') : TreeCrashedLb V V' 0 := by
  obtain ⟨k, hk, rfl⟩ := h
  exact ⟨k, Nat.zero_le _, hk, rfl⟩

/-- A smaller lower bound. -/
theorem TreeCrashedLb.mono {V V' : Hist} {n n' : Nat} (h : TreeCrashedLb V V' n) (hn : n' ≤ n) :
    TreeCrashedLb V V' n' := by
  obtain ⟨k, hnk, hk, rfl⟩ := h
  exact ⟨k, Nat.le_trans hn hnk, hk, rfl⟩

/-- A crash that kept every entry: the tree now, nothing logged. -/
theorem TreeCrashedLb.all {V V' : Hist} (h : TreeCrashedLb V V' V.2.length) : V' = (V.now, []) := by
  obtain ⟨k, hnk, hk, rfl⟩ := h
  have : k = V.2.length := Nat.le_antisymm hk hnk
  subst this
  show (replay ((V.2.take V.2.length).map (·.op)) V.1, ([] : List LogEntry)) = (V.now, [])
  rw [List.take_length]; rfl

/-- The tree a crash kept at least `n` entries of is the tree after `k ≥ n` of them. -/
theorem TreeCrashedLb.now {V V' : Hist} {n : Nat} (h : TreeCrashedLb V V' n) :
    ∃ k, n ≤ k ∧ k ≤ V.2.length ∧ V'.now = Hist.now (V.1, V.2.take k) ∧ V'.2 = [] := by
  obtain ⟨k, hnk, hk, rfl⟩ := h
  exact ⟨k, hnk, hk, rfl, rfl⟩

section after
variable {st st' : OsState} {V : Hist} {Γdf : GMap w64 (Ino × DirPh)} {Γc : GMap Nat (Nat × Iris.Qp)}

/-- **A machine crash keeps the committed entries**: from a state whose first `c` entries are
committed, the new tree is a crash that kept at least `c` of them. -/
theorem osCrash_lb (htc : TreeCoh st V Γdf Γc) (hc : OsCrash st st') (c : Nat)
    (hcm : ∀ y, y < c → st.fs.committed y) : TreeCrashedLb V (st'.fs.treeDur, []) c := by
  obtain ⟨-, -, -, -, -, -, ⟨S, hSlt, hcom, hcl, htr⟩, -⟩ := hc
  obtain ⟨k, hk, hiff⟩ := closed_prefix htc.seq hSlt hcl
  rw [keptOps_prefix _ S k hk hiff] at htr
  refine ⟨k, ?_, by rw [htc.hist]; exact hk, by rw [htc.hist, htr]⟩
  rcases Nat.eq_zero_or_pos c with h0 | hpos
  · omega
  · have := (hiff (c - 1)).1 (hcom _ (hcm _ (by omega)))
    omega

end after

end Fs
end Perennial

end
