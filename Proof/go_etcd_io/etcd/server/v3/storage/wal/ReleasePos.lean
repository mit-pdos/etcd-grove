/- Lean-first (no Rocq counterpart).

# A segment named below the release (open) index starts at or before `walReleasePos` (`walOpenPos`)

(pure; unit `locks`, session 5, `notes/wal-units/locks.md`.) A segment starting at the cut position `p`
is named `ix`, above the prefix's last index (`WalAbsD.nameBound`). If `ix < a` (`ReleaseLockTo(a)`'s
kept lock, `strict`) or `ix ≤ a` (`Open(a)`'s first lock), then `p` is in `walNameBound`'s set, and no
snapshot record of index `a` is before `p` (it would put `a` in the prefix's last index, below `ix`), so
`p` is at most the guard's position too. Unlike `readPos_le_openPos` (`ReadAllPos.lean`), no snapshot
record after `p` is needed.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadAllPos

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Fs WalEnc go_etcd_io.raft.v3

section pos
variable [GooseExts]

/-- **A segment's start is at most the name position** (see the file header). -/
theorem cutStart_le_namePos {H : WalHist} {p ix : Nat} {a : w64} (strict : Bool)
    (h : p = 0 ∨ (walCutPos H p ∧ p ≤ H.length ∧ walLastIdx (H.take p) + 1 ≤ ix ∧
      (if strict then ix < uint.nat a else ix ≤ uint.nat a))) :
    p ≤ min (walGuardPos H a) (walNameBound H (uint.nat a) strict) := by
  rcases h with h0 | ⟨hcp, hpl, hix, hia⟩
  · subst h0; exact Nat.zero_le _
  have hia' : ix ≤ uint.nat a := by
    cases strict <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hia <;> omega
  apply Nat.le_min.2
  constructor
  · unfold walGuardPos
    split
    · exact hpl
    split
    · next ha => subst ha; simp at hia'; omega
    split
    · next hg =>
      obtain ⟨⟨i, m, hi, hma⟩, -⟩ := hg
      have hip : p ≤ i := by
        rcases Nat.lt_or_ge i p with hlt | hge
        · exfalso
          have hmem : WalOpG.snap m ∈ H.take p := by
            apply List.mem_iff_getElem?.2
            exact ⟨i, by rw [List.getElem?_take, if_pos hlt]; exact hi⟩
          have h1 := walMaxSnap_mem (H.take p) 0 m hmem
          have h2 := walLastIdx_eq (H.take p)
          rw [hma] at h1
          omega
        · exact hge
      have hil : i < H.length := (List.getElem?_eq_some_iff.1 hi).1
      unfold walLastSnapPos
      refine Nat.le_trans hip (le_getLast_range_filter _ H.length i ?_)
      apply List.mem_filter.2 ⟨List.mem_range.2 hil, ?_⟩
      rw [hi]; simp [hma]
    · exact hpl
  · unfold walNameBound
    split
    · exact hpl
    · apply le_getLast_range_filter _ (H.length + 1) p
      apply List.mem_filter.2 ⟨List.mem_range.2 (by omega), ?_⟩
      cases strict
      · simp only [Bool.false_eq_true, ite_false, decide_eq_true_eq] at hia ⊢
        exact ⟨hcp, by omega⟩
      · simp only [ite_true, decide_eq_true_eq] at hia ⊢
        exact ⟨hcp, by omega⟩

/-- `ReleaseLockTo(a)`'s case: a segment named below `a` starts at or before `walReleasePos`. -/
theorem cutStart_le_releasePos {H : WalHist} {p ix : Nat} {a : w64}
    (h : p = 0 ∨ (walCutPos H p ∧ p ≤ H.length ∧ walLastIdx (H.take p) + 1 ≤ ix ∧ ix < uint.nat a)) :
    p ≤ walReleasePos H a := by
  unfold walReleasePos
  refine cutStart_le_namePos (ix := ix) true ?_
  rcases h with h | ⟨h1, h2, h3, h4⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, h2, h3, by simpa using h4⟩

/-- `Open(a)`'s case: a segment named at most `a` starts at or before `walOpenPos`. -/
theorem cutStart_le_openPos {H : WalHist} {p ix : Nat} {a : w64}
    (h : p = 0 ∨ (walCutPos H p ∧ p ≤ H.length ∧ walLastIdx (H.take p) + 1 ≤ ix ∧ ix ≤ uint.nat a)) :
    p ≤ walOpenPos H a := by
  unfold walOpenPos
  refine cutStart_le_namePos (ix := ix) false ?_
  rcases h with h | ⟨h1, h2, h3, h4⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, h2, h3, by simpa using h4⟩

end pos

end WalFs
end EtcdGrove
end Perennial

end
