/- Lean-first (no Rocq counterpart).

# The read position is at most `walOpenPos` (pure; W3/W5 of `notes/wal-fsext-plan.md`)

`ReadAll` reads from the segment `Open` selected: the last whose name's index `ix` is at most the
start's index `a` (`searchIndex`). A cut segment starting at `k` is named above the prefix's last
index (`WalAbsD.nameBound`), so `k` is in `walNameBound`'s set; and the fold matched a snapshot
record of index `a` after `k`, so `walLastSnapPos` (the guard's position) is at least `k`
(`readPos_le_openPos`): the `hpos` of `readAll_ok_pure`.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.WalHistLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Fs WalEnc go_etcd_io.raft.v3

section pos
variable [GooseExts]

/-- A member of a filtered range is at most its last element. -/
theorem le_getLast_range_filter (f : Nat → Bool) : ∀ (n x : Nat),
    x ∈ (List.range n).filter f → x ≤ ((List.range n).filter f).getLast?.getD 0
  | 0, x, hx => by simp at hx
  | n + 1, x, hx => by
    rw [List.range_succ, List.filter_append] at hx ⊢
    by_cases hf : f n = true
    · have e : [n].filter f = [n] := by simp [hf]
      rw [e] at hx ⊢
      rw [List.getLast?_append, List.getLast?_singleton]
      simp only [Option.some_or, Option.getD_some]
      rcases List.mem_append.1 hx with h | h
      · have := List.mem_range.1 (List.mem_filter.1 h).1; omega
      · simp at h; omega
    · have e : [n].filter f = [] := by simp [hf]
      rw [e, List.append_nil] at hx ⊢
      exact le_getLast_range_filter f n x hx

/-- **The read position is at most `walOpenPos`** (see the file header): `k = 0`, or `k` a cut
position of `I` whose segment is named `ix ≤ a` above the prefix's last index, with a snapshot
record of index `a` after `k`. -/
theorem readPos_le_openPos {I : WalHist} {k ix : Nat} {a : w64}
    (h : k = 0 ∨ (walCutPos I k ∧ k ≤ I.length ∧ walLastIdx (I.take k) + 1 ≤ ix ∧ ix ≤ uint.nat a ∧
      ∃ m, WalOpG.snap m ∈ I.drop k ∧ m.Index' = a)) :
    k ≤ walOpenPos I a := by
  rcases h with h0 | ⟨hcp, hkl, hix1, hix2, m, hm, hma⟩
  · subst h0; exact Nat.zero_le _
  unfold walOpenPos
  apply Nat.le_min.2
  constructor
  · unfold walGuardPos
    split
    · exact hkl
    split
    · next ha => subst ha; simp at hix2; omega
    split
    · -- The last snapshot record of index `a` is at or after `m`'s.
      obtain ⟨i, hi, hgi⟩ := List.mem_iff_getElem.1 hm
      have hi' : k + i < I.length := by simp at hi; omega
      have hgi' : I[k + i]? = some (WalOpG.snap m) := by
        rw [List.getElem?_eq_getElem hi', ← hgi, List.getElem_drop]
      unfold walLastSnapPos
      refine Nat.le_trans (Nat.le_add_right k i) (le_getLast_range_filter _ I.length (k + i) ?_)
      apply List.mem_filter.2 ⟨List.mem_range.2 hi', ?_⟩
      rw [hgi']; simp [hma]
    · exact hkl
  · unfold walNameBound
    split
    · exact hkl
    · apply le_getLast_range_filter _ (I.length + 1) k
      apply List.mem_filter.2 ⟨List.mem_range.2 (by omega), ?_⟩
      simp only [ite_false, Bool.false_eq_true, decide_eq_true_eq]
      exact ⟨hcp, by omega⟩

end pos

end WalFs
end EtcdGrove
end Perennial
