/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/handlers/CfgLog.lean (241f27e).
-/
/-
Pure lemmas on the configurations of a log (stage 4, package follow): what the follower's
`configurations` bookkeeping needs across a truncation (`appendEntries`' `DeleteRange` and the
rollback of the latest configuration to the committed one), an append (`StoreLogs`) and the scan of
the new entries (`processConfigurationLogEntry`). Stated over `proto.lastCfgIdx` and proved from
`proto.lastCfgIdx_spec`, `lastCfgIdx_append_noCfg`, `lastCfgIdx_append_cfg` (by their statements).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.proto.Cfg

@[expose] public section

noncomputable section

namespace Perennial
namespace github_com.hashicorp.raft
namespace proto

theorem ent_take_of_le (L : RLog) (m k : Nat) (h : k ≤ m) : ent (L.take m) k = ent L k := by
  unfold ent
  split
  · rfl
  · rw [List.getElem?_take]; split <;> first | rfl | omega

theorem ent_append_of_le (L X : RLog) (k : Nat) (h : k ≤ L.length) : ent (L ++ X) k = ent L k := by
  unfold ent
  split
  · rfl
  · rw [List.getElem?_append_left (by omega)]

/-- `lastCfgIdx` is determined by its characterization. -/
theorem lastCfgIdx_unique (L : RLog) (n : Nat) (h1 : n ≤ L.length)
    (h2 : n = 0 ∨ ∃ e, ent L n = some e ∧ e.kind = kConfig)
    (h3 : ∀ k e, n < k → ent L k = some e → e.kind ≠ kConfig) : lastCfgIdx L = n := by
  obtain ⟨g1, g2, g3⟩ := lastCfgIdx_spec L
  rcases Nat.lt_trichotomy (lastCfgIdx L) n with h | h | h
  · rcases h2 with h2 | ⟨e, he, hk⟩
    · omega
    · exact absurd hk (g3 n e h he)
  · exact h
  · rcases g2 with g2 | ⟨e, he, hk⟩
    · omega
    · exact absurd hk (h3 _ e h he)

/-- A prefix through the latest configuration has the same latest configuration. -/
theorem lastCfgIdx_take_of_le (L : RLog) (m : Nat) (h : lastCfgIdx L ≤ m) :
    lastCfgIdx (L.take m) = lastCfgIdx L := by
  obtain ⟨g1, g2, g3⟩ := lastCfgIdx_spec L
  apply lastCfgIdx_unique
  · simp only [List.length_take]; omega
  · rcases g2 with g2 | ⟨e, he, hk⟩
    · left; exact g2
    · right; exact ⟨e, by rw [ent_take_of_le _ _ _ h]; exact he, hk⟩
  · intro k e hk he
    have hkm : k ≤ m := by
      unfold ent at he; split at he
      · simp at he
      · rw [List.getElem?_take] at he; split at he
        · omega
        · simp at he
    rw [ent_take_of_le _ _ _ hkm] at he
    exact g3 k e hk he

/-- The rollback: truncating at `m` in `[c, li)` where `li` is the latest configuration and `c` the
one before it leaves `c` the latest. -/
theorem lastCfgIdx_take_rollback (L : RLog) (m : Nat)
    (hc : lastCfgIdx (L.take (lastCfgIdx L - 1)) ≤ m) (hm : m < lastCfgIdx L) :
    lastCfgIdx (L.take m) = lastCfgIdx (L.take (lastCfgIdx L - 1)) := by
  have := lastCfgIdx_take_of_le (L.take (lastCfgIdx L - 1)) m hc
  rw [List.take_take, Nat.min_eq_left (by omega)] at this
  exact this

/-- One more entry of the log scanned (`processConfigurationLogEntry` on the entry at `n + 1`). -/
theorem lastCfgIdx_take_succ (L : RLog) (n : Nat) (e : Entry) (he : ent L (n + 1) = some e) :
    lastCfgIdx (L.take (n + 1)) = if e.kind = kConfig then n + 1 else lastCfgIdx (L.take n) := by
  have hl : L.take (n + 1) = L.take n ++ [e] := by
    unfold ent at he
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel] at he
    rw [List.take_succ, he]; rfl
  have hn : (L.take n).length = n := by
    unfold ent at he
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel] at he
    have := (List.getElem?_eq_some_iff.1 he).1
    simp only [List.length_take]; omega
  rw [hl]
  split
  · rename_i h; rw [lastCfgIdx_append_cfg _ _ h, hn]
  · rename_i h
    exact lastCfgIdx_append_noCfg _ _ (by intro x hx; simp at hx; rw [hx]; exact h)

theorem lastCfgIdx_le_length (L : RLog) : lastCfgIdx L ≤ L.length := (lastCfgIdx_spec L).1

end proto
end github_com.hashicorp.raft
end Perennial
