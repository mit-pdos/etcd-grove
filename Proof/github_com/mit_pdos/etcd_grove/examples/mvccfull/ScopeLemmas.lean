/- Lean-first (no Rocq counterpart).

# `mvccfull`: `inScope`'s checks give `runCfgOk`

The number of keys at depth `d` (`keysOf_length_succ`: `(3 ^ (d + 1) - 3) / 2`, so fewer than
`2 ^ 60` exactly up to depth 37), and `runCfgOk_of`: the facts `inScope` checks (`config.go`) give
`Run.spec`'s scope.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.Run
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.hashing

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open github_com.mit_pdos.etcd_grove.examples.mvccfull

/-- A non-empty prefix's keys: `(3 ^ (n + 1) - 1) / 2` of them. -/
theorem walkM_length_ne : ∀ (n : Nat) (p : GoString), p ≠ [] →
    2 * (walkM p n).length + 1 = 3 ^ (n + 1)
  | 0, p, hp => by simp [walkM, hp]
  | n + 1, p, hp => by
    have h1 := walkM_length_ne n (p ++ [W8 97]) (by simp)
    have h2 := walkM_length_ne n (p ++ [W8 98]) (by simp)
    have h3 := walkM_length_ne n (p ++ [W8 99]) (by simp)
    simp only [walkM, hp, if_false, List.length_append, List.length_singleton]
    rw [Nat.pow_succ]
    omega

/-- The keys at depth `n + 1`: `(3 ^ (n + 2) - 3) / 2` of them. -/
theorem keysOf_length_succ (n : Nat) : 2 * (keysOf (n + 1)).length + 3 = 3 ^ (n + 2) := by
  have h1 := walkM_length_ne n [W8 97] (by simp)
  have h2 := walkM_length_ne n [W8 98] (by simp)
  have h3 := walkM_length_ne n [W8 99] (by simp)
  unfold keysOf
  simp only [walkM, if_true, List.nil_append, List.length_append, List.length_nil]
  rw [Nat.pow_succ]
  omega

/-- **Fewer than `2 ^ 60` keys up to depth 37.** -/
theorem keysOf_length_lt (d : Nat) (h : d ≤ 37) : (keysOf d).length < 2 ^ 60 := by
  cases d with
  | zero => simp [keysOf, walkM]
  | succ n =>
    have hk := keysOf_length_succ n
    have hp : 3 ^ (n + 2) ≤ 3 ^ 38 := Nat.pow_le_pow_right (by decide) (by omega)
    have h38 : (3 : Nat) ^ 38 < 2 ^ 61 := by decide
    have h61 : (2 : Nat) ^ 61 = 2 * 2 ^ 60 := by decide
    omega

/-- `hashing` false: the hashes' weight not positive, and some weight of the first six positive. -/
theorem readMix_of_hashing {w : List Int} (hh : hashingM w = false)
    (hsum : ((w.take 6).map (fun x => max 0 x)).sum < 2 ^ 63) : readMixOk w := by
  unfold hashingM at hh
  simp only [Bool.or_eq_false_iff, Bool.not_eq_eq_eq_not, Bool.not_false, decide_eq_false_iff_not,
    List.any_eq_true, List.mem_range, decide_eq_true_eq] at hh
  obtain ⟨⟨i, hi, hpos⟩, h5⟩ := hh
  exact ⟨by omega, ⟨i, hi, hpos⟩, hsum⟩

/-- **`inScope`'s checks give `runCfgOk`.** -/
theorem runCfgOk_of [GooseExts] (cfg : Config) (wr : List w64)
    (hops0 : 0 ≤ sint.Z cfg.Ops') (hops : sint.Z cfg.Ops' < 2 ^ 38)
    (hrs : 2 * max 0 (sint.Z cfg.Readers') + 4 * max 0 (sint.Z cfg.Streams') + 3 ≤ 2 ^ 28)
    (hbl : sint.Z cfg.BatchLimit' ≤ 2 ^ 57) (hcbl : sint.Z cfg.CompactionBatchLimit' ≤ 2 ^ 56)
    (hd : sint.Z cfg.Depth' ≤ 37) (hmv : sint.Z cfg.MaxVal' ≤ 2 ^ 20)
    (hh : hashingM (wr.map sint.Z) = false)
    (hsum : (((wr.map sint.Z).take 6).map (fun x => max 0 x)).sum < 2 ^ 63) :
    runCfgOk cfg wr := by
  have hdn : sint.nat (normalizeM cfg).Depth' ≤ 37 := by
    unfold normalizeM
    simp only
    split
    · decide
    · word
  refine ⟨readMix_of_hashing hh hsum, hops0, hops, hrs, ?_, ?_, keysOf_length_lt _ hdn, hmv,
    by omega⟩
  · unfold limOf
    split
    · exact hbl
    · decide
  · unfold cblOf mvcc.batchLimitOk
    split
    · refine ⟨by omega, ?_⟩
      show _ ≤ (2 : Int) ^ 56
      exact hcbl
    · decide

end mvccfull
end EtcdGrove
end Perennial
