/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/InmemStore__DeleteRange.lean (241f27e).
-/
/-
The proof of `raft.(*InmemStore).DeleteRange`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.InmemStore__DeleteRange

@[expose] public section

set_option linter.deprecated false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.hashicorp.raft

open proto

/-- The loop invariant of `DeleteRange`: the keys in `[mn, j)` are deleted (or `mx` is the
largest word, and the loop never ends). -/
def delInv (lm0 : GMap w64 Loc) (mn mx j : w64) (lm : GMap w64 Loc) : Prop :=
  uint.nat mx = 2 ^ 64 - 1 ∨
  (uint.nat mn ≤ uint.nat j ∧ uint.nat j ≤ Max.max (uint.nat mn) (uint.nat mx + 1) ∧
   ∀ key : w64, lm !! key =
     if uint.nat mn ≤ uint.nat key ∧ uint.nat key < uint.nat j then none else lm0 !! key)

theorem delInv_init (lm0 : GMap w64 Loc) (mn mx : w64) : delInv lm0 mn mx mn lm0 := by
  right
  refine ⟨Nat.le_refl _, by omega, ?_⟩
  intro key; rw [if_neg (by omega)]

theorem delInv_step (lm0 : GMap w64 Loc) (mn mx j : w64) (lm : GMap w64 Loc)
    (h : delInv lm0 mn mx j lm) (hj : uint.nat j ≤ uint.nat mx) :
    delInv lm0 mn mx (j + W64 1) (GMap.delete j lm) := by
  rcases h with h | ⟨h1, h2, h3⟩
  · left; exact h
  by_cases hm : uint.nat mx = 2 ^ 64 - 1
  · left; exact hm
  right
  have hlt : uint.nat mx < 2 ^ 64 := mx.isLt
  have hj1 : uint.nat (j + W64 1) = uint.nat j + 1 := by word
  rw [hj1]
  refine ⟨by omega, by omega, ?_⟩
  intro key
  by_cases hk : key = j
  · subst hk; rw [GMap.lookup_delete, if_pos (by omega)]
  · rw [GMap.lookup_delete_ne _ (Ne.symm hk), h3 key]
    have hne : uint.nat key ≠ uint.nat j := by
      intro h; apply hk; apply BitVec.eq_of_toNat_eq; simp only [uint.nat] at h; exact h
    by_cases hr : uint.nat mn ≤ uint.nat key ∧ uint.nat key < uint.nat j
    · rw [if_pos hr, if_pos (by omega)]
    · rw [if_neg hr, if_neg (by omega)]

theorem delInv_exit (lm0 : GMap w64 Loc) (mn mx j : w64) (lm : GMap w64 Loc)
    (h : delInv lm0 mn mx j lm) (hj : ¬uint.nat j ≤ uint.nat mx) (hmx : uint.nat mx < 2 ^ 64 - 1) :
    ∀ key : w64, lm !! key =
      if uint.nat mn ≤ uint.nat key ∧ uint.nat key ≤ uint.nat mx then none else lm0 !! key := by
  have hlt : uint.nat j < 2 ^ 64 := j.isLt
  rcases h with h | ⟨h1, h2, h3⟩
  · omega
  intro key
  rw [h3 key]
  by_cases hr : uint.nat mn ≤ uint.nat key ∧ uint.nat key ≤ uint.nat mx
  · rw [if_pos (by omega), if_pos hr]
  · rw [if_neg (by omega), if_neg hr]

theorem ent_take (L : RLog) (n k : Nat) (h : k ≤ n) : ent (L.take n) k = ent L k := by
  unfold ent
  split
  · rfl
  · rw [List.getElem?_take_of_lt (by omega)]

end github_com.hashicorp.raft

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

open github_com.hashicorp.raft proto

theorem github_com.hashicorp.raft.InmemStore.DeleteRange.wp_proof :
    github_com.hashicorp.raft.InmemStore.DeleteRange.spec (GF := GF) (hG := hG) := by
  sorry -- hraft_robust L0: re-proved by its stage (HANDOFF.md)

end proof

end Perennial
