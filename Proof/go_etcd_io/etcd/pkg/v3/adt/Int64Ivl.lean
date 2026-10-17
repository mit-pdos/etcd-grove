/-
The int64 intervals of `interval_tree.go` (`Int64Comparable`, `NewInt64Point`), for etcd#22358
(2026-10-17, branch `pr-verify/etcd-22358`): the signed order `Int64Comparable.Compare` is
meant to implement, the interval value, and what `NewInt64Point` returns. Lean-first (no Rocq
counterpart). The tree's proof (`Defs.lean`, `ownIvt`) covers string-affine intervals only; no
in-tree caller uses the int64 intervals outside tests.
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.adt.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace adt

open Iris Iris.BI go_etcd_io.etcd.pkg.v3.adt

/-- The three-way comparison of two int64s in the signed order: `-1`, `0` or `1`. -/
def int64Cmp (v w : w64) : Int :=
  if sint.Z v < sint.Z w then -1 else if sint.Z w < sint.Z v then 1 else 0

/-- The end of `NewInt64Point(a)`: `a + 1`, except at `MaxInt64`, which has no successor, where
it is `a` (the empty interval `[a, a)`). -/
def int64PointEnd (a : w64) : w64 :=
  if sint.Z a = 2 ^ 63 - 1 then a else a + 1

/-- The point interval keeps `Begin ≤ End` in the signed order (what the old `a + 1`, wrapping
to `MinInt64` at `MaxInt64`, broke), and is `[a, a + 1)` exactly, as integers, below
`MaxInt64`. -/
theorem int64PointEnd_spec (a : w64) :
    sint.Z a ≤ sint.Z (int64PointEnd a) ∧
    (sint.Z a < 2 ^ 63 - 1 → sint.Z (int64PointEnd a) = sint.Z a + 1) ∧
    (sint.Z a = 2 ^ 63 - 1 → int64PointEnd a = a) := by
  unfold int64PointEnd
  by_cases h : sint.Z a = 2 ^ 63 - 1
  · rw [ite_eq_left h]
    exact ⟨Int.le_refl _, fun h' => by omega, fun _ => rfl⟩
  · rw [ite_eq_right h]
    have : sint.Z a < 2 ^ 63 - 1 := by word
    exact ⟨by word, fun _ => by word, fun h' => absurd h' h⟩

/-- `int64Cmp` is a three-way comparison of the signed order. -/
theorem int64Cmp_spec (v w : w64) :
    (int64Cmp v w = -1 ↔ sint.Z v < sint.Z w) ∧
    (int64Cmp v w = 0 ↔ v = w) ∧
    (int64Cmp v w = 1 ↔ sint.Z w < sint.Z v) := by
  unfold int64Cmp
  by_cases h1 : sint.Z v < sint.Z w
  · rw [ite_eq_left h1]
    have hne : v ≠ w := fun h => by subst h; omega
    exact ⟨⟨fun _ => h1, fun _ => rfl⟩, ⟨fun h => by omega, fun h => absurd h hne⟩,
      ⟨fun h => by omega, fun h => by omega⟩⟩
  rw [ite_eq_right h1]
  by_cases h2 : sint.Z w < sint.Z v
  · rw [ite_eq_left h2]
    have hne : v ≠ w := fun h => by subst h; omega
    exact ⟨⟨fun h => by omega, fun h => by omega⟩, ⟨fun h => by omega, fun h => absurd h hne⟩,
      ⟨fun _ => h2, fun _ => rfl⟩⟩
  · rw [ite_eq_right h2]
    have : v = w := by word
    exact ⟨⟨fun h => by omega, fun h => by omega⟩, ⟨fun _ => this, fun _ => rfl⟩,
      ⟨fun h => by omega, fun h => by omega⟩⟩

/-- The old `Compare` (before etcd#22358): the sign of the wrapping difference `v - w`. -/
def int64CmpOld (v w : w64) : Int :=
  if sint.Z (v - w) < 0 then -1 else if 0 < sint.Z (v - w) then 1 else 0

/-- The old `Compare` is not the signed order: `MaxInt64` compares below `MinInt64` and below
`-1` (etcd#22357). -/
theorem int64CmpOld_wrong :
    int64CmpOld (W64 (2 ^ 63 - 1)) (W64 (-2 ^ 63)) = -1 ∧
    int64Cmp (W64 (2 ^ 63 - 1)) (W64 (-2 ^ 63)) = 1 ∧
    int64CmpOld (W64 (2 ^ 63 - 1)) (W64 (-1)) = -1 ∧
    int64Cmp (W64 (2 ^ 63 - 1)) (W64 (-1)) = 1 := by
  unfold int64CmpOld int64Cmp; decide

/-- The old `NewInt64Point(MaxInt64)`'s end, `MaxInt64 + 1`, wraps to `MinInt64`: `End < Begin`. -/
theorem int64PointOld_wrong :
    sint.Z (W64 (2 ^ 63 - 1) + 1) < sint.Z (W64 (2 ^ 63 - 1)) := by decide

theorem int64Cmp_lt_zero (v w : w64) : int64Cmp v w < 0 ↔ sint.Z v < sint.Z w := by
  unfold int64Cmp
  by_cases h1 : sint.Z v < sint.Z w
  · rw [ite_eq_left h1]; constructor <;> intro <;> omega
  · rw [ite_eq_right h1]
    by_cases h2 : sint.Z w < sint.Z v
    · rw [ite_eq_left h2]; constructor <;> intro <;> omega
    · rw [ite_eq_right h2]; constructor <;> intro <;> omega

theorem int64Cmp_le_zero (v w : w64) : int64Cmp v w ≤ 0 ↔ sint.Z v ≤ sint.Z w := by
  unfold int64Cmp
  by_cases h1 : sint.Z v < sint.Z w
  · rw [ite_eq_left h1]; constructor <;> intro <;> omega
  · rw [ite_eq_right h1]
    by_cases h2 : sint.Z w < sint.Z v
    · rw [ite_eq_left h2]; constructor <;> intro <;> omega
    · rw [ite_eq_right h2]; constructor <;> intro <;> omega

theorem int64Cmp_ge_zero (v w : w64) : int64Cmp v w ≥ 0 ↔ sint.Z w ≤ sint.Z v := by
  unfold int64Cmp
  by_cases h1 : sint.Z v < sint.Z w
  · rw [ite_eq_left h1]; constructor <;> intro <;> omega
  · rw [ite_eq_right h1]
    by_cases h2 : sint.Z w < sint.Z v
    · rw [ite_eq_left h2]; constructor <;> intro <;> omega
    · rw [ite_eq_right h2]; constructor <;> intro <;> omega

/-- `ivl.Compare(c)` (`Interval.Compare`) of the interval `x` against `y` over
`Int64Comparable`s, as its Go body computes it (as `ivlCmp` of `Model.lean` is for string-affine
ones): `-1` if `x` is left of `y`, `1` if right, `0` if they overlap. The tree's queries call it
with the query as `x` (`intervalNode.visit`, `intervalTree.find`, `Intersects`). -/
def int64IvlCmp (x y : w64 × w64) : Int :=
  if int64Cmp x.1 y.1 < 0 ∧ int64Cmp x.2 y.1 ≤ 0 then -1
  else if int64Cmp x.1 y.2 ≥ 0 then 1 else 0

/-- The query `NewInt64Point(MaxInt64)` (`[MaxInt64, MaxInt64)`) overlaps no interval `[b, e)`:
it is right of every one (no half-open int64 interval contains `MaxInt64`). -/
theorem int64IvlCmp_maxPoint (b e : w64) :
    int64IvlCmp (W64 (2 ^ 63 - 1), int64PointEnd (W64 (2 ^ 63 - 1))) (b, e) = 1 := by
  have hM : int64PointEnd (W64 (2 ^ 63 - 1)) = W64 (2 ^ 63 - 1) :=
    (int64PointEnd_spec _).2.2 (by decide)
  rw [hM]
  have hMv : sint.Z (W64 (2 ^ 63 - 1)) = 2 ^ 63 - 1 := by decide
  have hb : sint.Z b ≤ 2 ^ 63 - 1 := by word
  have he : sint.Z e ≤ 2 ^ 63 - 1 := by word
  unfold int64IvlCmp
  simp only [int64Cmp_lt_zero, int64Cmp_le_zero, int64Cmp_ge_zero, hMv]
  split
  · omega
  · first | rfl | (split <;> omega)

/-- Below `MaxInt64`, the query `NewInt64Point(a)` overlaps exactly the intervals `[b, e)` with
`b ≤ a < e` (signed), is left of those with `a < b` and right of those with `e ≤ a`. -/
theorem int64IvlCmp_point (a b e : w64) (ha : sint.Z a < 2 ^ 63 - 1) :
    (int64IvlCmp (a, int64PointEnd a) (b, e) = 0 ↔ sint.Z b ≤ sint.Z a ∧ sint.Z a < sint.Z e) ∧
    (int64IvlCmp (a, int64PointEnd a) (b, e) = -1 ↔ sint.Z a < sint.Z b) ∧
    (int64IvlCmp (a, int64PointEnd a) (b, e) = 1 ↔ sint.Z b ≤ sint.Z a ∧ sint.Z e ≤ sint.Z a) := by
  have hE := (int64PointEnd_spec a).2.1 ha
  unfold int64IvlCmp
  simp only [int64Cmp_lt_zero, int64Cmp_le_zero, int64Cmp_ge_zero, hE]
  split
  · refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> intro <;> omega
  · split
    · refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> intro <;> omega
    · refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> intro <;> omega

section defs
variable [ext : FfiSyntax] [GoGlobalContext]

/-- The int64 interval value `[a, b)` as the Go `Interval` (its `Comparable`s are
`Int64Comparable`s). -/
def int64Ivl (a b : w64) : Interval :=
  { Begin' := interface.mkOk Int64Comparable.ty #a,
    End' := interface.mkOk Int64Comparable.ty #b }

end defs

end adt
end EtcdGrove
end Perennial
