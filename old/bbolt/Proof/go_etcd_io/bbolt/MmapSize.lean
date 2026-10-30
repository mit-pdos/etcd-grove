/-
`mmapSizeOf`'s bounds: it maps at least what it is asked to (`mmapSizeOf_ge`), and at most
`MaxMapSize` (`mmapSizeOf_le`).
-/
module

public import Spec.go_etcd_io.bbolt.DB__mmapSize

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

/-- `mmapSizeOf` maps at least what it is asked to, and something. -/
theorem mmapSizeOf_ge (size ps s : Int) (h0 : 0 ≤ size) (hps : 0 < ps)
    (h : mmapSizeOf size ps = some s) : size ≤ s ∧ 0 < s := by
  unfold mmapSizeOf at h
  split at h
  · rename_i i hi
    injection h with h; subst h
    have := List.find?_some hi
    simp only [decide_eq_true_eq] at this
    exact ⟨this, Int.pow_pos (by decide)⟩
  · rename_i hnone
    have h30 : ¬ size ≤ 2 ^ (15 + 15) := by
      have := List.find?_eq_none.1 hnone 15 (List.mem_range.2 (by decide))
      simpa using this
    split at h
    · cases h
    · rename_i hmax
      injection h with h; subst h
      try dsimp only
      generalize hs1 : (if size % 1073741824 > 0 then size + 1073741824 - size % 1073741824
        else size) = s1
      have hs1ge : size ≤ s1 := by rw [← hs1]; split <;> omega
      have hlt := Int.lt_ediv_add_one_mul_self s1 hps
      generalize (s1 / ps + 1) * ps = q at hlt ⊢
      constructor
      · rw [Int.le_min]; refine ⟨?_, by omega⟩; split <;> omega
      · rw [Int.lt_min]; refine ⟨?_, by decide⟩; split <;> omega

/-- `mmapSizeOf` maps at most `MaxMapSize`. -/
theorem mmapSizeOf_le (size ps s : Int) (h : mmapSizeOf size ps = some s) :
    s ≤ 281474976710655 := by
  unfold mmapSizeOf at h
  split at h
  · rename_i i hi
    injection h with h; subst h
    have hi16 : i < 16 := List.mem_range.1 (List.mem_of_find?_eq_some hi)
    have : (2 : Nat) ^ (15 + i) ≤ 2 ^ 30 := Nat.pow_le_pow_right (by decide) (by omega)
    have h2 : ((2 : Nat) ^ (15 + i) : Nat) = ((2 : Int) ^ (15 + i)) := by push_cast; rfl
    have : (2 : Nat) ^ 30 = 1073741824 := by decide
    omega
  · split at h
    · cases h
    · injection h with h; subst h
      exact Int.min_le_right _ _

end bbolt
end EtcdGrove
end Perennial
