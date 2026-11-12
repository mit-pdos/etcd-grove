/-
The read path's (U6, `notes/bbolt-proof-plan.md`) pure facts about searches: what `sort.Search`'s
result is for a predicate false then true.
-/
module

public import Perennial.Golang.Defn.String

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace bbolt

namespace Read

/-- The length of the leading run of `f` over `[s, s + m)`, when `f` holds below `s + idx` and
fails at `s + idx`. -/
theorem takeWhile_range'_length (f : Nat → Bool) :
    ∀ (idx s m : Nat), idx ≤ m → (∀ k < idx, f (s + k) = true) →
      (idx < m → f (s + idx) = false) → ((List.range' s m).takeWhile f).length = idx
  | 0, s, 0, _, _, _ => rfl
  | 0, s, m + 1, _, _, hat => by
    have : f s = false := by simpa using hat (by omega)
    simp [List.range'_succ, this]
  | idx + 1, s, 0, h, _, _ => by omega
  | idx + 1, s, m + 1, h, hb, hat => by
    have h0 : f s = true := by simpa using hb 0 (by omega)
    rw [List.range'_succ, List.takeWhile_cons, if_pos h0, List.length_cons,
      takeWhile_range'_length f idx (s + 1) m (by omega)
        (fun k hk => by have := hb (k + 1) (by omega); rwa [show s + (k + 1) = s + 1 + k by omega] at this)
        (fun hk => by have := hat (by omega); rwa [show s + (idx + 1) = s + 1 + idx by omega] at this)]

/-- The length of the leading run of `f` over `[0, n)`. -/
theorem takeWhile_range_length (f : Nat → Bool) (idx n : Nat) (hle : idx ≤ n)
    (hb : ∀ k < idx, f k = true) (hat : idx < n → f idx = false) :
    ((List.range n).takeWhile f).length = idx := by
  rw [List.range_eq_range']
  exact takeWhile_range'_length f idx 0 n hle (by simpa using hb) (by simpa using hat)

end Read

end bbolt
end EtcdGrove
end Perennial
