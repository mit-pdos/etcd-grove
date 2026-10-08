/-
List facts for the proofs of `items`' methods (slice shifting).
-/
import Perennial.Std.List

namespace Perennial
namespace EtcdGrove
namespace Btree

/-- `insertAt`: after `append(s, zero)` and `copy(s[i+1:], s[i:])`, the slice is
`take (i + 1) (vs ++ [z]) ++ drop i vs`; storing at `i` gives the insertion. -/
theorem insertAt_list {A : Type} (vs : List A) (z x : A) (i : Nat) (hi : i ≤ vs.length) :
    ((vs ++ [z]).take (i + 1) ++ vs.drop i).set i x = vs.take i ++ x :: vs.drop i := by
  have h1 : (vs ++ [z]).take (i + 1) = vs.take i ++ [(vs ++ [z])[i]'(by simp; omega)] := by
    rw [List.take_add_one, List.getElem?_eq_getElem (by simp; omega)]
    simp only [Option.toList_some]
    rw [List.take_append_of_le_length hi]
  rw [h1, List.append_assoc, List.set_append_right _ _ (by simp; omega)]
  simp [List.length_take, Nat.min_eq_left hi]

/-- `insertAt`'s `copy(s[i+1:], s[i:])` on `vs ++ [z]` (of length `n + 1`). -/
theorem shiftRight_list {A : Type} (vs : List A) (z : A) (i : Nat) (hi : i ≤ vs.length) :
    (vs ++ [z]).take (i + 1) ++
        ((subslice i (vs.length + 1) (vs ++ [z])).take (vs.length + 1 - (i + 1)) ++
          (subslice (i + 1) (vs.length + 1) (vs ++ [z])).drop (vs.length + 1 - i)) ++
      (vs ++ [z]).drop (vs.length + 1) =
    (vs ++ [z]).take (i + 1) ++ vs.drop i := by
  have hL : (vs ++ [z]).length = vs.length + 1 := by simp
  have ht : (vs ++ [z]).take (vs.length + 1) = vs ++ [z] := List.take_of_length_le (by omega)
  have h1 : (vs ++ [z]).drop (vs.length + 1) = [] := List.drop_of_length_le (by omega)
  have h2 : ((vs ++ [z]).drop (i + 1)).drop (vs.length + 1 - i) = [] :=
    List.drop_of_length_le (by simp; omega)
  have h3 : ((vs ++ [z]).drop i).take (vs.length + 1 - (i + 1)) = vs.drop i := by
    rw [List.drop_append_of_le_length hi, List.take_append_of_le_length (by simp),
      List.take_of_length_le (by simp)]
  simp only [subslice, ht, h1, h2, h3, List.append_nil]

end Btree
end EtcdGrove
end Perennial
