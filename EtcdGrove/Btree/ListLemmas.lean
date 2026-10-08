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

end Btree
end EtcdGrove
end Perennial
