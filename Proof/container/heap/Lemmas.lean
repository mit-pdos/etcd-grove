/-
Pure lemmas of the proofs of `container/heap`'s `up`, `down`, `Fix`, `Push` (2026-10-26).
Lean-first (no Rocq counterpart).
-/
module

public import Proof.container.heap.Defs
public import Perennial.Std.List

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace heap

/-- `Swap` permutes the contents. -/
theorem listSwap_perm {A : Type} (xs : List A) (i j : Nat) :
    (lease.listSwap xs i j).Perm xs := by
  unfold lease.listSwap
  split
  · rename_i a b ha hb
    exact Permutation_insert_swap xs i j a b ha hb
  · exact List.Perm.refl _

end heap
end EtcdGrove
end Perennial
