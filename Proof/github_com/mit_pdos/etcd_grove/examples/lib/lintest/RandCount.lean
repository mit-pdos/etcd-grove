/- Lean-first (no Rocq counterpart).

# lintest: the examples' random counts and indices

Each example's `Main` (`examples/lib/lintest/<ex>/<ex>.go`) runs `1 + int(primitive.RandomUint64()
% MaxClients)` clients of `1 + int(primitive.RandomUint64() % MaxOps)` operations each: whatever
the random numbers, a count between 1 and its cap, so `Run`'s bounds hold (`0 ≤ clients < 2^31`,
`0 ≤ ops`, `clients * ops < 2^60`) when the caps' product is below `2^60`. Their generators pick a value as `vals[RandomUint64() %
n]` of a slice `vals` of length `n`, an index in bounds.
-/
module

public import Perennial.Std.Word.Automation

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace lintest

/-- `1 + int(r % n)` is between 1 and `n`, for a cap `0 < n < 2^62`. -/
theorem randCount_bounds (r : w64) (n : Nat) (h0 : 0 < n) (h1 : n < 2 ^ 62) :
    1 ≤ sint.Z (W64 1 + r % W64 n) ∧ sint.Z (W64 1 + r % W64 n) ≤ n := by
  have hn : (W64 n).toNat = n := by word
  have hm : (r % W64 n).toNat < n := by
    rw [BitVec.toNat_umod, hn]; exact Nat.mod_lt _ h0
  constructor <;> word

/-- `r % n` indexes a slice of length `n`, for `0 < n < 2^62` (the index `sint.Z` of the
`uint64` remainder, as Goose converts it). -/
theorem randIndex_bounds (r : w64) (n : Nat) (h0 : 0 < n) (h1 : n < 2 ^ 62) :
    0 ≤ sint.Z (r % W64 n) ∧ sint.Z (r % W64 n) < sint.Z (W64 n) := by
  have hn : (W64 n).toNat = n := by word
  have hm : (r % W64 n).toNat < n := by
    rw [BitVec.toNat_umod, hn]; exact Nat.mod_lt _ h0
  constructor <;> word

/-- `Run`'s bounds on two counts drawn below the caps `c` and `o`. -/
theorem randCounts_runBounds (r1 r2 : w64) (c o : Nat) (hc : 0 < c) (ho : 0 < o)
    (hc' : c < 2 ^ 31) (ho' : o < 2 ^ 31) (hco : c * o < 2 ^ 60) :
    0 ≤ sint.Z (W64 1 + r1 % W64 c) ∧ sint.Z (W64 1 + r1 % W64 c) < 2 ^ 31 ∧
    0 ≤ sint.Z (W64 1 + r2 % W64 o) ∧
    sint.Z (W64 1 + r1 % W64 c) * sint.Z (W64 1 + r2 % W64 o) < 2 ^ 60 := by
  have h1 := randCount_bounds r1 c hc (by omega)
  have h2 := randCount_bounds r2 o ho (by omega)
  refine ⟨by omega, by omega, by omega, ?_⟩
  have : sint.Z (W64 1 + r1 % W64 c) * sint.Z (W64 1 + r2 % W64 o) ≤ (c : Int) * o :=
    Int.mul_le_mul h1.2 h2.2 (by omega) (by omega)
  have : ((c * o : Nat) : Int) < 2 ^ 60 := by exact_mod_cast hco
  push_cast at this
  omega

end lintest
end EtcdGrove
end Perennial
