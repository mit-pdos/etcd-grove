/-
Lemmas on running sums of entry sizes, shared by the proofs of `limitSize` and `entsSize`
(2026-11-13: moved out of `limitSize.lean`, where a proof file exposed them: `etc/gen-interface.py
--layout`).
-/
module

public import Proof.go_etcd_io.raft.v3.PbContent

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open go_etcd_io.raft.v3

/-- The sizes of a prefix one entry longer. -/
theorem entrySize_sum_take_succ [GooseExts] (cs : List EntryC) (i : Nat) (c : EntryC)
    (h : cs[i]? = some c) :
    ((cs.take (i + 1)).map entrySize).sum = ((cs.take i).map entrySize).sum + entrySize c := by
  rw [List.take_add_one, h]
  simp

/-- A `uint64` sum that does not wrap, of a running sum and a non-negative `int` size. -/
theorem w64_add_exact (acc ni : w64) (a e : Nat) (Ha : uint.nat acc = a) (Hni : sint.Z ni = e)
    (he : e < 2 ^ 63) (h : a + e < 2 ^ 64) : uint.nat (acc + ni) = a + e := by
  word

end EtcdGrove
end Perennial
