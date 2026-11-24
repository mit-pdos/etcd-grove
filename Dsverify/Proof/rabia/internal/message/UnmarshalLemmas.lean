/-
Pure lemmas the `Unmarshal` proofs share (`ConsensusObj__Unmarshal.lean`, `Command__Unmarshal.lean`):
out of `ConsensusObj__Unmarshal.lean`, a proof file, so that a sibling proof needs no import of it
(CLAUDE.md, "Import tiers").
-/
module

public import Dsverify.Proof.rabia.internal.message.Internal

@[expose] public section

namespace Perennial.rabia.internal.message

theorem w32_ofNat_toNat' (x : w32) : BitVec.ofNat 32 x.toNat = x := by simp

theorem subslice_of_drop' {A : Type} (a : Nat) (l X Y : List A) (h : l.drop a = X ++ Y) :
    subslice a (a + X.length) l = X := by
  rw [subslice_comm, h, Nat.add_sub_cancel_left, List.take_left]

end Perennial.rabia.internal.message
