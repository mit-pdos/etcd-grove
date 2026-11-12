/-
Lean-first (no Rocq counterpart).

# Porcupine's bitset, in pure terms (2026-10-14)

A `bitset` (`bitset.go`) is a `[]uint64`: bit `i` is bit `i % 64` of word `i / 64`. Its specs
(`Spec/github_com/anishathalye/porcupine/bitset__*.lean`, `newBitset.lean`) are about the list
of words `ws`; this file has what the words mean (`bsBit`), what `set` and `clear` do to them
(`bsSet`, `bsClear`, in the form the Go semantics computes), and the lemmas relating them.
-/
module

public import Proof.github_com.anishathalye.porcupine.Defs

@[expose] public section

namespace Perennial
namespace github_com.anishathalye.porcupine

/-- The number of words of a bitset of `n` bits (`newBitset`). -/
def bsChunks (n : Nat) : Nat := n / 64 + if n % 64 = 0 then 0 else 1

/-- Bit `i` of a bitset's words (`false` past its end). -/
def bsBit (ws : List w64) (i : Nat) : Bool := (ws.getD (i / 64) 0).getLsbD (i % 64)

/-- `b.set(pos)`'s words. -/
def bsSet (ws : List w64) (pos : w64) : List w64 :=
  ws.set (uint.nat pos / 64) (ws.getD (uint.nat pos / 64) 0 ||| W64 1 <<< (pos % W64 64))

/-- `b.clear(pos)`'s words. -/
def bsClear (ws : List w64) (pos : w64) : List w64 :=
  ws.set (uint.nat pos / 64) (ws.getD (uint.nat pos / 64) 0 &&& ~~~(W64 1 <<< (pos % W64 64)))

theorem getLsbD_or_bit (w : w64) (pos : w64) (j : Nat) (hj : j < 64) :
    (w ||| W64 1 <<< (pos % W64 64)).getLsbD j = (w.getLsbD j || decide (j = uint.nat pos % 64)) := by
  have hk : (pos % W64 64).toNat = uint.nat pos % 64 := by
    simp only [uint.nat]; word
  rw [BitVec.getLsbD_or, BitVec.shiftLeft_eq', hk]
  simp only [BitVec.getLsbD_shiftLeft, show W64 1 = 1#64 from rfl, BitVec.getLsbD_one]
  by_cases h : j = uint.nat pos % 64 <;> simp [h, hj] <;> omega

theorem getLsbD_andnot_bit (w : w64) (pos : w64) (j : Nat) (hj : j < 64) :
    (w &&& ~~~(W64 1 <<< (pos % W64 64))).getLsbD j =
      (w.getLsbD j && !decide (j = uint.nat pos % 64)) := by
  have hk : (pos % W64 64).toNat = uint.nat pos % 64 := by
    simp only [uint.nat]; word
  rw [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.shiftLeft_eq', hk]
  simp only [BitVec.getLsbD_shiftLeft, show W64 1 = 1#64 from rfl, BitVec.getLsbD_one]
  by_cases h : j = uint.nat pos % 64 <;> simp [h, hj] <;> omega

theorem bsBit_set (ws : List w64) (pos : w64) (i : Nat) (h : uint.nat pos / 64 < ws.length) :
    bsBit (bsSet ws pos) i = (bsBit ws i || decide (i = uint.nat pos)) := by
  unfold bsBit bsSet
  by_cases hq : i / 64 = uint.nat pos / 64
  · simp only [List.getD_eq_getElem?_getD, hq, List.getElem?_set_self h, Option.getD_some]
    rw [getLsbD_or_bit _ _ _ (Nat.mod_lt _ (by decide))]
    congr 1
    simp only [decide_eq_decide]; omega
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hq)]
    have : i ≠ uint.nat pos := fun h' => hq (h' ▸ rfl)
    simp [this]

theorem bsBit_clear (ws : List w64) (pos : w64) (i : Nat) (h : uint.nat pos / 64 < ws.length) :
    bsBit (bsClear ws pos) i = (bsBit ws i && !decide (i = uint.nat pos)) := by
  unfold bsBit bsClear
  by_cases hq : i / 64 = uint.nat pos / 64
  · simp only [List.getD_eq_getElem?_getD, hq, List.getElem?_set_self h, Option.getD_some]
    rw [getLsbD_andnot_bit _ _ _ (Nat.mod_lt _ (by decide))]
    congr 2
    simp only [decide_eq_decide]; omega
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hq)]
    have : i ≠ uint.nat pos := fun h' => hq (h' ▸ rfl)
    simp [this]

theorem bsBit_replicate (k i : Nat) : bsBit (List.replicate k (W64 0)) i = false := by
  unfold bsBit
  simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> simp

@[simp] theorem bsSet_length (ws : List w64) (pos : w64) : (bsSet ws pos).length = ws.length := by
  simp [bsSet]

@[simp] theorem bsClear_length (ws : List w64) (pos : w64) :
    (bsClear ws pos).length = ws.length := by
  simp [bsClear]

/-- A bit below `n` is in a word of a bitset of `n` bits. -/
theorem bsChunks_gt (n i : Nat) (h : i < n) : i / 64 < bsChunks n := by
  unfold bsChunks; split <;> omega

end github_com.anishathalye.porcupine
end Perennial
