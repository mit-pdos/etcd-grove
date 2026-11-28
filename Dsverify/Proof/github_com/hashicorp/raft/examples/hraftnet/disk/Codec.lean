/-
(hraft_robust R3) The disk's file encoding (`codec.go`), as pure functions: unsigned integers as 8 bytes,
little-endian (`encU64`); byte strings length-prefixed (`encBytes`).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.disk.Base

@[expose] public section

noncomputable section

namespace Perennial

namespace github_com.hashicorp.raft.examples.hraftnet.disk

/-- `putUint64`'s bytes: `x`'s eight bytes, least significant first. -/
def encU64 (x : w64) : List w8 := (List.range 8).map (fun i : Nat => W8 (uint.Z (x >>> W64 (8 * (i : Int)))))

theorem encU64_length (x : w64) : (encU64 x).length = 8 := by simp [encU64]

theorem encU64_take_succ (x : w64) (i : Nat) (hi : i < 8) :
    (encU64 x).take (i + 1) = (encU64 x).take i ++ [W8 (uint.Z (x >>> W64 (8 * (i : Int))))] := by
  unfold encU64
  rw [List.take_add_one, List.getElem?_map, List.getElem?_range hi]
  rfl

/-- `putBytes`'s bytes: the length, then the bytes. -/
def encBytes (s : List w8) : List w8 := encU64 (W64 s.length) ++ s

/-! ### The decoder's accumulator (as `etcd/wal`'s `U64Acc.lean`, the same loop: copied, since nothing outside
`WalTester/` may import it) -/

/-- `x`'s low `i` bytes. -/
def u64Acc (x : w64) (i : Nat) : w64 := x &&& ((1 <<< (8 * i)) - 1)

theorem u64Acc_mask : ∀ i, i ≤ 8 → ((1 <<< (8 * i)) - 1 : w64) = BitVec.ofNat 64 (2 ^ (8 * i) - 1) := by
  decide +kernel

theorem getLsbD_u64Acc (x : w64) (i j : Nat) (hi : i ≤ 8) :
    (u64Acc x i).getLsbD j = (x.getLsbD j && decide (j < 8 * i)) := by
  unfold u64Acc
  rw [u64Acc_mask i hi, BitVec.getLsbD_and, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one]
  by_cases h : j < 64
  · simp [h]
  · simp [BitVec.getLsbD_of_ge x j (by omega)]

theorem u64Acc_zero (x : w64) : u64Acc x 0 = W64 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  rw [getLsbD_u64Acc _ _ _ (by omega)]; simp [W64]

theorem u64Acc_eight (x : w64) : u64Acc x 8 = x := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  rw [getLsbD_u64Acc _ _ _ (by omega)]; simp; omega

theorem W64_uint_Z_w8 (b : w8) : W64 (uint.Z b) = b.setWidth 64 := by
  apply BitVec.eq_of_toNat_eq; simp [W64, uint.Z]

theorem W8_uint_Z (v : w64) : W8 (uint.Z v) = v.setWidth 8 := by
  apply BitVec.eq_of_toNat_eq; simp [W8, uint.Z]

theorem u64Acc_step (x : w64) (i : Nat) (hi : i < 8) :
    u64Acc x i ||| ((W8 (uint.Z (x >>> W64 (8 * (i : Int))))).setWidth 64 <<< (W64 8 * W64 i)) =
      u64Acc x (i + 1) := by
  have h1 : (W64 (8 * (i : Int))).toNat = 8 * i := by
    simp [W64]; omega
  have h2 : (W64 8 * W64 i).toNat = 8 * i := by
    simp [W64]; omega
  rw [W8_uint_Z, BitVec.ushiftRight_eq', BitVec.shiftLeft_eq', h1, h2]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, getLsbD_u64Acc _ _ _ (by omega : i ≤ 8),
    getLsbD_u64Acc _ _ _ (by omega : i + 1 ≤ 8)]
  by_cases a : j < 8 * i
  · simp [a, hj, show j < 8 * (i+1) by omega]
  · by_cases b : j < 8 * (i + 1)
    · have : 8 * i + (j - 8 * i) = j := by omega
      simp [a, b, hj, show j - 8 * i < 8 by omega, show j - 8 * i < 64 by omega, this]
    · have : ¬ j - 8 * i < 8 := by omega
      simp [a, b, hj, this]

theorem u64Acc_step' (x : w64) (i : Nat) (hi : i < 8) :
    u64Acc x i ||| (W64 (uint.Z (W8 (uint.Z (x >>> W64 (8 * (i : Int)))))) <<< (W64 8 * W64 i)) =
      u64Acc x (i + 1) := by
  rw [W64_uint_Z_w8]; exact u64Acc_step x i hi

theorem encU64_getElem? (x : w64) (i : Nat) (hi : i < 8) :
    (encU64 x)[i]? = some (W8 (uint.Z (x >>> W64 (8 * (i : Int))))) := by
  simp [encU64, hi]

/-! ### List lemmas of the encoders' and decoders' loops (codec round trip) -/

theorem dk_flatMap_take_succ {α β : Type} (l : List α) (f : α → List β) (i : Nat) (x : α)
    (h : l[i]? = some x) : (l.take (i + 1)).flatMap f = (l.take i).flatMap f ++ f x := by
  rw [List.take_add_one, h]; simp

theorem dk_flatMap_take_length {α β : Type} (l : List α) (f : α → List β) (i : Nat)
    (h : i = l.length) : (l.take i).flatMap f = l.flatMap f := by
  rw [h, List.take_length]

theorem dk_flatMap_drop {α β : Type} (l : List α) (f : α → List β) (i : Nat) (x : α)
    (h : l[i]? = some x) : (l.drop i).flatMap f = f x ++ (l.drop (i + 1)).flatMap f := by
  rw [List.drop_eq_getElem_cons (List.getElem?_eq_some_iff.1 h).1]
  rw [(List.getElem?_eq_some_iff.1 h).2]; simp

/-- A slice's length as a word. -/
theorem dk_w64_of_length {α : Type} (l : List α) (n : w64) (h : l.length = sint.nat n ∧ 0 ≤ sint.Z n) :
    n = W64 l.length := by
  rw [h.1]; word

/-- A loop index below a slice's length. -/
theorem dk_idx_lt (i n : w64) (k : Nat) (h : k = sint.nat n ∧ 0 ≤ sint.Z n) (hi : 0 ≤ sint.Z i)
    (hlt : sint.Z i < sint.Z n) : sint.nat i < k := by
  rw [h.1]; word

/-- A loop index at a slice's length. -/
theorem dk_idx_eq (i n : w64) (k : Nat) (h : k = sint.nat n ∧ 0 ≤ sint.Z n) (hi : sint.Z i ≤ sint.Z n)
    (hge : ¬ sint.Z i < sint.Z n) : sint.nat i = k := by
  rw [h.1]; word

theorem dk_idx_succ (i n : w64) (hi : 0 ≤ sint.Z i) (hlt : sint.Z i < sint.Z n) :
    sint.nat (i + W64 1) = sint.nat i + 1 ∧ 0 ≤ sint.Z (i + W64 1) ∧ sint.Z (i + W64 1) ≤ sint.Z n := by
  refine ⟨?_, ?_, ?_⟩ <;> word

theorem dk_toNat_sint (i : w64) : (sint.Z i).toNat = sint.nat i := rfl

section rep
open Iris Iris.BI Iris.ProofMode
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.disk.Assumptions]

/-- **The decoder `r` has the bytes `cs` still to read**, no read past the end yet (its input is read-only). -/
def readerSt (r : Loc) (cs : List w8) : IProp GF :=
  iprop(∃ sl : GoSlice, r ↦ reader.mk sl false ∗ sl ↦*□ cs)

/-- A suffix of a read-only slice (gryff's `ownSlice_suffix`, read-only). -/
theorem ownSlice_suffix_ro (k : w64) (s : GoSlice) (vs : List w8)
    (hk : 0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z s.len) :
    (s ↦*□ vs : IProp GF) ⊢ slice.slice s w8 k s.len ↦*□ vs.drop (sint.nat k) := by
  iintro #Hs
  ihave Hs' := (ownSlice_trivial_slice s DFrac.discard vs).1 $$ Hs
  icases (ownSlice_split k s DFrac.discard vs (W64 0) s.len ⟨by decide, hk.1, hk.2⟩).1 $$ Hs'
    with ⟨-, Hs'⟩
  have h0 : sint.nat k - sint.nat (W64 0) = sint.nat k := by
    rw [show sint.nat (W64 0) = 0 from rfl]; omega
  rw [h0]
  iexact Hs'

end rep

end github_com.hashicorp.raft.examples.hraftnet.disk

end Perennial
