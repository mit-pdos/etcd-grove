/-
Lean-first (no Rocq counterpart).

# The oracle's decoder (`decoder`, `oracle.go`; W4c U5)

`decRep d bs k`: the decoder at `d` reads the bytes `bs` (read-only), at offset `k`, with `ok` set,
the encoding at most 1 GiB (`tOrSmall`'s bound, so that no offset wraps). The pure facts its
methods' proofs need: the byte-by-byte decoding of `tU64` (`u64Acc`, `U64Acc.lean`), and offsets
through `List.drop`.
-/
module

public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.Rep
public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.CandsLemmas
public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.U64Acc

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.etcd.wal

section pure
variable [GooseExts]

/-- The `i`-th byte of `tU64 x`. -/
theorem tU64_getElem? (x : w64) (i : Nat) (hi : i < 8) :
    (tU64 x)[i]? = some (W8 (uint.Z (x >>> W64 (8 * (i : Int))))) := by
  simp [tU64, hi]

/-- Reading past a prefix. -/
theorem drop_app {bs a r : List w8} {k : Nat} (h : bs.drop k = a ++ r) (hk : k ≤ bs.length) :
    bs.drop (k + a.length) = r ∧ k + a.length ≤ bs.length := by
  constructor
  · rw [← List.drop_drop, h, List.drop_left]
  · have := congrArg List.length h
    simp at this; omega

/-- Reading past a prefix (the offset need not be in bounds). -/
theorem drop_app' {bs a r : List w8} {k : Nat} (h : bs.drop k = a ++ r) :
    bs.drop (k + a.length) = r := by
  rw [← List.drop_drop, h, List.drop_left]

/-- The offset reached, from the bytes left. -/
theorem drop_eq_len {bs a r : List w8} {k k' : Nat} (h1 : bs.drop k = a ++ r) (h2 : bs.drop k' = r)
    (hk0 : k ≤ bs.length) (hk : k' ≤ bs.length) : k' = k + a.length := by
  have e1 := congrArg List.length h1
  have e2 := congrArg List.length h2
  simp at e1 e2; omega

theorem flatMap_length_ge {α : Type} (l : List α) (f : α → List w8) (n : Nat)
    (hf : ∀ x, n ≤ (f x).length) : n * l.length ≤ (l.flatMap f).length := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons, Nat.mul_succ]
    have := hf x; omega

theorem tOpBytes_length_ge (o : TOp) : 8 ≤ (tOpBytes o).length := by
  simp [tOpBytes, tU64_length]

theorem tEntBytes_length_ge (e : TEnt) : 8 ≤ (tEntBytes e).length := by
  simp [tEntBytes, tU64_length]

end pure

section rep
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.wal.Assumptions]

/-- **The decoder at `d` reads `bs` at offset `k`**, `ok` set. -/
def decRep (d : Loc) (bs : List w8) (k : Nat) : IProp GF :=
  iprop(∃ sl : GoSlice, d ↦ (decoder.mk sl (W64 k) true) ∗ sl ↦*□ bs ∗
    ⌜k ≤ bs.length ∧ bs.length ≤ 0x40000000⌝)

/-- The offset's bounds. -/
theorem decRep_len (d : Loc) (bs : List w8) (k : Nat) :
    decRep (GF := GF) d bs k ⊢ decRep d bs k ∗ ⌜k ≤ bs.length ∧ bs.length ≤ 0x40000000⌝ := by
  unfold decRep
  iintro ⟨%sl, Hd, #Hsl, %Hb⟩
  isplitl
  · iexists sl
    iframe
    isplitl []
    · iexact Hsl
    ipureintro; exact Hb
  ipureintro; exact Hb

/-- The decoder's points-to, to read its fields, and back. -/
theorem decRep_acc (d : Loc) (bs : List w8) (k : Nat) :
    decRep (GF := GF) d bs k ⊢
      ∃ sl, d ↦ (decoder.mk sl (W64 k) true) ∗ (d ↦ (decoder.mk sl (W64 k) true) -∗ decRep d bs k) := by
  unfold decRep
  iintro ⟨%sl, Hd, #Hsl, %Hb⟩
  iexists sl
  iframe
  iintro Hd
  iexists sl
  iframe
  isplitl []
  · iexact Hsl
  ipureintro; exact Hb

theorem candsElems_nil : ⊢ candsElems (GF := GF) [] [] := by
  unfold candsElems
  iintro
  isplitr
  · ipureintro; rfl
  imodintro
  iintro %i %v %o %h
  simp at h

end rep

end etcd_wal
end EtcdGrove
end Perennial
