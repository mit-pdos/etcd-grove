/-
`enc`'s vocabulary (`examples/etcd/dist/enc`): the encodings (`encU64`, `encBool`, `encStr`: a
`uint64`/`int64`/`int` as its 8 little-endian bytes, a bool as one byte, a string as its length then
its bytes) and the two objects, an encoder holding the bytes appended so far (`ownEnc e bs`, with its
slice's capacity) and a decoder holding the bytes left and its flag (`ownDec d bs ok`). A decoder's
read either succeeds, with the bytes the value's encoding followed by the rest (only when every read
so far did, `ok`), or leaves the flag false; `Done` says the flag is true and nothing is left. So a
decoding whose `Done` returns true read the encodings of the values it returned, in order, and
nothing else: what the codecs' specs say (`notes/etcd-dist-p9.md`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Base
public import Perennial.Std.Word.LittleEndian

@[expose] public section

noncomputable section

namespace Perennial
namespace github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc

open Iris Iris.BI

/-! ## The encodings -/

/-- A `uint64` (an `int64`, an `int`: their two's complement): 8 bytes, little-endian. -/
def encU64 (x : w64) : List w8 := u64Le x

/-- A bool: one byte, 0 or 1. -/
def encBool (b : Bool) : List w8 := [if b then W8 1 else W8 0]

/-- A string: its length, then its bytes. -/
def encStr (s : GoString) : List w8 := encU64 (W64 s.length) ++ s

theorem encU64_length (x : w64) : (encU64 x).length = 8 := by
  simp [encU64, u64Le_length]

/-- An encoding is read back from its bytes, whatever follows. -/
theorem encU64_append_inj {x y : w64} {r r' : List w8} (h : encU64 x ++ r = encU64 y ++ r') :
    x = y ∧ r = r' := by
  have hl : (encU64 x).length = (encU64 y).length := by rw [encU64_length, encU64_length]
  obtain ⟨h1, h2⟩ := List.append_inj h hl
  exact ⟨u64Le_inj h1, h2⟩

theorem encBool_append_inj {x y : Bool} {r r' : List w8} (h : encBool x ++ r = encBool y ++ r') :
    x = y ∧ r = r' := by
  cases x <;> cases y <;> simp_all [encBool] <;> exact absurd h (by decide)

theorem encStr_append_inj {s t : GoString} {r r' : List w8} (h : encStr s ++ r = encStr t ++ r')
    (hs : s.length < 2 ^ 64) (ht : t.length < 2 ^ 64) : s = t ∧ r = r' := by
  simp only [encStr, List.append_assoc] at h
  obtain ⟨hn, h⟩ := encU64_append_inj h
  have hl : s.length = t.length := by
    have := congrArg (fun w : w64 => w.toNat) hn
    simp only [W64, BitVec.toNat_ofInt] at this
    omega
  exact List.append_inj h hl

/-! ## The objects -/

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Assumptions]

/-- The encoder at `e` holds the bytes `bs`. -/
def ownEnc (e : Loc) (bs : List w8) : IProp GF :=
  iprop(∃ s : GoSlice, e ↦ ({ B' := s } : Enc) ∗ s ↦* bs ∗ ownSliceCap w8 s (DFrac.own 1))

/-- The decoder at `d` has the bytes `bs` left and the flag `ok`. -/
def ownDec (d : Loc) (bs : List w8) (ok : Bool) : IProp GF :=
  iprop(∃ (s : GoSlice) (dq : DFrac), d ↦ ({ B' := s, Ok' := ok } : Dec) ∗ s ↦*{dq} bs)

/-- What a read of a value `x` encoded as `en x` leaves, from the bytes `bs` and the flag `ok`:
the rest of the bytes, every read so far and this one having succeeded, or a false flag. -/
def decPost (d : Loc) (bs : List w8) (ok : Bool) {A : Type} (en : A → List w8) (x : A) :
    IProp GF :=
  iprop((∃ r, ⌜ok = true ∧ bs = en x ++ r⌝ ∗ ownDec d r true) ∨ ∃ r, ownDec d r false)

end defs

end github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc
end Perennial
