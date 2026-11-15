/-
A freelist page's bytes split into what `Read` reads (U2, `notes/bbolt-proof-plan.md`): the
header (`p ↦{dq} pageHdr pg`), the overflow count cell (`(p +ₗ 16) ↦{dq} c` when the header's
count is `0xFFFF`, the form U1's `Page.FreelistPageIds` takes), and the ids' bytes, which are the
encodings of `flIds pg` (`Model/Mvcc.lean`) and a `[]Pgid` there (`ownSlice_of_bytes`).
-/
module

public import Proof.go_etcd_io.bbolt.Model.Mvcc
public import Proof.go_etcd_io.bbolt.internal.common.Lemmas.Layout
public import Proof.go_etcd_io.bbolt.internal.common.Lemmas.Bytes
public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.SliceLen

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt


open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.common

/-! ## Pure -/

section pure
variable [GooseExts]

theorem bytesAt_add (B : List w8) (off a b : Nat) :
    bytesAt B off (a + b) = bytesAt B off a ++ bytesAt B (off + a) b := by
  unfold bytesAt
  rw [List.take_add]
  simp [List.drop_drop]

/-- `n` words decoded at `off` re-encode to the `8 n` bytes there. -/
theorem words_flatMap (B : List w8) (off n : Nat) (h : off + 8 * n ≤ B.length) :
    ((List.range n).map fun i => (decode (bytesAt B (off + 8 * i) 8) : w64)).flatMap encode =
      bytesAt B off (8 * n) := by
  induction n with
  | zero => simp [bytesAt]
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.flatMap_append, ih (by omega),
      show 8 * (n + 1) = 8 * n + 8 by omega, bytesAt_add]
    simp only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [ByteEncoding.encode_decode]
    unfold bytesAt; simp; omega

theorem flIds_length (pg : List w8) : (flIds pg).length = (flCountIdx pg).1 := by
  simp [flIds]

theorem flIds_bytes (pg : List w8)
    (h : 16 + 8 * (flCountIdx pg).2 + 8 * (flCountIdx pg).1 ≤ pg.length) :
    (flIds pg).flatMap encode = bytesAt pg (16 + 8 * (flCountIdx pg).2) (8 * (flCountIdx pg).1) :=
  words_flatMap pg _ _ h

theorem flCountIdx_snd_le (pg : List w8) : (flCountIdx pg).2 ≤ 1 := by
  unfold flCountIdx; split <;> simp

/-- The overflow form of the count: `pageCount pg < 0xFFFF` is the header's count not being
`0xFFFF`. -/
theorem count_ne_iff (pg : List w8) :
    (pageHdr pg).count' = W16 65535 ↔ ¬ pageCount pg < 0xFFFF := by
  unfold pageCount
  constructor
  · intro h; rw [h]; decide
  · intro h; apply BitVec.eq_of_toNat_eq
    have := (pageHdr pg).count'.isLt; simp at h ⊢; omega

theorem flCountIdx_eq (pg : List w8) :
    flCountIdx pg = (if (pageHdr pg).count' = W16 65535 then
      ((decode (bytesAt pg 16 8) : w64).toNat, 1) else (pageCount pg, 0)) := by
  unfold flCountIdx
  by_cases h : (pageHdr pg).count' = W16 65535
  · rw [if_neg ((count_ne_iff pg).1 h), if_pos h]
  · have : pageCount pg < 0xFFFF := Decidable.of_not_not (fun h' => h ((count_ne_iff pg).2 h'))
    rw [if_pos this, if_neg h]

end pure

/-! ## The split -/

section
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [go_etcd_io.bbolt.internal.common.Assumptions]

theorem bytesPointsto_split3 (l : Loc) (dq : DFrac) (B : List w8) (a b : Nat)
    (h : a + b ≤ B.length) :
    bytesPointsto (GF := GF) l dq B ⊣⊢
      bytesPointsto l dq (B.take a) ∗ bytesPointsto (l +ₗ (a : Int)) dq (bytesAt B a b) ∗
        bytesPointsto (l +ₗ ((a + b : Nat) : Int)) dq (B.drop (a + b)) := by
  have e : B = B.take a ++ (bytesAt B a b ++ B.drop (a + b)) := by
    unfold bytesAt
    rw [← List.drop_drop, List.take_append_drop, List.take_append_drop]
  have ha : (B.take a).length = a := by simp; omega
  have hb : (bytesAt B a b).length = b := by unfold bytesAt; simp; omega
  have hl : (l +ₗ (a : Int)) +ₗ (b : Int) = l +ₗ ((a + b : Nat) : Int) := by
    simp [Loc.add, Int.add_assoc]
  constructor
  · iintro H
    ihave H := bytesPointsto_congr _ _ _ _ e $$ H
    icases (bytesPointsto_app l dq _ _).1 $$ H with ⟨H1, H2⟩
    icases (bytesPointsto_app _ dq _ _).1 $$ H2 with ⟨H2, H3⟩
    rw [ha, hb, hl]
    iframe
  · iintro ⟨H1, H2, H3⟩
    iapply bytesPointsto_congr _ _ _ _ e.symm
    iapply (bytesPointsto_app l dq _ _).2
    iframe H1
    rw [ha]
    iapply (bytesPointsto_app _ dq _ _).2
    iframe H2
    rw [hb, hl]
    iexact H3


/-- The bytes of the elements of `vs`, from a positive address, are a slice of the plain `e` with
those elements (Perennial's `unsafememory` example's `ownSlice_of_bytes`). -/
theorem ownSlice_of_bytes' {V : Type} {n : Nat} [ZeroVal V] [ByteEncoding V n]
    [TypedPointsto (GF := GF) V] [BytesView (GF := GF) V] (e : go.GoType) [TypeRepr e V] {a : Nat}
    (hlay : go.PlainLayout e n a) (s : GoSlice) (vs : List V) (dq : DFrac) (hl : 0 < s.ptr.addr)
    (hlen : sint.Z s.len = vs.length) (hcap : sint.Z s.len ≤ sint.Z s.cap) :
    bytesPointsto (GF := GF) s.ptr dq (vs.flatMap encode) ⊢ s ↦*{dq} vs := by
  rw [ownSlice_unseal]; unfold ownSliceDef
  iintro Hb
  iright
  isplitl [Hb]
  · iapply (typedPointsto_array_bytes e hlay s.ptr (sint.Z s.len) (array.mk _ vs) dq hl).2
    iframe Hb
    ipureintro; exact hlen.symm
  · ipureintro; exact hcap

/-- A slice of plain `e` at a positive address is the bytes of its elements. -/
theorem ownSlice_to_bytes' {V : Type} {n : Nat} [ZeroVal V] [ByteEncoding V n]
    [TypedPointsto (GF := GF) V] [BytesView (GF := GF) V] (e : go.GoType) [TypeRepr e V] {a : Nat}
    (hlay : go.PlainLayout e n a) (s : GoSlice) (vs : List V) (dq : DFrac) (hl : 0 < s.ptr.addr) :
    (s ↦*{dq} vs : IProp GF) ⊢ bytesPointsto s.ptr dq (vs.flatMap encode) := by
  iintro Hs
  icases ownSlice_bytes_acc e hlay s vs dq hl $$ Hs with ⟨Hb, _⟩
  iexact Hb

/-- The count cell of a freelist page: the first id slot, when the header's count is `0xFFFF`. -/
def flCountCell (p : Loc) (pg : List w8) (dq : DFrac) : IProp GF :=
  if (pageHdr pg).count' = W16 65535 then
    typedPointsto (p +ₗ 16) (decode (bytesAt pg 16 8) : w64) dq
  else iprop(True)

/-- **A freelist page's bytes, opened**: its header, its count cell, and the bytes of its ids
after them, with the way back. -/
theorem flPage_open (p : Loc) (pg : List w8) (dq : DFrac) (hp : 0 < p.addr)
    (hsz : 16 + 8 * (flCountIdx pg).2 + 8 * (flCountIdx pg).1 ≤ pg.length) :
    bytesPointsto (GF := GF) p dq pg ⊢
      typedPointsto p (pageHdr pg) dq ∗ flCountCell p pg dq ∗
      bytesPointsto (p +ₗ ((16 + 8 * (flCountIdx pg).2 : Nat) : Int)) dq
        ((flIds pg).flatMap encode) ∗
      (typedPointsto p (pageHdr pg) dq ∗ flCountCell p pg dq ∗
        bytesPointsto (p +ₗ ((16 + 8 * (flCountIdx pg).2 : Nat) : Int)) dq
          ((flIds pg).flatMap encode) -∗ bytesPointsto p dq pg) := by
  have hk := flCountIdx_snd_le pg
  generalize hK : (flCountIdx pg).2 = k at hsz hk ⊢
  generalize hN : (flCountIdx pg).1 = n at hsz
  have hids : (flIds pg).flatMap encode = bytesAt pg (16 + 8 * k) (8 * n) := by
    rw [flIds_bytes pg (by rw [hK, hN]; exact hsz), hK, hN]
  rw [hids]
  have hhdr : pg.take 16 = encode (pageHdr pg) := by
    unfold pageHdr bytesAt
    rw [List.drop_zero, ByteEncoding.encode_decode]; simp; omega
  -- the count cell's bytes
  have hcc : ∀ (P : IProp GF), (bytesPointsto (p +ₗ (16 : Nat)) dq (bytesAt pg 16 (8 * k)) ⊣⊢
      flCountCell p pg dq) := by
    intro _
    unfold flCountCell
    by_cases hc : (pageHdr pg).count' = W16 65535
    · have : k = 1 := by rw [← hK, flCountIdx_eq, if_pos hc]
      subst this
      rw [if_pos hc, show 8 * 1 = 8 from rfl,
        show bytesAt pg 16 8 = encode (decode (bytesAt pg 16 8) : w64) by
          rw [ByteEncoding.encode_decode]; unfold bytesAt; simp; omega]
      rw [ByteEncoding.decode_encode]
      exact (typedPointsto_bytes _ _ dq (by simp [Loc.add]; omega)).symm
    · have : k = 0 := by rw [← hK, flCountIdx_eq, if_neg hc]
      subst this
      rw [if_neg hc]
      simp only [Nat.mul_zero]
      unfold bytesAt
      simp only [List.take_zero]
      unfold bytesPointsto
      constructor <;> iintro _ <;> itrivial
  iintro H
  icases (bytesPointsto_split3 p dq pg 16 (8 * k + 8 * n) (by omega)).1 $$ H with ⟨H1, H2, H3⟩
  ihave H2 := bytesPointsto_congr _ _ _ _ (bytesAt_add pg 16 (8 * k) (8 * n)) $$ H2
  icases (bytesPointsto_app _ dq _ _).1 $$ H2 with ⟨H2, H4⟩
  ihave H1 := bytesPointsto_congr _ _ _ _ hhdr $$ H1
  icases (typedPointsto_bytes p (pageHdr pg) dq hp).2 $$ H1 with H1
  icases (hcc iprop(True)).1 $$ H2 with H2
  have hlen : ((bytesAt pg 16 (8 * k)).length : Int) = 8 * k := by
    unfold bytesAt; simp; omega
  have hloc : (p +ₗ ((16 : Nat) : Int)) +ₗ ((bytesAt pg 16 (8 * k)).length : Int) =
      p +ₗ ((16 + 8 * k : Nat) : Int) := by
    rw [hlen]; simp [Loc.add, Int.add_assoc]
  rw [hloc]
  iframe H1 H2 H4
  iintro ⟨H1, H2, H4⟩
  iapply (bytesPointsto_split3 p dq pg 16 (8 * k + 8 * n) (by omega)).2
  isplitl [H1]
  · iapply bytesPointsto_congr _ _ _ _ hhdr.symm
    iapply (typedPointsto_bytes p (pageHdr pg) dq hp).1 $$ H1
  iframe H3
  iapply bytesPointsto_congr _ _ _ _ (bytesAt_add pg 16 (8 * k) (8 * n)).symm
  iapply (bytesPointsto_app _ dq _ _).2
  isplitl [H2]
  · iapply (hcc iprop(True)).2 $$ H2
  rw [hloc]
  iexact H4

end

end bbolt
end EtcdGrove
end Perennial
