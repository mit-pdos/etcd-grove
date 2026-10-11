/-
From a page's bytes to the structs bbolt reads them as: decoding little-endian bytes
(`leBytes_leInt`: encoding the decoded bytes gives them back), the page header of a page's
bytes (`pageOf`), and the typed view of a header inside a page's bytes (`page_header_bytes`).
-/
module

public import Proof.go_etcd_io.bbolt.PageModel
public import Proof.go_etcd_io.bbolt.internal.common.Bytes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.common

theorem leInt_cons (b : w8) (bs : List w8) : leInt (b :: bs) = (b.toNat : Int) + 256 * leInt bs := by
  simp [leInt]

theorem leInt_nonneg (bs : List w8) : 0 ≤ leInt bs := by
  induction bs with
  | nil => simp [leInt]
  | cons b bs ih => rw [leInt_cons]; omega

theorem leInt_lt (bs : List w8) : leInt bs < 2 ^ (8 * bs.length) := by
  induction bs with
  | nil => show (0 : Int) < 1; decide
  | cons b bs ih =>
    rw [leInt_cons, List.length_cons, show 8 * (bs.length + 1) = 8 + 8 * bs.length by omega,
      Int.pow_add]
    have hb := b.isLt
    rw [show (2 : Nat) ^ 8 = 256 by rfl] at hb
    have : (b.toNat : Int) < 256 := by omega
    generalize (2 : Int) ^ (8 * bs.length) = M at *
    have : (2 : Int) ^ 8 = 256 := by decide
    rw [this]
    omega

/-- Encoding decoded bytes gives them back. -/
theorem leBytes_leInt (bs : List w8) : leBytes bs.length (leInt bs) = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    rw [List.length_cons, leInt_cons]
    simp only [leBytes]
    have hb := b.isLt
    rw [show (2 : Nat) ^ 8 = 256 by rfl] at hb
    have hb' : (b.toNat : Int) < 256 := by omega
    have hn := leInt_nonneg bs
    congr 1
    · apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofInt]
      have : ((b.toNat : Int) + 256 * leInt bs) % (2 ^ 8 : Nat) = b.toNat := by
        rw [show ((2 ^ 8 : Nat) : Int) = 256 by decide]; omega
      rw [this]; omega
    · rw [show ((b.toNat : Int) + 256 * leInt bs) / 256 = leInt bs by omega]
      exact ih

theorem bytesAt_length (pg : List w8) (off n : Nat) (h : off + n ≤ pg.length) :
    (bytesAt pg off n).length = n := by
  simp [bytesAt]; omega

/-- The `n` bytes at `off`, encoded from their value (`leAt`). -/
theorem leBytes_leAt (pg : List w8) (off n : Nat) (h : off + n ≤ pg.length) :
    leBytes n ((leAt pg off n : Nat) : Int) = bytesAt pg off n := by
  unfold leAt
  rw [Int.toNat_of_nonneg (leInt_nonneg _)]
  have := leBytes_leInt (bytesAt pg off n)
  rw [bytesAt_length pg off n h] at this
  exact this

theorem leAt_lt (pg : List w8) (off n : Nat) : leAt pg off n < 2 ^ (8 * n) := by
  unfold leAt
  have h1 := leInt_lt ((pg.drop off).take n)
  have h2 := leInt_nonneg ((pg.drop off).take n)
  have hl : ((pg.drop off).take n).length ≤ n := by simp only [List.length_take]; omega
  have : (2 : Int) ^ (8 * ((pg.drop off).take n).length) ≤ 2 ^ (8 * n) := by
    exact_mod_cast Nat.pow_le_pow_right (by decide) (by omega)
  have : ((leInt ((pg.drop off).take n)).toNat : Int) < 2 ^ (8 * n) := by omega
  exact_mod_cast this

theorem bytesAt_append (pg : List w8) (off n m : Nat) :
    bytesAt pg off n ++ bytesAt pg (off + n) m = bytesAt pg off (n + m) := by
  unfold bytesAt
  rw [List.take_add, List.drop_drop]

section header
variable [ext : FfiSyntax]

/-- The page header of a page's bytes. -/
def pageOf (pg : List w8) : Page :=
  Page.mk (W64 (pageId pg)) (W16 (pageFlags pg)) (W16 (pageCount pg)) (W32 (pageOverflow pg))

theorem toNat_W64 (x : Nat) (h : x < 2 ^ 64) : (W64 (x : Int)).toNat = x := by
  simp; omega
theorem toNat_W32 (x : Nat) (h : x < 2 ^ 32) : (W32 (x : Int)).toNat = x := by
  simp; omega
theorem toNat_W16 (x : Nat) (h : x < 2 ^ 16) : (W16 (x : Int)).toNat = x := by
  simp; omega

/-- A page header's bytes are the first 16 of the page. -/
theorem pageBytes_pageOf (pg : List w8) (h : 16 ≤ pg.length) :
    pageBytes (pageOf pg) = pg.take 16 := by
  unfold pageBytes pageOf
  simp only
  unfold pageId pageFlags pageCount pageOverflow
  rw [toNat_W64 _ (leAt_lt pg 0 8), toNat_W16 _ (leAt_lt pg 8 2), toNat_W16 _ (leAt_lt pg 10 2),
    toNat_W32 _ (leAt_lt pg 12 4)]
  rw [leBytes_leAt pg 0 8 (by omega), leBytes_leAt pg 8 2 (by omega),
    leBytes_leAt pg 10 2 (by omega), leBytes_leAt pg 12 4 (by omega)]
  rw [List.append_assoc, List.append_assoc, bytesAt_append pg 10 2 4, bytesAt_append pg 8 2 6,
    bytesAt_append pg 0 8 8]
  simp [bytesAt]

end header

section view
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

include package_sem in
/-- A page's bytes are its header (as a `Page`) and the rest. -/
theorem page_header_bytes (l : Loc) (q : DFrac) (pg : List w8) (h : 16 ≤ pg.length)
    (hc : l.locCar ≠ 0) :
    bytesPointsto (GF := GF) l q pg ⊣⊢ l ↦{q} pageOf pg ∗ bytesPointsto (l +ₗ 16) q (pg.drop 16) := by
  have Hpg : pg = pg.take 16 ++ pg.drop 16 := (List.take_append_drop 16 pg).symm
  refine (BIBase.BiEntails.of_eq (congrArg (bytesPointsto l q) Hpg)).trans ?_
  refine (bytesPointsto_app l q _ _).trans ?_
  rw [List.length_take, Nat.min_eq_left h, ← pageBytes_pageOf pg h]
  exact sep_congr (Page_bytes (hG := hG) l (pageOf pg) q hc).symm .rfl

end view

end bbolt
end EtcdGrove
end Perennial
