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

/-- The bytes of a leaf element: `flags`, `pos`, `ksize`, `vsize` (4 each). -/
def leafElemBytes (e : leafPageElement) : List w8 :=
  leBytes 4 e.flags'.toNat ++ leBytes 4 e.pos'.toNat ++ leBytes 4 e.ksize'.toNat ++
    leBytes 4 e.vsize'.toNat

/-- The bytes of a branch element: `pos`, `ksize` (4 each), `pgid` (8). -/
def branchElemBytes (e : branchPageElement) : List w8 :=
  leBytes 4 e.pos'.toNat ++ leBytes 4 e.ksize'.toNat ++ leBytes 8 e.pgid'.toNat

/-- Leaf element `i` of a page's bytes. -/
def leafElemOf (pg : List w8) (i : Nat) : leafPageElement :=
  leafPageElement.mk (W32 (leafFlags pg i)) (W32 (leafPos pg i)) (W32 (leafKsize pg i))
    (W32 (leafVsize pg i))

/-- Branch element `i` of a page's bytes. -/
def branchElemOf (pg : List w8) (i : Nat) : branchPageElement :=
  branchPageElement.mk (W32 (branchPos pg i)) (W32 (branchKsize pg i)) (W64 (branchPgid pg i))

theorem leafElemBytes_of (pg : List w8) (i : Nat) (h : elemOff i + 16 ≤ pg.length) :
    leafElemBytes (leafElemOf pg i) = bytesAt pg (elemOff i) 16 := by
  unfold leafElemBytes leafElemOf
  simp only
  unfold leafFlags leafPos leafKsize leafVsize
  rw [toNat_W32 _ (leAt_lt _ _ 4), toNat_W32 _ (leAt_lt _ _ 4), toNat_W32 _ (leAt_lt _ _ 4),
    toNat_W32 _ (leAt_lt _ _ 4)]
  rw [leBytes_leAt pg _ 4 (by omega), leBytes_leAt pg _ 4 (by omega),
    leBytes_leAt pg _ 4 (by omega), leBytes_leAt pg _ 4 (by omega)]
  rw [List.append_assoc, List.append_assoc, bytesAt_append pg (elemOff i + 8) 4 4,
    bytesAt_append pg (elemOff i + 4) 4 8, bytesAt_append pg (elemOff i) 4 12]

theorem branchElemBytes_of (pg : List w8) (i : Nat) (h : elemOff i + 16 ≤ pg.length) :
    branchElemBytes (branchElemOf pg i) = bytesAt pg (elemOff i) 16 := by
  unfold branchElemBytes branchElemOf
  simp only
  unfold branchPos branchKsize branchPgid
  rw [toNat_W32 _ (leAt_lt _ _ 4), toNat_W32 _ (leAt_lt _ _ 4), toNat_W64 _ (leAt_lt _ _ 8)]
  rw [leBytes_leAt pg _ 4 (by omega), leBytes_leAt pg _ 4 (by omega),
    leBytes_leAt pg _ 8 (by omega)]
  rw [List.append_assoc, bytesAt_append pg (elemOff i + 4) 4 8, bytesAt_append pg (elemOff i) 4 12]

/-- The meta of 64 bytes (any 64 bytes are one: its fields are integers). -/
def metaOf (l : List w8) : Meta :=
  Meta.mk (W32 (leAt l 0 4)) (W32 (leAt l 4 4)) (W32 (leAt l 8 4)) (W32 (leAt l 12 4))
    (InBucket.mk (W64 (leAt l 16 8)) (W64 (leAt l 24 8))) (W64 (leAt l 32 8)) (W64 (leAt l 40 8))
    (W64 (leAt l 48 8)) (W64 (leAt l 56 8))

/-- A meta's bytes are the first 64 of the bytes it is read from. -/
theorem metaBytes_metaOf (l : List w8) (h : 64 ≤ l.length) : metaBytes (metaOf l) = l.take 64 := by
  unfold metaBytes inBucketBytes metaOf
  simp only
  rw [toNat_W32 _ (leAt_lt l 0 4), toNat_W32 _ (leAt_lt l 4 4), toNat_W32 _ (leAt_lt l 8 4),
    toNat_W32 _ (leAt_lt l 12 4), toNat_W64 _ (leAt_lt l 16 8), toNat_W64 _ (leAt_lt l 24 8),
    toNat_W64 _ (leAt_lt l 32 8), toNat_W64 _ (leAt_lt l 40 8), toNat_W64 _ (leAt_lt l 48 8),
    toNat_W64 _ (leAt_lt l 56 8)]
  rw [leBytes_leAt l 0 4 (by omega), leBytes_leAt l 4 4 (by omega), leBytes_leAt l 8 4 (by omega),
    leBytes_leAt l 12 4 (by omega), leBytes_leAt l 16 8 (by omega), leBytes_leAt l 24 8 (by omega),
    leBytes_leAt l 32 8 (by omega), leBytes_leAt l 40 8 (by omega), leBytes_leAt l 48 8 (by omega),
    leBytes_leAt l 56 8 (by omega)]
  simp only [List.append_assoc]
  rw [bytesAt_append l 48 8 8, bytesAt_append l 40 8 16, bytesAt_append l 32 8 24,
    bytesAt_append l 24 8 32, bytesAt_append l 16 8 40, bytesAt_append l 12 4 48,
    bytesAt_append l 8 4 52, bytesAt_append l 4 4 56, bytesAt_append l 0 4 60]
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

include package_sem in
theorem leafElem_fields (l : Loc) (h : l.locCar ≠ 0) :
    structFieldRef leafPageElement go!"flags" l = l ∧
    structFieldRef leafPageElement go!"pos" l = l +ₗ 4 ∧
    structFieldRef leafPageElement go!"ksize" l = l +ₗ 8 ∧
    structFieldRef leafPageElement go!"vsize" l = l +ₗ 12 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have H0 : structFieldRef leafPageElement go!"flags" l = l +ₗ 0 := by solve_field_ref
    simpa using H0
  all_goals solve_field_ref

include package_sem in
theorem branchElem_fields (l : Loc) (h : l.locCar ≠ 0) :
    structFieldRef branchPageElement go!"pos" l = l ∧
    structFieldRef branchPageElement go!"ksize" l = l +ₗ 4 ∧
    structFieldRef branchPageElement go!"pgid" l = l +ₗ 8 := by
  refine ⟨?_, ?_, ?_⟩
  · have H0 : structFieldRef branchPageElement go!"pos" l = l +ₗ 0 := by solve_field_ref
    simpa using H0
  all_goals solve_field_ref

theorem leafElemBytes_split (l : Loc) (dq : DFrac) (e : leafPageElement) :
    bytesPointsto (GF := GF) l dq (leafElemBytes e) ⊣⊢
      bytesPointsto l dq (leBytes 4 e.flags'.toNat) ∗
      bytesPointsto (l +ₗ 4) dq (leBytes 4 e.pos'.toNat) ∗
      bytesPointsto (l +ₗ 8) dq (leBytes 4 e.ksize'.toNat) ∗
      bytesPointsto (l +ₗ 12) dq (leBytes 4 e.vsize'.toNat) := by
  unfold leafElemBytes
  rw [List.append_assoc, List.append_assoc]
  refine ((bytesPointsto_app _ _ _ _).trans (sep_congr .rfl ((bytesPointsto_app _ _ _ _).trans
    (sep_congr .rfl (bytesPointsto_app _ _ _ _))))).trans ?_
  simp only [leBytes_length, loc_add_assoc]
  exact .rfl

theorem branchElemBytes_split (l : Loc) (dq : DFrac) (e : branchPageElement) :
    bytesPointsto (GF := GF) l dq (branchElemBytes e) ⊣⊢
      bytesPointsto l dq (leBytes 4 e.pos'.toNat) ∗
      bytesPointsto (l +ₗ 4) dq (leBytes 4 e.ksize'.toNat) ∗
      bytesPointsto (l +ₗ 8) dq (leBytes 8 e.pgid'.toNat) := by
  unfold branchElemBytes
  rw [List.append_assoc]
  refine ((bytesPointsto_app _ _ _ _).trans (sep_congr .rfl (bytesPointsto_app _ _ _ _))).trans ?_
  simp only [leBytes_length, loc_add_assoc]
  exact .rfl

include package_sem in
/-- A leaf element is its bytes. -/
theorem leafElem_bytes (l : Loc) (e : leafPageElement) (dq : DFrac) (h : l.locCar ≠ 0) :
    l ↦{dq} e ⊣⊢ bytesPointsto (GF := GF) l dq (leafElemBytes e) := by
  obtain ⟨H1, H2, H3, H4⟩ := leafElem_fields (hG := hG) l h
  rw [typedPointsto_unseal_eq]
  simp only [TypedPointsto.typedPointstoDef]
  rw [H1, H2, H3, H4]
  refine Iris.BI.BiEntails.trans ?_ (leafElemBytes_split l dq e).symm
  constructor
  · iintro ⟨⟨H1, H2, H3, H4, -⟩, -⟩
    isplitl [H1]; · iapply (typedPointsto_w32_bytes _ _ _).1 $$ H1
    isplitl [H2]; · iapply (typedPointsto_w32_bytes _ _ _).1 $$ H2
    isplitl [H3]; · iapply (typedPointsto_w32_bytes _ _ _).1 $$ H3
    iapply (typedPointsto_w32_bytes _ _ _).1 $$ H4
  · iintro ⟨H1, H2, H3, H4⟩
    isplitl [H1 H2 H3 H4]
    · isplitl [H1]; · iapply (typedPointsto_w32_bytes _ _ _).2 $$ H1
      isplitl [H2]; · iapply (typedPointsto_w32_bytes _ _ _).2 $$ H2
      isplitl [H3]; · iapply (typedPointsto_w32_bytes _ _ _).2 $$ H3
      isplitl [H4]; · iapply (typedPointsto_w32_bytes _ _ _).2 $$ H4
      itrivial
    · ipureintro; exact loc_ne_null_of_car l h

include package_sem in
/-- A branch element is its bytes. -/
theorem branchElem_bytes (l : Loc) (e : branchPageElement) (dq : DFrac) (h : l.locCar ≠ 0) :
    l ↦{dq} e ⊣⊢ bytesPointsto (GF := GF) l dq (branchElemBytes e) := by
  obtain ⟨H1, H2, H3⟩ := branchElem_fields (hG := hG) l h
  rw [typedPointsto_unseal_eq]
  simp only [TypedPointsto.typedPointstoDef]
  rw [H1, H2, H3]
  refine Iris.BI.BiEntails.trans ?_ (branchElemBytes_split l dq e).symm
  constructor
  · iintro ⟨⟨H1, H2, H3, -⟩, -⟩
    isplitl [H1]; · iapply (typedPointsto_w32_bytes _ _ _).1 $$ H1
    isplitl [H2]; · iapply (typedPointsto_w32_bytes _ _ _).1 $$ H2
    iapply (typedPointsto_w64_bytes _ _ _).1 $$ H3
  · iintro ⟨H1, H2, H3⟩
    isplitl [H1 H2 H3]
    · isplitl [H1]; · iapply (typedPointsto_w32_bytes _ _ _).2 $$ H1
      isplitl [H2]; · iapply (typedPointsto_w32_bytes _ _ _).2 $$ H2
      isplitl [H3]; · iapply (typedPointsto_w64_bytes _ _ _).2 $$ H3
      itrivial
    · ipureintro; exact loc_ne_null_of_car l h

/-- A page's bytes around `n` of them at `off`. -/
theorem bytesPointsto_around (l : Loc) (q : DFrac) (pg : List w8) (off n : Nat)
    (h : off + n ≤ pg.length) :
    bytesPointsto (GF := GF) l q pg ⊣⊢ bytesPointsto l q (pg.take off) ∗
      bytesPointsto (l +ₗ (off : Int)) q (bytesAt pg off n) ∗
      bytesPointsto (l +ₗ ((off + n : Nat) : Int)) q (pg.drop (off + n)) := by
  have Hpg : pg = pg.take off ++ (bytesAt pg off n ++ pg.drop (off + n)) := by
    unfold bytesAt
    rw [← List.drop_drop, List.take_append_drop, List.take_append_drop]
  refine (BIBase.BiEntails.of_eq (congrArg (bytesPointsto l q) Hpg)).trans ?_
  refine (bytesPointsto_app _ _ _ _).trans (sep_congr ?_ ?_)
  · exact .rfl
  · rw [List.length_take, Nat.min_eq_left (by omega)]
    refine (bytesPointsto_app _ _ _ _).trans (sep_congr .rfl ?_)
    rw [bytesAt_length pg off n h, loc_add_assoc,
      show ((off + n : Nat) : Int) = (off : Int) + (n : Int) by omega]
    exact .rfl

include package_sem in
/-- Leaf element `i` inside a page's bytes. -/
theorem leafElem_in_page (l : Loc) (q : DFrac) (pg : List w8) (i : Nat)
    (h : elemOff i + 16 ≤ pg.length) (hc : l.locCar ≠ 0) :
    bytesPointsto (GF := GF) l q pg ⊣⊢ bytesPointsto l q (pg.take (elemOff i)) ∗
      (l +ₗ (elemOff i : Int)) ↦{q} leafElemOf pg i ∗
      bytesPointsto (l +ₗ ((elemOff i + 16 : Nat) : Int)) q (pg.drop (elemOff i + 16)) := by
  refine (bytesPointsto_around l q pg (elemOff i) 16 h).trans (sep_congr .rfl (sep_congr ?_ .rfl))
  rw [← leafElemBytes_of pg i h]
  exact (leafElem_bytes (hG := hG) _ _ q (by simpa [Loc.add] using hc)).symm

include package_sem in
/-- Branch element `i` inside a page's bytes. -/
theorem branchElem_in_page (l : Loc) (q : DFrac) (pg : List w8) (i : Nat)
    (h : elemOff i + 16 ≤ pg.length) (hc : l.locCar ≠ 0) :
    bytesPointsto (GF := GF) l q pg ⊣⊢ bytesPointsto l q (pg.take (elemOff i)) ∗
      (l +ₗ (elemOff i : Int)) ↦{q} branchElemOf pg i ∗
      bytesPointsto (l +ₗ ((elemOff i + 16 : Nat) : Int)) q (pg.drop (elemOff i + 16)) := by
  refine (bytesPointsto_around l q pg (elemOff i) 16 h).trans (sep_congr .rfl (sep_congr ?_ .rfl))
  rw [← branchElemBytes_of pg i h]
  exact (branchElem_bytes (hG := hG) _ _ q (by simpa [Loc.add] using hc)).symm

/-- The `n` bytes at `off` of the page at `l`, as a slice (a key or a value). -/
def sliceAt (l : Loc) (off n : Nat) : GoSlice :=
  slice.mk (l +ₗ (off : Int)) (W64 (n : Int)) (W64 (n : Int))

/-- `n` bytes inside a page's bytes, taken out as a byte slice (and given back). -/
theorem bytes_slice_acc (l : Loc) (q : DFrac) (pg : List w8) (off n : Nat)
    (h : off + n ≤ pg.length) (hn : n < 2 ^ 32) (hc : l.locCar ≠ 0) :
    bytesPointsto (GF := GF) l q pg ⊢ sliceAt l off n ↦*{q} bytesAt pg off n ∗
      (sliceAt l off n ↦*{q} bytesAt pg off n -∗ bytesPointsto l q pg) := by
  iintro H
  icases (bytesPointsto_around l q pg off n h).1 $$ H with ⟨Hpre, Hmid, Hpost⟩
  have Hlen := bytesAt_length pg off n h
  have Hcar : (l +ₗ (off : Int)).locCar ≠ 0 := by simpa [Loc.add] using hc
  by_cases hz : n = 0
  · subst hz
    have Hnil : bytesAt pg off 0 = [] := by simp [bytesAt]
    rw [Hnil]
    isplitl []
    · iapply ownSlice_empty (V := w8) q _ (by unfold sliceAt; simp) (by unfold sliceAt; simp)
      iapply array_empty
      exact loc_ne_null_of_car _ Hcar
    · iintro -
      iapply (bytesPointsto_around l q pg off 0 h).2
      iframe

  · have Hne : bytesAt pg off n ≠ [] := by
      intro e; rw [e] at Hlen; simp at Hlen; omega
    isplitl [Hmid]
    · iapply (ownSlice_bytes (sliceAt l off n) _ q Hne).2
      unfold sliceAt; simp only
      iframe
      ipureintro; constructor <;> word
    · iintro Hs
      icases (ownSlice_bytes (sliceAt l off n) _ q Hne).1 $$ Hs with ⟨Hmid, -⟩
      iapply (bytesPointsto_around l q pg off n h).2
      iframe

end view

end bbolt
end EtcdGrove
end Perennial
