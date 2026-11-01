/-
Lean-first (no Rocq counterpart). Mapped cells and the file's bytes: with the `OsMeta` of a
file, the client's halves of a range of mapped cells hold the bytes the client holds a fraction
of (`cellsR_agree`, `osCell_agree` byte by byte). `cellsB base lo B` is the client's halves of
the cells `[lo, lo + B.length)`, holding `B`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.Store
public import GooseLang.Ext.OsFs.Truncate

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.mit_pdos.etcd_grove.examples.bboltfs

section cells
variable [GooseExts] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : NaHeapGS Loc val GF]

/-- The client halves of the cells `[lo, lo + B.length)` of the mapping at `base`, holding `B`. -/
def cellsB (base : Loc) (lo : Nat) (B : List w8) : IProp GF :=
  cellsR (GF := GF) base lo B.length (fun i => byteCell (B.getD (i - lo) 0))

theorem cellsR_cons (base : Loc) (lo n : Nat) (vf : Nat → val) :
    cellsR (GF := GF) base lo (n + 1) vf ⊣⊢
      heapPointsto (hG := hG) (base +ₗ ((lo : Nat) : Int)) (DFrac.own (1 : Qp).half) (vf lo) ∗
        cellsR base (lo + 1) n vf := by
  unfold cellsR
  rw [List.range'_succ]
  exact BigSepL.bigSepL_cons

theorem cellsB_cons (base : Loc) (lo : Nat) (b : w8) (B : List w8) :
    cellsB (GF := GF) base lo (b :: B) ⊣⊢
      heapPointsto (hG := hG) (base +ₗ ((lo : Nat) : Int)) (DFrac.own (1 : Qp).half) (byteCell b) ∗
        cellsB base (lo + 1) B := by
  unfold cellsB
  refine (cellsR_cons _ _ _ _).trans (sep_congr (by simp) ?_)
  apply cellsR_congr
  intro i h1 _
  rw [show i - lo = (i - (lo + 1)) + 1 by omega]
  simp

theorem cellsB_append (base : Loc) (lo : Nat) (B C : List w8) :
    cellsB (GF := GF) base lo (B ++ C) ⊣⊢ cellsB base lo B ∗ cellsB base (lo + B.length) C := by
  induction B generalizing lo with
  | nil =>
    simp only [List.nil_append, List.length_nil, Nat.add_zero]
    refine (emp_sep (PROP := IProp GF)).symm.trans (sep_congr ?_ .rfl)
    unfold cellsB cellsR; simp only [List.length_nil, List.range'_zero]
    exact BigSepL.bigSepL_nil.symm
  | cons b B ih =>
    simp only [List.cons_append, List.length_cons]
    refine (cellsB_cons _ _ _ _).trans ?_
    refine (sep_congr .rfl (ih (lo + 1))).trans ?_
    rw [show lo + 1 + B.length = lo + (B.length + 1) by omega]
    refine (sep_assoc ..).symm.trans (sep_congr (cellsB_cons _ _ _ _).symm .rfl)

/-- The client halves of the cells `[lo, lo + n)` of the mapping at `base`, holding anything. -/
def cellsAny (base : Loc) (lo n : Nat) : IProp GF := iprop(∃ vf, cellsR (GF := GF) base lo n vf)

theorem cellsAny_append (base : Loc) (lo n1 n2 : Nat) :
    cellsAny (GF := GF) base lo n1 ∗ cellsAny base (lo + n1) n2 ⊢ cellsAny base lo (n1 + n2) := by
  unfold cellsAny
  iintro ⟨⟨%vf1, H1⟩, ⟨%vf2, H2⟩⟩
  iexists (fun i => if i < lo + n1 then vf1 i else vf2 i)
  iapply (cellsR_append _ _ _ _ _).2
  isplitl [H1]
  · iapply (cellsR_congr _ _ _ _ _ (fun i _ h => by simp [h])).1 $$ H1
  · iapply (cellsR_congr _ _ _ _ _ (fun i h _ => by simp [show ¬ i < lo + n1 by omega])).1 $$ H2

theorem cellsAny_split (base : Loc) (lo n1 n2 : Nat) :
    cellsAny (GF := GF) base lo (n1 + n2) ⊢ cellsAny base lo n1 ∗ cellsAny base (lo + n1) n2 := by
  unfold cellsAny
  iintro ⟨%vf, H⟩
  icases (cellsR_append _ _ _ _ _).1 $$ H with ⟨H1, H2⟩
  isplitl [H1]
  · iexists vf; iexact H1
  · iexists vf; iexact H2

theorem cellsAny_zero (base : Loc) (lo : Nat) : ⊢ cellsAny (GF := GF) base lo 0 := by
  unfold cellsAny cellsR
  iexists (fun _ => #())
  simp only [List.range'_zero]
  iapply BigSepL.bigSepL_nil.2; iempintro

theorem cellsB_any (base : Loc) (lo : Nat) (B : List w8) :
    cellsB (GF := GF) base lo B ⊢ cellsAny base lo B.length := by
  unfold cellsB cellsAny
  iintro H
  iexists _; iexact H

/-- Cells page by page, as one range. -/
theorem pages_any (base : Loc) (P : Nat → IProp GF)
    (h : ∀ r, P r ⊢ cellsAny (GF := GF) base (4096 * r) 4096) :
    ∀ k s, ([∗list] r ∈ List.range' s k, P r) ⊢ cellsAny base (4096 * s) (4096 * k)
  | 0, s => by
    iintro _
    iapply cellsAny_zero
  | k + 1, s => by
    iintro H
    rw [List.range'_succ]
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨H1, H2⟩
    ihave H1 := h s $$ H1
    ihave H2 := pages_any base P h k (s + 1) $$ H2
    rw [show 4096 * (k + 1) = 4096 + 4096 * k by omega]
    iapply cellsAny_append
    rw [show 4096 * s + 4096 = 4096 * (s + 1) by omega]
    iframe


/-- A non-empty range of mapped cells from the mapping's start lies in `(0, maxAddr]`. -/
theorem cellsR_bounds (base : Loc) (n : Nat) (vf : Nat → val) (h : 0 < n) :
    cellsR (GF := GF) base 0 n vf ⊢ ⌜0 < base.addr ∧ base.addr + n ≤ maxAddr⌝ := by
  iintro H
  rw [show n = (n - 1) + 1 by omega]
  icases (cellsR_append _ _ _ _ _).1 $$ H with ⟨H1, H2⟩
  icases (cellsR_cons _ _ _ _).1 $$ H2 with ⟨Hl, -⟩
  icases heapPointsto_lt_maxAddr _ _ _ $$ Hl with %Hlt
  icases heapPointsto_pos _ _ _ $$ Hl with %Hp
  simp only [Loc.add] at Hlt Hp
  rcases Nat.eq_zero_or_pos (n - 1) with h0 | h0
  · ipureintro; rw [h0] at Hlt Hp ⊢; simp at Hlt Hp ⊢; omega
  · rw [show n - 1 = 1 + (n - 1 - 1) by omega]
    icases (cellsR_append _ _ _ _ _).1 $$ H1 with ⟨H0, -⟩
    icases (cellsR_cons _ _ _ _).1 $$ H0 with ⟨H0, -⟩
    icases heapPointsto_pos _ _ _ $$ H0 with %Hp0
    simp only [Loc.add] at Hp0
    ipureintro; omega

end cells

section agree
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt] [GoGlobalContext]
  [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

theorem osBytes_cons (p : GoString) (off : Nat) (dq : DFrac) (x : w8 × Bool) (xs : List (w8 × Bool)) :
    osBytes (L := L) p off dq (x :: xs) ⊣⊢ osByte (L := L) p off dq x ∗ osBytes (L := L) p (off + 1) dq xs := by
  unfold osBytes osByte; exact bytesG_cons _ _ _ _ _ _

theorem osBytes_nil (p : GoString) (off : Nat) (dq : DFrac) :
    osBytes (L := L) p off dq [] ⊣⊢ emp := by
  unfold osBytes; exact bytesG_nil _ _ _ _

/-- The client halves of mapped cells `[lo, lo + xs.length)` hold the bytes `xs` of the file, of
which the client holds a fraction, given its `OsMeta`. -/
theorem cellsR_agree (e : Expr) (htv : toVal e = none) (p : GoString) (dqm : DFrac) (m : OsMeta)
    (base : Loc) (len : Nat) (hb : m.maps !! base = some len) (dqb : DFrac) (hE : ↑osN ⊆ E)
    (Φ : val → IProp GF) :
    ∀ (xs : List (w8 × Bool)) (lo : Nat) (vf : Nat → val), lo + xs.length ≤ len →
    ⊢ osInv (L := L) -∗ osMeta (L := L) p dqm (some m) -∗ osBytes (L := L) p lo dqb xs -∗
      cellsR base lo xs.length vf -∗
      (osMeta (L := L) p dqm (some m) -∗ osBytes (L := L) p lo dqb xs -∗
        cellsB base lo (xs.map Prod.fst) -∗ WP e @ s; E {{ Φ }}) -∗
      WP e @ s; E {{ Φ }}
  | [], lo, vf, _ => by
    iintro #Hinv Hm _ _ HΦ
    iapply HΦ $$ Hm [] []
    · iapply (osBytes_nil _ _ _).2; iempintro
    · unfold cellsB cellsR; simp only [List.map_nil, List.length_nil, List.range'_zero]
      iapply BigSepL.bigSepL_nil.2; iempintro
  | x :: xs, lo, vf, hl => by
    simp only [List.length_cons] at hl
    iintro #Hinv Hm Hb Hc HΦ
    icases (osBytes_cons _ _ _ _ _).1 $$ Hb with ⟨Hx, Hb⟩
    simp only [List.length_cons]
    icases (cellsR_cons _ _ _ _).1 $$ Hc with ⟨Hcx, Hc⟩
    iapply osCell_agree (L := L) e htv p dqm m base len lo hb (by omega) dqb x _ (vf lo) hE Φ
      $$ Hinv Hm Hx Hcx
    iintro %Hv Hm Hx Hcx
    iapply cellsR_agree e htv p dqm m base len hb dqb hE Φ xs (lo + 1) vf (by omega)
      $$ Hinv Hm Hb Hc
    iintro Hm Hb Hc
    iapply HΦ $$ Hm [Hx Hb] [Hcx Hc]
    · iapply (osBytes_cons _ _ _ _ _).2; iframe
    · simp only [List.map_cons]
      iapply (cellsB_cons _ _ _ _).2
      rw [Hv]
      iframe

end agree

end github_com.mit_pdos.etcd_grove.examples.bboltfs

end Perennial
