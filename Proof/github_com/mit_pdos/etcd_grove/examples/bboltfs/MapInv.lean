/-
Lean-first (no Rocq counterpart). The mapping's invariant (`mapInv`, `DB.lean`): closing it with
the whole of its token (`mapInv_close`, a remap or `Close`), allocating it (`mapInv_alloc`), and
the cells of a whole mapping as the writer's and the invariant's (`mapCells_gather`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.mit_pdos.etcd_grove.examples.bboltfs

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]

theorem mapInv_close (γ : DBNames) (p : GoString) (base : Loc) (len : Nat) (γm : GName) :
    mapInv (GF := GF) γ p base len γm ∗ ghostVar γm 1 () ⊢ |={⊤}=> ▷ mapCells (GF := GF) γ p base len := by
  iintro ⟨#Hinv, Htok⟩
  unfold mapInv
  imod inv_acc (by simp) $$ Hinv with ⟨Hi, Hclose⟩
  icases Hi with (Hc | >Htok2)
  · imod Hclose $$ [Htok] with _
    · inext; iright; iexact Htok
    imodintro; iexact Hc
  · icombine Htok Htok2 gives % ⟨Hbad, _⟩
    exfalso
    simp only [Qp.le_iff, Qp.val_add, Qp.val_one] at Hbad
    grind

theorem mapInv_alloc (γ : DBNames) (p : GoString) (base : Loc) (len : Nat) :
    mapCells (GF := GF) γ p base len ⊢
      |={⊤}=> ∃ γm, ghostVar γm 1 () ∗ mapInv (GF := GF) γ p base len γm := by
  iintro Hc
  imod ghostVar_alloc () with ⟨%γm, Htok⟩
  imod inv_alloc mapN ⊤ iprop(mapCells (GF := GF) γ p base len ∨ ghostVar γm 1 ()) $$ [Hc] with #Hinv
  · inext; ileft; iexact Hc
  imodintro
  iexists γm
  iframe
  unfold mapInv
  iexact Hinv

/-- The invariant's pages `[s, s + k)`: their contents, and their cells as one range. -/
theorem pagesCells_split (p : GoString) (base : Loc) :
    ∀ k s, ([∗list] r ∈ List.range' s k, ∃ B, pageIs (GF := GF) p r B ∗ cellsB (GF := GF) base (4096 * r) B) ⊢
      ([∗list] r ∈ List.range' s k, ∃ B, pageIs (GF := GF) p r B) ∗
        cellsAny (GF := GF) base (4096 * s) (4096 * k)
  | 0, s => by
    iintro _
    isplitr
    · simp only [List.range'_zero]; iapply BigSepL.bigSepL_nil.2; iempintro
    · iapply cellsAny_zero
  | k + 1, s => by
    iintro H
    rw [List.range'_succ]
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨⟨%B, #HB, Hc⟩, H2⟩
    icases pagesCells_split p base k (s + 1) $$ H2 with ⟨H2, Hc2⟩
    isplitl [H2]
    · iapply BigSepL.bigSepL_cons.2
      iframe H2
      iexists B; iexact HB
    · iunfold pageIs at HB
      icases HB with ⟨%HBl, -⟩
      ihave Hc := cellsB_any _ _ _ $$ Hc
      rw [HBl, show 4096 * (k + 1) = 4096 + 4096 * k by omega]
      iapply cellsAny_append
      rw [show 4096 * s + 4096 = 4096 * (s + 1) by omega]
      iframe

/-- The cells of a whole mapping, from the writer's and the invariant's. -/
theorem mapCells_gather (base : Loc) (hwm len : Nat) (h2 : 2 ≤ hwm) (hl : 4096 * hwm ≤ len) (mc : List w8)
    (hmc : mc.length = 128) :
    writerCells (GF := GF) base hwm len ∗ cellsB (GF := GF) base 16 (mc.take 64) ∗
      cellsB (GF := GF) base 4112 (mc.drop 64) ∗ cellsAny (GF := GF) base 8192 (4096 * (hwm - 2)) ⊢
      cellsAny (GF := GF) base 0 len := by
  unfold writerCells
  iintro ⟨⟨H0, H80, H4096, H4176, Htop⟩, Hm0, Hm1, Hp⟩
  ihave Hm0 := cellsB_any _ _ _ $$ Hm0
  ihave Hm1 := cellsB_any _ _ _ $$ Hm1
  simp only [List.length_take, List.length_drop, hmc] at *
  rw [show min 64 128 = 64 by omega, show 128 - 64 = 64 by omega]
  rw [show len = 16 + (64 + (4016 + (16 + (64 + (4016 + (4096 * (hwm - 2) + (len - 4096 * hwm))))))) by omega]
  iapply cellsAny_append
  isplitl [H0]
  · unfold cellsAny; iexact H0
  iapply cellsAny_append; iframe Hm0
  iapply cellsAny_append
  isplitl [H80]
  · unfold cellsAny; iexact H80
  iapply cellsAny_append
  isplitl [H4096]
  · unfold cellsAny; iexact H4096
  iapply cellsAny_append
  iframe Hm1
  iapply cellsAny_append
  isplitl [H4176]
  · unfold cellsAny; iexact H4176
  iapply cellsAny_append
  iframe Hp
  rw [show 0 + 16 + 64 + 4016 + 16 + 64 + 4016 + 4096 * (hwm - 2) = 4096 * hwm by omega]
  rw [show 16 + (64 + (4016 + (16 + (64 + (4016 + (4096 * (hwm - 2) + (len - 4096 * hwm))))))) -
    4096 * hwm = len - 4096 * hwm by omega]
  unfold cellsAny; iexact Htop

/-- The cells of a whole mapping, as the writer's and the invariant's. -/
theorem mapCells_scatter (base : Loc) (hwm len : Nat) (h2 : 2 ≤ hwm) (hl : 4096 * hwm ≤ len)
    (vf : Nat → val) :
    cellsR (GF := GF) base 0 len vf ⊢
      writerCells (GF := GF) base hwm len ∗ cellsR (GF := GF) base 16 64 vf ∗
        cellsR (GF := GF) base 4112 64 vf ∗ cellsR (GF := GF) base 8192 (4096 * (hwm - 2)) vf := by
  unfold writerCells
  iintro H
  rw [show len = 16 + (64 + (4016 + (16 + (64 + (4016 + (4096 * (hwm - 2) + (len - 4096 * hwm))))))) by omega]
  icases (cellsR_append _ _ _ _ _).1 $$ H with ⟨H0, H⟩
  icases (cellsR_append _ _ _ _ _).1 $$ H with ⟨Hm0, H⟩
  icases (cellsR_append _ _ _ _ _).1 $$ H with ⟨H80, H⟩
  icases (cellsR_append _ _ _ _ _).1 $$ H with ⟨H4096, H⟩
  icases (cellsR_append _ _ _ _ _).1 $$ H with ⟨Hm1, H⟩
  icases (cellsR_append _ _ _ _ _).1 $$ H with ⟨H4176, H⟩
  icases (cellsR_append _ _ _ _ _).1 $$ H with ⟨Hp, Htop⟩
  simp only [Nat.zero_add] at *
  rw [show 16 + (64 + (4016 + (16 + (64 + (4016 + (4096 * (hwm - 2) + (len - 4096 * hwm))))))) -
    4096 * hwm = len - 4096 * hwm by omega]
  rw [show 16 + 64 + 4016 + 16 + 64 + 4016 + 4096 * (hwm - 2) = 4096 * hwm by omega]
  iframe Hm0 Hm1 Hp
  isplitl [H0]; · iexists vf; iexact H0
  isplitl [H80]; · iexists vf; iexact H80
  isplitl [H4096]; · iexists vf; iexact H4096
  isplitl [H4176]; · iexists vf; iexact H4176
  iexists vf; iexact Htop


/-- `db.dataref` in the state `st`. -/
def mapSlice : MapSt → GoSlice
  | some (base, len, _) => ⟨base, W64 len, W64 len⟩
  | none => slice.nil

/-- `db.meta0` in the state `st`. -/
def mapPtr0 : MapSt → Loc
  | some (base, _, _) => base +ₗ 16
  | none => null

/-- `db.meta1` in the state `st`. -/
def mapPtr1 : MapSt → Loc
  | some (base, _, _) => base +ₗ 4112
  | none => null

theorem pointsto_halves {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (l : Loc) (v : V) :
    typedPointsto (GF := GF) l v (DFrac.own 1) ⊣⊢
      typedPointsto l v (DFrac.own (1 : Qp).half) ∗ typedPointsto l v (DFrac.own (1 : Qp).half) := by
  conv => lhs; rw [← Qp.half_add_half 1]
  exact (typedPointsto_frac l v).fractional _ _

theorem mapFields_eq (db : Loc) (dq : DFrac) (st : MapSt) :
    mapFields (GF := GF) db dq st ⊣⊢
      db.[DB, go!"dataref"] ↦{dq} mapSlice st ∗ db.[DB, go!"meta0"] ↦{dq} mapPtr0 st ∗
        db.[DB, go!"meta1"] ↦{dq} mapPtr1 st := by
  rcases st with _ | ⟨base, len, γm⟩ <;> exact .rfl

/-- The two halves of the mapping fields, as the whole fields. -/
theorem mapFields_join (db : Loc) (st : MapSt) :
    mapFields (GF := GF) db (DFrac.own (1 : Qp).half) st ∗ mapFields db (DFrac.own (1 : Qp).half) st ⊣⊢
      db.[DB, go!"dataref"] ↦ mapSlice st ∗ db.[DB, go!"meta0"] ↦ mapPtr0 st ∗
        db.[DB, go!"meta1"] ↦ mapPtr1 st := by
  refine (sep_congr (mapFields_eq db _ st) (mapFields_eq db _ st)).trans ?_
  constructor
  · iintro ⟨⟨A1, B1, C1⟩, ⟨A2, B2, C2⟩⟩
    isplitl [A1 A2]
    · iapply (pointsto_halves _ _).2; iframe
    isplitl [B1 B2]
    · iapply (pointsto_halves _ _).2; iframe
    · iapply (pointsto_halves _ _).2; iframe
  · iintro ⟨A, B, C⟩
    icases (pointsto_halves _ _).1 $$ A with ⟨A1, A2⟩
    icases (pointsto_halves _ _).1 $$ B with ⟨B1, B2⟩
    icases (pointsto_halves _ _).1 $$ C with ⟨C1, C2⟩
    isplitl [A1 B1 C1]
    · iframe
    · iframe

theorem mapSlice_nil_iff (st : MapSt) (h : ∀ base len γm, st = some (base, len, γm) → 0 < base.addr) :
    (mapSlice st = slice.nil ↔ st = none) := by
  rcases st with _ | ⟨base, len, γm⟩
  · simp [mapSlice]
  · have := h base len γm rfl
    simp only [mapSlice, reduceCtorEq, iff_false]
    intro he; have := congrArg GoSlice.ptr he; simp [slice.nil] at this; subst this
    simp [null] at *

section agree
variable [go.BasicIntoValInj] {s : Stuckness} {E : CoPset}

/-- The new mapping's cells of the committed pages hold their bytes. -/
theorem pages_agree (e : Expr) (htv : toVal e = none) (p : GoString) (dqm : DFrac) (m : OsMeta)
    (base : Loc) (len : Nat) (hb : m.maps !! base = some len) (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ∀ (k r0 : Nat) (vf : Nat → val), 4096 * (r0 + k) ≤ len →
    ⊢ osInv (GF := GF) -∗ osMeta (GF := GF) p dqm (some m) -∗
      ([∗list] r ∈ List.range' r0 k, ∃ B, pageIs (GF := GF) p r B) -∗
      cellsR (GF := GF) base (4096 * r0) (4096 * k) vf -∗
      (osMeta (GF := GF) p dqm (some m) -∗
        ([∗list] r ∈ List.range' r0 k, ∃ B, pageIs (GF := GF) p r B ∗ cellsB (GF := GF) base (4096 * r) B) -∗
        WP e @ s; E {{ Φ }}) -∗
      WP e @ s; E {{ Φ }}
  | 0, r0, vf, _ => by
    iintro #Hinv Hm _ _ HΦ
    iapply HΦ $$ Hm []
    simp only [List.range'_zero]; iapply BigSepL.bigSepL_nil.2; iempintro
  | k + 1, r0, vf, hl => by
    iintro #Hinv Hm Hps Hc HΦ
    rw [List.range'_succ]
    icases BigSepL.bigSepL_cons.1 $$ Hps with ⟨⟨%B, #HB⟩, Hps⟩
    rw [show 4096 * (k + 1) = 4096 + 4096 * k by omega]
    icases (cellsR_append _ _ _ _ _).1 $$ Hc with ⟨Hc0, Hc⟩
    iunfold pageIs at HB
    icases HB with ⟨%HBl, #HBs⟩
    iapply cellsR_agree e htv p dqm m base len hb DFrac.discard hE Φ (B.map (·, true)) (4096 * r0) vf
      (by simp; omega) $$ Hinv Hm HBs [Hc0]
    · simp only [List.length_map, HBl]; iexact Hc0
    iintro Hm _ Hc0
    rw [show 4096 * r0 + 4096 = 4096 * (r0 + 1) by omega]
    iapply pages_agree e htv p dqm m base len hb hE Φ k (r0 + 1) vf (by omega) $$ Hinv Hm Hps Hc
    iintro Hm Hps
    iapply HΦ $$ Hm
    iapply BigSepL.bigSepL_cons.2
    iframe Hps
    iexists B
    simp only [List.map_map, Function.comp_def, List.map_id']
    iframe Hc0
    unfold pageIs; iframe HBs; ipureintro; exact HBl

/-- The new mapping's cells of a window `[a, a + n)` of bytes the client holds a fraction of. -/
theorem window_agree (e : Expr) (htv : toVal e = none) (p : GoString) (dqm : DFrac) (m : OsMeta)
    (base : Loc) (len : Nat) (hb : m.maps !! base = some len) (hE : ↑osN ⊆ E) (Φ : val → IProp GF)
    (dq : DFrac) (xs : List (w8 × Bool)) (a n : Nat) (vf : Nat → val) (h : a + n ≤ xs.length)
    (hl : a + n ≤ len) :
    ⊢ osInv (GF := GF) -∗ osMeta (GF := GF) p dqm (some m) -∗ osBytes (GF := GF) p 0 dq xs -∗
      cellsR (GF := GF) base a n vf -∗
      (osMeta (GF := GF) p dqm (some m) -∗ osBytes (GF := GF) p 0 dq xs -∗
        cellsB (GF := GF) base a (((xs.map Prod.fst).drop a).take n) -∗ WP e @ s; E {{ Φ }}) -∗
      WP e @ s; E {{ Φ }} := by
  iintro #Hinv Hm Hb Hc HΦ
  icases (osBytes_window p dq xs a n h).1 $$ Hb with ⟨H1, H2, H3⟩
  have hlen : ((xs.drop a).take n).length = n := by simp; omega
  iapply cellsR_agree e htv p dqm m base len hb dq hE Φ ((xs.drop a).take n) a vf (by omega)
    $$ Hinv Hm H2 [Hc]
  · rw [hlen]; iexact Hc
  iintro Hm H2 Hc
  iapply HΦ $$ Hm [H1 H2 H3]
  · iapply (osBytes_window p dq xs a n h).2; iframe
  · simp only [List.map_take, List.map_drop]; iexact Hc

end agree

end lemmas

end github_com.mit_pdos.etcd_grove.examples.bboltfs

end Perennial
