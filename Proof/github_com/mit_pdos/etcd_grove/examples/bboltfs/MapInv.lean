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

instance cellsR_timeless (base : Loc) (lo n : Nat) (vf : Nat → val) :
    Timeless (cellsR (GF := GF) base lo n vf) := by
  unfold cellsR; exact BigSepL.bigSepL_timeless (fun _ => inferInstance)

instance osBytes_timeless' (p : GoString) (off : Nat) (dq : DFrac) (xs : List (w8 × Bool)) :
    Timeless (osBytes (GF := GF) p off dq xs) := by
  unfold osBytes bytesG; exact BigSepL.bigSepL_timeless (fun _ => inferInstance)

instance mapCells_timeless (γ : DBNames) (p : GoString) (base : Loc) (len : Nat) :
    Timeless (_root_.Perennial.github_com.mit_pdos.etcd_grove.examples.bboltfs.mapCells (GF := GF) γ p base len) := by
  unfold _root_.Perennial.github_com.mit_pdos.etcd_grove.examples.bboltfs.mapCells
  haveI : ∀ r, Timeless iprop(∃ B, pageIs (GF := GF) p r B ∗ cellsB (GF := GF) base (4096 * r) B) := by
    intro r; unfold pageIs cellsB; infer_instance
  haveI : ∀ n, Timeless iprop([∗list] r ∈ List.range' 2 n,
      ∃ B, pageIs (GF := GF) p r B ∗ cellsB (GF := GF) base (4096 * r) B) := fun _ =>
    BigSepL.bigSepL_timeless (fun _ => inferInstance)
  haveI : ∀ lo B, Timeless (cellsB (GF := GF) base lo B) := by intro lo B; unfold cellsB; infer_instance
  haveI : ∀ x : List w8 × Bool × Nat, Timeless (ghostVar (GF := GF) γ.cur (1 : Qp).half.half x) := fun _ => inferInstance
  haveI : ∀ b : Bool, Timeless (ghostVar (GF := GF) γ.out (1 : Qp).half b) := fun _ => inferInstance
  infer_instance

/-- Two halves of the same bytes of a file, as the whole (they agree). -/
theorem osBytes_join (p : GoString) :
    ∀ (xs ys : List (w8 × Bool)) (off : Nat), xs.length = ys.length →
    osBytes (GF := GF) p off (DFrac.own (1 : Qp).half) xs ∗
      osBytes (GF := GF) p off (DFrac.own (1 : Qp).half) ys ⊢
      osBytes (GF := GF) p off (DFrac.own 1) xs
  | [], _, off, _ => by
    iintro -; iapply (osBytes_nil p off _).2; iempintro
  | x :: xs, [], _, h => by simp at h
  | x :: xs, y :: ys, off, h => by
    iintro ⟨H1, H2⟩
    icases (osBytes_cons p off _ x xs).1 $$ H1 with ⟨Hx, H1⟩
    icases (osBytes_cons p off _ y ys).1 $$ H2 with ⟨Hy, H2⟩
    iapply (osBytes_cons p off _ x xs).2
    unfold osByte
    icases gElem_valid_2 _ _ _ _ _ x y $$ Hx Hy with %Hxy
    obtain ⟨-, rfl⟩ := Hxy
    isplitl [Hx Hy]
    · conv => rhs; rw [← Qp.half_add_half 1]
      iapply (gElem_split _ _ _ _ _ _).2; iframe
    · iapply osBytes_join p xs ys (off + 1) (by simpa using h); iframe

/-- Three halves of a ghost variable cannot be. -/
theorem ghostVar_halves3 (γ : GName) (x y z : Nat × Nat) :
    ghostVar (GF := GF) γ (1 : Qp).half x ∗ ghostVar γ (1 : Qp).half y ∗ ghostVar γ (1 : Qp).half z ⊢
      False := by
  iintro ⟨H1, H2, H3⟩
  icombine H1 H2 gives % ⟨_, Hxy⟩
  subst Hxy
  ihave H12 := (ghostVar_split_half γ 1 x).2 $$ [H1 H2]
  · iframe
  icombine H12 H3 gives % ⟨Hbad, _⟩
  exfalso
  have h : 0 < ((1 : Qp).half).val := ((1 : Qp).half).2
  simp only [Qp.le_iff, Qp.val_add, Qp.val_one] at Hbad
  grind

/-! ### Lending cells to readers (`lentCells`, `metaLent`) -/

theorem bytes_frac (a b : Qp) : ∀ (B : List w8) (l : Loc),
    bytesPointsto (GF := GF) l (DFrac.own (a + b)) B ⊣⊢
      bytesPointsto (GF := GF) l (DFrac.own a) B ∗ bytesPointsto (GF := GF) l (DFrac.own b) B
  | [], l => by
    unfold bytesPointsto
    exact ⟨by iintro _; isplitl <;> itrivial, by iintro _; itrivial⟩
  | x :: B, l => by
    unfold bytesPointsto
    have h1 := (heapPointsto_fractional l (LitV (LitByte x))).fractional a b
    have h2 := bytes_frac a b B (l +ₗ 1)
    refine (sep_congr h1 h2).trans ?_
    exact ⟨by iintro ⟨⟨H1, H2⟩, ⟨H3, H4⟩⟩; iframe, by iintro ⟨⟨H1, H2⟩, ⟨H3, H4⟩⟩; iframe⟩

/-- The client halves of mapped cells, as byte points-tos. -/
theorem cellsB_bytes (base : Loc) : ∀ (B : List w8) (lo : Nat),
    cellsB (GF := GF) base lo B ⊣⊢
      bytesPointsto (GF := GF) (base +ₗ ((lo : Nat) : Int)) (DFrac.own (1 : Qp).half) B
  | [], lo => by
    unfold cellsB cellsR bytesPointsto
    simp only [List.length_nil, List.range'_zero]
    exact ⟨by iintro _; itrivial, by iintro _; iapply BigSepL.bigSepL_nil.2; iempintro⟩
  | x :: B, lo => by
    refine (cellsB_cons _ _ _ _).trans ?_
    unfold bytesPointsto
    refine sep_congr .rfl ((cellsB_bytes base B (lo + 1)).trans ?_)
    rw [loc_add_assoc]
    exact .of_eq (by congr 2 <;> omega)

theorem qp_rest (s : Qp) (d : Qp) (h : d + s ≤ 1) :
    ∃ e : Qp, e + (d + s).half.half = (1 : Qp).half := by
  obtain ⟨c, hc⟩ := Qp.lt_iff_exists_add.1
    (show (d + s).half.half < (1 : Qp).half by simp only [Qp.le_iff, Qp.lt_iff, Qp.val_add, Qp.val_half, Qp.val_one] at h ⊢; grind)
  exact ⟨c, Subtype.ext (by have := congrArg Subtype.val hc; simp only [Qp.val_add] at this ⊢; grind)⟩

theorem qp_rest1 (s : Qp) (h : s.half + s.half ≤ 1) :
    ∃ e : Qp, e + s.half.half = (1 : Qp).half := by
  obtain ⟨c, hc⟩ := Qp.lt_iff_exists_add.1
    (show s.half.half < (1 : Qp).half by simp only [Qp.le_iff, Qp.lt_iff, Qp.val_add, Qp.val_half, Qp.val_one] at h ⊢; grind)
  exact ⟨c, Subtype.ext (by have := congrArg Subtype.val hc; simp only [Qp.val_add] at this ⊢; grind)⟩

/-- `Qp` equalities, through their values. -/
macro "qp_eq" : tactic => `(tactic| (apply Subtype.ext; simp only [Qp.val_add, Qp.val_half, Qp.val_one] at *; grind))

theorem lent_intro (γm γl : GName) (k : Nat) (l : Loc) (B : List w8) :
    k ↪[γl] B ∗ bytesPointsto (GF := GF) l (DFrac.own (1 : Qp).half) B ⊢
      lentCells (GF := GF) γm γl k l B := by
  iintro ⟨Hk, Hb⟩
  unfold lentCells
  iexists none
  dsimp only
  iframe

/-- With the whole of `γm`, a group is unlent. -/
theorem lent_full (γm γl : GName) (k : Nat) (l : Loc) (B : List w8) :
    lentCells (GF := GF) γm γl k l B ∗ ghostVar γm 1 () ⊢
      (k ↪[γl] B ∗ bytesPointsto (GF := GF) l (DFrac.own (1 : Qp).half) B) ∗ ghostVar γm 1 () := by
  iintro ⟨Hl, Hm⟩
  unfold lentCells
  icases Hl with ⟨%o, Ho⟩
  rcases o with _ | d
  · iframe
  · icases Ho with ⟨%e, %he, Hd, -, -⟩
    icombine Hd Hm gives % ⟨Hbad, _⟩
    exfalso
    simp only [Qp.le_iff, Qp.val_add, Qp.val_one] at Hbad
    have := d.2; grind

/-- A reader deposits `s` of `γm` and borrows `s/4` of the cells and of the loan token. -/
theorem lent_borrow (γm γl : GName) (k : Nat) (l : Loc) (B : List w8) (s : Qp) :
    lentCells (GF := GF) γm γl k l B ∗ ghostVar γm s () ⊢
      lentCells (GF := GF) γm γl k l B ∗ k ↪[γl]{#s.half.half} B ∗
        bytesPointsto (GF := GF) l (DFrac.own s.half.half) B := by
  iintro ⟨Hl, Hs⟩
  unfold lentCells
  icases Hl with ⟨%o, Ho⟩
  rcases o with _ | d
  · icases Ho with ⟨Hk, Hb⟩
    icases (ghostVar_split_half γm s ()).1 $$ Hs with ⟨Hs1, Hs2⟩
    icombine Hs1 Hs2 gives % ⟨Hsv, _⟩
    ihave Hs := (ghostVar_split_half γm s ()).2 $$ [Hs1 Hs2]
    · iframe
    obtain ⟨e, he⟩ := qp_rest1 s Hsv
    icases (show k ↪[γl] B ⊢ k ↪[γl]{#((1 : Qp).half + e)} B ∗ k ↪[γl]{#s.half.half} B by
      have h := ((ghostMapElem_fractional k γl B).fractional ((1 : Qp).half + e) s.half.half).1
      rwa [show ((1 : Qp).half + e) + s.half.half = 1 by qp_eq] at h) $$ Hk with ⟨Hk, Hk'⟩
    icases (show bytesPointsto (GF := GF) l (DFrac.own (1 : Qp).half) B ⊢
        bytesPointsto (GF := GF) l (DFrac.own e) B ∗ bytesPointsto (GF := GF) l (DFrac.own s.half.half) B by
      rw [← he]; exact (bytes_frac e s.half.half B l).1) $$ Hb with ⟨Hb, Hb'⟩
    iframe Hk' Hb'
    iexists (some s)
    iexists e
    iframe
    ipureintro; exact he
  · icases Ho with ⟨%e, %he, Hd, Hk, Hb⟩
    icombine Hd Hs gives % ⟨Hds, _⟩
    obtain ⟨e', he'⟩ := qp_rest s d Hds
    have hee : e = e' + s.half.half := by qp_eq
    rw [hee]
    icases (bytes_frac e' s.half.half B l).1 $$ Hb with ⟨Hb, Hb'⟩
    rw [show (1 : Qp).half + (e' + s.half.half) = ((1 : Qp).half + e') + s.half.half by qp_eq]
    icases ((ghostMapElem_fractional k γl B).fractional _ _).1 $$ Hk with ⟨Hk, Hk'⟩
    iframe Hk' Hb'
    iexists (some (d + s))
    iexists e'
    iframe
    ipureintro; exact he'

/-- A reader gives back its loan, and gets back its deposit. -/
theorem lent_return (γm γl : GName) (k : Nat) (l : Loc) (B B' : List w8) (s : Qp) :
    lentCells (GF := GF) γm γl k l B ∗ k ↪[γl]{#s.half.half} B' ∗
        bytesPointsto (GF := GF) l (DFrac.own s.half.half) B' ⊢
      lentCells (GF := GF) γm γl k l B ∗ ghostVar γm s () := by
  iintro ⟨Hl, Hk', Hb'⟩
  unfold lentCells
  icases Hl with ⟨%o, Ho⟩
  rcases o with _ | d
  · icases Ho with ⟨Hk, -⟩
    icombine Hk Hk' gives % ⟨Hbad, _⟩
    exfalso
    have := DFrac.valid_own_op Hbad
    simp at this
  · icases Ho with ⟨%e, %he, Hd, Hk, Hb⟩
    icombine Hk Hk' gives % ⟨Hv, HB⟩
    subst HB
    have Hv' : ((1 : Qp).half + e + s.half.half).val ≤ 1 := Hv
    by_cases hsd : s = d
    · subst hsd
      iframe Hd
      iexists none
      dsimp only
      isplitl [Hk Hk']
      · have h := ((ghostMapElem_fractional k γl B).fractional ((1 : Qp).half + e) s.half.half).2
        rw [show ((1 : Qp).half + e) + s.half.half = 1 by qp_eq] at h
        iapply h
        iframe
      · rw [← he]
        iapply (bytes_frac e s.half.half B l).2
        iframe
    · obtain ⟨d', hd'⟩ := Qp.lt_iff_exists_add.1 (show s < d by
        have h1 : s.val ≠ d.val := fun h => hsd (Subtype.ext h)
        have := congrArg Subtype.val he
        simp only [Qp.lt_iff, Qp.val_add, Qp.val_half, Qp.val_one] at this Hv' ⊢; grind)
      subst hd'
      icases ((ghostVar_fractional γm ()).fractional s d').1 $$ Hd with ⟨Hs, Hd⟩
      iframe Hs
      iexists (some d')
      iexists (e + s.half.half)
      isplitr
      · ipureintro; qp_eq
      iframe Hd
      isplitl [Hk Hk']
      · rw [show (1 : Qp).half + (e + s.half.half) = ((1 : Qp).half + e) + s.half.half by qp_eq]
        iapply ((ghostMapElem_fractional k γl B).fractional _ _).2
        iframe
      · iapply (bytes_frac e s.half.half B l).2
        iframe

instance lentCells_timeless (γm γl : GName) (k : Nat) (l : Loc) (B : List w8) :
    Timeless (lentCells (GF := GF) γm γl k l B) := by
  unfold lentCells
  refine @exists_timeless _ _ _ _ (fun o => ?_)
  rcases o with _ | d <;> dsimp only <;> infer_instance

instance mapLend_timeless (γ : DBNames) (p : GoString) (base : Loc) (len : Nat) (γm γl : GName) :
    Timeless (mapLend (GF := GF) γ p base len γm γl) := by
  unfold mapLend metaLent metaBytes
  haveI : ∀ r B, Timeless (pageIs (GF := GF) p r B) := by intro r B; unfold pageIs; infer_instance
  haveI : ∀ x : List w8 × Bool × Nat, Timeless (ghostVar (GF := GF) γ.cur (1 : Qp).half.half x) := fun _ => inferInstance
  haveI : ∀ (q : Qp) (b : Bool), Timeless (ghostVar (GF := GF) γ.out q b) := fun _ _ => inferInstance
  haveI : ∀ q : Qp, Timeless (ghostVar (GF := GF) γm q ()) := fun _ => inferInstance
  haveI : ∀ K : GMap Nat (List w8), Timeless (ghostMapAuth (GF := GF) γl 1 K) := fun _ => by
    unfold ghostMapAuth; infer_instance
  haveI : ∀ T : GMap Nat (Option w64), Timeless (ghostMapAuth (GF := GF) γ.txs (1 : Qp).half T) := fun _ => by
    unfold ghostMapAuth; infer_instance
  haveI : ∀ (dq : DFrac) (mc : List w8), Timeless (ghostMapElem (GF := GF) γl 0 dq mc) := fun _ _ => inferInstance
  haveI : ∀ (l : Loc) (dq : DFrac) (bs : List w8), Timeless (bytesPointsto (GF := GF) l dq bs) :=
    fun l dq bs => bytesPointsto_timeless l dq bs
  haveI : ∀ n, Timeless iprop([∗list] r ∈ List.range' 2 n,
      ∃ B, pageIs (GF := GF) p r B ∗ lentCells (GF := GF) γm γl r (base +ₗ ((4096 * r : Nat) : Int)) B) :=
    fun _ => BigSepL.bigSepL_timeless (fun _ => inferInstance)
  refine @exists_timeless _ _ _ _ (fun mp => @exists_timeless _ _ _ _ (fun fl =>
    @exists_timeless _ _ _ _ (fun hwm => @exists_timeless _ _ _ _ (fun K => ?_))))
  refine @sep_timeless _ _ _ _ inferInstance (@sep_timeless _ _ _ _ inferInstance
    (@sep_timeless _ _ _ _ inferInstance (@sep_timeless _ _ _ _ inferInstance
      (@sep_timeless _ _ _ _ inferInstance ?_))))
  refine @or_timeless _ _ _ _ ?_ ?_
  · infer_instance
  · infer_instance

/-- The pages of a `mapLend`, with the whole of `γm`: none is lent. -/
theorem pages_unlend (p : GoString) (base : Loc) (γm γl : GName) : ∀ L : List Nat,
    ([∗list] r ∈ L, ∃ B, pageIs (GF := GF) p r B ∗
        lentCells (GF := GF) γm γl r (base +ₗ ((4096 * r : Nat) : Int)) B) ∗ ghostVar γm 1 () ⊢
      ([∗list] r ∈ L, ∃ B, pageIs (GF := GF) p r B ∗ cellsB (GF := GF) base (4096 * r) B) ∗
        ghostVar γm 1 ()
  | [] => by
    iintro ⟨-, Hm⟩; iframe; iapply BigSepL.bigSepL_nil.2; iempintro
  | r :: L => by
    iintro ⟨H, Hm⟩
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨⟨%B, #HB, Hl⟩, H⟩
    icases lent_full γm γl r _ B $$ [Hl Hm] with ⟨⟨-, Hb⟩, Hm⟩
    · iframe
    icases pages_unlend p base γm γl L $$ [H Hm] with ⟨H, Hm⟩
    · iframe
    iframe Hm
    iapply BigSepL.bigSepL_cons.2
    iframe H
    iexists B; iframe HB
    iapply (cellsB_bytes base B (4096 * r)).2; iexact Hb

/-- The pages of a `mapCells`, lendable, with their loan tokens. -/
theorem pages_lend (p : GoString) (base : Loc) (γm γl : GName) : ∀ (n s : Nat) (K : GMap Nat (List w8)),
    (∀ k, s ≤ k → K.lookup k = none) →
    ghostMapAuth γl 1 K ∗
      ([∗list] r ∈ List.range' s n, ∃ B, pageIs (GF := GF) p r B ∗ cellsB (GF := GF) base (4096 * r) B) ⊢
      |==> ∃ K', ghostMapAuth γl 1 K' ∗ ⌜∀ k, (k < s ∨ s + n ≤ k) → K'.lookup k = K.lookup k⌝ ∗
        ([∗list] r ∈ List.range' s n, ∃ B, pageIs (GF := GF) p r B ∗
          lentCells (GF := GF) γm γl r (base +ₗ ((4096 * r : Nat) : Int)) B)
  | 0, s, K, _ => by
    iintro ⟨Ha, -⟩
    imodintro
    iexists K; iframe
    isplitr
    · ipureintro; intro k _; rfl
    simp only [List.range'_zero]; iapply BigSepL.bigSepL_nil.2; iempintro
  | n + 1, s, K, hK => by
    iintro ⟨Ha, H⟩
    rw [List.range'_succ]
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨⟨%B, #HB, Hc⟩, H⟩
    imod ghost_map_insert (V := List w8) s B (hK s (Nat.le_refl s)) $$ Ha with ⟨Ha, Hk⟩
    imod pages_lend p base γm γl n (s + 1) (K.insert s B) (fun k hk => by
        show (K.insert s B) !! k = none
        rw [GMap.lookup_insert_ne _ _ (by omega)]; exact hK k (by omega)) $$ [Ha H] with ⟨%K', Ha, %HK', H⟩
    · iframe
    imodintro
    iexists K'; iframe Ha
    isplitr
    · ipureintro
      intro k hk
      rw [HK' k (by omega)]
      show (K.insert s B) !! k = K !! k
      rw [GMap.lookup_insert_ne _ _ (by omega)]
    iapply BigSepL.bigSepL_cons.2
    iframe H
    iexists B; iframe HB
    iapply lent_intro
    iframe Hk
    iapply (cellsB_bytes base B (4096 * s)).1; iexact Hc

/-- With the whole of `γm`, the invariant's contents as `mapCells`. -/
theorem mapLend_full (γ : DBNames) (p : GoString) (base : Loc) (len : Nat) (γm γl : GName) :
    mapLend (GF := GF) γ p base len γm γl ∗ ghostVar γm 1 () ⊢
      mapCells (GF := GF) γ p base len ∗ ghostVar γm 1 () := by
  iintro ⟨Hc, Hm⟩
  unfold mapLend
  icases Hc with ⟨%mp, %fl, %hwm, %K, Hcur, %Hl, -, -, Hpages, Hmeta⟩
  icases pages_unlend p base γm γl _ $$ [Hpages Hm] with ⟨Hpages, Hm⟩
  · iframe
  unfold mapCells
  icases Hmeta with (⟨Hout, -⟩ | ⟨Hout, %mc, %Hmc, Hml⟩)
  · iframe Hm
    iexists mp, fl, hwm
    isplitl [Hcur]; · iexact Hcur
    isplitr; · ipureintro; exact Hl
    isplitl [Hpages]; · iexact Hpages
    ileft; iexact Hout
  · unfold metaLent metaBytes
    icases Hml with (⟨-, Hb0, Hb1⟩ | ⟨-, Hd, -⟩)
    · iframe Hm
      iexists mp, fl, hwm
      isplitl [Hcur]; · iexact Hcur
      isplitr; · ipureintro; exact Hl
      isplitl [Hpages]; · iexact Hpages
      iright; iframe Hout
      iexists mc
      isplitl [Hb0]
      · iapply (cellsB_bytes base _ 16).2; iexact Hb0
      isplitl [Hb1]
      · iapply (cellsB_bytes base _ 4112).2; iexact Hb1
      ipureintro; exact Hmc
    · icombine Hd Hm gives % ⟨Hbad, _⟩
      exfalso
      simp only [Qp.le_iff, Qp.val_add, Qp.val_one] at Hbad
      have := metaDep.2; grind

/-- `mapCells`, lendable, with a fresh authority over its loan tokens. -/
theorem mapLend_alloc (γ : DBNames) (p : GoString) (base : Loc) (len : Nat) (γm : GName) :
    mapCells (GF := GF) γ p base len ⊢ |==> ∃ γl, mapLend (GF := GF) γ p base len γm γl := by
  iintro Hc
  unfold mapCells
  icases Hc with ⟨%mp, %fl, %hwm, Hcur, %Hl, Hpages, Hmeta⟩
  imod ghost_map_alloc_empty (K := Nat) (V := List w8) with ⟨%γl, Ha⟩
  iexists γl
  unfold mapLend
  icases Hmeta with (Hout | ⟨Hout, %mc, Hc0, Hc1, %Hmc⟩)
  · imod ghost_map_insert (V := List w8) 0 [] (by rfl) $$ Ha with ⟨Ha, Hk⟩
    imod pages_lend p base γm γl (hwm - 2) 2 _ (fun k hk => by
        show (GMap.insert 0 [] ∅ : GMap Nat (List w8)) !! k = none
        rw [GMap.lookup_insert_ne _ _ (by omega)]; rfl) $$ [Ha Hpages] with ⟨%K', Ha, %HK', Hpages⟩
    · iframe
    imodintro
    iexists mp, fl, hwm, K'
    isplitl [Hcur]; · iexact Hcur
    isplitr; · ipureintro; exact Hl
    isplitl [Ha]; · iexact Ha
    isplitr
    · ipureintro
      intro k hk hh
      rw [HK' k (by omega)]
      show (GMap.insert 0 [] ∅ : GMap Nat (List w8)) !! k = none
      rw [GMap.lookup_insert_ne _ _ (by omega)]; rfl
    isplitl [Hpages]; · iexact Hpages
    ileft; iframe Hout
    iexists []; iexact Hk
  · imod ghost_map_insert (V := List w8) 0 mc (by rfl) $$ Ha with ⟨Ha, Hk⟩
    imod pages_lend p base γm γl (hwm - 2) 2 _ (fun k hk => by
        show (GMap.insert 0 mc ∅ : GMap Nat (List w8)) !! k = none
        rw [GMap.lookup_insert_ne _ _ (by omega)]; rfl) $$ [Ha Hpages] with ⟨%K', Ha, %HK', Hpages⟩
    · iframe
    imodintro
    iexists mp, fl, hwm, K'
    isplitl [Hcur]; · iexact Hcur
    isplitr; · ipureintro; exact Hl
    isplitl [Ha]; · iexact Ha
    isplitr
    · ipureintro
      intro k hk hh
      rw [HK' k (by omega)]
      show (GMap.insert 0 mc ∅ : GMap Nat (List w8)) !! k = none
      rw [GMap.lookup_insert_ne _ _ (by omega)]; rfl
    isplitl [Hpages]; · iexact Hpages
    iright; iframe Hout
    iexists mc
    isplitr
    · ipureintro; exact Hmc
    unfold metaLent metaBytes
    ileft; iframe Hk
    isplitl [Hc0]
    · iapply (cellsB_bytes base _ 16).1; iexact Hc0
    · iapply (cellsB_bytes base _ 4112).1; iexact Hc1

theorem mapInv_close (γ : DBNames) (p : GoString) (base : Loc) (len : Nat) (γm : GName) :
    mapInv (GF := GF) γ p base len γm ∗ ghostVar γm 1 () ⊢ |={⊤}=> ▷ mapCells (GF := GF) γ p base len := by
  iintro ⟨#Hinv, Htok⟩
  unfold mapInv
  icases Hinv with ⟨%γl, #Hinv⟩
  imod inv_acc (by simp) $$ Hinv with ⟨Hi, Hclose⟩
  icases Hi with (>Hc | >Htok2)
  · icases mapLend_full γ p base len γm γl $$ [Hc Htok] with ⟨Hc, Htok⟩
    · iframe
    imod Hclose $$ [Htok] with _
    · inext; iright; iexact Htok
    imodintro; inext; iexact Hc
  · icombine Htok Htok2 gives % ⟨Hbad, _⟩
    exfalso
    simp only [Qp.le_iff, Qp.val_add, Qp.val_one] at Hbad
    grind

theorem mapInv_alloc (γ : DBNames) (p : GoString) (base : Loc) (len : Nat) :
    mapCells (GF := GF) γ p base len ⊢
      |={⊤}=> ∃ γm, ghostVar γm 1 () ∗ mapInv (GF := GF) γ p base len γm := by
  iintro Hc
  imod ghostVar_alloc () with ⟨%γm, Htok⟩
  imod mapLend_alloc γ p base len γm $$ Hc with ⟨%γl, Hc⟩
  imod inv_alloc mapN ⊤ iprop(mapLend (GF := GF) γ p base len γm γl ∨ ghostVar γm 1 ()) $$ [Hc] with #Hinv
  · inext; ileft; iexact Hc
  imodintro
  iexists γm
  iframe
  unfold mapInv
  iexists γl
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
