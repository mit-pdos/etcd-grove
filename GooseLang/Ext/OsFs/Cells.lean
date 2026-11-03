/-
The mapped cells across a step of the Linux file extension: the invariant's share of every
mapped cell (`cellsRes`), and how a step that renders the cells (`HeapRendered`) turns the
invariant's share for the old state, with the client's halves of the cells it changes, into the
share for the new state, with the client's halves of the cells it gives back (`cells_step`).
-/
module

public import GooseLang.Ext.OsFs.Ghost
public import GooseLang.Ext.OsFs.Heap

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.Std ProofMode
open goose_heap

section cells
variable [GooseExts] [GoGlobalContext] {GF : BundledGFunctors} [hG : NaHeapGS Loc val GF]

/-- The invariant's share of a mapped cell: half, or all of it while a change is in flight. -/
def cellFrac (b : Bool) : DFrac := DFrac.own (if b then 1 else (1 : Qp).half)

/-- The invariant's share of the mapped cells of the view `cv`. -/
def cellsRes (cv : GMap Loc (Option w8 × Bool)) : IProp GF :=
  [∗map] l ↦ x ∈ cv, heapPointsto l (cellFrac x.2) (toCellVal x.1)

instance cellsRes_timeless (cv : GMap Loc (Option w8 × Bool)) :
    Timeless (cellsRes (GF := GF) cv) := by
  unfold cellsRes; infer_instance

/-- The client's halves of the cells of `C`. -/
def halves (C : GMap Loc val) : IProp GF :=
  [∗map] l ↦ v ∈ C, heapPointsto l (DFrac.own (1 : Qp).half) v

/-- `Φ` of every cell of `T` that `m` has. -/
def listOpt {V : Type} (m : GMap Loc V) (Φ : Loc → V → IProp GF) : List Loc → IProp GF
  | [] => iprop(emp)
  | l :: T => iprop((match m !! l with | some x => Φ l x | none => iprop(emp)) ∗ listOpt m Φ T)

/-- `m` without the keys of `T`. -/
def deleteList {V : Type} : List Loc → GMap Loc V → GMap Loc V
  | [], m => m
  | l :: T, m => deleteList T (GMap.delete l m)

theorem lookup_deleteList {V : Type} : ∀ (T : List Loc) (m : GMap Loc V) (k : Loc),
    deleteList T m !! k = if k ∈ T then none else m !! k
  | [], m, k => by simp [deleteList]
  | l :: T, m, k => by
    simp only [deleteList, lookup_deleteList T, List.mem_cons, GMap.lookup_delete_iff]
    by_cases h1 : k = l
    · simp [h1]
    · by_cases h2 : k ∈ T
      · simp [h2]
      · simp [h1, h2, Ne.symm h1]

theorem listOpt_congr {V : Type} {m m' : GMap Loc V} {Φ : Loc → V → IProp GF} :
    ∀ {T : List Loc}, (∀ k ∈ T, m !! k = m' !! k) → listOpt m Φ T = listOpt m' Φ T
  | [], _ => rfl
  | l :: T, H => by
    simp only [listOpt]
    rw [H l List.mem_cons_self, listOpt_congr (fun k hk => H k (List.mem_cons_of_mem _ hk))]

theorem bigSepM_split_list {V : Type} (Φ : Loc → V → IProp GF) :
    ∀ (T : List Loc) (_ : T.Nodup) (m : GMap Loc V),
    ([∗map] l ↦ x ∈ m, Φ l x) ⊣⊢ ([∗map] l ↦ x ∈ deleteList T m, Φ l x) ∗ listOpt m Φ T
  | [], _, m => by
    simp only [deleteList, listOpt]
    exact (sep_emp).symm
  | l :: T, hT, m => by
    have hl : l ∉ T := (List.nodup_cons.1 hT).1
    have IH := bigSepM_split_list Φ T (List.nodup_cons.1 hT).2 (GMap.delete l m)
    have hc : listOpt (GMap.delete l m) Φ T = listOpt m Φ T :=
      listOpt_congr fun k hk => GMap.lookup_delete_ne _ (fun e => hl (e ▸ hk))
    rw [hc] at IH
    simp only [deleteList, listOpt]
    cases hml : m !! l with
    | none =>
      have : GMap.delete l m = m := by
        apply GMap.ext; intro k
        show GMap.delete l m !! k = m !! k
        rw [GMap.lookup_delete_iff]; split <;> simp_all
      rw [this] at IH ⊢
      refine IH.trans ?_
      exact ⟨by iintro ⟨H1, H2⟩; iframe, by iintro ⟨H1, -, H2⟩; iframe⟩
    | some x =>
      refine (BigSepM.bigSepM_delete (Φ := Φ) (m := m) (i := l) hml).trans ?_
      refine (sep_congr .rfl IH).trans ?_
      exact ⟨by iintro ⟨H1, H2, H3⟩; iframe, by iintro ⟨H2, H1, H3⟩; iframe⟩

theorem cellsRes_lookup (h : GMap Loc (NonAtomic val)) (cv : GMap Loc (Option w8 × Bool)) :
    naHeapCtx tls h ⊢ cellsRes (GF := GF) cv -∗
      ⌜∀ l x, cv !! l = some x → ∃ m, h !! l = some (m, toCellVal x.1)⌝ := by
  iintro Hσ Hc
  iapply pure_forall.2
  iintro %l
  iapply pure_forall.2
  iintro %x
  by_cases hx : cv !! l = some x
  · unfold cellsRes
    icases BigSepM.bigSepM_lookup (Φ := fun l (x : Option w8 × Bool) =>
      heapPointsto (hG := hG) l (cellFrac x.2) (toCellVal x.1)) hx $$ Hc with Hl
    icases heapPointsto_na_acc l _ _ $$ Hl with ⟨Hl, -⟩
    icases na_heap_read tls h l _ _ $$ Hσ Hl with %⟨m, n, Hh, -⟩
    ipureintro; exact fun _ => ⟨m, Hh⟩
  · ipureintro; intro h; exact absurd h hx

theorem fullPts_modes (h : GMap Loc (NonAtomic val)) :
    ∀ (T : List Loc), naHeapCtx tls h ⊢ fullPts (GF := GF) h T -∗
      ⌜∀ l ∈ T, ∀ x, h !! l = some x → x.1 = Reading 0⌝
  | [] => by iintro _ _; ipureintro; simp
  | l :: T => by
    simp only [fullPts]
    iintro Hσ ⟨Hl, HT⟩
    icases fullPts_modes h T $$ Hσ HT with %HT'
    unfold fullPt
    cases hl : h !! l with
    | none =>
      ipureintro
      intro k hk x hx
      rcases List.mem_cons.1 hk with rfl | hk
      · simp [hl] at hx
      · exact HT' k hk x hx
    | some y =>
      dsimp only
      icases heapPointsto_na_acc l _ _ $$ Hl with ⟨Hl, -⟩
      icases na_heap_read_1 tls h l _ $$ Hσ Hl with %⟨lk, Hh, Hlk⟩
      ipureintro
      intro k hk x hx
      rcases List.mem_cons.1 hk with rfl | hk
      · rw [hl] at hx Hh
        have e1 := congrArg (fun o => o.map Prod.fst) hx
        have e2 := congrArg (fun o => o.map Prod.fst) Hh
        simp only [Option.map_some, Option.some.injEq] at e1 e2
        rw [← e1, e2]
        cases lk with
        | Writing => cases Hlk
        | Reading n => cases Hlk; rfl
      · exact HT' k hk x hx

theorem heapPointsto_halves (l : Loc) (v : val) :
    heapPointsto (hG := hG) l (DFrac.own 1) v ⊣⊢
      heapPointsto l (DFrac.own (1 : Qp).half) v ∗ heapPointsto l (DFrac.own (1 : Qp).half) v := by
  have := (heapPointsto_fractional (hG := hG) l v).fractional (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at this
  exact this

theorem mapped_of_cellView {st : OsState} {l : Loc} {x : Option w8 × Bool}
    (h : cellView st !! l = some x) : Mapped st l := by
  by_cases hm : Mapped st l
  · exact hm
  · rw [cellView_none hm] at h; cases h

theorem cellView_isSome {st : OsState} (hwf : OsWf st) {l : Loc} (h : Mapped st l) :
    ∃ x, cellView st !! l = some x := by
  obtain ⟨p, i, hpi⟩ := h; exact ⟨_, cellView_mapsTo hwf hpi⟩

/-- A step renders the mapped cells (`HeapRendered`): the invariant's share of the cells of the
old view and the client's halves `Cin` become the share of the new view and the halves `Cout`.
`T` lists the cells whose share changes hands (every other cell keeps its view): the cells of
`Cin` and `Cout`, and those the invariant holds all of before or after. -/
theorem cells_step (st st' : OsState) (h h' : GMap Loc (NonAtomic val)) (T : List Loc)
    (Cin Cout : GMap Loc val) (hwf : OsWf st) (hwf' : OsWf st')
    (hr : HeapRendered st st' h h') (hfr : MapsFresh st st' h)
    (hmaps : ∀ b m, st'.maps !! b = some m → st.maps !! b = none ∨ st.maps !! b = some m)
    (hT : T.Nodup)
    (hTdom : ∀ l ∈ T, Mapped st l ∨ Mapped st' l)
    (hin : ∀ l v, Cin !! l = some v → l ∈ T ∧ ∃ ob, cellView st !! l = some (ob, false))
    (hout : ∀ l v, Cout !! l = some v → l ∈ T ∧
      ∃ ob, cellView st' !! l = some (ob, false) ∧ v = toCellVal ob)
    (hTin : ∀ l ∈ T, Cin !! l = none → ∀ x, cellView st !! l = some x → x.2 = true)
    (hTout : ∀ l ∈ T, Cout !! l = none → ∀ x, cellView st' !! l = some x → x.2 = true)
    (hU : ∀ l, l ∉ T → cellView st' !! l = cellView st !! l) :
    naHeapCtx tls h ∗ cellsRes (GF := GF) (cellView st) ∗ halves Cin ⊢ |==>
      (naHeapCtx tls h' ∗ cellsRes (cellView st') ∗ halves Cout) := by
  obtain ⟨hr1, hr2, hr3, hr4⟩ := hr
  iintro ⟨Hσ, Hc, Hin⟩
  icases cellsRes_lookup h (cellView st) $$ Hσ Hc with %Hag
  -- split the shares at `T`
  unfold cellsRes halves
  icases (bigSepM_split_list (fun l (x : Option w8 × Bool) =>
      heapPointsto (hG := hG) l (cellFrac x.2) (toCellVal x.1)) T hT (cellView st)).1 $$ Hc
    with ⟨Hrest, HcT⟩
  icases (bigSepM_split_list (fun l (v : val) =>
      heapPointsto (hG := hG) l (DFrac.own (1 : Qp).half) v) T hT Cin).1 $$ Hin
    with ⟨Hin0, HinT⟩
  -- the cells of `T`, whole
  have Hcomb : ∀ T' : List Loc, (∀ k ∈ T', k ∈ T) →
      listOpt (GF := GF) (cellView st) (fun l x =>
        heapPointsto (hG := hG) l (cellFrac x.2) (toCellVal x.1)) T' ∗
      listOpt Cin (fun l v => heapPointsto (hG := hG) l (DFrac.own (1 : Qp).half) v) T' ⊢
      fullPts h T' := by
    intro T' hT'
    induction T' with
    | nil => simp only [listOpt, fullPts]; iintro _; iempintro
    | cons l T' ih =>
      simp only [listOpt, fullPts]
      have hlT := hT' l List.mem_cons_self
      iintro ⟨⟨H1, H2⟩, H3, H4⟩
      isplitr [H2 H4]
      · unfold fullPt
        cases hcv : cellView st !! l with
        | some x =>
          obtain ⟨m, hm⟩ := Hag l x hcv
          rw [hm]
          cases hc : Cin !! l with
          | some v =>
            obtain ⟨-, ob, hob⟩ := hin l v hc
            rw [hcv] at hob; cases hob
            dsimp only
            icombine H1 H3 gives %⟨-, Heq⟩
            subst Heq
            iapply (heapPointsto_halves l _).2
            simp only [cellFrac, Bool.false_eq_true, ↓reduceIte]
            iframe
          | none =>
            have := hTin l hlT hc x hcv
            obtain ⟨ob, b⟩ := x; simp only at this; subst this
            dsimp only
            simp only [cellFrac, ↓reduceIte]
            iexact H1
        | none =>
          cases hc : Cin !! l with
          | some v =>
            obtain ⟨-, ob, hob⟩ := hin l v hc; rw [hcv] at hob; cases hob
          | none =>
            -- a new cell: free in `h`
            have hnm : ¬ Mapped st l := fun hm => by
              obtain ⟨x, hx⟩ := cellView_isSome hwf hm; rw [hcv] at hx; cases hx
            obtain ⟨p, i, b, m, hm, hp, hi, rfl⟩ := (hTdom l hlT).resolve_left hnm
            have hb : st.maps !! b = none := by
              rcases hmaps b m hm with hb | hb
              · exact hb
              · exact absurd ⟨p, i, b, m, hb, hp, hi, rfl⟩ hnm
            rw [(hfr b m hm hb).2 i hi]
            iempintro
      · iapply ih (fun k hk => hT' k (List.mem_cons_of_mem _ hk))
        iframe
  ihave HT := Hcomb T (fun k hk => hk) $$ [HcT HinT]
  · iframe
  icases fullPts_modes h T $$ Hσ HT with %Hmodes
  -- reshape the heap at `T`
  have hout' : ∀ l, l ∉ T → h' !! l = h !! l := by
    intro l hl
    have hU' := hU l hl
    by_cases hm' : Mapped st' l
    · obtain ⟨p, i, hpi⟩ := hm'
      have hv' := cellView_mapsTo hwf' hpi
      have hm : Mapped st l := mapped_of_cellView (hU' ▸ hv')
      obtain ⟨m, v0, h0, h1⟩ := hr1 l p i hpi hm
      rw [h1, h0]
      obtain ⟨m2, hm2⟩ := Hag l _ (hU' ▸ hv')
      rw [h0] at hm2; cases hm2
      rw [cellVal_eq]
    · have hnm : ¬ Mapped st l := fun hm => by
        obtain ⟨x, hx⟩ := cellView_isSome hwf hm
        rw [← hU', cellView_none hm'] at hx; cases hx
      exact hr4 l hm' hnm
  have hmode' : ∀ l ∈ T, ∀ x, h' !! l = some x → x.1 = Reading 0 := by
    intro l hl x hx
    by_cases hm' : Mapped st' l
    · obtain ⟨p, i, hpi⟩ := hm'
      by_cases hm : Mapped st l
      · obtain ⟨m, v0, h0, h1⟩ := hr1 l p i hpi hm
        rw [h1] at hx; cases hx
        exact Hmodes l hl (m, v0) h0
      · rw [hr2 l p i hpi hm] at hx; cases hx; rfl
    · by_cases hm : Mapped st l
      · rw [hr3 l hm' hm] at hx; cases hx
      · exact absurd (hTdom l hl) (by rintro (h | h) <;> contradiction)
  have haddr : ∀ l ∈ T, (h' !! l).isSome → 0 < l.addr ∧ l.addr < maxAddr := by
    intro l hl hs
    by_cases hm' : Mapped st' l
    · obtain ⟨p, i, b, m, hm, -, hi, rfl⟩ := hm'
      obtain ⟨-, h1, h2, -⟩ := hwf'.maps b m hm
      simp only [Loc.add]; omega
    · by_cases hm : Mapped st l
      · rw [hr3 l hm' hm] at hs; cases hs
      · exact absurd (hTdom l hl) (by rintro (h | h) <;> contradiction)
  imod heap_reshape T hT h h' hout' hmode' haddr $$ [Hσ HT] with ⟨Hσ, HT⟩
  · iframe
  -- split the cells of `T` back
  have Hsplit : ∀ T' : List Loc, (∀ k ∈ T', k ∈ T) →
      fullPts (GF := GF) h' T' ⊢
      listOpt (cellView st') (fun l x =>
        heapPointsto (hG := hG) l (cellFrac x.2) (toCellVal x.1)) T' ∗
      listOpt Cout (fun l v => heapPointsto (hG := hG) l (DFrac.own (1 : Qp).half) v) T' := by
    intro T' hT'
    induction T' with
    | nil => simp only [listOpt, fullPts]; iintro _; isplitl [] <;> iempintro
    | cons l T' ih =>
      simp only [listOpt, fullPts]
      have hlT := hT' l List.mem_cons_self
      iintro ⟨H1, H2⟩
      ihave ⟨H3, H4⟩ := ih (fun k hk => hT' k (List.mem_cons_of_mem _ hk)) $$ H2
      iframe H3 H4
      unfold fullPt
      by_cases hm' : Mapped st' l
      · obtain ⟨p, i, hpi⟩ := hm'
        have hv' := cellView_mapsTo hwf' hpi
        have hh' : ∃ m, h' !! l = some (m, cellVal st' p i) := by
          by_cases hm : Mapped st l
          · obtain ⟨m, v0, -, h1⟩ := hr1 l p i hpi hm; exact ⟨m, h1⟩
          · exact ⟨_, hr2 l p i hpi hm⟩
        obtain ⟨m, hh'⟩ := hh'
        rw [hh', hv', cellVal_eq]
        dsimp only
        cases hc : Cout !! l with
        | some v =>
          obtain ⟨-, ob, hob, rfl⟩ := hout l v hc
          rw [hv'] at hob
          simp only [Option.some.injEq, Prod.mk.injEq] at hob
          obtain ⟨rfl, hdec⟩ := hob
          simp only [cellFrac, hdec, Bool.false_eq_true, ↓reduceIte]
          iapply (heapPointsto_halves l _).1 $$ H1
        | none =>
          have := hTout l hlT hc _ hv'
          simp only at this
          simp only [cellFrac, this, ↓reduceIte]
          iframe H1
      · have hcv : cellView st' !! l = none := cellView_none hm'
        have hc : Cout !! l = none := by
          cases hc : Cout !! l with
          | none => rfl
          | some v => obtain ⟨-, ob, hob, -⟩ := hout l v hc; rw [hcv] at hob; cases hob
        have hm : Mapped st l := (hTdom l hlT).resolve_right hm'
        rw [hcv, hc, hr3 l hm' hm]
        isplitl [] <;> iempintro
  ihave ⟨HcT', HoutT⟩ := Hsplit T (fun k hk => hk) $$ HT
  imodintro
  iframe Hσ
  have hdel : deleteList T (cellView st') = deleteList T (cellView st) := by
    apply GMap.ext; intro k
    show deleteList T (cellView st') !! k = deleteList T (cellView st) !! k
    rw [lookup_deleteList, lookup_deleteList]
    split
    · rfl
    · exact hU k ‹_›
  have hdelC : deleteList T Cout = ∅ := by
    apply GMap.ext; intro k
    show deleteList T Cout !! k = (∅ : GMap Loc val) !! k
    rw [lookup_deleteList]
    split
    · rfl
    · cases hc : Cout !! k with
      | none => rfl
      | some v => exact absurd (hout k v hc).1 ‹_›
  isplitl [Hrest HcT']
  · iapply (bigSepM_split_list (fun l (x : Option w8 × Bool) =>
      heapPointsto (hG := hG) l (cellFrac x.2) (toCellVal x.1)) T hT (cellView st')).2
    rw [hdel]
    iframe
  · iapply (bigSepM_split_list (fun l (v : val) =>
      heapPointsto (hG := hG) l (DFrac.own (1 : Qp).half) v) T hT Cout).2
    rw [hdelC]
    iframe HoutT
    iapply BigSepM.bigSepM_empty.2
    iempintro

/-- The cells `[lo, lo + n)` of the mapping at `base`, holding `vf i`. -/
def mkCellsR (base : Loc) (vf : Nat → val) (lo : Nat) : Nat → GMap Loc val
  | 0 => ∅
  | n + 1 => <[base +ₗ ((lo + n : Nat) : Int) := vf (lo + n)]> (mkCellsR base vf lo n)

theorem lookup_mkCellsR (base : Loc) (vf : Nat → val) (lo : Nat) :
    ∀ (n : Nat) (l : Loc), mkCellsR base vf lo n !! l =
      if h : base.addr ≤ l.addr ∧ lo ≤ (l.addr - base.addr).toNat ∧
          (l.addr - base.addr).toNat < lo + n
        then some (vf (l.addr - base.addr).toNat) else none
  | 0, l => by simp [mkCellsR]
  | n + 1, l => by
    simp only [mkCellsR, GMap.lookup_insert_eq_iff, lookup_mkCellsR base vf lo n]
    by_cases he : base +ₗ ((lo + n : Nat) : Int) = l
    · subst he
      rw [if_pos rfl, dif_pos (by simp only [Loc.add]; omega)]
      congr 2; simp only [Loc.add]; omega
    · rw [if_neg he]
      have : ¬ (l.addr - base.addr).toNat = lo + n ∨ ¬ base.addr ≤ l.addr := by
        by_cases h1 : base.addr ≤ l.addr
        · left; intro h2; apply he; cases l; simp [Loc.add] at h1 h2 ⊢; omega
        · right; exact h1
      split <;> split <;> first | rfl | omega

/-- The client's halves of the cells `[lo, lo + n)` of the mapping at `base`. -/
def cellsR (base : Loc) (lo n : Nat) (vf : Nat → val) : IProp GF :=
  [∗list] i ∈ List.range' lo n, heapPointsto (hG := hG) (base +ₗ ((i : Nat) : Int))
    (DFrac.own (1 : Qp).half) (vf i)

theorem cellsR_halves (base : Loc) (lo : Nat) (vf : Nat → val) :
    ∀ n, cellsR (GF := GF) base lo n vf ⊣⊢ halves (mkCellsR base vf lo n)
  | 0 => by
    unfold cellsR halves; simp only [mkCellsR]
    exact ⟨by iintro _; iapply BigSepM.bigSepM_empty.2; iempintro,
      by iintro _; simp only [List.range'_zero]; iapply BigSepL.bigSepL_nil.2; iempintro⟩
  | n + 1 => by
    have IH := cellsR_halves base lo vf n
    unfold cellsR halves at *
    rw [List.range'_concat, Nat.one_mul]
    simp only [mkCellsR]
    refine BigSepL.bigSepL_append.trans ?_
    refine BIBase.BiEntails.trans ?_ (BigSepM.bigSepM_insert (Φ := fun l (v : val) =>
      heapPointsto (hG := hG) l (DFrac.own (1 : Qp).half) v) ?_).symm
    · refine (sep_congr IH .rfl).trans ?_
      refine (sep_congr .rfl BigSepL.bigSepL_singleton).trans ?_
      exact ⟨by iintro ⟨H1, H2⟩; iframe, by iintro ⟨H1, H2⟩; iframe⟩
    · show mkCellsR base vf lo n !! _ = none
      rw [lookup_mkCellsR, dif_neg (by simp only [Loc.add]; omega)]

end cells

end Perennial
