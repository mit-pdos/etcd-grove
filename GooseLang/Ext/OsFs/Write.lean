/-
WP specs of the Linux file extension's two-step changes: `pwrite` (`PWriteStart`,
`PWriteFinish`).
-/
module

public import GooseLang.Ext.OsFs.Specs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode
open goose_heap

/-! ## Bytes written -/

theorem resizeBytes_length (c : List w8) (sz : Nat) : (resizeBytes c sz).length = sz := by
  unfold resizeBytes; simp; omega

/-- Closes a goal about list lookups after its conditionals are split. -/
local macro "lst_tac" : tactic => `(tactic| (repeat' split) <;>
  first | rfl | omega | (exfalso; omega) |
    (simp_all only [List.getElem?_eq_none_iff, Option.some.injEq, reduceCtorEq]; omega) |
    (simp_all; done) | (congr 1; omega))

theorem resizeBytes_getElem? (c : List w8) (sz i : Nat) :
    (resizeBytes c sz)[i]? = if i < sz then (if i < c.length then c[i]? else some 0) else none := by
  unfold resizeBytes
  simp only [List.getElem?_append, List.length_take, List.getElem?_take, List.getElem?_replicate]
  lst_tac

theorem writeBytes_length (c : List w8) (off : Nat) (d : List w8) (hd : d ≠ []) :
    (writeBytes c off d).length = max c.length (off + d.length) := by
  unfold writeBytes; rw [if_neg hd]
  simp only [List.length_append, List.length_take, List.length_drop, resizeBytes_length]
  omega

theorem writeBytes_getElem? (c : List w8) (off : Nat) (d : List w8) (hd : d ≠ []) (i : Nat) :
    (writeBytes c off d)[i]? =
      if i < off then (if i < c.length then c[i]? else some 0)
      else if i < off + d.length then d[i - off]? else c[i]? := by
  unfold writeBytes; rw [if_neg hd]
  have hl := resizeBytes_length c (max c.length off)
  simp only [List.getElem?_append, List.length_append, List.length_take, hl, List.getElem?_take,
    List.getElem?_drop, resizeBytes_getElem?]
  have hmin : min off (max c.length off) = off := by omega
  simp only [hmin]
  have hdl : 0 < d.length := List.length_pos_iff.2 hd
  by_cases h1 : i < off
  · simp only [h1, ↓reduceIte, show i < max c.length off by omega,
      show i < off + d.length by omega]
  · simp only [h1, ↓reduceIte]
    by_cases h2 : i < off + d.length
    · simp only [show i < off + d.length by omega, ↓reduceIte]
    · simp only [h2, ↓reduceIte, show off + d.length + (i - (off + d.length)) = i by omega]
      by_cases h3 : i < c.length
      · simp only [h3, show i < max c.length off by omega, ↓reduceIte]
      · simp only [h3, show ¬ i < max c.length off by omega, ↓reduceIte]
        exact (List.getElem?_eq_none (by omega)).symm

/-! ## The cells of a range of every mapping of a file -/

/-- `l` is byte `i` of one of the mappings `L` (base, length), with `i ∈ [lo, hi)`. -/
def InCells (L : List (Loc × Nat)) (lo hi : Nat) (l : Loc) (i : Nat) : Prop :=
  ∃ b len, (b, len) ∈ L ∧ lo ≤ i ∧ i < hi ∧ i < len ∧ l = b +ₗ (i : Int)

/-- The mappings `L` are disjoint. -/
abbrev MapsDisj (L : List (Loc × Nat)) : Prop :=
  L.Pairwise (fun x y => x.1.addr + (x.2 : Int) ≤ y.1.addr ∨ y.1.addr + (y.2 : Int) ≤ x.1.addr)

theorem mapsDisj_toList (M : GMap Loc Nat)
    (h : ∀ b1 l1 b2 l2, M !! b1 = some l1 → M !! b2 = some l2 → b1 ≠ b2 →
      b1.addr + (l1 : Int) ≤ b2.addr ∨ b2.addr + (l2 : Int) ≤ b1.addr) : MapsDisj M.toList := by
  have hnd : (M.toList.map (·.1)).Nodup := Iris.Std.LawfulFiniteMap.toList_noDupKeys (m := M)
  unfold List.Nodup at hnd; rw [List.pairwise_map] at hnd
  refine hnd.imp_of_mem (fun {x y} hx hy hne => ?_)
  exact h x.1 x.2 y.1 y.2 ((GMap.mem_toList _ _ _).1 hx) ((GMap.mem_toList _ _ _).1 hy) hne

section mapsCells
variable [GooseExts] [GoGlobalContext]

theorem lookup_mkCellsR_iff (b : Loc) (vf : Nat → val) (lo n : Nat) (l : Loc) (v : val) :
    mkCellsR b vf lo n !! l = some v ↔
      ∃ i, lo ≤ i ∧ i < lo + n ∧ l = b +ₗ (i : Int) ∧ v = vf i := by
  rw [lookup_mkCellsR]
  constructor
  · intro h
    split at h
    · rename_i hc; cases h
      exact ⟨_, hc.2.1, hc.2.2, by cases l; cases b; simp [Loc.add] at hc ⊢; omega, rfl⟩
    · cases h
  · rintro ⟨i, h1, h2, rfl, rfl⟩
    rw [dif_pos (by simp only [Loc.add]; omega)]
    congr 2; simp only [Loc.add]; omega

/-- The cells `[lo, hi)` of the mappings `L`, each cut at its length, holding `vf i` at byte `i`
of the file. -/
def mapsCells (lo hi : Nat) (vf : Nat → val) : List (Loc × Nat) → GMap Loc val
  | [] => ∅
  | bl :: L => mkCellsR bl.1 vf (min lo bl.2) (min hi bl.2 - min lo bl.2) ∪ mapsCells lo hi vf L

theorem lookup_mapsCells (lo hi : Nat) (vf : Nat → val) :
    ∀ (L : List (Loc × Nat)), MapsDisj L → ∀ l v,
      (mapsCells lo hi vf L !! l = some v ↔ ∃ i, InCells L lo hi l i ∧ v = vf i)
  | [], _, l, v => by simp [mapsCells, InCells]
  | bl :: L, hd, l, v => by
    have IH := lookup_mapsCells lo hi vf L (List.pairwise_cons.1 hd).2
    simp only [mapsCells, GMap.lookup_union]
    constructor
    · intro h
      cases h1 : mkCellsR bl.1 vf (min lo bl.2) (min hi bl.2 - min lo bl.2) !! l with
      | some w =>
        rw [h1] at h; cases h
        obtain ⟨i, hi1, hi2, rfl, rfl⟩ := (lookup_mkCellsR_iff _ _ _ _ _ _).1 h1
        exact ⟨i, ⟨bl.1, bl.2, List.mem_cons_self, by omega, by omega, by omega, rfl⟩, rfl⟩
      | none =>
        rw [h1] at h
        obtain ⟨i, ⟨b, len, hm, h2⟩, rfl⟩ := (IH l v).1 h
        exact ⟨i, ⟨b, len, List.mem_cons_of_mem _ hm, h2⟩, rfl⟩
    · rintro ⟨i, ⟨b, len, hm, h1, h2, h3, rfl⟩, rfl⟩
      rcases List.mem_cons.1 hm with he | hm
      · subst he
        rw [(lookup_mkCellsR_iff _ _ _ _ _ _).2 ⟨i, by omega, by omega, rfl, rfl⟩]; rfl
      · have hn : mkCellsR bl.1 vf (min lo bl.2) (min hi bl.2 - min lo bl.2) !! (b +ₗ (i : Int)) =
            none := by
          cases h0 : mkCellsR bl.1 vf (min lo bl.2) (min hi bl.2 - min lo bl.2) !! (b +ₗ (i : Int)) with
          | none => rfl
          | some w =>
            exfalso
            obtain ⟨j, hj1, hj2, he, -⟩ := (lookup_mkCellsR_iff _ _ _ _ _ _).1 h0
            have hd1 := (List.pairwise_cons.1 hd).1 (b, len) hm
            have : b.addr + i = bl.1.addr + j := by simpa [Loc.add] using congrArg Loc.addr he
            simp only at hd1; omega
        rw [hn]
        exact (IH _ _).2 ⟨i, ⟨b, len, hm, h1, h2, h3, rfl⟩, rfl⟩

theorem mkCellsR_disj_mapsCells (lo hi : Nat) (vf vf' : Nat → val) (bl : Loc × Nat)
    (L : List (Loc × Nat)) (hd : MapsDisj (bl :: L)) (C : GMap Loc val)
    (hC : ∀ l, (C !! l).isSome → ∃ i, InCells L lo hi l i) :
    mkCellsR bl.1 vf' (min lo bl.2) (min hi bl.2 - min lo bl.2) ##ₘ C := by
  rw [GMap.map_disjoint_spec]
  intro l x y h1 h2
  obtain ⟨j, hj1, hj2, rfl, -⟩ := (lookup_mkCellsR_iff _ _ _ _ _ _).1 h1
  obtain ⟨i, b, len, hm, -, -, hi3, he⟩ := hC _ (by rw [h2]; rfl)
  have hd1 := (List.pairwise_cons.1 hd).1 (b, len) hm
  have : bl.1.addr + j = b.addr + i := by simpa [Loc.add] using congrArg Loc.addr he
  simp only at hd1; omega

variable {GF : BundledGFunctors} [hG : NaHeapGS Loc val GF]

theorem halves_union (C1 C2 : GMap Loc val) (hd : C1 ##ₘ C2) :
    halves (GF := GF) (C1 ∪ C2) ⊣⊢ halves C1 ∗ halves C2 := by
  unfold halves
  have h := BigSepM.bigSepM_union (Φ := fun l (v : val) =>
    heapPointsto (hG := hG) l (DFrac.own (1 : Qp).half) v) (m₁ := C1) (m₂ := C2)
    (fun k ⟨a, b⟩ => hd k a b)
  rw [gmap_union_eq]
  exact h

theorem halves_mapsCells (lo hi : Nat) (vf : Nat → val) :
    ∀ (L : List (Loc × Nat)), MapsDisj L →
      halves (GF := GF) (mapsCells lo hi vf L) ⊣⊢
        [∗list] bl ∈ L, cellsR bl.1 (min lo bl.2) (min hi bl.2 - min lo bl.2) vf
  | [], _ => by
    simp only [mapsCells, halves]
    exact ⟨by iintro _; iapply BigSepL.bigSepL_nil.2; iempintro,
      by iintro _; iapply BigSepM.bigSepM_empty.2; iempintro⟩
  | bl :: L, hd => by
    simp only [mapsCells]
    refine (halves_union _ _ (mkCellsR_disj_mapsCells lo hi vf vf bl L hd _ (fun l h => ?_))).trans ?_
    · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 h
      obtain ⟨i, hi, -⟩ := (lookup_mapsCells lo hi vf L (List.pairwise_cons.1 hd).2 l v).1 hv
      exact ⟨i, hi⟩
    refine BIBase.BiEntails.trans ?_ BigSepL.bigSepL_cons.symm
    exact sep_congr (cellsR_halves _ _ _ _).symm (halves_mapsCells lo hi vf L (List.pairwise_cons.1 hd).2)

theorem halves_mapsCells_ex (lo hi : Nat) :
    ∀ (L : List (Loc × Nat)), MapsDisj L →
      ([∗list] bl ∈ L, ∃ vf, cellsR (GF := GF) bl.1 (min lo bl.2) (min hi bl.2 - min lo bl.2) vf) ⊢
        ∃ C, halves C ∗ ⌜∀ l, (C !! l).isSome ↔ ∃ i, InCells L lo hi l i⌝
  | [], _ => by
    iintro _
    iexists ∅
    isplitl
    · unfold halves; iapply BigSepM.bigSepM_empty.2; iempintro
    · ipureintro; intro l; simp [InCells]
  | bl :: L, hd => by
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨⟨%vf, H1⟩, H2⟩
    icases halves_mapsCells_ex lo hi L (List.pairwise_cons.1 hd).2 $$ H2 with ⟨%C, H2, %hC⟩
    have hdj := mkCellsR_disj_mapsCells lo hi vf vf bl L hd C (fun l h => (hC l).1 h)
    iexists (mkCellsR bl.1 vf (min lo bl.2) (min hi bl.2 - min lo bl.2) ∪ C)
    isplitl
    · iapply (halves_union _ _ hdj).2
      iframe H2
      iapply (cellsR_halves _ _ _ _).1 $$ H1
    · ipureintro
      intro l
      simp only [GMap.lookup_union]
      constructor
      · intro h
        cases h1 : mkCellsR bl.1 vf (min lo bl.2) (min hi bl.2 - min lo bl.2) !! l with
        | some w =>
          obtain ⟨i, hi1, hi2, rfl, rfl⟩ := (lookup_mkCellsR_iff _ _ _ _ _ _).1 h1
          exact ⟨i, bl.1, bl.2, List.mem_cons_self, by omega, by omega, by omega, rfl⟩
        | none =>
          rw [h1] at h
          obtain ⟨i, b, len, hm, h2⟩ := (hC l).1 (by simpa using h)
          exact ⟨i, b, len, List.mem_cons_of_mem _ hm, h2⟩
      · rintro ⟨i, b, len, hm, h1, h2, h3, rfl⟩
        rcases List.mem_cons.1 hm with he | hm
        · subst he
          rw [(lookup_mkCellsR_iff _ _ _ _ _ _).2 ⟨i, by omega, by omega, rfl, rfl⟩]; rfl
        · have := (hC _).2 ⟨i, b, len, hm, h1, h2, h3, rfl⟩
          cases h0 : mkCellsR bl.1 vf (min lo bl.2) (min hi bl.2 - min lo bl.2) !! (b +ₗ (i : Int))
          · simpa using this
          · rfl

end mapsCells

/-! ## Adding a change in flight -/

theorem exists_fresh {V : Type} (M : GMap Nat V) : ∃ t, M !! t = none := by
  refine ⟨(M.toList.map (·.1)).sum + 1, ?_⟩
  cases h : M !! ((M.toList.map (·.1)).sum + 1) with
  | none => rfl
  | some v =>
    exfalso
    have hm : (M.toList.map (·.1)).sum + 1 ∈ M.toList.map (·.1) :=
      List.mem_map.2 ⟨_, (GMap.mem_toList _ _ _).2 h, rfl⟩
    have : ∀ (L : List Nat) (x : Nat), x ∈ L → x ≤ L.sum := by
      intro L x hx
      induction L with
      | nil => cases hx
      | cons a L ih =>
        rcases List.mem_cons.1 hx with rfl | hx
        · simp
        · have := ih hx; simp; omega
    have := this _ _ hm; omega

section addTok
variable {st : OsState} {t : Nat} {c : OsChange}

theorem inflightAt_addTok (ht : st.inflight !! t = none) (q : GoString) (i : Nat) :
    InflightAt { st with inflight := <[t := c]> st.inflight } q i ↔
      InflightAt st q i ∨ (c.path = q ∧ Affects st c i) := by
  constructor
  · rintro ⟨t', c', h1, h2, h3⟩
    by_cases he : t = t'
    · subst he; rw [GMap.lookup_insert] at h1; cases h1; exact .inr ⟨h2, h3⟩
    · rw [GMap.lookup_insert_ne _ _ he] at h1; exact .inl ⟨t', c', h1, h2, h3⟩
  · rintro (⟨t', c', h1, h2, h3⟩ | ⟨h2, h3⟩)
    · have he : t ≠ t' := fun e => by subst e; rw [ht] at h1; cases h1
      exact ⟨t', c', by rw [GMap.lookup_insert_ne _ _ he]; exact h1, h2, h3⟩
    · exact ⟨t, c, GMap.lookup_insert _ _ _, h2, h3⟩

theorem osWf_addTok (hwf : OsWf st) (ht : st.inflight !! t = none) {f : OsFile}
    (hf : st.file c.path = some f) (hfree : ∀ i, Affects st c i → ¬ InflightAt st c.path i) :
    OsWf { st with inflight := <[t := c]> st.inflight } := by
  refine { hwf with infl := fun t' c' h => ?_, infl_disj := fun t1 c1 t2 c2 i h1 h2 hne hp => ?_ }
  · by_cases he : t = t'
    · subst he; rw [GMap.lookup_insert] at h; cases h; exact ⟨f, hf⟩
    · rw [GMap.lookup_insert_ne _ _ he] at h; exact hwf.infl t' c' h
  · show Affects st c1 i → ¬ Affects st c2 i
    by_cases e1 : t = t1 <;> by_cases e2 : t = t2
    · subst e1 e2; exact absurd rfl hne
    · subst e1; rw [GMap.lookup_insert] at h1; cases h1
      rw [GMap.lookup_insert_ne _ _ e2] at h2
      exact fun ha hb => hfree i ha ⟨t2, c2, h2, hp.symm, hb⟩
    · subst e2; rw [GMap.lookup_insert] at h2; cases h2
      rw [GMap.lookup_insert_ne _ _ e1] at h1
      exact fun ha hb => hfree i hb ⟨t1, c1, h1, hp, ha⟩
    · rw [GMap.lookup_insert_ne _ _ e1] at h1; rw [GMap.lookup_insert_ne _ _ e2] at h2
      exact hwf.infl_disj t1 c1 t2 c2 i h1 h2 hne hp

/-- The ghost maps after the first step of a change `c` on the file `p`: its `OsMeta` becomes
`om` (bounds widened to the change's target), the bytes it takes are marked not clean, and its
token records what it took. -/
theorem osCoh_addTok {Γb Γm Γf Γt} (hcoh : OsCoh st Γb Γm Γf Γt) {p : GoString} {f : OsFile}
    {m om : OsMeta} {q : Qp} {xs : List (w8 × Bool)} (hcp : c.path = p)
    (hf : st.file p = some f) (Hml : Γm !! p = some (some m))
    (hom : om.size = m.size ∧ om.named = m.named ∧ om.ok = m.ok ∧ om.maps = m.maps ∧
      om.lo ≤ m.lo ∧ m.hi ≤ om.hi ∧ om.lo ≤ c.target st ∧ c.target st ≤ om.hi)
    (ht : st.inflight !! t = none) (hfree : ∀ i, Affects st c i → ¬ InflightAt st p i)
    (hq : Reaches st c → q = 1)
    (hfrac : ∀ t ti, Γt !! t = some ti → ti.c.path = p → ti.q ≠ 1)
    (hwhole : q = 1 → ∀ t c', st.inflight !! t = some c' → c'.path ≠ p)
    (hlen : xs.length = affHi st c - affLo st c)
    (hxs : ∀ k (hk : k < xs.length), Γb !! (p, affLo st c + k) = some xs[k]) :
    OsCoh { st with inflight := <[t := c]> st.inflight }
      (insertBytes p (affLo st c) (xs.map (fun x => (x.1, false))) Γb) (<[p := some om]> Γm) Γf
      (<[t := ⟨c, q, xs.map Prod.fst, om⟩]> Γt) := by
  subst hcp
  obtain ⟨hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8⟩ := hom
  have hΓt : Γt !! t = none := by
    have := hcoh.toks t; rw [ht] at this
    cases h : Γt !! t
    · rfl
    · rw [h] at this; cases this
  have hI := inflightAt_addTok (c := c) ht
  have hfp : st.files !! c.path = some (some f) := file_eq_some.1 hf
  refine ⟨fun q' => ?_, fun q' => ?_, fun q' m' hm => ?_, fun q' i x hx => ?_,
    fun q' f1 i h1 hi => ?_, hcoh.fds, fun t' => ?_, fun t' ti h => ?_, fun t' ti h hq1 => ?_,
    fun t' ti h => ?_⟩
  · rw [GMap.lookup_insert_eq_iff]; split
    · subst_vars; simp [hfp]
    · exact hcoh.meta_dom q'
  · rw [GMap.lookup_insert_eq_iff]; split
    · subst_vars; simp [hfp]
    · exact hcoh.meta_none q'
  · obtain ⟨fm, hfm, hmo⟩ : ∃ fm, st.files !! q' = some (some fm) ∧
        MetaOk st q' (if c.path = q' then m else m') fm := by
      rw [GMap.lookup_insert_eq_iff] at hm
      split at hm
      · subst_vars; simp only [↓reduceIte]; exact hcoh.meta_some _ m Hml
      · rename_i hne; simp only [hne, ↓reduceIte]; exact hcoh.meta_some q' m' hm
    refine ⟨fm, hfm, ?_⟩
    rw [GMap.lookup_insert_eq_iff] at hm
    split at hm
    · subst_vars; cases hm; simp only [↓reduceIte] at hmo
      refine ⟨hs1 ▸ hmo.size, hs2 ▸ hmo.named, Nat.le_trans hs5 hmo.lo, Nat.le_trans hmo.hi hs6,
        fun hok => hmo.ok (hs3 ▸ hok), fun b len => hs4 ▸ hmo.maps b len, fun t' c' h1 h2 => ?_⟩
      by_cases he : t = t'
      · subst he; rw [GMap.lookup_insert] at h1; cases h1; exact ⟨hs7, hs8⟩
      · rw [GMap.lookup_insert_ne _ _ he] at h1
        have := hmo.targets t' c' h1 h2
        exact (show om.lo ≤ c'.target st ∧ c'.target st ≤ om.hi from ⟨by omega, by omega⟩)
    · rename_i hne; simp only [hne, ↓reduceIte] at hmo
      refine ⟨hmo.size, hmo.named, hmo.lo, hmo.hi, hmo.ok, hmo.maps, fun t' c' h1 h2 => ?_⟩
      by_cases he : t = t'
      · subst he; rw [GMap.lookup_insert] at h1; cases h1; exact absurd h2 hne
      · rw [GMap.lookup_insert_ne _ _ he] at h1; exact hmo.targets t' c' h1 h2
  · rw [lookup_insertBytes] at hx
    split at hx
    · rename_i hr
      obtain ⟨rfl, h1, h2⟩ := hr
      have hk : i - affLo st c < xs.length := by simp at h2; omega
      obtain ⟨f1, hf1, hb, -⟩ := hcoh.bytes _ _ _ (hxs _ hk)
      rw [List.getElem?_map, List.getElem?_eq_getElem hk] at hx; cases hx
      rw [show affLo st c + (i - affLo st c) = i by omega] at hb
      exact ⟨f1, hf1, hb, fun h => by cases h⟩
    · obtain ⟨f1, h1, hb, hc⟩ := hcoh.bytes q' i x hx
      refine ⟨f1, h1, hb, fun hx2 => ⟨(hc hx2).1, ?_⟩⟩
      rw [hI]
      rintro (h | ⟨rfl, ha⟩)
      · exact (hc hx2).2 h
      · rename_i hr
        rw [hf] at h1; cases h1
        have hi : i < f.cur.length := (List.getElem?_eq_some_iff.1 hb).1
        have hm := List.mem_range'_1.1 ((affects_iff_affRange st c i f hf hi).1 ha)
        exact hr ⟨rfl, hm.1, by simp; omega⟩
  · rw [lookup_insertBytes]
    split
    · rename_i hr; rw [List.getElem?_eq_getElem (by simp at hr ⊢; omega)]; rfl
    · exact hcoh.bytes_full q' f1 i h1 hi
  · rw [GMap.lookup_insert_eq_iff, GMap.lookup_insert_eq_iff]
    split
    · rfl
    · exact hcoh.toks t'
  · rw [GMap.lookup_insert_eq_iff] at h
    split at h
    · cases h; exact hq
    · exact hcoh.tok_q t' ti h
  · intro t'' c'' hne h''
    rw [GMap.lookup_insert_eq_iff] at h
    split at h
    · subst_vars; cases h
      rw [GMap.lookup_insert_ne _ _ (Ne.symm hne)] at h''
      exact hwhole hq1 t'' c'' h''
    · rename_i htt
      by_cases he : t = t''
      · subst he; rw [GMap.lookup_insert] at h''; cases h''
        intro hp; exact hfrac t' ti h hp.symm hq1
      · rw [GMap.lookup_insert_ne _ _ he] at h''
        exact hcoh.tok_alone t' ti h hq1 t'' c'' hne h''
  · rw [GMap.lookup_insert_eq_iff] at h
    split at h
    · cases h
      refine ⟨f, hf, ?_⟩
      apply List.ext_getElem
      · simp [affRange, hlen]; rfl
      · intro k h1 h2
        simp only [List.length_map] at h1
        obtain ⟨f1, hf1, hb, -⟩ := hcoh.bytes _ _ _ (hxs _ h1)
        rw [hf] at hf1; cases hf1
        simp only [List.getElem_map, affRange, List.getElem_range']
        rw [List.getD_eq_getElem?_getD, Nat.one_mul]
        show _ = (f.cur[affLo st c + k]?).getD 0
        rw [hb]; rfl
    · obtain ⟨f1, h1, hsv⟩ := hcoh.tok_saved t' ti h
      exact ⟨f1, h1, hsv⟩

end addTok

/-! ## A heap rendered for a state with the same mappings -/

section render
variable [GooseExts] [GoGlobalContext]
attribute [local instance] Classical.propDecidable

/-- `h` with the cells mapped in `st'` showing `st'`, each keeping its mode. -/
noncomputable def renderHeap (st' : OsState) (h : GMap Loc (NonAtomic val)) :
    GMap Loc (NonAtomic val) :=
  ⟨fun l => if hm : Mapped st' l then
      (h !! l).map (fun x => (x.1, cellVal st' hm.choose hm.choose_spec.choose)) else h !! l,
   by
    obtain ⟨L, hL⟩ := h.finite
    refine ⟨L, fun k hk => hL k ?_⟩
    split at hk
    · simpa using hk
    · exact hk⟩

theorem heapRendered_render {st st' : OsState} {h : GMap Loc (NonAtomic val)} (hwf' : OsWf st')
    (hm : st'.maps = st.maps) (Hh : ∀ l, Mapped st l → (h !! l).isSome) :
    HeapRendered st st' h (renderHeap st' h) := by
  have hM : ∀ l p i, MapsTo st' l p i ↔ MapsTo st l p i := by
    intro l p i; simp only [MapsTo, hm]
  have hMd : ∀ l, Mapped st' l ↔ Mapped st l := fun l =>
    ⟨fun ⟨p, i, h⟩ => ⟨p, i, (hM l p i).1 h⟩, fun ⟨p, i, h⟩ => ⟨p, i, (hM l p i).2 h⟩⟩
  have hlk : ∀ l, renderHeap st' h !! l = (if hm : Mapped st' l then
      (h !! l).map (fun x => (x.1, cellVal st' hm.choose hm.choose_spec.choose)) else h !! l) :=
    fun _ => rfl
  refine ⟨fun l p i hpi hmd => ?_, fun l p i hpi hn => absurd ((hMd l).1 ⟨p, i, hpi⟩) hn,
    fun l hn hmd => absurd ((hMd l).2 hmd) hn, fun l hn _ => ?_⟩
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (Hh l hmd)
    refine ⟨x.1, x.2, hx, ?_⟩
    have hm' : Mapped st' l := ⟨p, i, hpi⟩
    rw [hlk, dif_pos hm', hx]
    obtain ⟨rfl, rfl⟩ := mapsTo_unique hwf' hm'.choose_spec.choose_spec hpi
    rfl
  · rw [hlk, dif_neg hn]

end render

/-! ## Specs -/

/-- The `OsMeta` of a file while a write of `n` bytes at `off` is in flight: its size may grow up
to `off + n`. -/
def pwMeta (m : OsMeta) (off n : Nat) : OsMeta := { m with hi := max m.hi (off + n) }

section ghost
variable {GF : BundledGFunctors} (hL : OsGS GF)

/-- A fraction `q` of a file's `OsMeta`: no change in flight on it holds the whole, and if `q = 1`,
none is in flight on it. -/
theorem tokRes_meta_own {st : OsState} {Γt : GMap Nat TokInfo} {p : GoString} {q : Qp}
    {mo : Option OsMeta} :
    ⊢ tokRes hL st Γt -∗ gElem hL hL.γm p (DFrac.own q) mo -∗
      ⌜q = 1 → ∀ t ti, Γt !! t = some ti → ti.c.path ≠ p⌝ := by
  iintro Htok Hm
  by_cases hq : q = 1
  · subst hq
    icases tokRes_meta_whole hL $$ Htok Hm with %H
    ipureintro; exact fun _ => H
  · ipureintro; exact fun h => absurd h hq

/-- Replacing the `OsMeta` of a file by `om`, which must be `m` unless the client holds all of
it. -/
theorem meta_replace {Γm : GMap GoString (Option OsMeta)} {p : GoString} {q : Qp} {m om : OsMeta}
    (hq : q ≠ 1 → om = m) :
    gAuth hL hL.γm Γm ∗ gElem hL hL.γm p (DFrac.own q) (some m) ⊢ |==>
      (gAuth hL hL.γm (<[p := some om]> Γm) ∗ gElem hL hL.γm p (DFrac.own q) (some om)) := by
  iintro ⟨HA, Hm⟩
  by_cases h1 : q = 1
  · subst h1; iapply gAuth_update hL $$ HA Hm
  · rw [hq h1]
    icases gAuth_lookup hL _ _ _ _ _ $$ HA Hm with %Hl
    have : <[p := some m]> Γm = Γm := by
      apply GMap.ext; intro k
      show (<[p := some m]> Γm) !! k = Γm !! k
      rw [GMap.lookup_insert_eq_iff]; split
      · subst_vars; exact Hl.symm
      · rfl
    rw [this]; imodintro; iframe

end ghost

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt] [GoGlobalContext]
  [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}
attribute [local instance] Classical.propDecidable

/-- The client's halves of the cells `[lo, hi)` of every mapping in `M` (cut at its length),
holding anything. -/
def mcellsAny (M : GMap Loc Nat) (lo hi : Nat) : IProp GF :=
  [∗map] b ↦ len ∈ M, ∃ vf, cellsR b (min lo len) (min hi len - min lo len) vf

/-- The client's halves of the cells `[lo, hi)` of every mapping in `M`, holding `vf i` at byte
`i` of the file. -/
def mcells (M : GMap Loc Nat) (lo hi : Nat) (vf : Nat → val) : IProp GF :=
  [∗map] b ↦ len ∈ M, cellsR b (min lo len) (min hi len - min lo len) vf

/-- A `pwrite` of `data` at `off` of the file `p` between its two steps: what its first step
took (a fraction `q` of the `OsMeta` `m`, the bytes `xs`). -/
def pwTok (t : Nat) (p : GoString) (off : Nat) (data : List w8) (q : Qp) (m : OsMeta)
    (xs : List (w8 × Bool)) : IProp GF :=
  osTok (L := L) t ⟨⟨p, .write off data⟩, q, xs.map Prod.fst, pwMeta m off data.length⟩

theorem cellByte_eq (st : OsState) (p : GoString) (i : Nat) :
    cellByte st p i = if InflightAt st p i then none else (st.file p).bind (·.cur[i]?) := by
  unfold cellByte
  cases st.file p with
  | none => simp
  | some f =>
    dsimp only
    by_cases hi : i < f.cur.length
    · simp [hi, List.getElem?_eq_getElem hi]
    · simp [hi, List.getElem?_eq_none (Nat.le_of_not_lt hi)]

/-- The first step of `pwrite(fd, data, off)`, with the bytes it may change below the size
(`[min off size, min (off + n) size)`, whole), the client's halves of the cells of every mapping
over `[min off size, off + n)`, and a fraction `q` of the file's `OsMeta`, all of it if the write
may extend the file. They stay with the change until its second step (`wp_PWriteFinish`). -/
theorem wp_PWriteStart (fd off : w64) (data : List w8) (dq : DFrac) (d : OsFd) (q : Qp)
    (m : OsMeta) (xs : List (w8 × Bool)) (hE : ↑osN ⊆ E) (hwr : d.writable = true)
    (hoff : 0 ≤ off.toInt)
    (hlen : xs.length = min (off.toNat + data.length) m.size - min off.toNat m.size)
    (hq : m.size < off.toNat + data.length → q = 1) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osFd (L := L) fd dq d -∗ osMeta (L := L) d.path (DFrac.own q) (some m) -∗
      osBytes (L := L) d.path (min off.toNat m.size) (DFrac.own 1) xs -∗
      mcellsAny m.maps (min off.toNat m.size) (off.toNat + data.length) -∗
      (∀ t : Nat, osFd (L := L) fd dq d -∗ pwTok t d.path off.toNat data q m xs -∗
        Φ (osTokV t)) -∗
      WP (ExternalOp osFsExt.name "PWriteStart" (Val (PairV (#fd) (PairV (#off) (#data))))) @ s; E
        {{ Φ }} := by
  iintro #Hinv Hfd Hm Hbs Hc HΦ
  iapply wp_os_step "PWriteStart" _ Φ (by simp [val.isPanic]) hE $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %h Hw
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  icases osBytes_lookup hcoh d.path _ _ xs $$ HAb Htok Hbs with %Hbf
  unfold osFd osMeta osBytes
  icases bytesG_lookup _ d.path _ _ xs Γb $$ HAb Hbs with %Hbl
  icases gAuth_lookup _ _ _ _ _ _ $$ HAf Hfd with %Hfdl
  icases gAuth_lookup _ _ _ _ _ _ $$ HAm Hm with %Hml
  icases tokRes_meta_frac _ $$ Htok Hm with %Hfrac
  icases tokRes_meta_own _ $$ Htok Hm with %Hwhole
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hfd : st.fds !! fd = some d := hcoh.fds ▸ Hfdl
  obtain ⟨f, hf, hmo⟩ := coh_meta hcoh Hml
  have hsz : st.size d.path = m.size := by rw [size_of_file hf, hmo.size]
  have hszf := hwf.sizes d.path f hf
  have hfree : ∀ i, Affects st ⟨d.path, .write off.toNat data⟩ i → ¬ InflightAt st d.path i := by
    intro i ha
    by_cases hr : m.size < off.toNat + data.length
    · rintro ⟨t', c', h1, h2, -⟩
      exact noTok_of_whole hcoh (Hwhole (hq hr)) t' c' h1 h2
    · have : off.toNat ≤ i ∧ i < off.toNat + data.length := by
        simp [Affects, inRange, hsz] at ha; omega
      have hk : i - min off.toNat m.size < xs.length := by omega
      obtain ⟨-, -, -, hn⟩ := Hbf _ hk
      rw [show min off.toNat m.size + (i - min off.toNat m.size) = i by omega] at hn; exact hn
  have Hh : ∀ l, Mapped st l → (h !! l).isSome := by
    intro l hm
    obtain ⟨x, hx⟩ := cellView_isSome hwf hm
    obtain ⟨m0, hm0⟩ := Hag l x hx
    rw [hm0]; rfl
  obtain ⟨t0, ht0⟩ := exists_fresh st.inflight
  imodintro
  isplitr
  · ipureintro
    have hwf0 := osWf_addTok (t := t0) (c := ⟨d.path, .write off.toNat data⟩) hwf ht0 hf hfree
    exact ⟨_, _, _, ⟨fd, off, data, d, t0, rfl, hfd, hwr, hoff, ⟨hfree, ht0, rfl⟩, rfl⟩,
      mapsFresh_same rfl, heapRendered_render hwf0 rfl Hh⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsOsStep] at Hst
  obtain ⟨fd', off', data', d', t, hv, hfd', -, -, ⟨-, ht, hst'⟩, rfl⟩ := Hst
  injection hv with h1 h2; injection h2 with h3 h4
  cases go.intoVal_inj h1; cases go.intoVal_inj h3; cases go.intoVal_inj h4
  simp only [FdOpen, hfd, Option.some.injEq] at hfd'; subst hfd'
  subst hst'
  generalize hc : (⟨d.path, .write off.toNat data⟩ : OsChange) = c at hfree Hr Hfr ⊢
  have hcp : c.path = d.path := by rw [← hc]
  have hlo : affLo st c = min off.toNat m.size := by rw [← hc]; simp [affLo, hsz]
  have hhi : affHi st c = min (off.toNat + data.length) m.size := by rw [← hc]; simp [affHi, hsz]
  have haff : ∀ i, Affects st c i ↔ min off.toNat m.size ≤ i ∧ i < off.toNat + data.length := by
    intro i; rw [← hc]; simp [Affects, inRange, hsz]
  have hwf1 := osWf_addTok (t := t) (c := c) hwf ht (hcp ▸ hf) (hcp ▸ hfree)
  have hom : pwMeta m off.toNat data.length = m ∨ q = 1 := by
    by_cases hr : m.size < off.toNat + data.length
    · exact .inr (hq hr)
    · left
      have h1 := hmo.hi; have h2 := hmo.size
      have : max m.hi (off.toNat + data.length) = m.hi := by omega
      unfold pwMeta; rw [this]
  have hcoh1 := osCoh_addTok (t := t) (q := q) (m := m) (om := pwMeta m off.toNat data.length)
    (xs := xs) hcoh hcp hf Hml
    ⟨rfl, rfl, rfl, rfl, Nat.le_refl _, Nat.le_max_left _ _,
      by rw [← hc]; simp only [OsChange.target, hsz, pwMeta]; have := hmo.lo; have := hmo.size
         omega,
      by rw [← hc]; simp only [OsChange.target, hsz, pwMeta]; have := hmo.hi; have := hmo.size
         omega⟩
    ht (hcp ▸ hfree) (fun hr => hq (by rw [← hc] at hr; simpa [Reaches, hsz] using hr))
    Hfrac (fun h1 => noTok_of_whole hcoh (Hwhole h1)) (by rw [hlo, hhi, hlen])
    (fun k hk => by rw [hlo]; exact Hbl k hk)
  -- the cells: the client's halves of the cells the write may change go to the invariant
  have hdisj : MapsDisj m.maps.toList := mapsDisj_toList _ (fun b1 l1 b2 l2 h1 h2 hne =>
    hwf.maps_disj b1 _ b2 _ ((hmo.maps b1 l1).1 h1) ((hmo.maps b2 l2).1 h2) hne)
  unfold mcellsAny
  ihave Hc := (BigSepM.bigSepM_toList (Φ := fun (b : Loc) (len : Nat) =>
    iprop(∃ vf, cellsR b (min (min off.toNat m.size) len)
      (min (off.toNat + data.length) len - min (min off.toNat m.size) len) vf))).1 $$ Hc
  icases halves_mapsCells_ex (min off.toNat m.size) (off.toNat + data.length) _ hdisj
    $$ Hc with ⟨%C, Hc, %hC⟩
  have hI := inflightAt_addTok (c := c) ht
  have hmapsC : ∀ l, (C !! l).isSome → ∃ i, MapsTo st l d.path i ∧ Affects st c i := by
    intro l hl
    obtain ⟨i, b, len, hm, h1, h2, h3, rfl⟩ := (hC l).1 hl
    exact ⟨i, ⟨b, ⟨d.path, len⟩, (hmo.maps b len).1 ((GMap.mem_toList _ _ _).1 hm), rfl, h3, rfl⟩,
      (haff i).2 ⟨h1, h2⟩⟩
  have hTmem : ∀ l, l ∈ C.toList.map (·.1) ↔ (C !! l).isSome := by
    intro l; simp only [List.mem_map]
    constructor
    · rintro ⟨⟨k, v⟩, hkv, rfl⟩; rw [(GMap.mem_toList _ _ _).1 hkv]; rfl
    · intro hl; obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hl
      exact ⟨(l, v), (GMap.mem_toList _ _ _).2 hv, rfl⟩
  have hTnd : (C.toList.map (·.1)).Nodup := Iris.Std.LawfulFiniteMap.toList_noDupKeys (m := C)
  imod cells_step st _ h h' (C.toList.map (·.1)) C ∅ hwf hwf1 Hr Hfr (fun b m0 h0 => .inr h0) hTnd
    (fun l hl => by obtain ⟨i, hi, -⟩ := hmapsC l ((hTmem l).1 hl); exact .inl ⟨_, _, hi⟩)
    (fun l v hl => by
      have hs : (C !! l).isSome := by rw [hl]; rfl
      obtain ⟨i, hi, ha⟩ := hmapsC l hs
      exact ⟨(hTmem l).2 hs, _, by rw [cellView_mapsTo hwf hi, decide_eq_false (hfree i ha)]⟩)
    (fun l v h => by simp at h)
    (fun l hl hn => by rw [(hTmem l).1 hl |> Option.isSome_iff_exists.1 |>.choose_spec] at hn; cases hn)
    (fun l hl _ x hx => by
      obtain ⟨i, hi, ha⟩ := hmapsC l ((hTmem l).1 hl)
      rw [cellView_mapsTo hwf1 hi] at hx; cases hx
      exact decide_eq_true ((hI _ _).2 (.inr ⟨hcp, ha⟩)))
    (fun l hl => by
      by_cases hm : Mapped st l
      · obtain ⟨q', i, hqi⟩ := hm
        rw [cellView_mapsTo hwf1 hqi, cellView_mapsTo hwf hqi, cellByte_eq, cellByte_eq]
        have hn : ¬ (c.path = q' ∧ Affects st c i) := by
          rintro ⟨hp, ha⟩
          obtain ⟨b, m0, hb, hp0, hi0, rfl⟩ := hqi
          have hb' : m.maps !! b = some m0.len := by
            rw [hmo.maps b m0.len, hb]; congr 1; cases m0; simp only at hp0 ⊢
            rw [hp0, ← hp, hcp]
          apply hl; apply (hTmem _).2; apply (hC _).2
          obtain ⟨h1, h2⟩ := (haff i).1 ha
          exact ⟨i, b, m0.len, (GMap.mem_toList _ _ _).2 hb', h1, h2, hi0, rfl⟩
        have hII : InflightAt { st with inflight := <[t := c]> st.inflight } q' i ↔
            InflightAt st q' i := by rw [hI]; exact ⟨fun h => h.resolve_right hn, .inl⟩
        simp only [hII]; rfl
      · rw [cellView_none (st := st) hm]; exact cellView_none hm)
    $$ [Hσ Hcells Hc] with ⟨Hσ, Hcells, -⟩
  · iframe
  -- the ghost maps
  imod meta_replace _ (om := pwMeta m off.toNat data.length) (fun h1 => hom.resolve_right h1)
    $$ [HAm Hm] with ⟨HAm, Hm⟩
  · iframe
  imod bytesG_update _ d.path _ xs (xs.map (fun x => (x.1, false))) Γb (by simp) $$ [HAb Hbs]
    with ⟨HAb, Hbs⟩
  · iframe
  have hΓt : Γt !! t = none := by
    have := hcoh.toks t; rw [ht] at this
    cases h0 : Γt !! t
    · rfl
    · rw [h0] at this; cases this
  imod gAuth_insert _ _ _ t ⟨c, q, xs.map Prod.fst, pwMeta m off.toNat data.length⟩ hΓt $$ HAt
    with ⟨HAt, Ht⟩
  imodintro
  iexists _, _, Γf, _
  iframe HAb HAm HAf HAt Hσ Hcells
  isplitl [Htok Hm Hbs]
  · isplitr
    · ipureintro; rw [← hlo]; exact ⟨hwf1, hcoh1⟩
    rw [show tokRes (gooseOsGS (L := L)) { st with inflight := <[t := c]> st.inflight }
        (<[t := ⟨c, q, xs.map Prod.fst, pwMeta m off.toNat data.length⟩]> Γt) =
      tokRes gooseOsGS st (<[t := ⟨c, q, xs.map Prod.fst, pwMeta m off.toNat data.length⟩]> Γt)
      from rfl]
    unfold tokRes
    iapply (BigSepM.bigSepM_insert (Φ := fun (_t : Nat) (ti : TokInfo) =>
      iprop(gElem gooseOsGS gooseOsGS.γm ti.c.path (DFrac.own ti.q) (some ti.om) ∗
        bytesG gooseOsGS ti.c.path (affLo st ti.c) (DFrac.own 1) (ti.saved.map (·, false))))
      hΓt).2
    simp only [List.map_map]
    rw [hcp, hlo, show List.map ((fun x => (x, false)) ∘ Prod.fst) xs =
      List.map (fun x => (x.fst, false)) xs from rfl]
    iframe
  iapply wp_value'
  iapply HΦ $$ Hfd
  unfold pwTok osTok
  rw [← hc]; iexact Ht

end specs

end Perennial
