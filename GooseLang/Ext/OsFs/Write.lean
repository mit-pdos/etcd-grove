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
      om.lo ≤ m.lo ∧ m.hi ≤ om.hi ∧ om.lo ≤ c.target st ∧ c.target st ≤ om.hi ∧ (om.dur, om.durHi) = (m.dur, m.durHi))
    (ht : st.inflight !! t = none) (hfree : ∀ i, Affects st c i → ¬ InflightAt st p i)
    (hq : Reaches st c → q = 1)
    (hfrac : ∀ t ti, Γt !! t = some ti → ti.c.path = p → ti.q ≠ 1)
    (hwhole : q = 1 → ∀ t c', st.inflight !! t = some c' → c'.path ≠ p)
    (hlen : xs.length = affHi st c - affLo st c)
    (hxs : ∀ k (hk : k < xs.length), Γb !! (p, affLo st c + k) = some xs[k]) :
    OsCoh { st with inflight := <[t := c]> st.inflight }
      (insertBytes p (affLo st c) (xs.map (fun x => (x.1, false))) Γb) (<[p := some om]> Γm) Γf
      (<[t := ⟨c, q, xs.map Prod.fst, om, xs.map Prod.snd⟩]> Γt) := by
  subst hcp
  obtain ⟨hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9⟩ := hom
  have hΓt : Γt !! t = none := by
    have := hcoh.toks t; rw [ht] at this
    cases h : Γt !! t
    · rfl
    · rw [h] at this; cases this
  have hI := inflightAt_addTok (c := c) ht
  have hfp : st.files !! c.path = some (some f) := file_eq_some.1 hf
  refine ⟨fun q' => ?_, fun q' => ?_, fun q' m' hm => ?_, fun q' i x hx => ?_,
    fun q' f1 i h1 hi => ?_, hcoh.fds, fun t' => ?_, fun t' ti h => ?_, fun t' ti h hq1 => ?_,
    fun t' ti h => ?_, fun t' ti h => ?_⟩
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
        fun hok => hmo.ok (hs3 ▸ hok), fun b len => hs4 ▸ hmo.maps b len, fun t' c' h1 h2 => ?_,
        (Prod.mk.inj hs9).1 ▸ hmo.dur, (Prod.mk.inj hs9).2 ▸ hmo.durLen⟩
      by_cases he : t = t'
      · subst he; rw [GMap.lookup_insert] at h1; cases h1; exact ⟨hs7, hs8⟩
      · rw [GMap.lookup_insert_ne _ _ he] at h1
        have := hmo.targets t' c' h1 h2
        exact (show om.lo ≤ c'.target st ∧ c'.target st ≤ om.hi from ⟨by omega, by omega⟩)
    · rename_i hne; simp only [hne, ↓reduceIte] at hmo
      refine ⟨hmo.size, hmo.named, hmo.lo, hmo.hi, hmo.ok, hmo.maps, fun t' c' h1 h2 => ?_, hmo.dur,
        hmo.durLen⟩
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
  · rw [GMap.lookup_insert_eq_iff] at h
    split at h
    · cases h
      intro j hj
      simp only [List.getElem?_map, Option.map_eq_some_iff] at hj
      obtain ⟨x, hx, hx2⟩ := hj
      have hk : j < xs.length := (List.getElem?_eq_some_iff.1 hx).1
      have hxe : xs[j] = x := (List.getElem?_eq_some_iff.1 hx).2
      obtain ⟨f1, hf1, -, hc⟩ := hcoh.bytes _ _ _ (hxs _ hk)
      exact ⟨by show j < affHi st c - affLo st c; omega, f1, hf1, (hc (by rw [hxe]; exact hx2)).1⟩
    · exact hcoh.tok_clean t' ti h

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

theorem tokRes_congr {st st' : OsState} {Γt : GMap Nat TokInfo}
    (h : ∀ t ti, Γt !! t = some ti → st'.size ti.c.path = st.size ti.c.path) :
    tokRes hL st Γt ⊢ tokRes hL st' Γt := by
  unfold tokRes
  apply BigSepM.bigSepM_mono
  intro t ti hti
  have : affLo st' ti.c = affLo st ti.c := by unfold affLo; rw [h t ti hti]
  rw [this]

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
  osTok (L := L) t ⟨⟨p, .write off data⟩, q, xs.map Prod.fst, pwMeta m off data.length, xs.map Prod.snd⟩

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
may extend the file. They stay with the change until its second step (`wp_osPWriteFinish`). -/
theorem wp_osPWriteStart (fd off : w64) (data : List w8) (dq : DFrac) (d : OsFd) (q : Qp)
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
         omega, rfl⟩
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
  imod gAuth_insert _ _ _ t ⟨c, q, xs.map Prod.fst, pwMeta m off.toNat data.length, xs.map Prod.snd⟩ hΓt $$ HAt
    with ⟨HAt, Ht⟩
  imodintro
  iexists _, _, Γf, _
  iframe HAb HAm HAf HAt Hσ Hcells
  isplitl [Htok Hm Hbs]
  · isplitr
    · ipureintro; rw [← hlo]; exact ⟨hwf1, hcoh1⟩
    rw [show tokRes (gooseOsGS (L := L)) { st with inflight := <[t := c]> st.inflight }
        (<[t := ⟨c, q, xs.map Prod.fst, pwMeta m off.toNat data.length, xs.map Prod.snd⟩]> Γt) =
      tokRes gooseOsGS st (<[t := ⟨c, q, xs.map Prod.fst, pwMeta m off.toNat data.length, xs.map Prod.snd⟩]> Γt)
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

/-! ## The second step of a write -/

/-- The size after a `pwrite` of `k` bytes at `off` of a file of size `sz`. -/
def pwSize (sz off k : Nat) : Nat := if k = 0 then sz else max sz (off + k)

/-- Byte `i` after a `pwrite` of the first `k` bytes of `data` at `off`, in the range its first
step took, from `lo` on, whose bytes were `xs`: the zero gap, the data, then the old bytes. -/
def pwByte (off : Nat) (data : List w8) (k lo : Nat) (xs : List (w8 × Bool)) (i : Nat) : w8 :=
  if i < off then 0 else if i < off + k then data.getD (i - off) 0 else (xs.getD (i - lo) (0, false)).1

/-- The file after a `pwrite` of the first `k` bytes of `data` at `off`. -/
def pwFile (f : OsFile) (off : Nat) (data : List w8) (k : Nat) : OsFile :=
  if k = 0 then f else f.change (writeBytes f.cur off (data.take k)) (min off f.cur.length) (off + k)

section pwFile
variable (f : OsFile) (off : Nat) (data : List w8) (k : Nat)

theorem pwFile_length (hk : k ≤ data.length) :
    (pwFile f off data k).cur.length = pwSize f.cur.length off k := by
  unfold pwFile pwSize
  split
  · rfl
  · rename_i h0
    simp only [OsFile.change]
    rw [writeBytes_length _ _ _ (List.ne_nil_of_length_pos (by rw [List.length_take]; omega)), List.length_take]; omega

theorem pwFile_getElem? (hk : k ≤ data.length) (i : Nat) :
    (pwFile f off data k).cur[i]? =
      if i < off then (if i < f.cur.length then f.cur[i]? else if k = 0 then none else some 0)
      else if i < off + k then data[i - off]? else f.cur[i]? := by
  unfold pwFile
  split
  · rename_i h0; subst h0
    by_cases h1 : i < off
    · simp only [h1, ↓reduceIte]; split
      · rfl
      · rw [List.getElem?_eq_none (by omega)]
    · simp [h1]
  · rename_i h0
    simp only [OsFile.change]
    rw [writeBytes_getElem? _ _ _ (List.ne_nil_of_length_pos (by rw [List.length_take]; omega)), List.length_take, List.getElem?_take]
    simp only [show min k data.length = k by omega, h0, ↓reduceIte]
    by_cases h1 : i < off
    · simp [h1]
    · simp only [h1, ↓reduceIte]; split
      · rw [if_pos (by omega)]
      · rfl

theorem pwFile_outside (hk : k ≤ data.length) (i : Nat)
    (hi : i < min off f.cur.length ∨ off + data.length ≤ i) :
    (pwFile f off data k).cur[i]? = f.cur[i]? := by
  rw [pwFile_getElem? _ _ _ _ hk]
  rcases hi with hi | hi
  · simp only [show i < off by omega, show i < f.cur.length by omega, ↓reduceIte]
  · simp only [show ¬ i < off by omega, show ¬ i < off + k by omega, ↓reduceIte]

theorem pwFile_inside (hk : k ≤ data.length) (xs : List (w8 × Bool))
    (hlen : xs.length = min (off + data.length) f.cur.length - min off f.cur.length)
    (hxs : ∀ j (hj : j < xs.length), f.cur[min off f.cur.length + j]? = some xs[j].1)
    (i : Nat) (h1 : min off f.cur.length ≤ i) (h2 : i < off + data.length) :
    (pwFile f off data k).cur[i]? =
      if i < pwSize f.cur.length off k then
        some (pwByte off data k (min off f.cur.length) xs i) else none := by
  rw [pwFile_getElem? _ _ _ _ hk]
  unfold pwSize pwByte
  by_cases hi1 : i < off
  · have : f.cur.length ≤ i := by omega
    simp only [hi1, show ¬ i < f.cur.length by omega, ↓reduceIte]
    by_cases hk0 : k = 0
    · simp [hk0, show ¬ i < f.cur.length by omega]
    · simp only [hk0, ↓reduceIte, show i < max f.cur.length (off + k) by omega]
  · simp only [hi1, ↓reduceIte]
    by_cases hi2 : i < off + k
    · have hk0 : k ≠ 0 := by omega
      simp only [hi2, hk0, ↓reduceIte, show i < max f.cur.length (off + k) by omega,
        List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_getElem (by omega)]; rfl
    · simp only [hi2, ↓reduceIte]
      by_cases hi3 : i < f.cur.length
      · have hj : i - min off f.cur.length < xs.length := by omega
        have := hxs _ hj
        rw [show min off f.cur.length + (i - min off f.cur.length) = i by omega] at this
        rw [this, if_pos (by split <;> omega), List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hj]; rfl
      · rw [List.getElem?_eq_none (by omega), if_neg (by split <;> omega)]

theorem pwFile_durable : (pwFile f off data k).durable = f.durable := by
  unfold pwFile; split <;> rfl
theorem pwFile_lost : (pwFile f off data k).lost = f.lost := by
  unfold pwFile; split <;> rfl
theorem pwFile_named : (pwFile f off data k).named = f.named := by
  unfold pwFile; split <;> rfl
theorem pwFile_dirty (i : Nat) : (pwFile f off data k).dirty i = true ↔
    f.dirty i = true ∨ (k ≠ 0 ∧ min off f.cur.length ≤ i ∧ i < off + k) := by
  unfold pwFile; split
  · simp_all
  · rename_i h0; simp [OsFile.change, inRange, h0]
theorem pwFile_sizeLo (hk : k ≤ data.length) (h : f.sizeLo ≤ f.cur.length) :
    (pwFile f off data k).sizeLo = f.sizeLo := by
  unfold pwFile; split
  · rfl
  · simp only [OsFile.change]
    rw [writeBytes_length _ _ _ (List.ne_nil_of_length_pos (by rw [List.length_take]; omega)), List.length_take]; omega
theorem pwFile_sizeHi (hk : k ≤ data.length) (h : f.cur.length ≤ f.sizeHi) :
    (pwFile f off data k).sizeHi = max f.sizeHi (pwSize f.cur.length off k) := by
  unfold pwFile pwSize; split
  · omega
  · simp only [OsFile.change]
    rw [writeBytes_length _ _ _ (List.ne_nil_of_length_pos (by rw [List.length_take]; omega)), List.length_take]; omega

end pwFile

section finish
variable {st : OsState} {Γb : GMap (GoString × Nat) (w8 × Bool)} {Γm : GMap GoString (Option OsMeta)}
  {Γf : GMap w64 OsFd} {Γt : GMap Nat TokInfo} {t : Nat} {ti : TokInfo} {p : GoString} {off : Nat}
  {data : List w8} {f : OsFile} {k : Nat}

theorem affects_congr1 {st st' : OsState} (c : OsChange) (h : st'.size c.path = st.size c.path)
    (i : Nat) : Affects st' c i = Affects st c i := by
  unfold Affects; rw [h]

theorem affRange_congr1 {st st' : OsState} (c : OsChange) (h : st'.size c.path = st.size c.path) :
    affRange st' c = affRange st c := by
  unfold affRange affLo affHi; rw [h]

theorem target_congr1 {st st' : OsState} (c : OsChange) (h : st'.size c.path = st.size c.path) :
    c.target st' = c.target st := by
  unfold OsChange.target; rw [h]

theorem reaches_congr1 {st st' : OsState} (c : OsChange) (h : st'.size c.path = st.size c.path) :
    Reaches st' c = Reaches st c := by
  unfold Reaches; rw [h]

/-- The state and the ghost maps after the second step of a write that wrote `k` bytes. -/
theorem pwFinish_coh (hwf : OsWf st) (hcoh : OsCoh st Γb Γm Γf Γt) (hti : Γt !! t = some ti)
    (hc : ti.c = ⟨p, .write off data⟩) (hf : st.file p = some f) (hk : k ≤ data.length)
    (Hml : Γm !! p = some (some ti.om)) (xs : List (w8 × Bool)) (hxs : ti.saved = xs.map Prod.fst)
    (hcl : ti.cl = xs.map Prod.snd) :
    let lo := min off f.cur.length
    let stk := ({ st with inflight := GMap.delete t st.inflight } : OsState).setFile p
      (pwFile f off data k)
    let ys := (List.range (min (off + data.length) (pwSize f.cur.length off k) - lo)).map
      (fun j => (pwByte off data k lo xs (lo + j),
        decide (off + k ≤ lo + j) && (xs.getD j (0, false)).2))
    (∀ t' c', t' ≠ t → st.inflight !! t' = some c' → stk.size c'.path = st.size c'.path) ∧
    (∀ q i, InflightAt stk q i ↔ InflightAt st q i ∧ ¬ (p = q ∧ Affects st ti.c i)) ∧
    OsWf stk ∧
    OsCoh stk (insertBytes p lo ys Γb)
      (<[p := some { ti.om with size := pwSize f.cur.length off k }]> Γm) Γf (GMap.delete t Γt) := by
  intro lo stk ys
  have hct : st.inflight !! t = some ti.c := by
    have := hcoh.toks t; rw [hti] at this; exact this.symm
  have hcp : ti.c.path = p := by rw [hc]
  have hsz := size_of_file hf
  obtain ⟨f0, hf0, hsv⟩ := hcoh.tok_saved t ti hti
  rw [hcp, hf] at hf0; cases hf0
  obtain ⟨f1, hf1, hmo⟩ := hcoh.meta_some p ti.om Hml
  rw [← file_eq_some, hf] at hf1; cases hf1
  have hszf := hwf.sizes p f hf
  have hlen := pwFile_length f off data k hk
  have haff : ∀ i, Affects st ti.c i ↔ lo ≤ i ∧ i < off + data.length := by
    intro i; rw [hc]; simp [Affects, inRange, hsz, lo]
  have hxslen : xs.length = min (off + data.length) f.cur.length - lo := by
    have := congrArg List.length hsv
    rw [hxs] at this; simp only [List.length_map, affRange, List.length_range'] at this
    rw [this, hc]; simp [affHi, affLo, hsz, lo]
  have hxsv : ∀ j (hj : j < xs.length), f.cur[lo + j]? = some xs[j].1 := by
    intro j hj
    have h1 := congrArg (·[j]?) hsv
    have hr : (affRange st ti.c)[j]? = some (affLo st ti.c + j) := by
      have hj' : j < affHi st ti.c - affLo st ti.c := by
        rw [hc]; simp only [affHi, affLo, hsz]; omega
      unfold affRange; rw [List.getElem?_range' hj', Nat.one_mul]
    simp only [hxs, List.getElem?_map, List.getElem?_eq_getElem hj, hr] at h1
    simp only [Option.map_some, Option.some.injEq] at h1
    rw [hc] at h1; simp only [affLo, hsz] at h1
    rw [h1, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
  -- the sizes of the other changes' files do not change
  have hsizes : ∀ t' c', t' ≠ t → st.inflight !! t' = some c' → stk.size c'.path = st.size c'.path := by
    intro t' c' hne h'
    show (({ st with inflight := GMap.delete t st.inflight } : OsState).setFile p _).size _ = _
    rw [size_setFile]; split
    · rename_i hp; subst hp
      rw [hlen, hsz]
      apply Classical.byContradiction; intro hne'
      have hr : Reaches st ti.c := by
        rw [hc]; unfold pwSize at hne'; simp only [Reaches, hsz]; split at hne' <;> omega
      exact hcoh.tok_alone t ti hti (hcoh.tok_q t ti hti hr) t' c' hne h' (by rw [hcp])
    · rfl
  have hIk : ∀ q i, InflightAt stk q i ↔ InflightAt st q i ∧ ¬ (p = q ∧ Affects st ti.c i) := by
    intro q i
    constructor
    · rintro ⟨t', c', h1, h2, h3⟩
      have h1' : st.inflight !! t' = some c' ∧ t' ≠ t := by
        change (GMap.delete t st.inflight) !! t' = some c' at h1
        rw [GMap.lookup_delete_iff] at h1; split at h1
        · cases h1
        · rename_i hne; exact ⟨h1, fun e => hne e.symm⟩
      rw [affects_congr1 c' (hsizes t' c' h1'.2 h1'.1)] at h3
      refine ⟨⟨t', c', h1'.1, h2, h3⟩, fun ⟨hp, ha⟩ => ?_⟩
      exact hwf.infl_disj t' c' t ti.c i h1'.1 hct h1'.2 (by rw [h2, hcp, hp]) h3 ha
    · rintro ⟨⟨t', c', h1, h2, h3⟩, hn⟩
      have hne : t' ≠ t := by
        rintro rfl; rw [hct] at h1; cases h1; exact hn ⟨by rw [← h2, hcp], h3⟩
      refine ⟨t', c', ?_, h2, ?_⟩
      · change (GMap.delete t st.inflight) !! t' = some c'
        rw [GMap.lookup_delete_ne _ (Ne.symm hne)]; exact h1
      · rw [affects_congr1 c' (hsizes t' c' hne h1)]; exact h3
  -- the bytes of the file that do not change
  have hsame : ∀ i, ¬ (k ≠ 0 ∧ lo ≤ i ∧ i < off + k) → i < pwSize f.cur.length off k →
      (pwFile f off data k).cur[i]? = f.cur[i]? ∧ i < f.cur.length := by
    intro i hn hi
    rw [pwFile_getElem? _ _ _ _ hk]
    by_cases hk0 : k = 0
    · subst hk0; unfold pwSize at hi; simp only [↓reduceIte] at hi
      refine ⟨?_, hi⟩
      by_cases h1 : i < off
      · simp [h1, hi]
      · simp [h1]
    · have : i < lo ∨ off + k ≤ i := by omega
      unfold pwSize at hi; simp only [hk0, ↓reduceIte] at hi
      rcases this with h | h
      · exact ⟨by simp [show i < off by omega, show i < f.cur.length by omega], by omega⟩
      · exact ⟨by simp [show ¬ i < off by omega, show ¬ i < off + k by omega], by omega⟩
  have hfk : stk.file p = some (pwFile f off data k) := file_setFile_eq _ _ _
  have hfq : ∀ q, q ≠ p → stk.file q = st.file q := fun q hq => file_setFile_ne _ _ (Ne.symm hq)
  have hex : ∀ q f0, st.file q = some f0 → ∃ f1, stk.file q = some f1 := by
    intro q f0 h0
    by_cases hq : q = p
    · subst hq; exact ⟨_, hfk⟩
    · exact ⟨f0, by rw [hfq q hq]; exact h0⟩
  have hdel : ∀ t' c', stk.inflight !! t' = some c' → st.inflight !! t' = some c' ∧ t' ≠ t := by
    intro t' c' h1
    change (GMap.delete t st.inflight) !! t' = some c' at h1
    rw [GMap.lookup_delete_iff] at h1; split at h1
    · cases h1
    · rename_i hne; exact ⟨h1, fun e => hne e.symm⟩
  have hwfk : OsWf stk := by
    refine ⟨fun fd d h => ?_, fun b m h => ?_, hwf.maps_disj, fun t' c' h => ?_,
      fun t1 c1 t2 c2 i h1 h2 hne hp => ?_, fun q f1 h1 => ?_, fun q f1 i h1 => ?_⟩
    · obtain ⟨f0, h0⟩ := hwf.fds fd d h; exact hex _ _ h0
    · obtain ⟨⟨f0, h0⟩, h1, h2, h3⟩ := hwf.maps b m h; exact ⟨hex _ _ h0, h1, h2, h3⟩
    · obtain ⟨f0, h0⟩ := hwf.infl t' c' (hdel t' c' h).1; exact hex _ _ h0
    · obtain ⟨h1, n1⟩ := hdel t1 c1 h1; obtain ⟨h2, n2⟩ := hdel t2 c2 h2
      rw [affects_congr1 c1 (hsizes t1 c1 n1 h1), affects_congr1 c2 (hsizes t2 c2 n2 h2)]
      exact hwf.infl_disj t1 c1 t2 c2 i h1 h2 hne hp
    · by_cases hq : q = p
      · subst hq; rw [hfk] at h1; cases h1
        rw [pwFile_sizeLo _ _ _ _ hk hszf.1, pwFile_sizeHi _ _ _ _ hk hszf.2, hlen]
        unfold pwSize; split <;> omega
      · rw [hfq q hq] at h1; exact hwf.sizes q f1 h1
    · by_cases hq : q = p
      · subst hq; rw [hfk] at h1; cases h1
        intro hd hl hi hdl
        rw [pwFile_durable, pwFile_lost] at *
        have hn : ¬ (k ≠ 0 ∧ lo ≤ i ∧ i < off + k) := by
          intro h; have := (pwFile_dirty f off data k i).2 (.inr h); rw [hd] at this; cases this
        have hd0 : f.dirty i = false := by
          cases h : f.dirty i
          · rfl
          · have := (pwFile_dirty f off data k i).2 (.inl h); rw [hd] at this; cases this
        rw [hlen] at hi
        obtain ⟨he, hil⟩ := hsame i hn hi
        rw [he]
        exact hwf.coherent q f i hf hd0 hl hil hdl
      · rw [hfq q hq] at h1; exact hwf.coherent q f1 i h1
  refine ⟨hsizes, hIk, hwfk, ?_⟩
  have hfp : st.files !! p = some (some f) := file_eq_some.1 hf
  have hysl : ys.length = min (off + data.length) (pwSize f.cur.length off k) - lo := by simp [ys]
  refine ⟨fun q => ?_, fun q => ?_, fun q m' hm => ?_, fun q i x hx => ?_, fun q f1 i h1 hi => ?_,
    hcoh.fds, fun t' => ?_, fun t' ti' h => ?_, fun t' ti' h hq1 => ?_, fun t' ti' h => ?_,
    fun t' ti' h => ?_⟩
  · rw [GMap.lookup_insert_eq_iff]
    show _ ↔ (({ st with inflight := GMap.delete t st.inflight } : OsState).setFile p _).files !! q = none
    rw [files_setFile]; split
    · simp
    · exact hcoh.meta_dom q
  · rw [GMap.lookup_insert_eq_iff]
    show _ ↔ (({ st with inflight := GMap.delete t st.inflight } : OsState).setFile p _).files !! q = some none
    rw [files_setFile]; split
    · simp
    · exact hcoh.meta_none q
  · have htg : ∀ c', (∃ t', stk.inflight !! t' = some c') → c'.target stk = c'.target st := by
      rintro c' ⟨t', h'⟩
      obtain ⟨h1, n1⟩ := hdel t' c' h'
      exact target_congr1 c' (hsizes t' c' n1 h1)
    rw [GMap.lookup_insert_eq_iff] at hm
    split at hm
    · rename_i hpq; subst hpq; cases hm
      refine ⟨pwFile f off data k, file_eq_some.1 hfk, ⟨by rw [hlen], by rw [pwFile_named, hmo.named],
        by rw [pwFile_sizeLo _ _ _ _ hk hszf.1]; exact hmo.lo, ?_, fun hok i => by
          rw [pwFile_lost]; exact hmo.ok hok i, hmo.maps, fun t' c' h1 h2 => ?_,
          fun i d h => by rw [pwFile_durable]; exact hmo.dur i d h, ?_⟩⟩
      · rw [pwFile_sizeHi _ _ _ _ hk hszf.2]
        have ht1 := hmo.targets t ti.c hct hcp
        have ht2 := hmo.hi
        rw [hc] at ht1; simp only [OsChange.target, hsz] at ht1
        unfold pwSize; split <;> simp only [Nat.max_le] at * <;> omega
      · rw [htg c' ⟨t', h1⟩]; exact hmo.targets t' c' (hdel t' c' h1).1 h2
      · rw [pwFile_durable]; exact hmo.durLen
    · rename_i hpq
      obtain ⟨f1, h1, hm1⟩ := hcoh.meta_some q m' hm
      refine ⟨f1, ?_, ⟨hm1.size, hm1.named, hm1.lo, hm1.hi, hm1.ok, hm1.maps, fun t' c' h1 h2 => ?_,
        hm1.dur, hm1.durLen⟩⟩
      · show (({ st with inflight := GMap.delete t st.inflight } : OsState).setFile p _).files !! q = _
        rw [files_setFile, if_neg hpq]; exact h1
      · rw [htg c' ⟨t', h1⟩]; exact hm1.targets t' c' (hdel t' c' h1).1 h2
  · rw [lookup_insertBytes] at hx
    split at hx
    · rename_i hr
      obtain ⟨rfl, h1, h2⟩ := hr
      rw [hysl] at h2
      have hj : i - lo < ys.length := by rw [hysl]; omega
      rw [List.getElem?_eq_getElem hj] at hx; cases hx
      refine ⟨_, hfk, ?_, fun h => ?_⟩
      · rw [pwFile_inside f off data k hk xs hxslen hxsv i h1 (by omega), if_pos (by omega)]
        simp [ys, show lo + (i - lo) = i by omega]; rfl
      · simp only [ys, List.getElem_map, List.getElem_range, Bool.and_eq_true,
          decide_eq_true_eq] at h
        obtain ⟨hge, hcl1⟩ := h
        rw [List.getD_eq_getElem?_getD] at hcl1
        cases hx' : xs[i - lo]? with
        | none => rw [hx'] at hcl1; cases hcl1
        | some x =>
          rw [hx'] at hcl1
          have hclj : ti.cl[i - lo]? = some true := by
            rw [hcl, List.getElem?_map, hx']; simp only [Option.map_some, Option.getD_some] at hcl1 ⊢
            rw [hcl1]
          obtain ⟨-, f2, hf2, hcp2⟩ := hcoh.tok_clean t ti hti _ hclj
          rw [hcp, hf] at hf2; cases hf2
          have hlo' : affLo st ti.c = lo := by rw [hc]; simp [affLo, hsz, lo]
          rw [hlo', show lo + (i - lo) = i by omega] at hcp2
          obtain ⟨c1, c2, c3, c4⟩ := hcp2
          have hil : i < f.cur.length := by have := hszf.1; omega
          have hn : ¬ (k ≠ 0 ∧ lo ≤ i ∧ i < off + k) := by omega
          have he := (hsame i hn (by unfold pwSize; split <;> omega)).1
          refine ⟨⟨?_, by rw [pwFile_lost]; exact c2, by rw [pwFile_sizeLo _ _ _ _ hk hszf.1]; exact c3,
            by rw [pwFile_durable, he]; exact c4⟩,
            fun hI => ((hIk _ _).1 hI).2 ⟨rfl, (haff i).2 ⟨h1, ?_⟩⟩⟩
          · cases hd : (pwFile f off data k).dirty i
            · rfl
            · rcases (pwFile_dirty f off data k i).1 hd with h | h
              · rw [c1] at h; cases h
              · exact absurd h hn
          · unfold pwSize at h2; split at h2 <;> omega
    · rename_i hr
      obtain ⟨f1, h1, hb, hcl⟩ := hcoh.bytes q i x hx
      by_cases hq : q = p
      · subst hq; rw [hf] at h1; cases h1
        have hil : i < f.cur.length := (List.getElem?_eq_some_iff.1 hb).1
        have hout : i < lo ∨ off + data.length ≤ i := by
          rw [hysl] at hr; simp only [_root_.true_and, not_and, Nat.not_lt] at hr
          unfold pwSize at hr; split at hr <;> omega
        have he := pwFile_outside f off data k hk i hout
        refine ⟨_, hfk, by rw [he]; exact hb, fun hx2 => ?_⟩
        obtain ⟨⟨c1, c2, c3, c4⟩, c5⟩ := hcl hx2
        refine ⟨⟨?_, by rw [pwFile_lost]; exact c2, by rw [pwFile_sizeLo _ _ _ _ hk hszf.1]; exact c3,
          by rw [pwFile_durable, he]; exact c4⟩, fun h => c5 ((hIk _ _).1 h).1⟩
        cases hd : (pwFile f off data k).dirty i
        · rfl
        · rcases (pwFile_dirty f off data k i).1 hd with h | ⟨-, h⟩
          · rw [c1] at h; cases h
          · omega
      · refine ⟨f1, by rw [hfq q hq]; exact h1, hb, fun hx2 => ?_⟩
        obtain ⟨c1, c2⟩ := hcl hx2
        exact ⟨c1, fun h => c2 ((hIk _ _).1 h).1⟩
  · rw [lookup_insertBytes]
    split
    · rename_i hr; rw [List.getElem?_eq_getElem (by omega)]; rfl
    · rename_i hr
      by_cases hq : q = p
      · subst hq; rw [hfk] at h1; cases h1
        rw [hlen] at hi
        have hn : ¬ (k ≠ 0 ∧ lo ≤ i ∧ i < off + k) := by
          rw [hysl] at hr; simp only [_root_.true_and, not_and, Nat.not_lt] at hr
          unfold pwSize at hr hi; split at hr <;> omega
        exact hcoh.bytes_full q f i hf (hsame i hn hi).2
      · rw [hfq q hq] at h1; exact hcoh.bytes_full q f1 i h1 hi
  · show (GMap.delete t Γt !! t').map TokInfo.c = (GMap.delete t st.inflight) !! t'
    rw [GMap.lookup_delete_iff, GMap.lookup_delete_iff]; split
    · rfl
    · exact hcoh.toks t'
  · rw [GMap.lookup_delete_iff] at h; split at h
    · cases h
    · rename_i hne
      have h' : st.inflight !! t' = some ti'.c := by
        have := hcoh.toks t'; rw [h] at this; exact this.symm
      rw [reaches_congr1 ti'.c (hsizes t' ti'.c (fun e => hne e.symm) h')]
      exact hcoh.tok_q t' ti' h
  · intro t'' c'' hne h''
    rw [GMap.lookup_delete_iff] at h; split at h
    · cases h
    · exact hcoh.tok_alone t' ti' h hq1 t'' c'' hne (hdel t'' c'' h'').1
  · rw [GMap.lookup_delete_iff] at h; split at h
    · cases h
    · rename_i hne
      have h' : st.inflight !! t' = some ti'.c := by
        have := hcoh.toks t'; rw [h] at this; exact this.symm
      have hne' : t' ≠ t := fun e => hne e.symm
      obtain ⟨f1, h1, hsv1⟩ := hcoh.tok_saved t' ti' h
      rw [affRange_congr1 ti'.c (hsizes t' ti'.c hne' h')]
      by_cases hq : ti'.c.path = p
      · rw [hq] at h1 ⊢; rw [hf] at h1; cases h1
        refine ⟨_, hfk, ?_⟩
        rw [hsv1]
        apply List.map_congr_left
        intro i hi
        have hil : i < f.cur.length := by
          have := List.mem_range'_1.1 hi
          have : affHi st ti'.c ≤ f.cur.length := by
            unfold affHi; rw [hq, hsz]; split <;> omega
          omega
        have ha : Affects st ti'.c i := (affects_iff_affRange st ti'.c i f (by rw [hq]; exact hf) hil).2 hi
        have hna := hwf.infl_disj t' ti'.c t ti.c i h' hct hne' (by rw [hq, hcp]) ha
        rw [haff] at hna
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          pwFile_outside f off data k hk i (by omega)]
      · exact ⟨f1, by rw [hfq _ hq]; exact h1, hsv1⟩
  · rw [GMap.lookup_delete_iff] at h; split at h
    · cases h
    · rename_i hne
      intro j hj
      have h' : st.inflight !! t' = some ti'.c := by
        have := hcoh.toks t'; rw [h] at this; exact this.symm
      have hne' : t' ≠ t := fun e => hne e.symm
      have hs' := hsizes t' ti'.c hne' h'
      obtain ⟨hjl, f1, h1, hcp1⟩ := hcoh.tok_clean t' ti' h j hj
      have hlo1 : affLo stk ti'.c = affLo st ti'.c := by unfold affLo; rw [hs']
      have hhi1 : affHi stk ti'.c = affHi st ti'.c := by unfold affHi; rw [hs']
      rw [hlo1, hhi1]
      refine ⟨hjl, ?_⟩
      by_cases hq : ti'.c.path = p
      · rw [hq] at h1 ⊢; rw [hf] at h1; cases h1
        refine ⟨_, hfk, ?_⟩
        obtain ⟨c1, c2, c3, c4⟩ := hcp1
        have hil : affLo st ti'.c + j < f.cur.length := by have := hszf.1; omega
        have hmem : affLo st ti'.c + j ∈ affRange st ti'.c := by
          unfold affRange; exact List.mem_range'_1.2 ⟨by omega, by omega⟩
        have ha : Affects st ti'.c (affLo st ti'.c + j) :=
          (affects_iff_affRange st ti'.c _ f (by rw [hq]; exact hf) hil).2 hmem
        have hna := hwf.infl_disj t' ti'.c t ti.c _ h' hct hne' (by rw [hq, hcp]) ha
        rw [haff] at hna
        have hout : affLo st ti'.c + j < lo ∨ off + data.length ≤ affLo st ti'.c + j := by omega
        have he := pwFile_outside f off data k hk _ hout
        refine ⟨?_, by rw [pwFile_lost]; exact c2, by rw [pwFile_sizeLo _ _ _ _ hk hszf.1]; exact c3,
          by rw [pwFile_durable, he]; exact c4⟩
        cases hd : (pwFile f off data k).dirty (affLo st ti'.c + j)
        · rfl
        · rcases (pwFile_dirty f off data k _).1 hd with h | ⟨-, h⟩
          · rw [c1] at h; cases h
          · omega
      · exact ⟨f1, by rw [hfq _ hq]; exact h1, hcp1⟩

theorem setFile_self {st : OsState} {p : GoString} {f : OsFile} (h : st.file p = some f) :
    st.setFile p f = st := by
  have hfp := file_eq_some.1 h
  have : <[p := some f]> st.files = st.files := by
    apply GMap.ext; intro k
    show (<[p := some f]> st.files) !! k = st.files !! k
    rw [GMap.lookup_insert_eq_iff]; split
    · subst_vars; exact hfp.symm
    · rfl
  cases st; simp only [OsState.setFile] at this ⊢; rw [this]

theorem pwFinish_state (st : OsState) (t : Nat) (p : GoString) (off : Nat) (data : List w8)
    (f : OsFile) (k : Nat) (hf : st.file p = some f) :
    (if k = 0 then ({ st with inflight := GMap.delete t st.inflight } : OsState) else
      ({ st with inflight := GMap.delete t st.inflight } : OsState).setFile p
        (f.change (writeBytes f.cur off (data.take k)) (min off f.cur.length) (off + k))) =
    ({ st with inflight := GMap.delete t st.inflight } : OsState).setFile p (pwFile f off data k) := by
  unfold pwFile
  split
  · exact (setFile_self (st := { st with inflight := GMap.delete t st.inflight }) hf).symm
  · rfl

theorem insertBytes_append (p : GoString) : ∀ (off : Nat) (xs ys : List (w8 × Bool))
    (m : GMap (GoString × Nat) (w8 × Bool)),
    insertBytes p off (xs ++ ys) m = insertBytes p (off + xs.length) ys (insertBytes p off xs m)
  | off, [], ys, m => by simp [insertBytes]
  | off, x :: xs, ys, m => by
    simp only [List.cons_append, insertBytes, List.length_cons]
    rw [insertBytes_append p (off + 1) xs ys, show off + 1 + xs.length = off + (xs.length + 1) by omega]

end finish

section specs2
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt] [GoGlobalContext]
  [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}
attribute [local instance] Classical.propDecidable

/-- The bytes `[min off sz, min (off + n) (pwSize sz off k))` after a `pwrite` of the first `k`
bytes of `data` (`n` bytes) at `off` of a file of size `sz`, whose bytes there were `xs`. A byte
past `off + k` is untouched and keeps its flag from `xs`; the others are not clean. -/
def pwBytes (sz off : Nat) (data : List w8) (k : Nat) (xs : List (w8 × Bool)) : List (w8 × Bool) :=
  (List.range (min (off + data.length) (pwSize sz off k) - min off sz)).map
    (fun j => (pwByte off data k (min off sz) xs (min off sz + j),
      decide (off + k ≤ min off sz + j) && (xs.getD j (0, false)).2))

/-- What a mapped cell at byte `i` shows after such a `pwrite`. -/
def pwCell (sz off : Nat) (data : List w8) (k : Nat) (xs : List (w8 × Bool)) (i : Nat) : val :=
  toCellVal (if i < pwSize sz off k then some (pwByte off data k (min off sz) xs i) else none)

/-- The second step of `pwrite(fd, data, off)`: it writes the first `k` bytes of `data`, all of
them with errno 0, or a prefix with a nonzero errno. What the first step took comes back: the
`OsMeta` with the new size, the bytes `[min off size, min (off + n) size')` (the zero gap, the data
written, then the old bytes), the bytes past the written prefix with the clean flags they had in
`xs` (the write left them untouched), the others not clean, and the client's halves of the mapped cells, which show
the new bytes. -/
theorem wp_osPWriteFinish (t : Nat) (p : GoString) (off : Nat) (data : List w8) (q : Qp)
    (m : OsMeta) (xs : List (w8 × Bool)) (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ pwTok (L := L) t p off data q m xs -∗
      (∀ k : Nat, ∀ e : w64, ⌜k ≤ data.length ∧ (k = data.length ∧ e = 0 ∨ e ≠ 0)⌝ -∗
        osMeta (L := L) p (DFrac.own q)
          (some { pwMeta m off data.length with size := pwSize m.size off k }) -∗
        osBytes (L := L) p (min off m.size) (DFrac.own 1) (pwBytes m.size off data k xs) -∗
        mcells m.maps (min off m.size) (off + data.length) (pwCell m.size off data k xs) -∗
        Φ (PairV (#(W64 k)) (#e))) -∗
      WP (ExternalOp osFsExt.name "PWriteFinish" (Val (osTokV t))) @ s; E {{ Φ }} := by
  iintro #Hinv Ht HΦ
  iapply wp_os_step "PWriteFinish" _ Φ (by simp [val.isPanic]) hE $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %h Hw
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  unfold pwTok osTok
  generalize hti0 : (⟨⟨p, .write off data⟩, q, xs.map Prod.fst, pwMeta m off data.length, xs.map Prod.snd⟩ :
    TokInfo) = ti
  icases gAuth_lookup _ _ _ _ _ _ $$ HAt Ht with %Hti
  have hct : st.inflight !! t = some ti.c := by
    have := hcoh.toks t; rw [Hti] at this; exact this.symm
  have hc : ti.c = ⟨p, .write off data⟩ := by rw [← hti0]
  obtain ⟨f, hf, -⟩ := hcoh.tok_saved t ti Hti
  rw [hc] at hf; simp only at hf
  unfold tokRes
  icases (BigSepM.bigSepM_delete (Φ := fun (_t : Nat) (ti : TokInfo) =>
      iprop(gElem gooseOsGS gooseOsGS.γm ti.c.path (DFrac.own ti.q) (some ti.om) ∗
        bytesG gooseOsGS ti.c.path (affLo st ti.c) (DFrac.own 1) (ti.saved.map (·, false))))
      Hti).1 $$ Htok with ⟨⟨Hm, Hbs⟩, Htok⟩
  icases gAuth_lookup _ _ _ _ _ _ $$ HAm Hm with %Hml
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hcp : ti.c.path = p := by rw [hc]
  rw [hcp] at Hml
  obtain ⟨f1, hf1, hmo⟩ := coh_meta hcoh Hml
  rw [hf] at hf1; cases hf1
  have hmsz : m.size = f.cur.length := by
    have := hmo.size; rw [← hti0] at this; simpa [pwMeta] using this
  have hsz := size_of_file hf
  have Hh : ∀ l, Mapped st l → (h !! l).isSome := by
    intro l hm
    obtain ⟨x, hx⟩ := cellView_isSome hwf hm
    obtain ⟨m0, hm0⟩ := Hag l x hx
    rw [hm0]; rfl
  have hxs : ti.saved = xs.map Prod.fst := by rw [← hti0]
  have hfin := fun k (hk : k ≤ data.length) =>
    pwFinish_coh (k := k) hwf hcoh Hti hc hf hk Hml xs hxs (by rw [← hti0])
  imodintro
  isplitr
  · ipureintro
    obtain ⟨-, -, hwfk, -⟩ := hfin data.length (Nat.le_refl _)
    refine ⟨_, renderHeap (({ st with inflight := GMap.delete t st.inflight } : OsState).setFile p
      (pwFile f off data data.length)) h, _, ⟨t, p, off, data, f, data.length, 0, rfl,
      by rw [hct, hc], hf, Nat.le_refl _, .inl ⟨rfl, rfl⟩, rfl, rfl⟩, ?_, ?_⟩
    · exact mapsFresh_same (by rw [pwFinish_state st t p off data f _ hf]; rfl)
    · rw [pwFinish_state st t p off data f _ hf]
      exact heapRendered_render hwfk rfl Hh
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsOsStep] at Hst
  obtain ⟨t', p', off', data', f', k, e, hv, hinfl, hf', hk, hke, hst', rfl⟩ := Hst
  have htt : t' = t := by injection hv with hv; exact (extVal_inj hv).symm
  subst htt
  rw [hct, hc] at hinfl; cases hinfl
  rw [hf] at hf'; cases hf'
  rw [pwFinish_state st t' p off data f k hf] at hst'
  subst hst'
  obtain ⟨hsizes, hIk, hwfk, hcohk⟩ := hfin k hk
  -- the meta
  have hq1 : q ≠ 1 → ({ pwMeta m off data.length with size := pwSize m.size off k } : OsMeta) =
      pwMeta m off data.length := by
    intro hq1
    have hnr : ¬ Reaches st ti.c := fun hr => hq1 (by
      have := hcoh.tok_q t' ti Hti hr; rw [← hti0] at this; exact this)
    rw [hc] at hnr; simp only [Reaches, hsz, Nat.not_lt] at hnr
    have : pwSize m.size off k = m.size := by unfold pwSize; split <;> omega
    rw [this]; rfl
  have hti_q : ti.q = q := by rw [← hti0]
  have hti_om : ti.om = pwMeta m off data.length := by rw [← hti0]
  have eqm : gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γm ti.c.path (DFrac.own ti.q) (some ti.om) ⊢
      gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γm p (DFrac.own q) (some (pwMeta m off data.length)) := by
    rw [hcp, hti_q, hti_om]
  ihave Hm := eqm $$ Hm
  imod meta_replace _ (om := { pwMeta m off data.length with size := pwSize m.size off k }) hq1
    $$ [HAm Hm] with ⟨HAm, Hm⟩
  · iframe
  -- the bytes
  have hlo : affLo st ti.c = min off m.size := by rw [hc, hmsz]; simp [affLo, hsz]
  have hxsl : xs.length = min (off + data.length) m.size - min off m.size := by
    obtain ⟨f2, hf2, hsv⟩ := hcoh.tok_saved t' ti Hti
    have := congrArg List.length hsv
    rw [hxs] at this; simp only [List.length_map, affRange, List.length_range'] at this
    rw [this, hc, hmsz]; simp [affHi, affLo, hsz]
  have eqb : bytesG (gooseOsGS (L := L)) ti.c.path (affLo st ti.c) (DFrac.own 1)
      (ti.saved.map (·, false)) ⊢
      bytesG (gooseOsGS (L := L)) p (min off m.size) (DFrac.own 1) (xs.map (fun x => (x.1, false))) := by
    rw [hcp, hlo, hxs, List.map_map]; exact .rfl
  ihave Hbs := eqb $$ Hbs
  icases bytesG_lookup _ p _ _ _ Γb $$ HAb Hbs with %Hbl
  have hxsv : ∀ j (hj : j < xs.length), f.cur[min off f.cur.length + j]? = some xs[j].1 := by
    intro j hj
    obtain ⟨f2, hf2, hb, -⟩ := hcoh.bytes _ _ _ (Hbl j (by simpa using hj))
    rw [hf] at hf2; cases hf2
    rw [← hmsz]; simpa using hb
  have hpw : pwBytes m.size off data k xs =
      (pwBytes m.size off data k xs).take xs.length ++ (pwBytes m.size off data k xs).drop xs.length :=
    (List.take_append_drop _ _).symm
  have hpwl : (pwBytes m.size off data k xs).length =
      min (off + data.length) (pwSize m.size off k) - min off m.size := by simp [pwBytes]
  have hl1 : ((pwBytes m.size off data k xs).take xs.length).length = xs.length := by
    rw [List.length_take, hpwl, hxsl]; unfold pwSize; split <;> omega
  imod bytesG_update _ p (min off m.size) (xs.map (fun x => (x.1, false)))
    ((pwBytes m.size off data k xs).take xs.length) Γb
    (by rw [hl1]; try simp) $$ [HAb Hbs] with ⟨HAb, Hbs1⟩
  · iframe
  imod bytesG_alloc _ p (min off m.size + xs.length) ((pwBytes m.size off data k xs).drop xs.length)
    _ (fun j hj => by
      rw [lookup_insertBytes, if_neg (by rw [hl1]; omega)]
      cases hb : Γb !! (p, min off m.size + xs.length + j) with
      | none => rfl
      | some x =>
        exfalso
        obtain ⟨f2, hf2, hb2, -⟩ := hcoh.bytes _ _ _ hb
        rw [hf] at hf2; cases hf2
        have := (List.getElem?_eq_some_iff.1 hb2).1
        simp only [List.length_drop, hpwl] at hj
        rw [hxsl, ← hmsz] at this; unfold pwSize at hj; split at hj <;> omega) $$ HAb with ⟨HAb, Hbs2⟩
  have hins : insertBytes p (min off m.size + xs.length) ((pwBytes m.size off data k xs).drop xs.length)
      (insertBytes p (min off m.size) ((pwBytes m.size off data k xs).take xs.length) Γb) =
      insertBytes p (min off m.size) (pwBytes m.size off data k xs) Γb := by
    conv => rhs; rw [hpw]
    rw [insertBytes_append, hl1]
  rw [hins]
  ihave Hbs := (bytesG_append _ p _ (min off m.size) ((pwBytes m.size off data k xs).take xs.length)
    ((pwBytes m.size off data k xs).drop xs.length)).2 $$ [Hbs1 Hbs2]
  · rw [hl1]; iframe
  rw [← hpw]
  -- the token
  imod gAuth_delete _ _ _ _ _ $$ HAt Ht with HAt
  -- the cells
  have hmaps : ti.om.maps = m.maps := by rw [hti_om]; rfl
  have hdisj : MapsDisj m.maps.toList := mapsDisj_toList _ (fun b1 l1 b2 l2 h1 h2 hne =>
    hwf.maps_disj b1 _ b2 _ ((hmo.maps b1 l1).1 (hmaps ▸ h1)) ((hmo.maps b2 l2).1 (hmaps ▸ h2)) hne)
  have haff : ∀ i, Affects st ti.c i ↔ min off m.size ≤ i ∧ i < off + data.length := by
    intro i; rw [hc, hmsz]; simp [Affects, inRange, hsz]
  generalize hC : mapsCells (min off m.size) (off + data.length) (pwCell m.size off data k xs)
    m.maps.toList = C
  have hClk := fun l v => hC ▸ lookup_mapsCells (min off m.size) (off + data.length)
    (pwCell m.size off data k xs) m.maps.toList hdisj l v
  have hTmem : ∀ l, l ∈ C.toList.map (·.1) ↔ (C !! l).isSome := by
    intro l; simp only [List.mem_map]
    constructor
    · rintro ⟨⟨k, v⟩, hkv, rfl⟩; rw [(GMap.mem_toList _ _ _).1 hkv]; rfl
    · intro hl; obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hl
      exact ⟨(l, v), (GMap.mem_toList _ _ _).2 hv, rfl⟩
  have hTnd : (C.toList.map (·.1)).Nodup := Iris.Std.LawfulFiniteMap.toList_noDupKeys (m := C)
  have hin : ∀ l, (C !! l).isSome → ∃ i, MapsTo st l p i ∧ Affects st ti.c i ∧
      C !! l = some (pwCell m.size off data k xs i) := by
    intro l hl
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hl
    obtain ⟨i, ⟨b, len, hm, h1, h2, h3, rfl⟩, rfl⟩ := (hClk _ v).1 hv
    exact ⟨i, ⟨b, ⟨p, len⟩, (hmo.maps b len).1 (hmaps ▸ (GMap.mem_toList _ _ _).1 hm), rfl, h3, rfl⟩,
      (haff i).2 ⟨h1, h2⟩, hv⟩
  have hfk : (({ st with inflight := GMap.delete t' st.inflight } : OsState).setFile p
      (pwFile f off data k)).file p = some (pwFile f off data k) := file_setFile_eq _ _ _
  imod cells_step st _ h h' (C.toList.map (·.1)) ∅ C hwf hwfk Hr Hfr (fun b m0 h0 => .inr h0) hTnd
    (fun l hl => by obtain ⟨i, hi, -⟩ := hin l ((hTmem l).1 hl); exact .inl ⟨_, _, hi⟩)
    (fun l v h => by simp at h)
    (fun l v hl => by
      have hs : (C !! l).isSome := by rw [hl]; rfl
      obtain ⟨i, hi, ha, hv⟩ := hin l hs
      rw [hl] at hv; cases hv
      have hn : ¬ InflightAt (({ st with inflight := GMap.delete t' st.inflight } : OsState).setFile p
          (pwFile f off data k)) p i := fun h => ((hIk _ _).1 h).2 ⟨rfl, ha⟩
      refine ⟨(hTmem l).2 hs, _, by rw [cellView_mapsTo hwfk hi, decide_eq_false hn], ?_⟩
      rw [cellByte_eq, if_neg hn, hfk]
      simp only [Option.bind_some]
      obtain ⟨h1, h2⟩ := (haff i).1 ha
      rw [hmsz] at h1 ⊢
      rw [pwFile_inside f off data k hk xs (by rw [← hmsz]; exact hxsl) hxsv i h1 h2]; rfl)
    (fun l hl _ x hx => by
      obtain ⟨i, hi, ha, -⟩ := hin l ((hTmem l).1 hl)
      rw [cellView_mapsTo hwf hi] at hx; cases hx
      exact decide_eq_true ⟨t', ti.c, hct, hcp, ha⟩)
    (fun l hl hn => by
      rw [Option.isSome_iff_exists.1 ((hTmem l).1 hl) |>.choose_spec] at hn; cases hn)
    (fun l hl => by
      by_cases hm : Mapped st l
      · obtain ⟨q', i, hqi⟩ := hm
        rw [cellView_mapsTo hwfk hqi, cellView_mapsTo hwf hqi, cellByte_eq, cellByte_eq]
        have hn : ¬ (p = q' ∧ Affects st ti.c i) := by
          rintro ⟨rfl, ha⟩
          obtain ⟨b, m0, hb, hp0, hi0, rfl⟩ := hqi
          have hb' : m.maps !! b = some m0.len := by
            rw [← hmaps, hmo.maps b m0.len, hb]; congr 1; cases m0; simp only at hp0 ⊢; rw [hp0]
          apply hl; apply (hTmem _).2
          obtain ⟨h1, h2⟩ := (haff i).1 ha
          rw [(hClk _ _).2 ⟨i, ⟨b, m0.len, (GMap.mem_toList _ _ _).2 hb', h1, h2, hi0, rfl⟩, rfl⟩]
          rfl
        have hII := hIk q' i
        have hII' : InflightAt (({ st with inflight := GMap.delete t' st.inflight } : OsState).setFile p
            (pwFile f off data k)) q' i ↔ InflightAt st q' i := by
          rw [hII]; constructor
          · exact fun h => h.1
          · intro h; refine ⟨h, hn⟩
        simp only [hII']
        congr 2
        by_cases hpq : p = q'
        · subst hpq; rw [hfk, hf]
          simp only [Option.bind_some]
          by_cases hI : InflightAt st p i
          · simp [hI]
          · have : ¬ Affects st ti.c i := fun ha => hn ⟨rfl, ha⟩
            rw [haff] at this
            rw [pwFile_outside f off data k hk i (by rw [← hmsz]; omega)]
        · rw [file_setFile_ne _ _ hpq]; rfl
      · rw [cellView_none (st := st) hm]; exact cellView_none hm)
    $$ [Hσ Hcells] with ⟨Hσ, Hcells, Hc⟩
  · iframe; unfold halves; iapply BigSepM.bigSepM_empty.2; iempintro
  imodintro
  iexists _, _, Γf, _
  iframe HAb HAm HAf HAt Hσ Hcells
  isplitl [Htok]
  · isplitr
    · ipureintro
      rw [show min off f.cur.length = min off m.size by rw [hmsz]] at hcohk
      rw [hti_om, show pwSize f.cur.length off k = pwSize m.size off k by rw [hmsz]] at hcohk
      have hpb : (List.range (min (off + data.length) (pwSize m.size off k) - min off m.size)).map
          (fun j => (pwByte off data k (min off m.size) xs (min off m.size + j),
            decide (off + k ≤ min off m.size + j) && (xs.getD j (0, false)).2)) =
          pwBytes m.size off data k xs := rfl
      rw [hpb] at hcohk
      exact ⟨hwfk, hcohk⟩
    have htc := tokRes_congr (gooseOsGS (L := L)) (st := st)
      (st' := ({ st with inflight := GMap.delete t' st.inflight } : OsState).setFile p
        (pwFile f off data k)) (Γt := GMap.delete t' Γt) (fun t2 ti2 h2 => by
      rw [GMap.lookup_delete_iff] at h2; split at h2
      · cases h2
      · rename_i hne
        have h2' : st.inflight !! t2 = some ti2.c := by
          have := hcoh.toks t2; rw [h2] at this; exact this.symm
        exact hsizes t2 ti2.c (fun e => hne e.symm) h2')
    unfold tokRes at htc
    iapply htc $$ Htok
  iapply wp_value'
  unfold osMeta osBytes
  iapply HΦ $$ %k %e %(And.intro hk hke) Hm Hbs
  unfold mcells
  iapply (BigSepM.bigSepM_toList (Φ := fun (b : Loc) (len : Nat) =>
    cellsR b (min (min off m.size) len) (min (off + data.length) len - min (min off m.size) len)
      (pwCell m.size off data k xs))).2
  iapply (halves_mapsCells _ _ _ _ hdisj).1
  rw [hC]; iexact Hc

end specs2

/-! ## Repeated writes (a retried `pwrite`) -/

theorem pwSize_pwSize (sz off j k : Nat) :
    pwSize (pwSize sz off j) off k = pwSize sz off (max j k) := by
  unfold pwSize
  by_cases hj : j = 0 <;> by_cases hk : k = 0 <;> simp [hj, hk] <;> omega

theorem pwBytes_length (sz off : Nat) (data : List w8) (k : Nat) (xs : List (w8 × Bool)) :
    (pwBytes sz off data k xs).length = min (off + data.length) (pwSize sz off k) - min off sz := by
  simp [pwBytes]

theorem pwBytes_getElem (sz off : Nat) (data : List w8) (k : Nat) (xs : List (w8 × Bool)) (i : Nat)
    (hi : i < (pwBytes sz off data k xs).length) :
    ((pwBytes sz off data k xs)[i]).1 = pwByte off data k (min off sz) xs (min off sz + i) := by
  simp [pwBytes]

/-- Before any write, the bytes of the range are the client's. -/
theorem pwBytes_zero (sz off : Nat) (data : List w8) (xs : List (w8 × Bool))
    (hlen : xs.length = min (off + data.length) sz - min off sz) :
    (pwBytes sz off data 0 xs).map Prod.fst = xs.map Prod.fst := by
  apply List.ext_getElem
  · simp [pwBytes, pwSize, hlen]
  · intro i h1 h2
    simp only [List.getElem_map]
    rw [pwBytes_getElem _ _ _ _ _ _ (by simpa using h1)]
    simp only [List.length_map] at h2
    unfold pwByte
    rw [if_neg (by omega), if_neg (by omega), List.getD_eq_getElem?_getD,
      show min off sz + i - min off sz = i by omega, List.getElem?_eq_getElem h2]; rfl

/-- A write of `k` bytes over the file a write of `j` bytes left: the file a write of `max j k`
bytes leaves. The bytes of the range: those before the second write's range (the first's zero
gap), then what the second wrote over the first. -/
theorem pwBytes_retry (sz off : Nat) (data : List w8) (j k : Nat) (xs ys : List (w8 × Bool))
    (hj : j ≤ data.length) (hk : k ≤ data.length)
    (hlen : xs.length = min (off + data.length) sz - min off sz)
    (hys : ys.map Prod.fst = (pwBytes sz off data j xs).map Prod.fst) :
    (ys.take (min off (pwSize sz off j) - min off sz) ++
      pwBytes (pwSize sz off j) off data k (ys.drop (min off (pwSize sz off j) - min off sz))).map
        Prod.fst = (pwBytes sz off data (max j k) xs).map Prod.fst := by
  have hyl : ys.length = min (off + data.length) (pwSize sz off j) - min off sz := by
    have := congrArg List.length hys; simp only [List.length_map, pwBytes_length] at this; exact this
  have hsz : sz ≤ pwSize sz off j := by unfold pwSize; split <;> omega
  have hval : ∀ i (hi : i < ys.length), ys[i].1 = pwByte off data j (min off sz) xs (min off sz + i) := by
    intro i hi
    have := congrArg (·[i]?) hys
    simp only [List.getElem?_map, List.getElem?_eq_getElem hi,
      List.getElem?_eq_getElem (show i < (pwBytes sz off data j xs).length by
        rw [pwBytes_length]; omega), Option.map_some, Option.some.injEq] at this
    rw [this, pwBytes_getElem]
  apply List.ext_getElem
  · simp only [List.length_map, List.length_append, List.length_take, pwBytes_length, hyl,
      pwSize_pwSize]
    unfold pwSize; split <;> split <;> omega
  · intro i h1 h2
    simp only [List.getElem_map]
    rw [pwBytes_getElem _ _ _ _ _ _ (by simpa using h2)]
    simp only [List.length_map, List.length_append, List.length_take] at h1
    rw [List.getElem_append]
    split
    · rename_i hlt
      simp only [List.length_take] at hlt
      rw [List.getElem_take, hval i (by omega)]
      unfold pwByte
      rw [if_pos (by unfold pwSize at *; split at hlt <;> omega),
        if_pos (by unfold pwSize at *; split at hlt <;> omega)]
    · rename_i hlt
      simp only [List.length_take, Nat.not_lt] at hlt
      have hlo : min off sz ≤ min off (pwSize sz off j) := by omega
      have hmin : min (min off (pwSize sz off j) - min off sz) ys.length =
          min off (pwSize sz off j) - min off sz := by rw [hyl]; omega
      rw [hmin] at hlt h1
      simp only [List.length_take, hmin]
      rw [pwBytes_getElem _ _ _ _ _ _ (by omega)]
      rw [show min off (pwSize sz off j) + (i - (min off (pwSize sz off j) - min off sz)) =
        min off sz + i by omega]
      unfold pwByte
      by_cases c1 : min off sz + i < off
      · rw [if_pos c1, if_pos c1]
      · rw [if_neg c1, if_neg c1]
        by_cases c2 : min off sz + i < off + k
        · rw [if_pos c2, if_pos (by omega)]
        · rw [if_neg c2]
          rw [List.getD_eq_getElem?_getD, List.getElem?_drop,
            show min off (pwSize sz off j) - min off sz + (min off sz + i - min off (pwSize sz off j))
              = i by omega]
          have hi : i < ys.length := by
            simp only [List.length_map, pwBytes_length] at h2
            rw [hyl]; unfold pwSize at h2 ⊢; split at h2 <;> split <;> omega
          rw [List.getElem?_eq_getElem hi]
          simp only [Option.getD_some]
          rw [hval i hi]
          unfold pwByte
          rw [if_neg c1]
          by_cases c3 : min off sz + i < off + j
          · rw [if_pos c3, if_pos (by omega)]
          · rw [if_neg c3, if_neg (by omega)]

section specs3
variable [GooseExts] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : NaHeapGS Loc val GF]

theorem cellsR_append (b : Loc) (lo n1 n2 : Nat) (vf : Nat → val) :
    cellsR (GF := GF) b lo (n1 + n2) vf ⊣⊢ cellsR b lo n1 vf ∗ cellsR b (lo + n1) n2 vf := by
  unfold cellsR
  rw [← List.range'_append_1]
  exact BigSepL.bigSepL_append

theorem cellsR_congr (b : Loc) (lo n : Nat) (vf vf' : Nat → val)
    (h : ∀ i, lo ≤ i → i < lo + n → vf i = vf' i) :
    cellsR (GF := GF) b lo n vf ⊣⊢ cellsR b lo n vf' := by
  unfold cellsR
  have hm : ∀ {k x}, (List.range' lo n)[k]? = some x → lo ≤ x ∧ x < lo + n :=
    fun hk => List.mem_range'_1.1 (List.mem_of_getElem? hk)
  constructor
  · apply BigSepL.bigSepL_mono; intro k x hk; rw [h x (hm hk).1 (hm hk).2]
  · apply BigSepL.bigSepL_mono; intro k x hk; rw [h x (hm hk).1 (hm hk).2]

/-- The client's halves of the cells of one mapping over `[lo, hi)`, cut at its length. -/
theorem cellsR_split (b : Loc) (len lo mid hi : Nat) (vf : Nat → val) (h1 : lo ≤ mid)
    (h2 : mid ≤ hi) :
    cellsR (GF := GF) b (min lo len) (min hi len - min lo len) vf ⊣⊢
      cellsR b (min lo len) (min mid len - min lo len) vf ∗
        cellsR b (min mid len) (min hi len - min mid len) vf := by
  rw [show min hi len - min lo len = (min mid len - min lo len) + (min hi len - min mid len) by omega]
  refine (cellsR_append _ _ _ _ _).trans ?_
  rw [show min lo len + (min mid len - min lo len) = min mid len by omega]
  exact .rfl

end specs3

section specs4
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt] [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

theorem mcellsAny_split (M : GMap Loc Nat) (lo mid hi : Nat) (h1 : lo ≤ mid) (h2 : mid ≤ hi) :
    mcellsAny (GF := GF) M lo hi ⊢ mcellsAny M lo mid ∗ mcellsAny M mid hi := by
  unfold mcellsAny
  rw [← BigSepM.bigSepM_sep_eq]
  apply BigSepM.bigSepM_mono
  intro b len _
  iintro ⟨%vf, H⟩
  icases (cellsR_split b len lo mid hi vf h1 h2).1 $$ H with ⟨H1, H2⟩
  isplitl [H1]
  · iexists vf; iexact H1
  · iexists vf; iexact H2

theorem mcellsAny_merge (M : GMap Loc Nat) (lo mid hi : Nat) (h1 : lo ≤ mid) (h2 : mid ≤ hi) :
    mcellsAny (GF := GF) M lo mid ∗ mcellsAny M mid hi ⊢ mcellsAny M lo hi := by
  unfold mcellsAny
  rw [← BigSepM.bigSepM_sep_eq]
  apply BigSepM.bigSepM_mono
  intro b len _
  iintro ⟨⟨%vf1, H1⟩, ⟨%vf2, H2⟩⟩
  iexists (fun i => if i < min mid len then vf1 i else vf2 i)
  iapply (cellsR_split b len lo mid hi _ h1 h2).2
  isplitl [H1]
  · iapply (cellsR_congr _ _ _ vf1 _ (fun i _ hi => by show vf1 i = if i < min mid len then vf1 i else vf2 i; rw [if_pos (by omega)])).1 $$ H1
  · iapply (cellsR_congr _ _ _ vf2 _ (fun i hi _ => by show vf2 i = if i < min mid len then vf1 i else vf2 i; rw [if_neg (by omega)])).1 $$ H2

theorem mcells_any (M : GMap Loc Nat) (lo hi : Nat) (vf : Nat → val) :
    mcells (GF := GF) M lo hi vf ⊢ mcellsAny M lo hi := by
  unfold mcells mcellsAny
  apply BigSepM.bigSepM_mono
  intro b len _
  iintro H; iexists vf; iexact H

end specs4

end Perennial
