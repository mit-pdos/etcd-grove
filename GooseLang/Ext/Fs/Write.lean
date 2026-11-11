/-
WP specs of `pwrite`, a two-step change (`PWriteStart`, `PWriteFinish`), on the per-byte model of
`Impl.lean`: the first step announces the write (each byte of its range gets its value as a new
crash candidate, stamped with the change's number) and takes the file's `OsMeta`, the bytes of the
range below the size and the client's halves of the mapped cells over it; the second lands a prefix
and gives them back, the bytes with the values landed and the candidates announced. Untrusted.
-/
module

public import GooseLang.Ext.Fs.Specs

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode
open goose_heap

/-! ## The interval of bytes that may not be durable -/

theorem touch_mem {m : OsMeta} {lo hi b : Nat} (h : m.dlo ≤ b ∧ b < m.dhi ∨ lo ≤ b ∧ b < hi) :
    (m.touch lo hi).dlo ≤ b ∧ b < (m.touch lo hi).dhi := by
  unfold OsMeta.touch
  split
  · rcases h with h | h
    · exact h
    · omega
  · split
    · rcases h with h | h
      · omega
      · exact h
    · simp only; omega

/-- A byte outside the interval `touch` gives was outside the old one and the added range. -/
theorem not_touch {m : OsMeta} {lo hi b : Nat}
    (h : ¬ ((m.touch lo hi).dlo ≤ b ∧ b < (m.touch lo hi).dhi)) :
    ¬ (m.dlo ≤ b ∧ b < m.dhi) ∧ ¬ (lo ≤ b ∧ b < hi) :=
  ⟨fun h1 => h (touch_mem (.inl h1)), fun h1 => h (touch_mem (.inr h1))⟩

@[simp] theorem touch_size (m : OsMeta) (lo hi : Nat) : (m.touch lo hi).size = m.size := by
  unfold OsMeta.touch; split <;> (try split) <;> rfl
@[simp] theorem touch_lo (m : OsMeta) (lo hi : Nat) : (m.touch lo hi).lo = m.lo := by
  unfold OsMeta.touch; split <;> (try split) <;> rfl
@[simp] theorem touch_hi (m : OsMeta) (lo hi : Nat) : (m.touch lo hi).hi = m.hi := by
  unfold OsMeta.touch; split <;> (try split) <;> rfl
@[simp] theorem touch_maps (m : OsMeta) (lo hi : Nat) : (m.touch lo hi).maps = m.maps := by
  unfold OsMeta.touch; split <;> (try split) <;> rfl
@[simp] theorem touch_zf (m : OsMeta) (lo hi : Nat) : (m.touch lo hi).zf = m.zf := by
  unfold OsMeta.touch; split <;> (try split) <;> rfl

@[simp] theorem announce_size (m : OsMeta) (lo hi tg : Nat) : (m.announce lo hi tg).size = m.size := by
  simp [OsMeta.announce]
@[simp] theorem announce_maps (m : OsMeta) (lo hi tg : Nat) : (m.announce lo hi tg).maps = m.maps := by
  simp [OsMeta.announce]
@[simp] theorem announce_lo (m : OsMeta) (lo hi tg : Nat) :
    (m.announce lo hi tg).lo = min m.lo tg := rfl
@[simp] theorem announce_hi (m : OsMeta) (lo hi tg : Nat) :
    (m.announce lo hi tg).hi = max m.hi tg := rfl
@[simp] theorem announce_zf (m : OsMeta) (lo hi tg : Nat) :
    (m.announce lo hi tg).zf = m.zf.map (fun z => if lo < hi then max z hi else z) := rfl
theorem announce_dlo (m : OsMeta) (lo hi tg : Nat) :
    (m.announce lo hi tg).dlo = (m.touch lo hi).dlo := rfl
theorem announce_dhi (m : OsMeta) (lo hi tg : Nat) :
    (m.announce lo hi tg).dhi = (m.touch lo hi).dhi := rfl

theorem announce_tc (m : OsMeta) (lo hi tg b : Nat) :
    (m.announce lo hi tg).tc !! b = if inRange lo hi b then none else m.tc !! b := by
  show (m.tc.filter (fun b _ => !inRange lo hi b)) !! b = _
  rw [GMap.lookup_filter]
  cases h : m.tc !! b <;> by_cases hr : inRange lo hi b <;> simp [hr]

/-- `MetaOk` of the `OsMeta` a change's first step leaves, for the file it leaves, from `MetaOk` of
the `OsMeta` before: the file's candidates change only in the announced range, its sizes do not. -/
theorem metaOk_announce {st st' : OsState} {i : Ino} {m : OsMeta} {f f' : OsFile} {lo hi tg : Nat}
    (hmo : MetaOk st i m f) (hsz : f'.size = f.size ∧ f'.sizeLo = f.sizeLo ∧ f'.sizeHi = f.sizeHi)
    (hcache : ∀ b, f'.cache b = f.cache b)
    (hcand : ∀ b, ¬ (lo ≤ b ∧ b < hi) → f'.cand b = f.cand b)
    (hmaps : ∀ b len, m.maps !! b = some len ↔ st'.proc.maps !! b = some ⟨i, len⟩)
    (htg : ∀ t c, st'.proc.inflight !! t = some c → c.ino = i → c.target = tg) :
    MetaOk st' i (m.announce lo hi tg) f' := by
  refine ⟨by simp [hmo.size, hsz.1], by simp; have := hmo.lo; omega,
    by simp; have := hmo.hi; omega, by simpa using hmaps, fun t c ht hc => ?_, ?_, ?_, ?_⟩
  · rw [htg t c ht hc]; exact ⟨Nat.min_le_right _ _, Nat.le_max_right _ _⟩
  · intro b hb hn
    rw [announce_dlo, announce_dhi] at hn
    obtain ⟨h1, h2⟩ := not_touch hn
    rw [hcand b h2, hcache b]; exact hmo.dur b (by omega) h1
  · intro z hz
    simp only [announce_zf, Option.map_eq_some_iff] at hz
    obtain ⟨z0, hz0, rfl⟩ := hz
    obtain ⟨h1, h2⟩ := hmo.zf z0 hz0
    refine ⟨by split <;> omega, fun b hb => ?_⟩
    rw [hcand b (by split at hb <;> omega)]; exact h2 b (by split at hb <;> omega)
  · intro b c hb hc
    rw [announce_tc] at hc
    split at hc
    · cases hc
    · rename_i hr
      rw [hcand b (by simpa [inRange] using hr)]
      exact hmo.tail b c (by rw [← hsz.1]; exact hb) hc

/-! ## The bytes and the file of a write -/

theorem written_getD_in (f : OsFile) (off : Nat) (d : List w8) (b : Nat) (h1 : off ≤ b)
    (h2 : b < off + d.length) : (f.written off d).getD b 0 = d.getD (b - off) 0 := by
  rw [written_getD, if_pos ⟨h1, h2⟩]

/-- A write of `data` at `off` (no past the end) is the change the ghost state records. -/
theorem ofWrite_is (i : Ino) (f : OsFile) (off : Nat) (data : List w8) (n : Nat) (m0 : OsMeta)
    (saved : List ByteG) (hsz : m0.size = f.size) (hgap : off ≤ f.size) :
    (TokInfo.mk i (.write off data) n m0 saved).Is (OsChange.ofWrite i f off data) := by
  refine ⟨rfl, rfl, by simp [TokInfo.lo, OsChange.ofWrite, hsz], rfl,
    by simp [TokInfo.target, OsChange.ofWrite, hsz], fun b hb => ?_⟩
  simp [OsChange.ofWrite, inRange] at hb
  simp only [OsChange.ofWrite, TokInfo.val]
  have h1 : off ≤ b := by omega
  rw [if_pos h1, written_getD_in _ _ _ _ h1 hb.2]

/-- The bytes `xs` of the range of a write of `data` at `off` below the size, as its first step
leaves them: each with the byte of the data as a new candidate, stamped `n`. -/
def pwAnn (data : List w8) (n : Nat) (xs : List ByteG) : List ByteG :=
  xs.mapIdx (fun j x => (x.1, x.2 ++ [(data.getD j 0, n)]))

@[simp] theorem pwAnn_length (data : List w8) (n : Nat) (xs : List ByteG) :
    (pwAnn data n xs).length = xs.length := by simp [pwAnn]

theorem pwAnn_getElem (data : List w8) (n : Nat) (xs : List ByteG) (j : Nat)
    (hj : j < (pwAnn data n xs).length) :
    (pwAnn data n xs)[j] = ((xs[j]'(by simpa using hj)).1, (xs[j]'(by simpa using hj)).2 ++
      [(data.getD j 0, n)]) := by
  simp [pwAnn]


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

theorem exists_fresh2 {V W : Type} (M : GMap Nat V) (N : GMap Nat W) :
    ∃ t, M !! t = none ∧ N !! t = none := by
  have bound : ∀ {X : Type} (K : GMap Nat X) (t : Nat), (K.toList.map (·.1)).sum < t → K !! t = none := by
    intro X K t ht
    cases h : K !! t with
    | none => rfl
    | some v =>
      exfalso
      have hm : t ∈ K.toList.map (·.1) := List.mem_map.2 ⟨_, (GMap.mem_toList _ _ _).2 h, rfl⟩
      have : ∀ (L : List Nat) (x : Nat), x ∈ L → x ≤ L.sum := by
        intro L x hx
        induction L with
        | nil => cases hx
        | cons a L ih =>
          rcases List.mem_cons.1 hx with rfl | hx
          · simp
          · have := ih hx; simp; omega
      have := this _ _ hm; omega
  refine ⟨(M.toList.map (·.1)).sum + (N.toList.map (·.1)).sum + 1, bound _ _ (by omega),
    bound _ _ (by omega)⟩
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
    (hm : st'.proc.maps = st.proc.maps) (Hh : ∀ l, Mapped st l → (h !! l).isSome) :
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

/-! ## A change's first step -/

section start
variable {st : OsState} {t : Nat} {c : OsChange}

/-- The state after a change's first step: the file announced, the change in flight. -/
abbrev startState (st : OsState) (p : Ino) (f : OsFile) (c : OsChange) (t : Nat) : OsState :=
  (st.stampFile p (f.announce c)).addInflight t c

theorem startState_file (st : OsState) (p : Ino) (f : OsFile) (c : OsChange) (t : Nat) (q : Ino) :
    (startState st p f c t).file q =
      if p = q then some (f.announce c (st.fs.stamp + 1)) else st.file q := by
  simp only [startState, OsState.addInflight, OsState.stampFile, OsState.file,
    GMap.lookup_insert_eq_iff]

theorem inflightAt_start (ht : st.proc.inflight !! t = none) (p : Ino) (f : OsFile) (q : Ino)
    (i : Nat) :
    InflightAt (startState st p f c t) q i ↔ InflightAt st q i ∨ (c.ino = q ∧ inRange c.lo c.hi i) := by
  constructor
  · rintro ⟨t', c', h1, h2, h3⟩
    by_cases he : t = t'
    · subst he; simp only [startState, OsState.addInflight, GMap.lookup_insert] at h1; cases h1
      exact .inr ⟨h2, h3⟩
    · simp only [startState, OsState.addInflight] at h1
      rw [GMap.lookup_insert_ne _ _ he] at h1; exact .inl ⟨t', c', h1, h2, h3⟩
  · rintro (⟨t', c', h1, h2, h3⟩ | ⟨h2, h3⟩)
    · have he : t ≠ t' := fun e => by subst e; rw [ht] at h1; cases h1
      have h1' : (startState st p f c t).proc.inflight !! t' = some c' := by
        simp only [startState, OsState.addInflight]; rw [GMap.lookup_insert_ne _ _ he]; exact h1
      exact ⟨t', c', h1', h2, h3⟩
    · exact ⟨t, c, by simp [startState, OsState.addInflight], h2, h3⟩

/-- `OsWf` after a change's first step, with no change in flight on its file. -/
theorem osWf_start (hwf : OsWf st) (ht : st.proc.inflight !! t = none) {p : Ino} {f : OsFile}
    (hf : st.file p = some f) (hcp : c.ino = p)
    (hnone : ∀ t' c', st.proc.inflight !! t' = some c' → c'.ino ≠ p) :
    OsWf (startState st p f c t) := by
  have hfile := startState_file st p f c t
  refine ⟨fun fd d h => ?_, fun b m h => ?_, hwf.maps_disj, fun t' c' h => ?_, ?_, ?_, ?_⟩
  · obtain ⟨f0, h0⟩ := hwf.fds fd d h; rw [hfile]; split
    · exact ⟨_, rfl⟩
    · exact ⟨_, h0⟩
  · obtain ⟨⟨f0, h0⟩, h1, h2, h3⟩ := hwf.maps b m h
    refine ⟨?_, h1, h2, h3⟩; rw [hfile]; split
    · exact ⟨_, rfl⟩
    · exact ⟨_, h0⟩
  · by_cases he : t = t'
    · subst he; simp only [startState, OsState.addInflight, GMap.lookup_insert] at h; cases h
      rw [hfile, if_pos hcp.symm]; exact ⟨_, rfl⟩
    · simp only [startState, OsState.addInflight] at h; rw [GMap.lookup_insert_ne _ _ he] at h
      obtain ⟨f0, h0⟩ := hwf.infl t' c' h; rw [hfile]; split
      · exact ⟨_, rfl⟩
      · exact ⟨_, h0⟩
  · intro t1 c1 t2 c2 h1 h2 hp
    simp only [startState, OsState.addInflight] at h1 h2
    rw [GMap.lookup_insert_eq_iff] at h1 h2
    split at h1 <;> split at h2
    · subst_vars; rfl
    · cases h1; exact absurd (hp.symm.trans hcp) (hnone _ _ h2)
    · cases h2; exact absurd (hp.trans hcp) (hnone _ _ h1)
    · exact hwf.infl_one t1 c1 t2 c2 h1 h2 hp
  · intro q f1 h1
    rw [hfile] at h1; split at h1
    · cases h1; exact hwf.sizes p f hf
    · exact hwf.sizes q f1 h1
  · intro q f1 b p0 h1 hp0
    rw [hfile] at h1
    show p0.2 ≤ st.fs.stamp + 1
    split at h1
    · cases h1
      simp only [OsFile.announce] at hp0
      split at hp0
      · rcases List.mem_append.1 hp0 with h | h
        · exact Nat.le_succ_of_le (hwf.stamps p f b p0 hf h)
        · simp at h; subst h; simp
      · exact Nat.le_succ_of_le (hwf.stamps p f b p0 hf hp0)
    · exact Nat.le_succ_of_le (hwf.stamps q f1 b p0 h1 hp0)

/-- **The ghost maps after a change's first step**, on a file whose whole `OsMeta` `m` the client
held (no change in flight on it): the bytes of the change's range below the size take their new
candidates (`saved`), the change's entry records it, and holds the file's `OsMeta`, announced. -/
theorem osCoh_start {Γb Γm Γf Γt} (hcoh : OsCoh st Γb Γm Γf Γt) (ht : st.proc.inflight !! t = none)
    {p : Ino} {f : OsFile} {m : OsMeta} (hf : st.file p = some f) (Hml : Γm !! p = some m)
    (hmo : MetaOk st p m f) (hnt : ∀ t' ti, Γt !! t' = some ti → ti.ino ≠ p)
    (ti : TokInfo) (hti : ti.Is c) (hp : ti.ino = p) (hm0 : ti.m0 = m)
    (hn : ti.n = st.fs.stamp + 1) (hlh : c.lo ≤ c.hi)
    (hlen : ti.saved.length = min c.hi f.size - c.lo)
    (hsv : ∀ j (hj : j < ti.saved.length), ti.saved[j] =
      (f.cache (c.lo + j), f.cand (c.lo + j) ++ [(c.val (c.lo + j), ti.n)])) :
    OsCoh (startState st p f c t) (insertBytes p c.lo ti.saved Γb) (<[p := ti.meta]> Γm) Γf
      (<[t := ti]> Γt) := by
  obtain ⟨hino, hkind, hlo, hhi, htg, hval⟩ := hti
  have hcp : c.ino = p := hino.trans hp
  have hΓt : Γt !! t = none := by
    have := hcoh.toks t; rw [ht] at this
    cases h : Γt !! t
    · rfl
    · rw [h] at this; cases this
  have hni := noInfl_of_noTok hcoh hnt
  have hfile := startState_file st p f c t
  let f' := f.announce c (st.fs.stamp + 1)
  have hcand' : ∀ b, f'.cand b = if inRange c.lo c.hi b then f.cand b ++ [(c.val b, st.fs.stamp + 1)]
      else f.cand b := fun b => rfl
  refine ⟨fun q => ?_, fun q m' hm => ?_, fun q b x hx => ?_, fun q f1 b h1 hb => ?_,
    hcoh.fds, fun t' => ?_, fun t' ti' c' h1 h2 => ?_, fun t' ti' h => ?_, fun t' ti' h => ?_,
    fun t' ti' h => ?_⟩
  · simp only [startState, OsState.addInflight, OsState.stampFile, GMap.lookup_insert_eq_iff]
    split
    · simp
    · exact hcoh.meta_dom q
  · rw [GMap.lookup_insert_eq_iff] at hm
    split at hm
    · subst_vars; cases hm
      refine ⟨f', by simp [startState, OsState.addInflight, OsState.stampFile, f'], ?_⟩
      have := metaOk_announce (st' := startState st ti.ino f c t) (f' := f') (lo := ti.lo) (hi := ti.hi)
        (tg := ti.target) hmo ⟨rfl, rfl, rfl⟩ (fun _ => rfl)
        (fun b hb => by
          simp only [f', OsFile.announce]
          rw [if_neg (by simp only [inRange, Bool.and_eq_true, decide_eq_true_eq]; rw [hlo, hhi]; exact hb)])
        hmo.maps (fun t' c' h1 h2 => by
          by_cases he : t = t'
          · subst he; simp only [startState, OsState.addInflight, GMap.lookup_insert] at h1
            cases h1; exact htg
          · simp only [startState, OsState.addInflight] at h1
            rw [GMap.lookup_insert_ne _ _ he] at h1
            exact absurd h2 (hni t' c' h1))
      rw [TokInfo.meta]; exact this
    · rename_i hne
      obtain ⟨f1, h1, hm1⟩ := hcoh.meta_some q m' hm
      refine ⟨f1, by simp only [startState, OsState.addInflight, OsState.stampFile,
        GMap.lookup_insert_eq_iff, if_neg hne]; exact h1, ?_⟩
      refine ⟨hm1.size, hm1.lo, hm1.hi, hm1.maps, fun t' c' h1' h2' => ?_, hm1.dur, hm1.zf, hm1.tail⟩
      by_cases he : t = t'
      · subst he; simp only [startState, OsState.addInflight, GMap.lookup_insert] at h1'
        cases h1'; exact absurd (hcp.symm.trans h2') hne
      · simp only [startState, OsState.addInflight] at h1'
        rw [GMap.lookup_insert_ne _ _ he] at h1'; exact hm1.targets t' c' h1' h2'
  · rw [lookup_insertBytes] at hx
    split at hx
    · rename_i hr
      obtain ⟨rfl, h1, h2⟩ := hr
      have hk : b - c.lo < ti.saved.length := by omega
      rw [List.getElem?_eq_getElem hk, hsv _ hk] at hx; cases hx
      refine ⟨f', by rw [hfile, if_pos rfl], by simp [f', OsFile.announce]; omega, ?_⟩
      rw [show c.lo + (b - c.lo) = b by omega, hcand', if_pos (by
        simp only [inRange, Bool.and_eq_true, decide_eq_true_eq]; omega), hn]; rfl
    · obtain ⟨f1, h1, hb, hx1⟩ := hcoh.bytes q b x hx
      by_cases hpq : p = q
      · subst hpq; rw [hf] at h1; cases h1
        refine ⟨f', by rw [hfile, if_pos rfl], hb, ?_⟩
        rw [hx1, hcand', if_neg]; · rfl
        rename_i hr
        simp only [inRange, Bool.and_eq_true, decide_eq_true_eq]
        intro ⟨h1, h2⟩; exact hr ⟨rfl, h1, by omega⟩
      · exact ⟨f1, by rw [hfile, if_neg hpq]; exact h1, hb, hx1⟩
  · rw [hfile] at h1; rw [lookup_insertBytes]
    split
    · rename_i hr; rw [List.getElem?_eq_getElem (by omega)]; rfl
    · split at h1
      · cases h1; exact hcoh.bytes_full _ f b (by subst_vars; exact hf) hb
      · exact hcoh.bytes_full q f1 b h1 hb
  · simp only [startState, OsState.addInflight, GMap.lookup_insert_eq_iff]
    split
    · rfl
    · exact hcoh.toks t'
  · simp only [startState, OsState.addInflight] at h2
    rw [GMap.lookup_insert_eq_iff] at h1 h2
    split at h1
    · cases h1; rename_i he; rw [if_pos he] at h2; cases h2
      exact ⟨hino, hkind, hlo, hhi, htg, hval⟩
    · rename_i he; rw [if_neg he] at h2; exact hcoh.tok_is t' ti' c' h1 h2
  · rw [GMap.lookup_insert_eq_iff] at h
    split at h
    · cases h; rw [hp, GMap.lookup_insert]
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm (hnt t' ti' h))]; exact hcoh.tok_meta t' ti' h
  · rw [GMap.lookup_insert_eq_iff] at h
    split at h
    · cases h
      refine ⟨f', by rw [hfile, hp, if_pos rfl], by rw [hm0, hmo.size]; rfl,
        by rw [← hlo, ← hhi]; exact hlh, by rw [hlen, hlo, hhi]; rfl⟩
    · obtain ⟨f1, h1, hrest⟩ := hcoh.tok_file t' ti' h
      exact ⟨f1, by rw [hfile, if_neg (Ne.symm (hnt t' ti' h))]; exact h1, hrest⟩
  · rw [GMap.lookup_insert_eq_iff] at h
    split at h
    · cases h
      refine ⟨f', by rw [hfile, hp, if_pos rfl], fun b hb => ⟨f.cand b, ?_, fun z hz hzb => ?_,
        fun c hsz hc => ?_⟩⟩
      · rw [hcand', if_pos (by rw [hlo, hhi]; exact hb), hn, hval b (by rw [hlo, hhi]; exact hb)]
      · rw [hm0] at hz; exact (hmo.zf z hz).2 b hzb
      · rw [hm0] at hsz hc; exact hmo.tail b c (by rw [← hmo.size]; exact hsz) hc
    · obtain ⟨f1, h1, hrest⟩ := hcoh.tok_cand t' ti' h
      exact ⟨f1, by rw [hfile, if_neg (Ne.symm (hnt t' ti' h))]; exact h1, hrest⟩

end start



/-! ## The first step of a write -/

theorem announce_contents (f : OsFile) (c : OsChange) (n : Nat) :
    (f.announce c n).contents = f.contents := rfl

open Classical in
theorem cellByte_eq (st : OsState) (p : Ino) (i : Nat) :
    cellByte st p i = if InflightAt st p i then none else (st.file p).bind (·.contents[i]?) := by
  unfold cellByte
  cases st.file p with
  | none => simp
  | some f =>
    dsimp only
    by_cases hi : i < f.contents.length
    · simp [hi, List.getElem?_eq_getElem hi]
    · simp [hi, List.getElem?_eq_none (Nat.le_of_not_lt hi)]

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [GoGlobalContext]
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

/-- A `pwrite` of `data` at `off` of the file `p` between its two steps, the change number `n`:
what its first step took (the `OsMeta` `m`, whole, the bytes `xs` of its range below the size,
with their new candidates); it starts inside the file. -/
def pwTok (t : Nat) (p : Ino) (off : Nat) (data : List w8) (m : OsMeta) (xs : List ByteG)
    (n : Nat) : IProp GF :=
  iprop(osTok (L := L) t ⟨p, .write off data, n, m, pwAnn data n xs⟩ ∗
    ⌜off ≤ m.size ∧ data ≠ [] ∧ xs.length = min (off + data.length) m.size - off⌝)

/-- The first step of `pwrite(fd, data, off)`, with the whole of the file's `OsMeta`, the bytes it
may change below the size (`[off, min (off + n) size)`, whole) and the client's halves of the cells
of every mapping over `[off, off + n)`. They stay with the change until its second step
(`wp_osPWriteFinish`), which gets the change's number `n`, past every candidate's stamp. The write
starts inside the file (`off ≤ size`) and is not empty. -/
theorem wp_osPWriteStart (fd off : w64) (data : List w8) (dq : DFrac) (d : OsFd)
    (m : OsMeta) (xs : List ByteG) (hE : ↑osN ⊆ E) (hwr : d.writable = true)
    (hoff : 0 ≤ off.toInt) (hgap : off.toNat ≤ m.size) (hd : data ≠ [])
    (hlen : xs.length = min (off.toNat + data.length) m.size - off.toNat) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osFd (L := L) fd dq d -∗ osMeta (L := L) d.ino (DFrac.own 1) m -∗
      osBytes (L := L) d.ino off.toNat (DFrac.own 1) xs -∗
      mcellsAny m.maps off.toNat (off.toNat + data.length) -∗
      (∀ t : Nat, ∀ n : Nat, ⌜(∀ x ∈ xs, ∀ q ∈ x.2, q.2 < n) ∧
          (∀ b c, m.size ≤ b → m.pc b = some c → ∀ q ∈ c, q.2 < n) ∧ 0 < n⌝ -∗
        osFd (L := L) fd dq d -∗
        pwTok t d.ino off.toNat data m xs n -∗ Φ (osTokV t)) -∗
      WP (ExternalOp fsExt.name "PWriteStart" (Val (PairV (#fd) (PairV (#off) (#data))))) @ s; E
        {{ Φ }} := by
  iintro #Hinv Hfd Hm Hbs Hc HΦ
  iapply wp_os_step "PWriteStart" _ Φ (by simp [val.isPanic]) hE (by simp [DataOp]) $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %h Hw
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  unfold osFd osMeta osBytes
  icases bytesG_lookup _ d.ino _ _ xs Γb $$ HAb Hbs with %Hbl
  icases gAuth_lookup _ _ _ _ _ _ $$ HAf Hfd with %Hfdl
  icases gAuth_lookup _ _ _ _ _ _ $$ HAm Hm with %Hml
  icases tokRes_meta_whole _ $$ Htok Hm with %Hnt
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hfd : st.proc.fds !! fd = some d := hcoh.fds ▸ Hfdl
  obtain ⟨f, hf, hmo⟩ := coh_meta hcoh Hml
  have hni := noInfl_of_noTok hcoh Hnt
  have hnb : ¬ BusyAt st d.ino := by rintro ⟨t', c', ht', hc'⟩; exact hni t' c' ht' hc'
  have hgapf : off.toNat ≤ f.size := hmo.size ▸ hgap
  have hxs : ∀ k (hk : k < xs.length), xs[k] = (f.cache (off.toNat + k), f.cand (off.toNat + k)) := by
    intro k hk
    obtain ⟨f1, hf1, -, hx⟩ := hcoh.bytes _ _ _ (Hbl k hk)
    rw [hf] at hf1; cases hf1; exact hx
  have Hh : ∀ l, Mapped st l → (h !! l).isSome := by
    intro l hm
    obtain ⟨x, hx⟩ := cellView_isSome hwf hm
    obtain ⟨m0, hm0⟩ := Hag l x hx
    rw [hm0]; rfl
  let c := OsChange.ofWrite d.ino f off.toNat data
  have hclo : c.lo = off.toNat := by simp [c, OsChange.ofWrite]; omega
  have haff : ∀ i, inRange c.lo c.hi i = true ↔ off.toNat ≤ i ∧ i < off.toNat + data.length := by
    intro i; rw [hclo]; simp [c, OsChange.ofWrite, inRange]
  obtain ⟨t0, ht0, hc0⟩ := exists_fresh2 st.proc.inflight st.proc.calls
  imodintro
  isplitr
  · ipureintro
    have hwf0 := osWf_start (c := c) hwf ht0 hf rfl hni
    exact ⟨_, _, _, ⟨fd, off, data, d, f, t0, rfl, hfd, hwr, hoff, hd, hf, hnb, ht0, hc0, rfl, rfl⟩,
      mapsFresh_same rfl, heapRendered_render hwf0 rfl Hh⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsFsStep] at Hst
  obtain ⟨fd', off', data', d', f', t, hv, hfd', -, -, -, hf', -, ht, -, hst', rfl⟩ := Hst
  injection hv with h1 h2; injection h2 with h3 h4
  cases go.intoVal_inj h1; cases go.intoVal_inj h3; cases go.intoVal_inj h4
  simp only [FdOpen, hfd, Option.some.injEq] at hfd'; subst hfd'
  rw [hf] at hf'; cases hf'
  subst hst'
  let n := st.fs.stamp + 1
  let ti : TokInfo := ⟨d.ino, .write off.toNat data, n, m, pwAnn data n xs⟩
  have hwf1 := osWf_start (c := c) hwf ht hf rfl hni
  have hti : ti.Is c := ofWrite_is d.ino f off.toNat data n m _ hmo.size hgapf
  have hcoh1 := osCoh_start (c := c) hcoh ht hf Hml hmo Hnt ti hti rfl rfl rfl
    (by simp [c, OsChange.ofWrite]; omega)
    (by show (pwAnn data n xs).length = _; rw [pwAnn_length, hlen, hmo.size, hclo]; rfl)
    (fun j hj => by
      simp only [ti] at hj ⊢
      rw [pwAnn_getElem, hxs j (by simpa using hj), hclo]
      congr 3
      have hj' : j < data.length := by
        have := hj; simp only [ti, pwAnn_length] at this; omega
      simp only [c, OsChange.ofWrite]; rw [written_getD_in _ _ _ _ (by omega) (by omega)]
      simp)
  have hI := inflightAt_start (c := c) (f := f) (p := d.ino) ht
  -- the cells: the client's halves of the cells the write may change go to the invariant
  have hdisj : MapsDisj m.maps.toList := mapsDisj_toList _ (fun b1 l1 b2 l2 h1 h2 hne =>
    hwf.maps_disj b1 _ b2 _ ((hmo.maps b1 l1).1 h1) ((hmo.maps b2 l2).1 h2) hne)
  unfold mcellsAny
  ihave Hc := (BigSepM.bigSepM_toList (Φ := fun (b : Loc) (len : Nat) =>
    iprop(∃ vf, cellsR b (min off.toNat len)
      (min (off.toNat + data.length) len - min off.toNat len) vf))).1 $$ Hc
  icases halves_mapsCells_ex off.toNat (off.toNat + data.length) _ hdisj
    $$ Hc with ⟨%C, Hc, %hC⟩
  have hmapsC : ∀ l, (C !! l).isSome → ∃ i, MapsTo st l d.ino i ∧ inRange c.lo c.hi i = true := by
    intro l hl
    obtain ⟨i, b, len, hm, h1, h2, h3, rfl⟩ := (hC l).1 hl
    exact ⟨i, ⟨b, ⟨d.ino, len⟩, (hmo.maps b len).1 ((GMap.mem_toList _ _ _).1 hm), rfl, h3, rfl⟩,
      (haff i).2 ⟨h1, h2⟩⟩
  have hTmem : ∀ l, l ∈ C.toList.map (·.1) ↔ (C !! l).isSome := by
    intro l; simp only [List.mem_map]
    constructor
    · rintro ⟨⟨k, v⟩, hkv, rfl⟩; rw [(GMap.mem_toList _ _ _).1 hkv]; rfl
    · intro hl; obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hl
      exact ⟨(l, v), (GMap.mem_toList _ _ _).2 hv, rfl⟩
  have hTnd : (C.toList.map (·.1)).Nodup := Iris.Std.LawfulFiniteMap.toList_noDupKeys (m := C)
  have hnoI : ∀ i, ¬ InflightAt st d.ino i := by
    rintro i ⟨t', c', h1, h2, -⟩; exact hni t' c' h1 h2
  imod cells_step st _ h h' (C.toList.map (·.1)) C ∅ hwf hwf1 Hr Hfr (fun b m0 h0 => .inr h0) hTnd
    (fun l hl => by obtain ⟨i, hi, -⟩ := hmapsC l ((hTmem l).1 hl); exact .inl ⟨_, _, hi⟩)
    (fun l v hl => by
      have hs : (C !! l).isSome := by rw [hl]; rfl
      obtain ⟨i, hi, ha⟩ := hmapsC l hs
      exact ⟨(hTmem l).2 hs, _, by rw [cellView_mapsTo hwf hi, decide_eq_false (hnoI i)]⟩)
    (fun l v h => by simp at h)
    (fun l hl hn => by rw [(hTmem l).1 hl |> Option.isSome_iff_exists.1 |>.choose_spec] at hn; cases hn)
    (fun l hl _ x hx => by
      obtain ⟨i, hi, ha⟩ := hmapsC l ((hTmem l).1 hl)
      rw [cellView_mapsTo hwf1 hi] at hx; cases hx
      exact decide_eq_true ((hI _ _).2 (.inr ⟨rfl, ha⟩)))
    (fun l hl => by
      by_cases hm : Mapped st l
      · obtain ⟨q', i, hqi⟩ := hm
        rw [cellView_mapsTo hwf1 hqi, cellView_mapsTo hwf hqi, cellByte_eq, cellByte_eq]
        have hn : ¬ (c.ino = q' ∧ inRange c.lo c.hi i = true) := by
          rintro ⟨hp, ha⟩
          obtain ⟨b, m0, hb, hp0, hi0, rfl⟩ := hqi
          have hb' : m.maps !! b = some m0.len := by
            rw [hmo.maps b m0.len, hb]; congr 1; cases m0; simp only at hp0 ⊢
            rw [hp0, ← hp]; rfl
          apply hl; apply (hTmem _).2; apply (hC _).2
          obtain ⟨h1, h2⟩ := (haff i).1 ha
          exact ⟨i, b, m0.len, (GMap.mem_toList _ _ _).2 hb', h1, h2, hi0, rfl⟩
        have hII : InflightAt (startState st d.ino f c t) q' i ↔ InflightAt st q' i := by
          rw [hI]; exact ⟨fun h => h.resolve_right hn, .inl⟩
        have hF : ((startState st d.ino f c t).file q').bind (·.contents[i]?) =
            (st.file q').bind (·.contents[i]?) := by
          rw [startState_file]; split
          · subst_vars; rw [hf]; rfl
          · rfl
        simp only [hII, hF]
      · rw [cellView_none (st := st) hm]; exact cellView_none hm)
    $$ [Hσ Hcells Hc] with ⟨Hσ, Hcells, -⟩
  · iframe
  -- the ghost maps
  imod gAuth_update _ _ _ _ _ ti.meta $$ HAm Hm with ⟨HAm, Hm⟩
  imod bytesG_update _ d.ino _ xs (pwAnn data n xs) Γb (by simp) $$ [HAb Hbs] with ⟨HAb, Hbs⟩
  · iframe
  have hΓt : Γt !! t = none := by
    have := hcoh.toks t; rw [ht] at this
    cases h0 : Γt !! t
    · rfl
    · rw [h0] at this; cases this
  imod gAuth_insert _ _ _ t ti hΓt $$ HAt with ⟨HAt, Ht⟩
  imodintro
  iexists _, _, Γf, _
  iframe HAb HAm HAf HAt Hσ Hcells
  isplitl [Htok Hm Hbs]
  · isplitr
    · ipureintro; rw [hclo] at hcoh1; exact ⟨hwf1, hcoh1⟩
    unfold tokRes
    iapply (BigSepM.bigSepM_insert (Φ := fun (_t : Nat) (ti : TokInfo) =>
      iprop(gElem gooseOsGS gooseOsGS.γm ti.ino (DFrac.own 1) ti.meta ∗
        bytesG gooseOsGS ti.ino ti.lo (DFrac.own 1) ti.saved)) hΓt).2
    have hlo' : ti.lo = off.toNat := by simp [ti, TokInfo.lo]; omega
    rw [hlo']
    iframe
  iapply wp_value'
  iapply HΦ $$ %t %n %(⟨fun x hx q hq => by
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
    rw [hxs k hk] at hq
    exact Nat.lt_succ_of_le (hwf.stamps d.ino f _ q hf hq), fun b c hb hc q hq => by
    rw [← hmo.pc_cand b c (by rw [← hmo.size]; exact hb) hc] at hq
    exact Nat.lt_succ_of_le (hwf.stamps d.ino f _ q hf hq), Nat.succ_pos _⟩) Hfd
  unfold pwTok osTok
  iframe Ht; ipureintro; exact ⟨hgap, hd, hlen⟩

end specs


/-! ## A change's second step: the change done -/

section done
variable {st : OsState} {t : Nat} {c : OsChange}

theorem MetaOk.mono_infl {st st' : OsState} {q : Ino} {m : OsMeta} {f : OsFile}
    (hm : st'.proc.maps = st.proc.maps)
    (hin : ∀ t c, st'.proc.inflight !! t = some c → st.proc.inflight !! t = some c)
    (h : MetaOk st q m f) : MetaOk st' q m f :=
  ⟨h.size, h.lo, h.hi, by rw [hm]; exact h.maps, fun t c ht => h.targets t c (hin t c ht), h.dur,
    h.zf, h.tail⟩

theorem doneInflight_sub (st : OsState) (t : Nat) :
    ∀ t' c', (st.doneInflight t).proc.inflight !! t' = some c' → st.proc.inflight !! t' = some c' := by
  intro t' c' h
  simp only [OsState.doneInflight, GMap.lookup_delete_iff] at h; split at h
  · cases h
  · exact h

theorem inflightAt_done (hwf : OsWf st) (hct : st.proc.inflight !! t = some c) (q : Ino) (i : Nat) :
    InflightAt (st.doneInflight t) q i ↔ InflightAt st q i ∧ q ≠ c.ino := by
  constructor
  · rintro ⟨t', c', h1, h2, h3⟩
    have h1' := doneInflight_sub st t t' c' h1
    have hne : t' ≠ t := by
      intro e; subst e; simp [OsState.doneInflight] at h1
    refine ⟨⟨t', c', h1', h2, h3⟩, fun hq => hne ?_⟩
    exact hwf.infl_one t' c' t c h1' hct (h2.trans hq)
  · rintro ⟨⟨t', c', h1, h2, h3⟩, hq⟩
    have hne : t' ≠ t := by intro e; subst e; rw [hct] at h1; cases h1; exact hq h2.symm
    have h1' : (st.doneInflight t).proc.inflight !! t' = some c' := by
      simp only [OsState.doneInflight]; rw [GMap.lookup_delete_ne _ (Ne.symm hne)]; exact h1
    exact ⟨t', c', h1', h2, h3⟩

theorem osWf_done (hwf : OsWf st) : OsWf (st.doneInflight t) :=
  { hwf with
    infl := fun t' c' h => hwf.infl t' c' (doneInflight_sub st t t' c' h)
    infl_one := fun t1 c1 t2 c2 h1 h2 hp =>
      hwf.infl_one t1 c1 t2 c2 (doneInflight_sub st t t1 c1 h1) (doneInflight_sub st t t2 c2 h2) hp }

/-- The ghost maps with the change `t` done (before its file is replaced): no change in flight on
its file any more. -/
theorem osCoh_done {Γb Γm Γf Γt} (hcoh : OsCoh st Γb Γm Γf Γt) :
    OsCoh (st.doneInflight t) Γb Γm Γf (GMap.delete t Γt) := by
  refine ⟨hcoh.meta_dom, fun q m hm => ?_, hcoh.bytes, hcoh.bytes_full, hcoh.fds, fun t' => ?_,
    fun t' ti c' h1 h2 => ?_, fun t' ti h => ?_, fun t' ti h => ?_, fun t' ti h => ?_⟩
  · obtain ⟨f, hf, hmo⟩ := hcoh.meta_some q m hm
    exact ⟨f, hf, hmo.mono_infl (st := st) rfl (doneInflight_sub st t)⟩
  · simp only [OsState.doneInflight, GMap.lookup_delete_iff]; split
    · rfl
    · exact hcoh.toks t'
  · rw [GMap.lookup_delete_iff] at h1; split at h1
    · cases h1
    · exact hcoh.tok_is t' ti c' h1 (doneInflight_sub st t t' c' h2)
  all_goals
    rw [GMap.lookup_delete_iff] at h; split at h
    · cases h
  · exact hcoh.tok_meta t' ti h
  · exact hcoh.tok_file t' ti h
  · exact hcoh.tok_cand t' ti h

/-- With the change `t` on `p` done, no other change in flight is on `p`. -/
theorem noTok_done {Γb Γm Γf Γt} (hwf : OsWf st) (hcoh : OsCoh st Γb Γm Γf Γt)
    (hct : st.proc.inflight !! t = some c) :
    ∀ t' ti, GMap.delete t Γt !! t' = some ti → ti.ino ≠ c.ino := by
  intro t' ti h hp
  rw [GMap.lookup_delete_iff] at h; split at h
  · cases h
  · rename_i hne
    have := hcoh.toks t'; rw [h] at this
    obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.1 this.symm
    have his := hcoh.tok_is t' ti c' h hc'
    exact hne (hwf.infl_one t c t' c' hct hc' (by rw [his.1, hp]))

end done


/-! ## The second step of a write -/

theorem insertBytes_append (p : Ino) : ∀ (off : Nat) (xs ys : List (ByteG))
    (m : GMap (Ino × Nat) (ByteG)),
    insertBytes p off (xs ++ ys) m = insertBytes p (off + xs.length) ys (insertBytes p off xs m)
  | off, [], ys, m => by simp [insertBytes]
  | off, x :: xs, ys, m => by
    simp only [List.cons_append, insertBytes, List.length_cons]
    rw [insertBytes_append p (off + 1) xs ys, show off + 1 + xs.length = off + (xs.length + 1) by omega]



/-- The size after a `pwrite` of `k` bytes at `off` of a file of size `sz`. -/
def pwSize (sz off k : Nat) : Nat := if k = 0 then sz else max sz (off + k)

/-- The `OsMeta` after a `pwrite` of `n` bytes at `off` that wrote `k`: as its first step left it,
with the size it leaves. -/
def pwPost (m : OsMeta) (off n k : Nat) : OsMeta :=
  { m.announce (min off m.size) (off + n) (max m.size (off + n)) with size := pwSize m.size off k }

/-- The candidates known past the size after a `pwrite` of `data` at `off` (inside the file),
announced as change `n`: each byte of its range past the old size with the data's byte as a new
candidate, stamped `n`; the rest of the range unknown; the other bytes as before. -/
def pwTail (m : OsMeta) (off : Nat) (data : List w8) (n : Nat) : GMap Nat Cands :=
  ⟨fun b => if inRange off (off + data.length) b then
      (if m.size ≤ b then (m.pc b).map (· ++ [(data.getD (b - off) 0, n)]) else none)
    else m.tc !! b,
   by
    obtain ⟨l, hl⟩ := m.tc.finite
    refine ⟨l ++ List.range (off + data.length), fun b h => ?_⟩
    by_cases h1 : inRange off (off + data.length) b = true
    · simp only [inRange, Bool.and_eq_true, decide_eq_true_eq] at h1
      exact List.mem_append_right _ (List.mem_range.2 h1.2)
    · simp only [h1] at h; exact List.mem_append_left _ (hl b (by simpa using h))⟩

theorem pwTail_lookup (m : OsMeta) (off : Nat) (data : List w8) (n b : Nat) :
    pwTail m off data n !! b = if inRange off (off + data.length) b then
      (if m.size ≤ b then (m.pc b).map (· ++ [(data.getD (b - off) 0, n)]) else none)
    else m.tc !! b := rfl

/-- `pwPost`, and, if `keep`, the candidates past the size the write leaves (`pwTail`). -/
def pwPostK (keep : Bool) (m : OsMeta) (off : Nat) (data : List w8) (k n : Nat) : OsMeta :=
  { pwPost m off data.length k with
    tc := cond keep (pwTail m off data n) (pwPost m off data.length k).tc }

theorem pwPostK_false (m : OsMeta) (off : Nat) (data : List w8) (k n : Nat) :
    pwPostK false m off data k n = pwPost m off data.length k := rfl

/-- Byte `i` (from `off` on) after a `pwrite` of the first `k` bytes of `data` at `off`, whose
bytes from `off` were `xs`: the data, then the old bytes. -/
def pwByte (off : Nat) (data : List w8) (k : Nat) (xs : List ByteG) (i : Nat) : w8 :=
  if i < off + k then data.getD (i - off) 0 else (xs.getD (i - off) (0, [])).1

/-- The bytes `[off, min (off + n) (pwSize sz off k))` after a `pwrite` of the first `k` bytes of
`data` (`n` bytes) at `off` of a file of size `sz`, whose bytes there were `xs` and whose bytes past
the size had the candidates `zs`: their values, and their candidates with the data's byte last,
stamped with the change's number. -/
def pwBytes (sz off : Nat) (data : List w8) (k nst : Nat) (xs : List ByteG) (zs : List Cands) :
    List ByteG :=
  (List.range (min (off + data.length) (pwSize sz off k) - off)).map (fun j =>
    (pwByte off data k xs (off + j),
      (if j < xs.length then (xs.getD j (0, [])).2 else zs.getD (j - xs.length) []) ++
        [(data.getD j 0, nst)]))

/-- What a mapped cell at byte `i` shows after such a `pwrite`. -/
def pwCell [GooseExts] (sz off : Nat) (data : List w8) (k : Nat) (xs : List ByteG) (i : Nat) : val :=
  toCellVal (if i < pwSize sz off k then some (pwByte off data k xs i) else none)

theorem pwBytes_length (sz off : Nat) (data : List w8) (k nst : Nat) (xs : List ByteG)
    (zs : List Cands) :
    (pwBytes sz off data k nst xs zs).length = min (off + data.length) (pwSize sz off k) - off := by
  simp [pwBytes]

theorem pwBytes_getElem (sz off : Nat) (data : List w8) (k nst : Nat) (xs : List ByteG)
    (zs : List Cands) (i : Nat) (hi : i < (pwBytes sz off data k nst xs zs).length) :
    ((pwBytes sz off data k nst xs zs)[i]).1 = pwByte off data k xs (off + i) := by
  simp [pwBytes]

section finish
variable {st : OsState} {Γb : GMap (Ino × Nat) ByteG} {Γm : GMap Ino OsMeta} {Γf : GMap w64 OsFd}
  {Γt : GMap Nat TokInfo}

/-- The file after a write `c` of `data` at `off` landed `k` bytes. -/
abbrev pwFile (f : OsFile) (c : OsChange) (off k : Nat) : OsFile :=
  let w := if k = 0 then c.lo else off + k
  f.land c w (max f.size w)

theorem pwFile_size (f : OsFile) (c : OsChange) (off k : Nat) (hlo : c.lo = off) (hgap : off ≤ f.size) :
    (pwFile f c off k).size = pwSize f.size off k := by
  simp only [pwFile, OsFile.land, pwSize]; split <;> omega

theorem pwFile_cache (f : OsFile) (c : OsChange) (off k b : Nat) (hlo : c.lo = off) :
    (pwFile f c off k).cache b = if off ≤ b ∧ b < off + k then c.val b else f.cache b := by
  simp only [pwFile, OsFile.land, inRange, Bool.and_eq_true, decide_eq_true_eq]
  split <;> split <;> split <;> (try rfl) <;> omega

/-- The state after the second step. -/
abbrev pwState (st : OsState) (t : Nat) (p : Ino) (f : OsFile) (c : OsChange) (off k : Nat) :
    OsState :=
  (st.doneInflight t).setFile p (pwFile f c off k)

end finish

section specs2
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [GoGlobalContext]
  [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}
attribute [local instance] Classical.propDecidable

/-- The second step of `pwrite(fd, data, off)`: it writes the first `k` bytes of `data`, all of
them with errno 0, or, with errno 0 too, a non-empty prefix (a short write: F6), or any prefix
with a nonzero errno. What the first step took comes back: the `OsMeta` with the new size, the bytes
`[off, min (off + n) size')` (the data written, then the old bytes), each with the candidates it had
and the data's byte, stamped `n`, last (the bytes the write added past the old size had the
candidates `zs`: the zero alone past the zeros known), and the client's halves of the mapped cells,
which show the new bytes. -/
theorem wp_osPWriteFinishK (keep : Bool) (t : Nat) (p : Ino) (off : Nat) (data : List w8)
    (m : OsMeta) (xs : List ByteG) (n : Nat) (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ pwTok (L := L) t p off data m xs n -∗
      (∀ k : Nat, ∀ e : w64, ∀ zs : List Cands,
        ⌜k ≤ data.length ∧ ((k = data.length ∨ 0 < k) ∧ e = 0 ∨ e ≠ 0) ∧
          zs.length = pwSize m.size off k - m.size ∧
          ∀ j z, m.zf = some z → z ≤ m.size + j → j < zs.length → zs[j]? = some [(0, 0)]⌝ -∗
        ⌜∀ j c, m.pc (m.size + j) = some c → j < zs.length → zs[j]? = some c⌝ -∗
        osMeta (L := L) p (DFrac.own 1) (pwPostK keep m off data k n) -∗
        osBytes (L := L) p off (DFrac.own 1) (pwBytes m.size off data k n xs zs) -∗
        mcells m.maps off (off + data.length) (pwCell m.size off data k xs) -∗
        Φ (PairV (#(W64 k)) (#e))) -∗
      WP (ExternalOp fsExt.name "PWriteFinish" (Val (osTokV t))) @ s; E {{ Φ }} := by
  iintro #Hinv Ht HΦ
  iapply wp_os_step "PWriteFinish" _ Φ (by simp [val.isPanic]) hE (by simp [DataOp]) $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %h Hw
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  unfold pwTok osTok
  icases Ht with ⟨Ht, %hpw⟩
  obtain ⟨hgap, hd, hxl⟩ := hpw
  have hcanon : min off m.size = off := Nat.min_eq_left hgap
  have hdl : 0 < data.length := List.length_pos_iff.2 hd
  icases gAuth_lookup _ _ _ _ _ _ $$ HAt Ht with %Hti
  obtain ⟨c, hct⟩ : ∃ c, st.proc.inflight !! t = some c := by
    have := hcoh.toks t; rw [Hti] at this; exact Option.isSome_iff_exists.1 this.symm
  obtain ⟨hcino, hckind, hclo, hchi, hctg, hcval⟩ := hcoh.tok_is t _ c Hti hct
  obtain ⟨f, hf, hm0, -, -⟩ := hcoh.tok_file t _ Hti
  obtain ⟨f', hf', hcand⟩ := hcoh.tok_cand t _ Hti
  rw [hf] at hf'; cases hf'
  have Hml := hcoh.tok_meta t _ Hti
  have htm : TokInfo.meta ⟨p, .write off data, n, m, pwAnn data n xs⟩ =
      m.announce off (off + data.length) (max m.size (off + data.length)) := by
    simp only [TokInfo.meta, TokInfo.lo, TokInfo.hi, TokInfo.target, hcanon]
  simp only [TokInfo.lo, TokInfo.hi, TokInfo.target, TokInfo.val, hcanon] at hclo hchi hctg hcval hcand hcino hckind hm0 hf Hml
  have hmsz : m.size = f.size := hm0
  subst hcino
  -- the change's resources
  unfold tokRes
  icases (BigSepM.bigSepM_delete (Φ := fun (_t : Nat) (ti : TokInfo) =>
      iprop(gElem gooseOsGS gooseOsGS.γm ti.ino (DFrac.own 1) ti.meta ∗
        bytesG gooseOsGS ti.ino ti.lo (DFrac.own 1) ti.saved)) Hti).1 $$ Htok with ⟨⟨Hm, Hbs⟩, Htok⟩
  have htlo : TokInfo.lo ⟨c.ino, .write off data, n, m, pwAnn data n xs⟩ = off := by
    simp [TokInfo.lo, hcanon]
  rw [htlo]
  rw [show TokInfo.meta ⟨c.ino, .write off data, n, m, pwAnn data n xs⟩ =
      m.announce off (off + data.length) (max m.size (off + data.length)) from htm]
  icases bytesG_lookup _ c.ino _ _ _ Γb $$ HAb Hbs with %Hbl
  rw [show TokInfo.meta ⟨c.ino, .write off data, n, m, pwAnn data n xs⟩ =
      m.announce off (off + data.length) (max m.size (off + data.length)) from htm] at Hml
  obtain ⟨f1, hf1, hmo⟩ := coh_meta hcoh Hml
  rw [hf] at hf1; cases hf1
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hgapf : off ≤ f.size := hmsz ▸ hgap
  have hszs := hwf.sizes c.ino f hf
  -- the bytes the change holds
  have hxs : ∀ j (hj : j < xs.length), (xs[j]).1 = f.cache (off + j) ∧
      f.cand (off + j) = (xs[j]).2 ++ [(data.getD j 0, n)] := by
    intro j hj
    obtain ⟨f1, hf1, -, hx⟩ := hcoh.bytes _ _ _ (Hbl j (by simpa using hj))
    rw [hf] at hf1; cases hf1
    rw [pwAnn_getElem] at hx
    simp only [Prod.mk.injEq] at hx
    exact ⟨hx.1, hx.2.symm⟩
  have hval : ∀ b, off ≤ b → b < off + data.length → c.val b = data.getD (b - off) 0 := by
    intro b h1 h2
    have hin : inRange c.lo c.hi b = true := by
      simp only [inRange, Bool.and_eq_true, decide_eq_true_eq, hclo, hchi]; exact ⟨h1, h2⟩
    rw [hcval b hin, if_pos h1]
  have hcandI : ∀ b, off ≤ b → b < off + data.length → ∃ c0, f.cand b = c0 ++ [(data.getD (b - off) 0, n)] ∧
      (∀ z, m.zf = some z → z ≤ b → c0 = [(0, 0)]) ∧
      ∀ c, m.size ≤ b → m.tc !! b = some c → c0 = c := by
    intro b h1 h2
    obtain ⟨c0, hc0, hz, htc⟩ := hcand b (by simp only [inRange, Bool.and_eq_true, decide_eq_true_eq]; omega)
    rw [if_pos h1] at hc0
    exact ⟨c0, hc0, hz, htc⟩
  have Hh : ∀ l, Mapped st l → (h !! l).isSome := by
    intro l hm
    obtain ⟨x, hx⟩ := cellView_isSome hwf hm
    obtain ⟨m0, hm0⟩ := Hag l x hx
    rw [hm0]; rfl
  have hfin := fun (k : Nat) (_hk : k ≤ data.length) => osWf_setFile' (osWf_done (t := t) hwf)
    (f' := pwFile f c off k) hf
    (by simp only [pwFile, OsFile.land]; omega)
    (fun b p0 hp0 => hwf.stamps c.ino f b p0 hf hp0)
  imodintro
  isplitr
  · ipureintro
    exact ⟨_, renderHeap (pwState st t c.ino f c off data.length) h, _,
      ⟨t, c, off, data, f, data.length, 0, rfl, hct, hckind, hf, Nat.le_refl _, .inl ⟨.inl rfl, rfl⟩,
        rfl, rfl⟩, mapsFresh_same rfl, heapRendered_render (hfin _ (Nat.le_refl _)) rfl Hh⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsFsStep] at Hst
  obtain ⟨t', c', off', data', f', k, e, hv, hinfl, hkind', hf', hk, hke, hst', rfl⟩ := Hst
  have htt : t = t' := by injection hv with hv; exact extVal_inj hv
  subst htt
  rw [hct, Option.some.injEq] at hinfl; subst hinfl
  rw [hckind] at hkind'
  injection hkind' with ho hd'; subst ho; subst hd'
  rw [hf, Option.some.injEq] at hf'; subst hf'
  subst hst'
  have hwf2 := hfin k hk
  have hsz2 : (pwFile f c off k).size = pwSize f.size off k := pwFile_size f c off k hclo hgapf
  have hcache := fun b => pwFile_cache f c off k b hclo
  have hpsz : ∀ b, b < pwSize f.size off k ↔ b < f.size ∨ (0 < k ∧ b < off + k) := by
    intro b; simp only [pwSize]; split <;> omega
  -- the new bytes' candidates before the change
  obtain ⟨zs, hzs0⟩ : ∃ zs : List Cands,
      zs = (List.range (pwSize f.size off k - f.size)).map (fun j => (f.cand (f.size + j)).dropLast) :=
    ⟨_, rfl⟩
  have hzsl : zs.length = pwSize f.size off k - f.size := by simp [hzs0]
  have hzs : ∀ b, f.size ≤ b → b < pwSize f.size off k →
      f.cand b = zs.getD (b - f.size) [] ++ [(data.getD (b - off) 0, n)] := by
    intro b h1 h2
    have h2' := (hpsz b).1 h2
    obtain ⟨c0, hc0, -⟩ := hcandI b (by omega) (by omega)
    rw [hc0]
    congr 1
    rw [List.getD_eq_getElem?_getD]
    simp only [hzs0, List.getElem?_map, List.getElem?_range (show b - f.size < pwSize f.size off k - f.size by omega),
      Option.map_some, Option.getD_some, show f.size + (b - f.size) = b by omega, hc0]
    simp
  -- the ghost maps
  obtain ⟨ys, hys0⟩ : ∃ ys, ys = pwBytes m.size off data k n xs zs := ⟨_, rfl⟩
  have hysl : ys.length = min (off + data.length) (pwSize f.size off k) - off := by
    simp only [hys0, pwBytes_length, hmsz]
  have hpp : pwPostK keep m off data k n =
      { m.announce off (off + data.length) (max m.size (off + data.length)) with
        size := pwSize m.size off k,
        tc := cond keep (pwTail m off data n)
          (m.announce off (off + data.length) (max m.size (off + data.length))).tc } := by
    simp only [pwPostK, pwPost, hcanon]
  have hcoh2 : OsCoh (pwState st t c.ino f c off k) (insertBytes c.ino off ys Γb)
      (<[c.ino := pwPostK keep m off data k n]> Γm) Γf (GMap.delete t Γt) := by
    refine osCoh_setFile (osCoh_done hcoh) hf
      (noTok_done hwf hcoh hct) _ _ _ rfl rfl ?_ ?_ ?_ ?_
    · -- the OsMeta
      have hlo := hmo.lo
      have hhi := hmo.hi
      simp only [announce_lo, announce_hi] at hlo hhi
      rw [hpp]
      refine ⟨by simp only [hsz2, hmsz], ?_, ?_,
        fun b len => by
          have h1 := hmo.maps b len; simp only [announce_maps] at h1; simp only [announce_maps]
          exact h1,
        fun t2 c2 h1 h2 => ?_, fun b hb hn => ?_, fun z hz => ?_, fun b cs hb hc => ?_⟩
      rotate_right
      · rw [show (pwFile f c off k).cand b = f.cand b from rfl]
        rw [hsz2] at hb
        have hfb : f.size ≤ b := by
          have : f.size ≤ pwSize f.size off k := by unfold pwSize; split <;> omega
          omega
        cases keep with
        | false => exact hmo.tail b cs hfb hc
        | true =>
          change pwTail m off data n !! b = some cs at hc
          rw [pwTail_lookup] at hc
          split at hc
          · rename_i hr
            split at hc
            · rename_i hms
              obtain ⟨c1, hc1, rfl⟩ := Option.map_eq_some_iff.1 hc
              simp only [inRange, Bool.and_eq_true, decide_eq_true_eq] at hr
              obtain ⟨c0, hc0, hz0, htc⟩ := hcand b
                (by simp only [inRange, Bool.and_eq_true, decide_eq_true_eq]; omega)
              rw [if_pos hr.1] at hc0
              rw [hc0]
              congr 1
              rcases OsMeta.pc_some hc1 with ht | ⟨z, hz, hzb, rfl⟩
              · exact htc c1 hms ht
              · exact hz0 z hz hzb
            · cases hc
          · rename_i hr
            exact hmo.tail b cs hfb (by rw [announce_tc, if_neg hr]; exact hc)
      · simp only [pwFile, OsFile.land, announce_lo]; omega
      · simp only [pwFile, OsFile.land, announce_hi]; split <;> omega
      · exfalso
        have h1' := doneInflight_sub st t t2 c2 h1
        have := hwf.infl_one t2 c2 t c h1' hct h2
        subst this; simp [OsState.setFile, OsState.doneInflight] at h1
      · have hn' : ¬ ((m.touch off (off + data.length)).dlo ≤ b ∧
            b < (m.touch off (off + data.length)).dhi) := hn
        obtain ⟨h1, h2⟩ := not_touch hn'
        rw [hsz2] at hb
        have hb' : b < f.size := by have := (hpsz b).1 hb; omega
        have := hmo.dur b hb' hn
        rw [show (pwFile f c off k).cand b = f.cand b from rfl, this, hcache b, if_neg (by omega)]
      · simp only [announce_zf, Option.map_eq_some_iff] at hz
        obtain ⟨z0, hz0, rfl⟩ := hz
        have := hmo.zf _ (by simp only [announce_zf, hz0]; rfl)
        refine ⟨?_, fun b hb => this.2 b hb⟩
        rw [hsz2]
        have hlt : off < off + data.length := by omega
        have h1 := this.1
        simp only [hlt, if_true] at h1 ⊢
        simp only [pwSize]; split <;> omega
    · intro b x hx
      rw [lookup_insertBytes] at hx
      split at hx
      · rename_i hr
        obtain ⟨-, h1, h2⟩ := hr
        have hj : b - off < ys.length := by omega
        rw [List.getElem?_eq_getElem hj] at hx; cases hx
        have hbz : b < pwSize f.size off k := by rw [hysl] at hj; omega
        have hbo : b < off + data.length := by rw [hysl] at hj; omega
        refine ⟨by rw [hsz2]; exact hbz, ?_⟩
        simp only [hys0, pwBytes, List.getElem_map, List.getElem_range]
        simp only [Prod.mk.injEq]
        constructor
        · rw [show off + (b - off) = b by omega, hcache b]
          unfold pwByte
          by_cases hlt : b < off + k
          · rw [if_pos hlt, if_pos ⟨h1, hlt⟩, hval b h1 hbo]
          · rw [if_neg hlt, if_neg (fun h => hlt h.2)]
            have hbx : b - off < xs.length := by
              have := (hpsz b).1 hbz; rw [hxl, hmsz]; omega
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hbx]
            simp only [Option.getD_some]
            have := (hxs _ hbx).1; rw [show off + (b - off) = b by omega] at this; exact this
        · show _ = f.cand b
          by_cases hbx : b - off < xs.length
          · rw [if_pos hbx]
            have := (hxs _ hbx).2
            rw [show off + (b - off) = b by omega] at this
            rw [this, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hbx]; rfl
          · rw [if_neg hbx]
            have hfb : f.size ≤ b := by rw [hxl, hmsz] at hbx; omega
            rw [hzs b hfb hbz, hxl, hmsz]
            congr 2; omega
      · obtain ⟨f1, hf1, hb, hx1⟩ := hcoh.bytes _ _ _ hx
        rw [hf] at hf1; cases hf1
        rename_i hr
        refine ⟨by rw [hsz2]; exact (hpsz b).2 (.inl hb), ?_⟩
        have hnot : ¬ (off ≤ b ∧ b < off + k) := by
          rintro ⟨h1, h2⟩
          apply hr; refine ⟨rfl, h1, ?_⟩
          rw [hysl]; have := (hpsz b).2 (.inr ⟨by omega, h2⟩); omega
        rw [hx1, hcache b, if_neg hnot]; rfl
    · intro b hb
      rw [lookup_insertBytes]
      split
      · rename_i hr; rw [List.getElem?_eq_getElem (by omega)]; rfl
      · rename_i hr
        apply hcoh.bytes_full _ f b hf
        rw [hsz2] at hb
        apply Classical.byContradiction; intro hfb
        apply hr; refine ⟨rfl, ?_, ?_⟩
        · have := (hpsz b).1 hb; omega
        · rw [hysl]; have := (hpsz b).1 hb; omega
    · intro q b hq; rw [lookup_insertBytes, if_neg (fun h => hq h.1)]
  -- the cells
  have hI2 := fun q i => (inflightAt_done (t := t) (c := c) hwf hct q i)
  have hmaps : ∀ b len, m.maps !! b = some len ↔ st.proc.maps !! b = some ⟨c.ino, len⟩ := by
    intro b len; have := hmo.maps b len; simpa using this
  have hdisj : MapsDisj m.maps.toList := mapsDisj_toList _ (fun b1 l1 b2 l2 h1 h2 hne =>
    hwf.maps_disj b1 _ b2 _ ((hmaps b1 l1).1 h1) ((hmaps b2 l2).1 h2) hne)
  generalize hC : mapsCells off (off + data.length) (pwCell m.size off data k xs) m.maps.toList = C
  have hClk := fun l v => hC ▸ lookup_mapsCells off (off + data.length)
    (pwCell m.size off data k xs) m.maps.toList hdisj l v
  have hTmem : ∀ l, l ∈ C.toList.map (·.1) ↔ (C !! l).isSome := by
    intro l; simp only [List.mem_map]
    constructor
    · rintro ⟨⟨k, v⟩, hkv, rfl⟩; rw [(GMap.mem_toList _ _ _).1 hkv]; rfl
    · intro hl; obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hl
      exact ⟨(l, v), (GMap.mem_toList _ _ _).2 hv, rfl⟩
  have hTnd : (C.toList.map (·.1)).Nodup := Iris.Std.LawfulFiniteMap.toList_noDupKeys (m := C)
  have hin : ∀ l, (C !! l).isSome → ∃ i, MapsTo st l c.ino i ∧ off ≤ i ∧ i < off + data.length ∧
      C !! l = some (pwCell m.size off data k xs i) := by
    intro l hl
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hl
    obtain ⟨i, ⟨b, len, hm, h1, h2, h3, rfl⟩, rfl⟩ := (hClk _ v).1 hv
    exact ⟨i, ⟨b, ⟨c.ino, len⟩, (hmaps b len).1 ((GMap.mem_toList _ _ _).1 hm), rfl, h3, rfl⟩,
      h1, h2, hv⟩
  have hfk : (pwState st t c.ino f c off k).file c.ino = some (pwFile f c off k) :=
    file_setFile_eq _ _ _
  have hcont_in : ∀ i, off ≤ i → i < off + data.length →
      (pwFile f c off k).contents[i]? =
        if i < pwSize m.size off k then some (pwByte off data k xs i) else none := by
    intro i h1 h2
    rw [contents_getElem?, hsz2, hmsz]
    by_cases hlt : i < pwSize f.size off k
    · rw [if_pos hlt, if_pos hlt, hcache i]
      congr 1
      unfold pwByte
      by_cases hk1 : i < off + k
      · rw [if_pos ⟨h1, hk1⟩, if_pos hk1, hval i h1 h2]
      · rw [if_neg (fun h => hk1 h.2), if_neg hk1]
        have hbx : i - off < xs.length := by
          have := (hpsz i).1 hlt; rw [hxl, hmsz]; omega
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hbx]
        simp only [Option.getD_some]
        have := (hxs _ hbx).1; rw [show off + (i - off) = i by omega] at this; exact this.symm
    · rw [if_neg hlt, if_neg hlt]
  have hcont_out : ∀ i, ¬ (off ≤ i ∧ i < off + data.length) →
      (pwFile f c off k).contents[i]? = f.contents[i]? := by
    intro i hi
    have hc := hcache i
    rw [if_neg (fun h => hi ⟨h.1, by omega⟩)] at hc
    rw [contents_getElem?, contents_getElem?, hsz2, hc]
    by_cases h1 : i < f.size
    · rw [if_pos ((hpsz i).2 (.inl h1)), if_pos h1]
    · rw [if_neg h1, if_neg]; intro h; have := (hpsz i).1 h; omega
  imod cells_step st _ h h' (C.toList.map (·.1)) ∅ C hwf hwf2 Hr Hfr (fun b m0 h0 => .inr h0) hTnd
    (fun l hl => by obtain ⟨i, hi, -⟩ := hin l ((hTmem l).1 hl); exact .inl ⟨_, _, hi⟩)
    (fun l v h => by simp at h)
    (fun l v hl => by
      have hs : (C !! l).isSome := by rw [hl]; rfl
      obtain ⟨i, hi, h1, h2, hv⟩ := hin l hs
      rw [hl] at hv; cases hv
      have hn : ¬ InflightAt (pwState st t c.ino f c off k) c.ino i := fun h =>
        ((hI2 _ _).1 h).2 rfl
      refine ⟨(hTmem l).2 hs, _, by rw [cellView_mapsTo hwf2 hi, decide_eq_false hn], ?_⟩
      rw [cellByte_eq, if_neg hn, hfk]
      simp only [Option.bind_some]
      rw [hcont_in i h1 h2]; rfl)
    (fun l hl _ x hx => by
      obtain ⟨i, hi, h1, h2, -⟩ := hin l ((hTmem l).1 hl)
      rw [cellView_mapsTo hwf hi] at hx; cases hx
      exact decide_eq_true ⟨t, c, hct, rfl, by
        simp only [inRange, Bool.and_eq_true, decide_eq_true_eq, hclo, hchi]; exact ⟨h1, h2⟩⟩)
    (fun l hl hn => by
      rw [Option.isSome_iff_exists.1 ((hTmem l).1 hl) |>.choose_spec] at hn; cases hn)
    (fun l hl => by
      by_cases hm : Mapped st l
      · obtain ⟨q', i, hqi⟩ := hm
        rw [cellView_mapsTo hwf2 hqi, cellView_mapsTo hwf hqi, cellByte_eq, cellByte_eq]
        by_cases hpq : c.ino = q'
        · subst hpq
          have hn : ¬ (off ≤ i ∧ i < off + data.length) := by
            rintro ⟨h1, h2⟩
            obtain ⟨b, m0, hb, hp0, hi0, rfl⟩ := hqi
            have hb' : m.maps !! b = some m0.len :=
              (hmaps b m0.len).2 (by rw [hb]; congr 1; cases m0; simp only at hp0 ⊢; rw [hp0])
            apply hl; apply (hTmem _).2
            rw [(hClk _ _).2 ⟨i, ⟨b, m0.len, (GMap.mem_toList _ _ _).2 hb', h1, h2, hi0, rfl⟩, rfl⟩]
            rfl
          have hnI : ¬ InflightAt st c.ino i := by
            rintro ⟨t2, c2, h1, h2, h3⟩
            have := hwf.infl_one t2 c2 t c h1 hct h2; subst this
            rw [hct] at h1; cases h1
            apply hn
            simp only [inRange, Bool.and_eq_true, decide_eq_true_eq, hclo, hchi] at h3; exact h3
          have hnI2 : ¬ InflightAt (pwState st t c.ino f c off k) c.ino i := fun h =>
            ((hI2 _ _).1 h).2 rfl
          rw [if_neg hnI, if_neg hnI2, hfk, hf]
          simp only [Option.bind_some]
          rw [hcont_out i hn]
          simp only [hnI, hnI2, decide_false]
        · have hII : InflightAt (pwState st t c.ino f c off k) q' i ↔ InflightAt st q' i := by
            have := hI2 q' i
            exact ⟨fun h => (this.1 h).1, fun h => this.2 ⟨h, fun e => hpq e.symm⟩⟩
          have hF : (pwState st t c.ino f c off k).file q' = st.file q' := file_setFile_ne _ _ hpq
          rw [hF]
          by_cases hq : InflightAt st q' i
          · rw [if_pos hq, if_pos (hII.2 hq)]; simp only [hII]
          · rw [if_neg hq, if_neg (fun h => hq (hII.1 h))]; simp only [hII]
      · rw [cellView_none (st := st) hm]; exact cellView_none hm)
    $$ [Hσ Hcells] with ⟨Hσ, Hcells, Hc⟩
  · iframe; unfold halves; iapply BigSepM.bigSepM_empty.2; iempintro
  -- the ghost resources
  imod gAuth_update _ _ _ _ _ (pwPostK keep m off data k n) $$ HAm Hm with ⟨HAm, Hm⟩
  have hl1 : (pwAnn data n xs).length = xs.length := pwAnn_length _ _ _
  have hys1 : (ys.take xs.length).length = xs.length := by
    rw [List.length_take, hysl, hxl, hmsz]; simp only [pwSize]; split <;> omega
  imod bytesG_update _ c.ino off (pwAnn data n xs) (ys.take xs.length) Γb (by rw [hys1, hl1])
    $$ [HAb Hbs] with ⟨HAb, Hbs1⟩
  · iframe
  have hfree : ∀ j, j < (ys.drop xs.length).length →
      insertBytes c.ino off (ys.take xs.length) Γb !! (c.ino, off + xs.length + j) = none := by
    intro j hj
    rw [lookup_insertBytes, if_neg (by rw [hys1]; omega)]
    cases hb : Γb !! (c.ino, off + xs.length + j) with
    | none => rfl
    | some x =>
      exfalso
      obtain ⟨f2, hf2, hb2, -⟩ := hcoh.bytes _ _ _ hb
      rw [hf] at hf2; cases hf2
      simp only [List.length_drop, hysl] at hj
      rw [hxl, hmsz] at hb2; simp only [pwSize] at hj; split at hj <;> omega
  imod bytesG_alloc _ c.ino (off + xs.length) (ys.drop xs.length) _ hfree $$ HAb
    with ⟨HAb, Hbs2⟩
  have hins : insertBytes c.ino (off + xs.length) (ys.drop xs.length)
      (insertBytes c.ino off (ys.take xs.length) Γb) = insertBytes c.ino off ys Γb := by
    conv => rhs; rw [← List.take_append_drop xs.length ys]
    rw [insertBytes_append, hys1]
  rw [hins]
  ihave Hbs := (bytesG_append _ c.ino _ off (ys.take xs.length) (ys.drop xs.length)).2 $$ [Hbs1 Hbs2]
  · rw [hys1]; iframe
  rw [List.take_append_drop]
  imod gAuth_delete _ _ _ _ _ $$ HAt Ht with HAt
  have hzsfact : ∀ j z, m.zf = some z → z ≤ m.size + j → j < zs.length → zs[j]? = some [(0, 0)] := by
    intro j z hz hzj hj
    rw [hzsl] at hj
    have hjb := (hpsz (f.size + j)).1 (by omega)
    obtain ⟨c0, hc0, hz0, -⟩ := hcandI (f.size + j) (by omega) (by omega)
    have := hz0 z hz (by rw [← hmsz]; exact hzj)
    simp only [hzs0, List.getElem?_map, List.getElem?_range hj, hc0, this, Option.map_some]
    simp
  imodintro
  iexists _, _, Γf, _
  iframe HAb HAm HAf HAt Hσ Hcells Htok
  isplitr
  · ipureintro; exact ⟨hwf2, hcoh2⟩
  iapply wp_value'
  unfold osMeta osBytes
  subst hys0
  have hzstc : ∀ j c, m.pc (m.size + j) = some c → j < zs.length → zs[j]? = some c := by
    intro j c hc hj
    rw [hzsl] at hj
    have hjb := (hpsz (f.size + j)).1 (by omega)
    obtain ⟨c0, hc0, hz0, htc⟩ := hcandI (f.size + j) (by omega) (by omega)
    have : c0 = c := by
      rcases OsMeta.pc_some hc with ht | ⟨z, hz, hzb, rfl⟩
      · exact htc c (by omega) (by rw [← hmsz]; exact ht)
      · exact hz0 z hz (by rw [← hmsz]; exact hzb)
    simp only [hzs0, List.getElem?_map, List.getElem?_range hj, hc0, this, Option.map_some]
    simp
  iapply HΦ $$ %k %e %zs %(⟨hk, hke, by rw [hzsl, hmsz], hzsfact⟩) %hzstc Hm Hbs
  unfold mcells
  iapply (BigSepM.bigSepM_toList (Φ := fun (b : Loc) (len : Nat) =>
    cellsR b (min off len) (min (off + data.length) len - min off len)
      (pwCell m.size off data k xs))).2
  iapply (halves_mapsCells _ _ _ _ hdisj).1
  rw [hC]; iexact Hc

/-- `wp_osPWriteFinishK` forgetting the candidates past the size: the `OsMeta` it leaves is
`pwPost`'s. -/
theorem wp_osPWriteFinish (t : Nat) (p : Ino) (off : Nat) (data : List w8) (m : OsMeta)
    (xs : List ByteG) (n : Nat) (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ pwTok (L := L) t p off data m xs n -∗
      (∀ k : Nat, ∀ e : w64, ∀ zs : List Cands,
        ⌜k ≤ data.length ∧ ((k = data.length ∨ 0 < k) ∧ e = 0 ∨ e ≠ 0) ∧
          zs.length = pwSize m.size off k - m.size ∧
          ∀ j z, m.zf = some z → z ≤ m.size + j → j < zs.length → zs[j]? = some [(0, 0)]⌝ -∗
        osMeta (L := L) p (DFrac.own 1) (pwPost m off data.length k) -∗
        osBytes (L := L) p off (DFrac.own 1) (pwBytes m.size off data k n xs zs) -∗
        mcells m.maps off (off + data.length) (pwCell m.size off data k xs) -∗
        Φ (PairV (#(W64 k)) (#e))) -∗
      WP (ExternalOp fsExt.name "PWriteFinish" (Val (osTokV t))) @ s; E {{ Φ }} := by
  iintro #Hinv Ht HΦ
  iapply wp_osPWriteFinishK false t p off data m xs n hE Φ $$ Hinv Ht
  iintro %k %e %zs %h %- Hm Hbs Hc
  rw [pwPostK_false]
  iapply HΦ $$ %k %e %zs %h Hm Hbs Hc

end specs2

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
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [GoGlobalContext]
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

end Fs
end Perennial

end
