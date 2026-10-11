/-
Carving a reader's pages out of the database's slots (and giving them back).

The database holds slot `s` of the mapping at `rem s`; a reader that begins takes `q` of every
slot its pages cover (`coversSlot`), as its pages (`pagesView`). `slots_carve`: the slots at
`rem` are the slots at `rem'` and the reader's pages at `q`, where `rem s = rem' s + q` on the
covered slots and `rem s = rem' s` elsewhere. Through `cellsIf q S n`, the cells at `q` of the
slots below `n` in `S`: they split along a disjoint union (`cellsIf_or`), and those of an
interval are its slots (`cellsIf_range`), so those of disjoint pages are the pages
(`cellsIf_pages`).
-/
module

public import Proof.go_etcd_io.bbolt.FilePages

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode

/-- A page's overflow is its first slot's (the header is in the first slot). -/
theorem pageOverflow_pageAt (bs : List w8) (ps id : Nat) (hps : 16 ≤ ps) :
    pageOverflow (pageAt bs ps id) = pageOverflow (slotAt bs ps id) := by
  have hA : ps ≤ pageSpan bs ps id * ps := by
    unfold pageSpan; rw [Nat.add_mul, Nat.one_mul]; omega
  unfold pageOverflow leAt pageAt slotAt
  simp only [List.drop_take, List.take_take]
  congr 3
  omega

section carve
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- Slot `s`'s cells at the fraction `q`. -/
def cellAt (data : Loc) (bs : List w8) (ps : Nat) (q : Qp) (s : Nat) : IProp GF :=
  bytesPointsto (data +ₗ ((s * ps : Nat) : Int)) (DFrac.own q) (slotAt bs ps s)

open Classical in
/-- The cells at `q` of the slots below `n` in `S`. -/
def cellsIf (data : Loc) (bs : List w8) (ps : Nat) (q : Qp) (S : Nat → Prop) (n : Nat) :
    IProp GF :=
  [∗list] s ∈ List.range n, if S s then cellAt data bs ps q s else emp

/-- Pointwise equivalent big separating conjunctions (on the list's elements). -/
theorem bigSepL_congr_mem {A : Type} {Φ Ψ : Nat → A → IProp GF} {l : List A}
    (h : ∀ k x, x ∈ l → (Φ k x ⊣⊢ Ψ k x)) :
    ([∗list] k ↦ x ∈ l, Φ k x) ⊣⊢ [∗list] k ↦ x ∈ l, Ψ k x :=
  ⟨BigSepL.bigSepL_mono fun {k x} hx => (h k x (List.mem_of_getElem? hx)).1,
   BigSepL.bigSepL_mono fun {k x} hx => (h k x (List.mem_of_getElem? hx)).2⟩

theorem cell_split (data : Loc) (bs : List w8) (ps : Nat) (a b : Qp) (s : Nat) :
    cellAt (GF := GF) data bs ps (a + b) s ⊣⊢ cellAt data bs ps a s ∗ cellAt data bs ps b s := by
  unfold cellAt
  exact (bytesPointsto_dfractional (GF := GF) _ _).dfractional (DFrac.own a) (DFrac.own b)

theorem emp_sep_eqv' (P : IProp GF) : P ⊣⊢ P ∗ emp := sep_emp.symm

open Classical in
/-- The database's slots at `rem` are its slots at `rem'` and the cells at `q` of `S`. -/
theorem slots_split (data : Loc) (bs : List w8) (ps : Nat) (rem rem' : Nat → Qp) (q : Qp)
    (S : Nat → Prop) (n : Nat)
    (hS : ∀ s < n, S s → rem s = rem' s + q) (hN : ∀ s < n, ¬ S s → rem s = rem' s) :
    slotsView (GF := GF) data bs ps rem (List.range n) ⊣⊢
      slotsView data bs ps rem' (List.range n) ∗ cellsIf data bs ps q S n := by
  unfold slotsView cellsIf
  refine Iris.BI.BiEntails.trans ?_ BigSepL.bigSepL_sep_eqv
  refine bigSepL_congr_mem fun _ x hx => ?_
  have hxn : x < n := List.mem_range.1 hx
  by_cases h : S x
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h), hS x hxn h]
    exact cell_split data bs ps (rem' x) q x
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h), hN x hxn h]
    exact emp_sep_eqv' _

open Classical in
/-- The cells of a disjoint union. -/
theorem cellsIf_or (data : Loc) (bs : List w8) (ps : Nat) (q : Qp) (S1 S2 : Nat → Prop)
    (n : Nat) (hd : ∀ s < n, S1 s → S2 s → False) :
    cellsIf (GF := GF) data bs ps q (fun s => S1 s ∨ S2 s) n ⊣⊢
      cellsIf data bs ps q S1 n ∗ cellsIf data bs ps q S2 n := by
  unfold cellsIf
  refine Iris.BI.BiEntails.trans ?_ BigSepL.bigSepL_sep_eqv
  refine bigSepL_congr_mem fun _ x hx => ?_
  have hxn : x < n := List.mem_range.1 hx
  by_cases h1 : S1 x <;> by_cases h2 : S2 x
  · exact absurd (hd x hxn h1 h2) id
  · rw [ite_eq_left_of_eq_true _ _ (eq_true (Or.inl h1)), ite_eq_left_of_eq_true _ _ (eq_true h1), ite_eq_right_of_eq_false _ _ (eq_false h2)]; exact emp_sep_eqv' _
  · rw [ite_eq_left_of_eq_true _ _ (eq_true (Or.inr h2)), ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_left_of_eq_true _ _ (eq_true h2)]; exact emp_sep.symm
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (show ¬(S1 x ∨ S2 x) from fun h => h.elim h1 h2)), ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_right_of_eq_false _ _ (eq_false h2)]
    exact emp_sep.symm

open Classical in
/-- The cells of equivalent sets. -/
theorem cellsIf_ext (data : Loc) (bs : List w8) (ps : Nat) (q : Qp) (S1 S2 : Nat → Prop)
    (n : Nat) (h : ∀ s < n, (S1 s ↔ S2 s)) :
    cellsIf (GF := GF) data bs ps q S1 n ⊣⊢ cellsIf data bs ps q S2 n := by
  unfold cellsIf
  refine bigSepL_congr_mem fun _ x hx => ?_
  have hxn : x < n := List.mem_range.1 hx
  by_cases h1 : S1 x
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h1), ite_eq_left_of_eq_true _ _ (eq_true ((h x hxn).1 h1))]; exact .rfl
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_right_of_eq_false _ _ (eq_false (fun h2 => h1 ((h x hxn).2 h2)))]; exact .rfl

open Classical in
/-- No cells. -/
theorem cellsIf_false (data : Loc) (bs : List w8) (ps : Nat) (q : Qp) (n : Nat) :
    cellsIf (GF := GF) data bs ps q (fun _ => False) n ⊣⊢ emp := by
  unfold cellsIf
  simp only [ite_false]
  exact BigSepL.bigSepL_emp

open Classical in
theorem bigSepL_ite_range' (data : Loc) (bs : List w8) (ps : Nat) (q : Qp) (S : Nat → Prop)
    (a k : Nat) (h : ∀ s, a ≤ s → s < a + k → ¬ S s) :
    ([∗list] s ∈ List.range' a k, if S s then cellAt (GF := GF) data bs ps q s else emp) ⊣⊢
      emp := by
  refine Iris.BI.BiEntails.trans (bigSepL_congr_mem fun _ x hx => ?_) BigSepL.bigSepL_emp
  rw [List.mem_range'_1] at hx
  rw [ite_eq_right_of_eq_false _ _ (eq_false (h x hx.1 hx.2))]; exact .rfl

open Classical in
/-- The cells of an interval inside `n` are its slots. -/
theorem cellsIf_range (data : Loc) (bs : List w8) (ps : Nat) (q : Qp) (a k n : Nat)
    (hk : a + k ≤ n) :
    cellsIf (GF := GF) data bs ps q (fun s => a ≤ s ∧ s < a + k) n ⊣⊢
      [∗list] s ∈ List.range' a k, cellAt data bs ps q s := by
  unfold cellsIf
  have Hr : List.range n = List.range' 0 a ++ (List.range' a k ++ List.range' (a + k) (n - a - k)) := by
    have e1 : List.range' a k ++ List.range' (a + k) (n - a - k) = List.range' a (k + (n - a - k)) :=
      List.range'_append_1 (s := a) (m := k)
    have e2 : List.range' 0 a ++ List.range' a (k + (n - a - k)) =
        List.range' 0 (a + (k + (n - a - k))) := by
      have := List.range'_append_1 (s := 0) (m := a) (n := k + (n - a - k)); rwa [Nat.zero_add] at this
    rw [e1, e2, List.range_eq_range']
    congr 1; omega
  rw [Hr]
  refine BigSepL.bigSepL_append.trans ?_
  refine (sep_congr (bigSepL_ite_range' data bs ps q _ 0 a (fun s _ h2 h => by omega))
    BigSepL.bigSepL_append).trans ?_
  refine emp_sep.trans ?_
  refine (sep_congr .rfl (bigSepL_ite_range' data bs ps q _ (a + k) (n - a - k)
    (fun s h1 _ h => by omega))).trans ?_
  refine sep_emp.trans ?_
  refine bigSepL_congr_mem fun _ x hx => ?_
  rw [List.mem_range'_1] at hx
  rw [ite_eq_left_of_eq_true _ _ (eq_true hx)]; exact .rfl

/-- The cells of disjoint pages of the file (inside `n`) are the pages. -/
theorem cellsIf_pages (data : Loc) (bs : List w8) (ps : Nat) (q : Qp) (n : Nat)
    (hps : 16 ≤ ps) (hfit : n * ps ≤ bs.length) :
    ∀ (P : GMap Nat (List w8)),
    (∀ id pg, P !! id = some pg → pg = pageAt bs ps id ∧ id + pageSpan bs ps id ≤ n) →
    pagesDisjoint P →
    cellsIf (GF := GF) data bs ps q (coversSlot P) n ⊣⊢ pagesView data ps q P := by
  intro P
  induction P using GMap.map_ind with
  | h0 =>
    intro _ _
    refine (cellsIf_ext data bs ps q _ (fun _ => False) n (fun s _ => ?_)).trans ?_
    · simp [coversSlot]
    refine (cellsIf_false data bs ps q n).trans ?_
    unfold pagesView
    exact BigSepM.bigSepM_empty.symm
  | hins id pg P hid ih =>
    intro hP hdisj
    have ⟨hpg, hin⟩ := hP id pg (GMap.lookup_insert P id pg)
    have hP' : ∀ id' pg', P !! id' = some pg' →
        pg' = pageAt bs ps id' ∧ id' + pageSpan bs ps id' ≤ n := by
      intro id' pg' h
      have hne : id ≠ id' := by rintro rfl; rw [hid] at h; cases h
      exact hP id' pg' (by rw [GMap.lookup_insert_ne P pg hne]; exact h)
    have hdisj' : pagesDisjoint P := by
      intro i1 p1 i2 p2 h1 h2 hne
      have hn1 : id ≠ i1 := by rintro rfl; rw [hid] at h1; cases h1
      have hn2 : id ≠ i2 := by rintro rfl; rw [hid] at h2; cases h2
      exact hdisj i1 p1 i2 p2 (by rw [GMap.lookup_insert_ne P pg hn1]; exact h1)
        (by rw [GMap.lookup_insert_ne P pg hn2]; exact h2) hne
    have hspan : 1 + pageOverflow pg = pageSpan bs ps id := by
      rw [hpg, pageOverflow_pageAt bs ps id hps]; rfl
    -- the inserted page's slots, and the others'
    have hcov : ∀ s < n, (coversSlot (<[id := pg]> P) s ↔
        ((id ≤ s ∧ s < id + pageSpan bs ps id) ∨ coversSlot P s)) := by
      intro s _
      unfold coversSlot
      constructor
      · rintro ⟨i, p, h, h1, h2⟩
        rw [GMap.lookup_insert_Some] at h
        rcases h with ⟨rfl, rfl⟩ | ⟨_, h⟩
        · left; rw [← hspan]; exact ⟨h1, h2⟩
        · right; exact ⟨i, p, h, h1, h2⟩
      · rintro (⟨h1, h2⟩ | ⟨i, p, h, h1, h2⟩)
        · exact ⟨id, pg, GMap.lookup_insert P id pg, h1, by rw [hspan]; exact h2⟩
        · have hne : id ≠ i := by rintro rfl; rw [hid] at h; cases h
          exact ⟨i, p, by rw [GMap.lookup_insert_ne P pg hne]; exact h, h1, h2⟩
    have hd : ∀ s < n, (id ≤ s ∧ s < id + pageSpan bs ps id) → coversSlot P s → False := by
      rintro s _ ⟨h1, h2⟩ ⟨i, p, h, h3, h4⟩
      have hne : id ≠ i := by rintro rfl; rw [hid] at h; cases h
      rcases hdisj id pg i p (GMap.lookup_insert P id pg)
        (by rw [GMap.lookup_insert_ne P pg hne]; exact h) hne with h5 | h5
      · rw [hspan] at h5; omega
      · omega
    refine (cellsIf_ext data bs ps q _ _ n hcov).trans ?_
    refine (cellsIf_or data bs ps q _ _ n hd).trans ?_
    refine (sep_congr (cellsIf_range data bs ps q id _ n hin) (ih hP' hdisj')).trans ?_
    unfold pagesView
    refine Iris.BI.BiEntails.trans ?_ (BigSepM.bigSepM_insert hid).symm
    refine sep_congr ?_ .rfl
    rw [hpg]
    refine (pageAt_slots data bs ps q id ?_).symm
    have := Nat.mul_le_mul_right ps hin; omega

/-- The reader's pages carved out of the database's slots. -/
theorem slots_carve (data : Loc) (bs : List w8) (ps : Nat) (rem rem' : Nat → Qp) (q : Qp)
    (n : Nat) (P : GMap Nat (List w8)) (hps : 16 ≤ ps) (hfit : n * ps ≤ bs.length)
    (hP : ∀ id pg, P !! id = some pg → pg = pageAt bs ps id ∧ id + pageSpan bs ps id ≤ n)
    (hdisj : pagesDisjoint P)
    (hS : ∀ s < n, coversSlot P s → rem s = rem' s + q)
    (hN : ∀ s < n, ¬ coversSlot P s → rem s = rem' s) :
    slotsView (GF := GF) data bs ps rem (List.range n) ⊣⊢
      slotsView data bs ps rem' (List.range n) ∗ pagesView data ps q P :=
  (slots_split data bs ps rem rem' q _ n hS hN).trans
    (sep_congr .rfl (cellsIf_pages data bs ps q n hps hfit P hP hdisj))

end carve

end bbolt
end EtcdGrove
end Perennial
