/-
The remap's `W` slots (U4d, `notes/bbolt-proof-plan.md`; `Mmap/Remap`'s plan, steps 5 and 7):
`wdbOK` characterizes the writer's slots `W` only up to membership (`W` may repeat), so the remap
works over `wSlots k C fl`, the slots in `[2, k)` that are no store slot, without repeats: below
the old mapping's slot count they are `slots_partition`'s `ws` (the cells `munmap` gathers,
`wCells_gather`); below the new mapping's or the file's, the new `W` (`wCells_carve`,
`wBytes_restrict`).
-/
module

public import Proof.go_etcd_io.bbolt.Mmap.Cells

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section wslots
variable [GooseExts]

/-- The slots in `[2, k)` that are no store slot of `C`/`fl`, without repeats. -/
def wSlots (k : Nat) (C : CommitSt) (fl : FLPg) : List Nat :=
  (List.range k).filter (fun s => decide (2 ≤ s ∧ s ∉ slotsOf C fl))

theorem mem_wSlots (k : Nat) (C : CommitSt) (fl : FLPg) (s : Nat) :
    s ∈ wSlots k C fl ↔ 2 ≤ s ∧ s < k ∧ s ∉ slotsOf C fl := by
  unfold wSlots
  simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1, h3⟩

theorem wSlots_nodup (k : Nat) (C : CommitSt) (fl : FLPg) : (wSlots k C fl).Nodup :=
  List.Pairwise.filter _ List.nodup_range

/-- `wdbOK`'s `W` in terms of the store slots. -/
theorem wdbOK_mem_W (w : WDb) (hok : wdbOK w) (s : Nat) :
    s ∈ w.W ↔ 2 ≤ s ∧ s < max (mapLen w.ms) w.m.size / 4096 ∧ s ∉ slotsOf w.C w.fl := by
  rw [hok.2.2.2.1 s, mem_slotsOf]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨h1, h2, fun h => h.elim h3 h4⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, fun h => h3 (.inl h), fun h => h3 (.inr h)⟩

/-- A slot list with `wdbOK`'s membership: `wSlots` of the bound. -/
theorem mem_W_of_wSlots (C : CommitSt) (fl : FLPg) (k : Nat) (s : Nat) :
    s ∈ wSlots k C fl ↔ 2 ≤ s ∧ s < k ∧ s ∉ treeSlots C ∧ s ∉ pendSlots fl := by
  rw [mem_wSlots, mem_slotsOf]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, fun h => h3 (.inl h), fun h => h3 (.inr h)⟩
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨h1, h2, fun h => h.elim h3 h4⟩

end wslots

section bigops
set_option linter.unusedSectionVars false
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

/-- A big separating conjunction over a list is monotone in its members. -/
theorem bigSepL_mono_mem' {A : Type} {Φ Ψ : A → IProp GF} {S : List A}
    (h : ∀ s ∈ S, Φ s ⊢ Ψ s) : ([∗list] s ∈ S, Φ s) ⊢ [∗list] s ∈ S, Ψ s :=
  BigSepL.bigSepL_mono fun {_ x} hk => h x (List.mem_of_getElem? hk)

/-- **The members of a list without repeats, from any list holding them.** -/
theorem bigSepL_sub_nodup {Φ : Nat → IProp GF} :
    ∀ (ws W : List Nat), ws.Nodup → (∀ s ∈ ws, s ∈ W) →
      ([∗list] s ∈ W, Φ s) ⊢ [∗list] s ∈ ws, Φ s
  | [], _, _, _ => by
    iintro -
    iapply BigSepL.bigSepL_nil.2; iempintro
  | s :: ws, W, hn, hsub => by
    have hs : s ∈ W := hsub s (List.mem_cons_self ..)
    obtain ⟨hns, hn'⟩ := List.nodup_cons.1 hn
    have ih := bigSepL_sub_nodup (Φ := Φ) ws (W.erase s) hn' fun t ht =>
      (List.mem_erase_of_ne (fun e => hns (by subst e; exact ht))).2 (hsub t (List.mem_cons_of_mem _ ht))
    refine (BigSepL.bigSepL_perm (List.perm_cons_erase hs)).1.trans ?_
    refine BigSepL.bigSepL_cons.1.trans ?_
    refine Entails.trans ?_ BigSepL.bigSepL_cons.2
    exact sep_mono .rfl ih

/-- **A conditional big separating conjunction is one over the members meeting the condition.** -/
theorem bigSepL_ite_filter {A : Type} (p : A → Bool) (Φ : A → IProp GF) :
    ∀ l : List A, ([∗list] x ∈ l, if p x then Φ x else iprop(emp)) ⊣⊢
      [∗list] x ∈ l.filter p, Φ x
  | [] => by simp only [List.filter_nil]; exact .rfl
  | x :: l => by
    have ih := bigSepL_ite_filter p Φ l
    rw [List.filter_cons]
    have hc := fun (y : A) (m : List A) (Ψ : A → IProp GF) =>
      (BigSepL.bigSepL_cons (PROP := IProp GF) (Φ := fun _ x => Ψ x) (x := y) (xs := m))
    by_cases hx : p x
    · rw [if_pos hx]
      refine (hc _ _ _).trans ((sep_congr ?_ ih).trans (hc _ _ _).symm)
      rw [if_pos hx]
      exact .rfl
    · rw [if_neg hx]
      refine (hc _ _ _).trans ((sep_congr ?_ ih).trans emp_sep)
      rw [if_neg hx]
      exact .rfl

/-- Two lists without repeats with the same members carry the same big separating conjunction. -/
theorem bigSepL_perm_nodup {A : Type} [DecidableEq A] (Φ : A → IProp GF) (l1 l2 : List A)
    (h1 : l1.Nodup) (h2 : l2.Nodup) (h : ∀ x, x ∈ l1 ↔ x ∈ l2) :
    ([∗list] x ∈ l1, Φ x) ⊣⊢ [∗list] x ∈ l2, Φ x :=
  BigSepL.bigSepL_perm ((List.perm_ext_iff_of_nodup h1 h2).2 h)

end bigops

section cells
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

omit hos in
/-- **The writer's cells of the old mapping `(b, L)`** (for `munmap`): `wCells`' slots inside it
are `wSlots (L / 4096)`, and the partial last slot. -/
theorem wCells_gather (w : WDb) (hok : wdbOK w) (b : Loc) (L : Nat) (hms : w.ms = some (b, L)) :
    wCells (GF := GF) (some (b, L)) w.W ⊢
      ([∗list] s ∈ wSlots (L / 4096) w.C w.fl, ∃ vf, cellsR (GF := GF) b (4096 * s) 4096 vf) ∗
      ∃ vf, cellsR (GF := GF) b (4096 * (L / 4096)) (L % 4096) vf := by
  unfold wCells
  refine sep_mono ?_ .rfl
  have hsub : ∀ s ∈ wSlots (L / 4096) w.C w.fl, s ∈ w.W := by
    intro s hs
    obtain ⟨h1, h2, h3⟩ := (mem_wSlots _ _ _ s).1 hs
    refine (wdbOK_mem_W w hok s).2 ⟨h1, ?_, h3⟩
    rw [hms]; simp only [mapLen]
    exact Nat.lt_of_lt_of_le h2 (Nat.div_le_div_right (Nat.le_max_left _ _))
  refine (bigSepL_sub_nodup _ _ (wSlots_nodup _ _ _) hsub).trans (bigSepL_mono_mem' fun s hs => ?_)
  have h2 := ((mem_wSlots _ _ _ s).1 hs).2.1
  have : 4096 * (s + 1) ≤ L := by omega
  simp only [this, ↓reduceIte]
  exact .rfl

omit hos in
/-- **The writer's cells of the new mapping `(b, L)`**: `wSlots (L / 4096)` and the partial last
slot are `wCells` of `wSlots k` for any `k` at least the mapping's slot count. -/
theorem wCells_carve (C : CommitSt) (fl : FLPg) (b : Loc) (L k : Nat) (hk : L / 4096 ≤ k) :
    ([∗list] s ∈ wSlots (L / 4096) C fl, ∃ vf, cellsR (GF := GF) b (4096 * s) 4096 vf) ∗
      (∃ vf, cellsR (GF := GF) b (4096 * (L / 4096)) (L % 4096) vf) ⊢
      wCells (GF := GF) (some (b, L)) (wSlots k C fl) := by
  unfold wCells
  refine sep_mono ?_ .rfl
  have e := bigSepL_ite_filter (GF := GF) (fun s => decide (4096 * (s + 1) ≤ L))
    (fun s => iprop(∃ vf, cellsR (GF := GF) b (4096 * s) 4096 vf)) (wSlots k C fl)
  simp only [decide_eq_true_eq] at e
  refine Entails.trans ?_ e.2
  refine (bigSepL_perm_nodup _ _ _ (wSlots_nodup _ _ _)
    (List.Pairwise.filter _ (wSlots_nodup _ _ _)) fun s => ?_).1
  rw [List.mem_filter, mem_wSlots, mem_wSlots, decide_eq_true_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, by omega, h3⟩, by omega⟩
  · rintro ⟨⟨h1, _, h3⟩, h4⟩; exact ⟨h1, by omega, h3⟩

/-- **The writer's page-cache bytes for a new slot list** `W'` (without repeats) whose slots
inside the file are old `W` slots. -/
theorem wBytes_restrict (p : GoString) (W W' : List Nat) (wb : Nat → List w8) (size : Nat)
    (hn : W'.Nodup) (hsub : ∀ s ∈ W', 4096 * s < size → s ∈ W) :
    wBytes (GF := GF) p W wb size ⊢ wBytes (GF := GF) p W' wb size := by
  unfold wBytes
  let F : Nat → IProp GF := fun s => iprop(if 4096 * (s + 1) ≤ size then
      iprop(∃ xs : List (w8 × Bool), osBytes p (4096 * s) (DFrac.own 1) xs ∗
        ⌜xs.map Prod.fst = wb s⌝)
    else if 4096 * s < size then
      iprop(∃ xs : List (w8 × Bool), osBytes p (4096 * s) (DFrac.own 1) xs ∗
        ⌜xs.map Prod.fst = (wb s).take (size - 4096 * s)⌝)
    else iprop(emp))
  show ([∗list] s ∈ W, F s) ⊢ [∗list] s ∈ W', F s
  have hF : ∀ s, F s ⊣⊢ if decide (4096 * s < size) then F s else iprop(emp) := by
    intro s
    by_cases h : 4096 * s < size
    · simp only [h, decide_true, ↓reduceIte]; exact .rfl
    · have h1 : ¬ 4096 * (s + 1) ≤ size := by omega
      simp only [F, h, h1, decide_false, ↓reduceIte, Bool.false_eq_true]; exact .rfl
  have hW' : ([∗list] s ∈ W', F s) ⊣⊢ [∗list] s ∈ W'.filter (fun s => decide (4096 * s < size)), F s :=
    (show ([∗list] s ∈ W', F s) ⊣⊢ [∗list] s ∈ W', if decide (4096 * s < size) then F s else iprop(emp)
      from ⟨bigSepL_mono_mem' fun s _ => (hF s).1, bigSepL_mono_mem' fun s _ => (hF s).2⟩).trans
      (bigSepL_ite_filter _ F W')
  refine Entails.trans ?_ hW'.2
  refine bigSepL_sub_nodup _ _ (List.Pairwise.filter _ hn) fun s hs => ?_
  rw [List.mem_filter, decide_eq_true_eq] at hs
  exact hsub s hs.1 hs.2

end cells

end bbolt
end EtcdGrove
end Perennial
