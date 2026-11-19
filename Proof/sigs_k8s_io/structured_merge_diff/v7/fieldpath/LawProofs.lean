/-
**`fieldpath`'s pure laws, proved** (`fieldpath/Vocab.lean`): finite sets, sets of paths, their
counts; and the helper facts the package's proofs share (membership in a quotient's list,
injectivity of the package's struct values).

Prove phase (2026-11-19, notes/smd-plan.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.NamedVocab
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.Objects
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Defs
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Vocab

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7

/-! ## Finite sets -/

namespace FSet
variable {α β : Type}

theorem mem_ofList' [DecidableEq α] (l : List α) (x : α) : x ∈ FSet.ofList l ↔ x ∈ l := by
  show decide (x ∈ l) = true ↔ _
  simp

theorem ind {p : FSet α → Prop} (h : ∀ l, p (FSet.ofList l)) (s : FSet α) : p s :=
  Quotient.inductionOn s h

theorem ext' [DecidableEq α] {a b : FSet α} (h : ∀ x, x ∈ a ↔ x ∈ b) : a = b := by
  induction a using FSet.ind with | h la =>
  induction b using FSet.ind with | h lb =>
  exact Quotient.sound (fun x => by
    have := h x; rw [mem_ofList', mem_ofList'] at this; exact this)

theorem ofList_eq_iff [DecidableEq α] (a b : List α) :
    FSet.ofList a = FSet.ofList b ↔ ∀ x, x ∈ a ↔ x ∈ b :=
  ⟨fun h x => by rw [← mem_ofList', ← mem_ofList', h], fun h => Quotient.sound h⟩

theorem mem_union' [DecidableEq α] (a b : FSet α) (x : α) :
    x ∈ FSet.union a b ↔ x ∈ a ∨ x ∈ b := by
  induction a using FSet.ind with | h la =>
  induction b using FSet.ind with | h lb =>
  show x ∈ (FSet.ofList (la ++ lb)) ↔ _
  simp only [mem_ofList', List.mem_append]

theorem mem_filter' [DecidableEq α] (p : α → Bool) (a : FSet α) (x : α) :
    x ∈ FSet.filter p a ↔ x ∈ a ∧ p x = true := by
  induction a using FSet.ind with | h la =>
  show x ∈ (FSet.ofList (la.filter p)) ↔ _
  simp only [mem_ofList', List.mem_filter]

theorem mem_bind' [DecidableEq α] [DecidableEq β] (f : α → List β) (a : FSet α) (y : β) :
    y ∈ FSet.bind f a ↔ ∃ x, x ∈ a ∧ y ∈ f x := by
  induction a using FSet.ind with | h la =>
  show y ∈ (FSet.ofList (la.flatMap f)) ↔ _
  simp only [mem_ofList', List.mem_flatMap]

theorem mem_map' [DecidableEq α] [DecidableEq β] (f : α → β) (a : FSet α) (y : β) :
    y ∈ FSet.map f a ↔ ∃ x, x ∈ a ∧ y = f x := by
  unfold FSet.map; rw [mem_bind']; simp

theorem mem_inter' [DecidableEq α] (a b : FSet α) (x : α) :
    x ∈ FSet.inter a b ↔ x ∈ a ∧ x ∈ b := by
  unfold FSet.inter; rw [mem_filter']; rfl

theorem mem_diff' [DecidableEq α] (a b : FSet α) (x : α) :
    x ∈ FSet.diff a b ↔ x ∈ a ∧ x ∉ b := by
  unfold FSet.diff; rw [mem_filter']
  show _ ∧ (!b.mem x) = true ↔ _ ∧ ¬ b.mem x = true
  simp

theorem any_iff (p : α → Bool) (a : FSet α) : a.any p = true ↔ ∃ x, (∃ l, FSet.ofList l = a ∧ x ∈ l) ∧ p x = true := by
  induction a using FSet.ind with | h la =>
  show la.any p = true ↔ _
  simp only [List.any_eq_true]
  constructor
  · rintro ⟨x, hx, hp⟩; exact ⟨x, ⟨la, rfl, hx⟩, hp⟩
  · rintro ⟨x, ⟨l, hl, hx⟩, hp⟩
    have : FSet.Same l la := Quotient.exact hl
    exact ⟨x, (this x).1 hx, hp⟩

theorem isEmpty_iff' [DecidableEq α] (a : FSet α) : a.isEmpty = true ↔ ∀ x, x ∉ a := by
  induction a using FSet.ind with | h la =>
  show (!la.any (fun _ => true)) = true ↔ _
  simp only [Bool.not_eq_true', List.any_eq_false, mem_ofList']
  simp

theorem mem_empty [DecidableEq α] (x : α) : x ∉ (FSet.empty : FSet α) := by
  unfold FSet.empty; rw [mem_ofList']; simp

end FSet

theorem FSet_mem_ofList_law_holds : FSet.mem_ofList.law := fun l x => FSet.mem_ofList' l x
theorem FSet_mem_union_law_holds : FSet.mem_union.law := fun a b x => FSet.mem_union' a b x
theorem FSet_mem_inter_law_holds : FSet.mem_inter.law := fun a b x => FSet.mem_inter' a b x
theorem FSet_mem_diff_law_holds : FSet.mem_diff.law := fun a b x => FSet.mem_diff' a b x
theorem FSet_mem_filter_law_holds : FSet.mem_filter.law := fun p a x => FSet.mem_filter' p a x
theorem FSet_mem_bind_law_holds : FSet.mem_bind.law := fun f a y => FSet.mem_bind' f a y
theorem FSet_isEmpty_iff_law_holds : FSet.isEmpty_iff.law := fun a => FSet.isEmpty_iff' a

/-! ## Counts -/

namespace FSet
variable {α : Type}

theorem card_ofList [DecidableEq α] (l : List α) : (FSet.ofList l).card = (dedupL l).length := rfl

theorem length_le_of_subset [DecidableEq α] {l₁ l₂ : List α} (h₁ : l₁.Nodup) (h : l₁ ⊆ l₂) :
    l₁.length ≤ l₂.length :=
  (List.subperm_of_subset h₁ h).length_le

theorem card_le_of_subset [DecidableEq α] (a b : FSet α) (h : ∀ x, x ∈ a → x ∈ b) :
    a.card ≤ b.card := by
  induction a using FSet.ind with | h la =>
  induction b using FSet.ind with | h lb =>
  rw [card_ofList, card_ofList]
  apply length_le_of_subset (nodup_dedupL la)
  intro x hx
  rw [mem_dedupL] at hx ⊢
  exact (mem_ofList' _ _).1 (h x ((mem_ofList' _ _).2 hx))

theorem hasCard_card' [DecidableEq α] (a : FSet α) : a.HasCard a.card := by
  induction a using FSet.ind with | h la =>
  refine ⟨dedupL la, nodup_dedupL la, ?_, rfl⟩
  exact Quotient.sound (fun x => mem_dedupL la x)

theorem hasCard_unique' (a : FSet α) (n m : Nat) (hn : a.HasCard n) (hm : a.HasCard m) : n = m := by
  obtain ⟨l1, hd1, he1, rfl⟩ := hn
  obtain ⟨l2, hd2, he2, rfl⟩ := hm
  have h : FSet.Same l1 l2 := Quotient.exact (he1.trans he2.symm)
  exact ((List.perm_ext_iff_of_nodup hd1 hd2).2 h).length_eq

theorem hasCard_iff [DecidableEq α] (a : FSet α) (n : Nat) : a.HasCard n ↔ a.card = n :=
  ⟨fun h => hasCard_unique' a _ _ (hasCard_card' a) h, fun h => h ▸ hasCard_card' a⟩

end FSet

theorem FSet_hasCard_exists_law_holds : FSet.hasCard_exists.law := by
  intro α a
  classical
  exact ⟨a.card, FSet.hasCard_card' a⟩

theorem FSet_hasCard_unique_law_holds : FSet.hasCard_unique.law :=
  fun a n m => FSet.hasCard_unique' a n m

theorem FSet_hasCard_card_law_holds : FSet.hasCard_card.law := fun a => FSet.hasCard_card' a

theorem FSet_hasCard_zero_law_holds : FSet.hasCard_zero.law := by
  intro α a n hn
  classical
  rw [FSet.isEmpty_iff']
  obtain ⟨l, hd, rfl, rfl⟩ := hn
  simp only [FSet.mem_ofList', List.length_eq_zero_iff]
  constructor
  · rintro rfl x hx; simp at hx
  · intro h; exact List.eq_nil_iff_forall_not_mem.2 h

theorem FSet_cardLt_mono_law_holds : FSet.cardLt_mono.law := by
  intro α _ a b n m hsub hnm hb
  unfold FSet.CardLt at *
  have := FSet.card_le_of_subset a b hsub
  omega

theorem FSet_card_union_law_holds : FSet.card_union.law := by
  intro α _ a b
  induction a using FSet.ind with | h la =>
  induction b using FSet.ind with | h lb =>
  show (FSet.dedupL (la ++ lb)).length ≤ (FSet.dedupL la).length + (FSet.dedupL lb).length
  rw [← List.length_append]
  apply FSet.length_le_of_subset (FSet.nodup_dedupL _)
  intro x hx
  simp only [FSet.mem_dedupL, List.mem_append] at hx ⊢
  exact hx

/-! ## Sets of paths -/

theorem PathSet_mem_ofList_law_holds : PathSet.mem_ofList.law := by
  intro ps q
  unfold PathSet.ofList
  rw [FSet.mem_ofList', List.mem_filter]
  cases q <;> simp

theorem PathSet_mem_tops_law_holds : PathSet.mem_tops.law := by
  intro S e
  unfold PathSet.tops
  rw [FSet.mem_bind']
  constructor
  · rintro ⟨q, hq, he⟩
    match q, he with
    | [e'], he => simp at he; subst he; exact hq
  · intro h; exact ⟨[e], h, by simp⟩

theorem PathSet_mem_deep_law_holds : PathSet.mem_deep.law := by
  intro S q
  unfold PathSet.deep
  rw [FSet.mem_filter']; simp

theorem PathSet_mem_heads_law_holds : PathSet.mem_heads.law := by
  intro S e
  unfold PathSet.heads
  rw [FSet.mem_bind']
  constructor
  · rintro ⟨q, hq, he⟩
    match q, he with
    | e' :: x :: r, he => simp at he; subst he; exact ⟨x :: r, by simp, hq⟩
  · rintro ⟨q, hq, h⟩
    match q, hq with
    | x :: r, _ => exact ⟨e :: x :: r, h, by simp⟩

theorem PathSet_mem_under_law_holds : PathSet.mem_under.law := by
  intro S e q
  unfold PathSet.under
  rw [FSet.mem_bind']
  constructor
  · rintro ⟨q', hq', hq⟩
    match q', hq with
    | e' :: x :: r, hq =>
      by_cases he : e' = e
      · subst he; simp at hq; subst hq; exact ⟨by simp, hq'⟩
      · simp [he] at hq
  · rintro ⟨hne, h⟩
    match q, hne with
    | x :: r, _ => exact ⟨e :: x :: r, h, by simp⟩

theorem PathSet_mem_rdiff_law_holds : PathSet.mem_rdiff.law := by
  intro A B q
  unfold PathSet.rdiff
  rw [FSet.mem_filter']
  simp only [Bool.not_eq_true', List.any_eq_false]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun r hr hB => h2 r hr hB⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun r hr hB => h2 r hr hB⟩

theorem PathSet_mem_prepend_law_holds : PathSet.mem_prepend.law := by
  intro pre S q
  unfold PathSet.prepend
  rw [FSet.mem_map']

/-! ## The order of path elements -/

namespace fpL

theorem gs_swap : ∀ a b : GoString, gsCompare b a = - gsCompare a b
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | x :: xs, y :: ys => by
    simp only [gsCompare]
    have := gs_swap xs ys
    by_cases h1 : x.toNat < y.toNat <;> by_cases h2 : y.toNat < x.toNat <;> simp only [h1, h2, ↓reduceIte] <;> omega

theorem gs_range : ∀ a b : GoString, gsCompare a b = -1 ∨ gsCompare a b = 0 ∨ gsCompare a b = 1
  | [], [] => by simp [gsCompare]
  | [], _ :: _ => by simp [gsCompare]
  | _ :: _, [] => by simp [gsCompare]
  | x :: xs, y :: ys => by
    simp only [gsCompare]
    have := gs_range xs ys
    by_cases h1 : x.toNat < y.toNat <;> by_cases h2 : y.toNat < x.toNat <;> simp only [h1, h2, ↓reduceIte] <;> first | omega | simp

theorem gs_zero : ∀ a b : GoString, gsCompare a b = 0 ↔ a = b
  | [], [] => by simp [gsCompare]
  | [], _ :: _ => by simp [gsCompare]
  | _ :: _, [] => by simp [gsCompare]
  | x :: xs, y :: ys => by
    simp only [gsCompare, List.cons.injEq]
    have := gs_zero xs ys
    by_cases h1 : x.toNat < y.toNat <;> by_cases h2 : y.toNat < x.toNat <;> simp only [h1, h2, ↓reduceIte]
    · omega
    · simp only [show (-1 : Int) ≠ 0 by decide, false_iff]; rintro ⟨rfl, -⟩; omega
    · simp only [show (1 : Int) ≠ 0 by decide, false_iff]; rintro ⟨rfl, -⟩; omega
    · rw [this]
      have : x = y := BitVec.eq_of_toNat_eq (by omega)
      simp [this]

theorem gs_trans : ∀ a b c : GoString, gsCompare a b < 0 → gsCompare b c < 0 → gsCompare a c < 0
  | [], _, [] => by intro h1 h2; cases ‹GoString› <;> simp [gsCompare] at h1 h2
  | [], _, _ :: _ => by intro _ _; simp [gsCompare]
  | _ :: _, [], _ => by intro h1 _; simp [gsCompare] at h1
  | _ :: _, _ :: _, [] => by intro _ h2; simp [gsCompare] at h2
  | x :: xs, y :: ys, z :: zs => by
    simp only [gsCompare]
    have := gs_trans xs ys zs
    by_cases h1 : x.toNat < y.toNat <;> by_cases h2 : y.toNat < x.toNat <;>
    by_cases h3 : y.toNat < z.toNat <;> by_cases h4 : z.toNat < y.toNat <;>
    by_cases h5 : x.toNat < z.toNat <;> by_cases h6 : z.toNat < x.toNat <;>
    simp only [h1, h2, h3, h4, h5, h6, ↓reduceIte] <;> omega

theorem int_swap (a b : w64) : intCompare b a = - intCompare a b := by
  unfold intCompare
  by_cases h1 : a.toInt > b.toInt <;> by_cases h2 : b.toInt > a.toInt <;>
  by_cases h3 : a.toInt = b.toInt <;>
  simp only [h1, h2, h3, beq_iff_eq, ↓reduceIte, eq_comm (a := b.toInt)] <;> omega

theorem int_zero (a b : w64) : intCompare a b = 0 ↔ a = b := by
  unfold intCompare
  constructor
  · intro h
    by_cases h3 : a.toInt = b.toInt
    · exact BitVec.toInt_inj.1 h3
    · by_cases h1 : a.toInt > b.toInt <;>
        simp only [h1, h3, beq_iff_eq, ↓reduceIte] at h <;> omega
  · rintro rfl; simp

theorem int_trans (a b c : w64) : intCompare a b < 0 → intCompare b c < 0 → intCompare a c < 0 := by
  unfold intCompare
  intro h1 h2
  by_cases g1 : a.toInt > b.toInt <;> by_cases g2 : a.toInt = b.toInt <;>
  by_cases g3 : b.toInt > c.toInt <;> by_cases g4 : b.toInt = c.toInt <;>
  by_cases g5 : a.toInt > c.toInt <;> by_cases g6 : a.toInt = c.toInt <;>
  simp only [g1, g2, g3, g4, g5, g6, beq_iff_eq, ↓reduceIte] at h1 h2 ⊢ <;> omega

end fpL

namespace fpL

/-- A field list's values are canonical (`PE.wf` of a key). -/
abbrev flWf (fl : FieldList) : Prop := fl.all (fun f => f.2.canon) = true

section fl
variable (hZ : UVal.compare_eq_zero.law) (hA : UVal.compare_antisymm.law)
  (hT : UVal.compare_trans.law)
include hZ hA

theorem fl_zero_anti : ∀ a b : FieldList, flWf a → flWf b →
    (flCompare a b = 0 ↔ a = b) ∧ (flCompare a b < 0 ↔ 0 < flCompare b a)
  | [], [] => by simp [flCompare]
  | [], _ :: _ => by simp [flCompare]
  | _ :: _, [] => by simp [flCompare]
  | (n, v) :: xs, (n', v') :: ys => by
    intro ha hb
    simp only [flWf, List.all_cons, Bool.and_eq_true] at ha hb
    have ih := fl_zero_anti xs ys ha.2 hb.2
    have uz := hZ v v' ha.1 hb.1
    have uz' := hZ v' v hb.1 ha.1
    have ua := hA v v' ha.1 hb.1
    have ua' := hA v' v hb.1 ha.1
    have gz := gs_zero n n'
    have gsw := gs_swap n n'
    simp only [flCompare, bne_iff_ne, ne_eq, List.cons.injEq, Prod.mk.injEq]
    by_cases g : gsCompare n n' = 0
    · have g' : gsCompare n' n = 0 := by omega
      have hn := gz.1 g
      simp only [g, g', not_true_eq_false, ↓reduceIte]
      by_cases u : UVal.compare v v' = 0
      · have hv := uz.1 u
        subst hv
        have u' : UVal.compare v v = 0 := u
        simp only [u', not_true_eq_false, ↓reduceIte, hn, true_and]
        exact ih
      · have u' : UVal.compare v' v ≠ 0 := fun h => u (uz.2 (uz'.1 h).symm)
        simp only [u, u', not_false_eq_true, ↓reduceIte]
        refine ⟨?_, ua⟩
        simp only [false_iff, not_and]
        intro hv _; exact absurd (uz.2 hv.2) u
    · have g' : gsCompare n' n ≠ 0 := by omega
      simp only [g, g', not_false_eq_true, ↓reduceIte]
      refine ⟨?_, by omega⟩
      simp only [false_iff, not_and]
      intro hn; exact absurd (gz.2 hn.1) g

end fl

theorem fl_trans (hZ : UVal.compare_eq_zero.law) (hT : UVal.compare_trans.law) :
    ∀ a b c : FieldList, flWf a → flWf b → flWf c →
    flCompare a b < 0 → flCompare b c < 0 → flCompare a c < 0
  | [], [], _ => by simp [flCompare]
  | [], _ :: _, [] => by simp [flCompare]
  | [], _ :: _, _ :: _ => by simp [flCompare]
  | _ :: _, [], _ => by simp [flCompare]
  | _ :: _, _ :: _, [] => by simp [flCompare]
  | (n1, v1) :: xs, (n2, v2) :: ys, (n3, v3) :: zs => by
    intro ha hb hc h1 h2
    simp only [flWf, List.all_cons, Bool.and_eq_true] at ha hb hc
    have ih := fl_trans hZ hT xs ys zs ha.2 hb.2 hc.2
    simp only [flCompare, bne_iff_ne, ne_eq] at h1 h2 ⊢
    by_cases g12 : gsCompare n1 n2 = 0
    · have := (gs_zero _ _).1 g12; subst this
      simp only [g12, not_true_eq_false, ↓reduceIte] at h1 ⊢
      by_cases g23 : gsCompare n1 n3 = 0
      · have := (gs_zero _ _).1 g23; subst this
        simp only [g23, not_true_eq_false, ↓reduceIte] at h2 ⊢
        by_cases u12 : UVal.compare v1 v2 = 0
        · have := (hZ _ _ ha.1 hb.1).1 u12; subst this
          simp only [u12, not_true_eq_false, ↓reduceIte] at h1 ⊢
          by_cases u23 : UVal.compare v1 v3 = 0
          · simp only [u23, not_true_eq_false, ↓reduceIte] at h2 ⊢
            exact ih h1 h2
          · simp only [u23, not_false_eq_true, ↓reduceIte] at h2 ⊢; exact h2
        · simp only [u12, not_false_eq_true, ↓reduceIte] at h1
          by_cases u23 : UVal.compare v2 v3 = 0
          · have := (hZ _ _ hb.1 hc.1).1 u23; subst this
            simp only [u12, not_false_eq_true, ↓reduceIte]; exact h1
          · simp only [u23, not_false_eq_true, ↓reduceIte] at h2
            have := hT _ _ _ ha.1 hb.1 hc.1 h1 h2
            simp only [show UVal.compare v1 v3 ≠ 0 by omega, not_false_eq_true, ↓reduceIte]
            exact this
      · simp only [g23, not_false_eq_true, ↓reduceIte] at h2 ⊢; exact h2
    · simp only [g12, not_false_eq_true, ↓reduceIte] at h1
      by_cases g23 : gsCompare n2 n3 = 0
      · have := (gs_zero _ _).1 g23; subst this
        simp only [g12, not_false_eq_true, ↓reduceIte]; exact h1
      · simp only [g23, not_false_eq_true, ↓reduceIte] at h2
        have := gs_trans _ _ _ h1 h2
        simp only [show gsCompare n1 n3 ≠ 0 by omega, not_false_eq_true, ↓reduceIte]
        exact this

end fpL

namespace fpL
section pe
variable (hZ : UVal.compare_eq_zero.law) (hA : UVal.compare_antisymm.law)
  (hT : UVal.compare_trans.law)

theorem gs_za (a b : GoString) : (gsCompare a b = 0 ↔ a = b) ∧ (gsCompare a b < 0 ↔ 0 < gsCompare b a) :=
  ⟨gs_zero a b, by have := gs_swap a b; omega⟩

theorem int_za (a b : w64) : (intCompare a b = 0 ↔ a = b) ∧ (intCompare a b < 0 ↔ 0 < intCompare b a) :=
  ⟨int_zero a b, by have := int_swap a b; omega⟩

include hZ hA in
theorem pe_zero_anti (a b : PE) (ha : a.wf = true) (hb : b.wf = true) :
    (PE.compare a b = 0 ↔ a = b) ∧ (PE.compare a b < 0 ↔ 0 < PE.compare b a) := by
  cases a <;> cases b <;> simp only [PE.compare, PE.wf, reduceCtorEq, PE.field.injEq, PE.key.injEq,
    PE.value.injEq, PE.index.injEq, iff_false] at ha hb ⊢
  all_goals first
    | exact gs_za _ _
    | exact fl_zero_anti hZ hA _ _ ha hb
    | exact ⟨hZ _ _ ha hb, hA _ _ ha hb⟩
    | exact int_za _ _
    | decide

include hZ hA in
theorem pe_zero (a b : PE) (ha : a.wf = true) (hb : b.wf = true) :
    PE.compare a b = 0 ↔ a = b := (pe_zero_anti hZ hA a b ha hb).1

include hZ hA in
theorem pe_anti (a b : PE) (ha : a.wf = true) (hb : b.wf = true) :
    PE.compare a b < 0 ↔ 0 < PE.compare b a := (pe_zero_anti hZ hA a b ha hb).2

include hZ hT in
theorem pe_trans (a b c : PE) (ha : a.wf = true) (hb : b.wf = true) (hc : c.wf = true) :
    PE.lt a b → PE.lt b c → PE.lt a c := by
  unfold PE.lt
  cases a <;> cases b <;> cases c <;> simp only [PE.compare, PE.wf] at ha hb hc ⊢ <;>
    intro h1 h2 <;> try omega
  · exact gs_trans _ _ _ h1 h2
  · exact fl_trans hZ hT _ _ _ ha hb hc h1 h2
  · exact hT _ _ _ ha hb hc h1 h2
  · exact int_trans _ _ _ h1 h2

include hZ hA hT in
theorem pe_sorted_ext : ∀ xs ys : List PE, (∀ x ∈ xs, x.wf = true) → (∀ y ∈ ys, y.wf = true) →
    PE.Sorted xs → PE.Sorted ys → (∀ x, x ∈ xs ↔ x ∈ ys) → xs = ys
  | [], [], _, _, _, _, _ => rfl
  | [], y :: _, _, _, _, _, h => by have := (h y).2 (by simp); simp at this
  | x :: _, [], _, _, _, _, h => by have := (h x).1 (by simp); simp at this
  | x :: xs, y :: ys, wx, wy, sx, sy, h => by
    unfold PE.Sorted at sx sy
    rw [List.pairwise_cons] at sx sy
    have wxx := wx x (by simp)
    have wyy := wy y (by simp)
    -- the heads are the least members
    have hxy : x = y := by
      have hx := (h x).1 (by simp)
      have hy := (h y).2 (by simp)
      rcases List.mem_cons.1 hx with e | hx
      · exact e
      rcases List.mem_cons.1 hy with e | hy
      · exact e.symm
      have l1 : PE.lt y x := sy.1 x hx
      have l2 : PE.lt x y := sx.1 y hy
      have := pe_trans hZ hT x y x wxx wyy wxx l2 l1
      unfold PE.lt at this
      have z := (pe_zero hZ hA x x wxx wxx).2 rfl
      omega
    subst hxy
    congr 1
    apply pe_sorted_ext xs ys (fun z hz => wx z (by simp [hz])) (fun z hz => wy z (by simp [hz]))
      sx.2 sy.2
    intro z
    constructor
    · intro hz
      have := (h z).1 (by simp [hz])
      rcases List.mem_cons.1 this with e | h'
      · subst e
        have l := sx.1 z hz
        unfold PE.lt at l
        have := (pe_zero hZ hA z z (wx z (by simp [hz])) (wx z (by simp [hz]))).2 rfl
        omega
      · exact h'
    · intro hz
      have := (h z).2 (by simp [hz])
      rcases List.mem_cons.1 this with e | h'
      · subst e
        have l := sy.1 z hz
        unfold PE.lt at l
        have := (pe_zero hZ hA z z (wy z (by simp [hz])) (wy z (by simp [hz]))).2 rfl
        omega
      · exact h'

end pe
end fpL

/-- The order laws over `value`'s (`UVal.compare_*`): instantiated by `PE_compare_*_law_holds`
once those are proved. -/
theorem PE_compare_eq_zero_law_of (hZ : UVal.compare_eq_zero.law) (hA : UVal.compare_antisymm.law) :
    PE.compare_eq_zero.law := fun a b ha hb => fpL.pe_zero hZ hA a b ha hb
theorem PE_compare_antisymm_law_of (hZ : UVal.compare_eq_zero.law) (hA : UVal.compare_antisymm.law) :
    PE.compare_antisymm.law := fun a b ha hb => fpL.pe_anti hZ hA a b ha hb
theorem PE_compare_trans_law_of (hZ : UVal.compare_eq_zero.law) (hT : UVal.compare_trans.law) :
    PE.compare_trans.law := fun a b c ha hb hc => fpL.pe_trans hZ hT a b c ha hb hc
theorem PE_sorted_ext_law_of (hZ : UVal.compare_eq_zero.law) (hA : UVal.compare_antisymm.law)
    (hT : UVal.compare_trans.law) : PE.sorted_ext.law := fpL.pe_sorted_ext hZ hA hT

end smd
end EtcdGrove
end Perennial
