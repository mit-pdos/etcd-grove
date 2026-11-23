/-
Generic big-separating-conjunction lemmas the epaxos proofs use.
-/
module

public import Iris

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.epaxosProof

open Iris Iris.BI BigSepL Iris.Algebra BigOpL

variable {PROP : Type _} [BI PROP] {A : Type _}

/-- Change one element of a list and the predicate at its index (the predicate elsewhere is
unchanged). -/
theorem bigSepL_set_acc : ∀ {Φ Ψ : Nat → A → PROP} {l : List A} {i : Nat} {x : A},
    l[i]? = some x → (∀ k, k ≠ i → Φ k = Ψ k) →
    ([∗list] k ↦ z ∈ l, Φ k z) ⊢ Φ i x ∗ ∀ y, Ψ i y -∗ [∗list] k ↦ z ∈ l.set i y, Ψ k z
  | Φ, Ψ, z :: zs, 0, x, h, hΨ => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst h
    have e : (fun k z => Φ (k + 1) z) = (fun k z => Ψ (k + 1) z) :=
      funext fun k => funext fun z => by rw [hΨ (k + 1) (by omega)]
    refine (bigSepL_cons.1).trans (sep_mono_right (forall_intro fun y => wand_intro ?_))
    refine sep_comm.1.trans ?_
    simp only [List.set_cons_zero]
    refine (sep_mono_right ?_).trans bigSepL_cons.2
    rw [e]
  | Φ, Ψ, z :: zs, j + 1, x, h, hΨ => by
    simp only [List.getElem?_cons_succ] at h
    have ih := bigSepL_set_acc (Φ := fun k z => Φ (k + 1) z) (Ψ := fun k z => Ψ (k + 1) z) h
      (fun k hk => hΨ (k + 1) (by omega))
    have e0 : Φ 0 = Ψ 0 := hΨ 0 (by omega)
    refine (bigSepL_cons.1).trans ((sep_mono_right ih).trans ?_)
    refine sep_left_comm.1.trans (sep_mono_right (forall_intro fun y => wand_intro ?_))
    simp only [List.set_cons_succ]
    refine (sep_mono_left (sep_mono_right (forall_elim y))).trans ?_
    refine sep_assoc.1.trans ((sep_mono_right wand_elim_left).trans ?_)
    rw [e0]
    exact bigSepL_cons.2

/-- Read one element (the predicate unchanged). -/
theorem bigSepL_get_acc {Φ : Nat → A → PROP} {l : List A} {i : Nat} {x : A} (h : l[i]? = some x) :
    ([∗list] k ↦ z ∈ l, Φ k z) ⊢ Φ i x ∗ (Φ i x -∗ [∗list] k ↦ z ∈ l, Φ k z) := by
  refine (bigSepL_set_acc (Ψ := Φ) h (fun _ _ => rfl)).trans (sep_mono_right ?_)
  refine (forall_elim x).trans ?_
  have hset : l.set i x = l := by
    have := List.getElem?_eq_some_iff.mp h
    rw [← this.2]; exact List.set_getElem_self this.1
  rw [hset]

/-- A big separating conjunction whose predicate at index `i` ignores the element: setting the
element at `i` changes nothing. -/
theorem bigSepL_set_irrel : ∀ {Φ : Nat → A → PROP} {l : List A} {i : Nat} (y : A),
    (∀ a b, Φ i a = Φ i b) →
    ([∗list] k ↦ z ∈ l.set i y, Φ k z) = [∗list] k ↦ z ∈ l, Φ k z
  | _, [], _, _, _ => rfl
  | Φ, z :: zs, 0, y, h => by
    simp only [List.set_cons_zero]
    show iprop(Φ 0 y ∗ [∗list] k ↦ z ∈ zs, Φ (k + 1) z) =
      iprop(Φ 0 z ∗ [∗list] k ↦ z ∈ zs, Φ (k + 1) z)
    rw [h y z]
  | Φ, z :: zs, j + 1, y, h => by
    simp only [List.set_cons_succ]
    show iprop(Φ 0 z ∗ [∗list] k ↦ z ∈ zs.set j y, Φ (k + 1) z) =
      iprop(Φ 0 z ∗ [∗list] k ↦ z ∈ zs, Φ (k + 1) z)
    rw [bigSepL_set_irrel (Φ := fun k z => Φ (k + 1) z) (i := j) y (fun a b => h a b)]

/-- Open element `i`; close with any new element and any predicate that agrees elsewhere. -/
theorem bigSepL_set_acc' [BIAffine PROP] {Φ : Nat → A → PROP} {l : List A} {i : Nat} {x : A}
    (h : l[i]? = some x) :
    ([∗list] k ↦ z ∈ l, Φ k z) ⊢ Φ i x ∗ ∀ (Ψ : Nat → A → PROP) (y : A),
      ⌜∀ k, k ≠ i → Φ k = Ψ k⌝ -∗ Ψ i y -∗ [∗list] k ↦ z ∈ l.set i y, Ψ k z := by
  have hi : i < l.length := (List.getElem?_eq_some_iff.mp h).1
  refine (bigSepL_delete_cond h).1.trans (sep_mono_right ?_)
  iintro Hrest %Ψ %y Hp Hy
  icases Hp with %hΨ
  have hy : (l.set i y)[i]? = some y := by simp [hi]
  iapply (bigSepL_delete_cond hy).2
  isplitl [Hy]
  · iexact Hy
  rw [bigSepL_set_irrel (Φ := fun k z => if k = i then emp else Ψ k z) y
    (fun a b => by simp)]
  have e : ([∗list] k ↦ z ∈ l, if k = i then emp else Φ k z) =
      ([∗list] k ↦ z ∈ l, if k = i then (emp : PROP) else Ψ k z) := by
    refine bigOpL_eq fun {k _} _ => ?_
    by_cases hk : k = i
    · simp [hk]
    · simp [hk, hΨ k hk]
  rw [← e]
  iexact Hrest

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.epaxosProof
