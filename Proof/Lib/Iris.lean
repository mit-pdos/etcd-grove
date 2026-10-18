/-
Facts about Iris's and Perennial's own resource definitions (fractions `Qp`/`DFrac`,
`Fractional`, ghost variables and ghost maps, `Persistent`/`Timeless` of an `if`) that belong to
no Go package. The heap's (map and typed points-to) are in `Proof/Lib/Heap.lean`.

They are kept here until Perennial (or Iris) has them: each is a candidate for an independent
Perennial proposal (CLAUDE.md, "Changes to Perennial"), and goes once its Perennial
counterpart lands. The copies they replace were each proved in a package's section, under that
package's assumptions (`notes/decisions.md`, "Proof/Lib: facts that belong to no Go package").
-/
module

public import Perennial.Ghost.GhostVar
public import Perennial.Ghost.GhostMap

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

/-! ## Fractions -/

theorem qp_half_add (q1 q2 : Qp) : (q1 + q2).half = q1.half + q2.half :=
  Subtype.ext (by simp only [Qp.val_half, Qp.val_add]; grind)

theorem qp_one_add_not_le (q : Qp) : ¬ ((1 : Qp) + q ≤ 1) := by
  intro h
  have h' : ((1 : Qp) + q).val ≤ (1 : Qp).val := h
  have := q.2
  simp at h'
  grind

theorem qp_add_one_not_le (q : Qp) : ¬ (q + (1 : Qp) ≤ 1) := by
  intro h
  have h' : (q + (1 : Qp)).val ≤ (1 : Qp).val := h
  have := q.2
  simp at h'
  grind

/-- A fraction as two halves. -/
theorem dfrac_own_half_half (q : Qp) :
    (DFrac.own q : DFrac) = DFrac.own q.half • DFrac.own q.half := by
  have h := Qp.half_add_half q
  calc (DFrac.own q : DFrac) = DFrac.own (q.half + q.half) := by rw [h]
    _ = DFrac.own q.half • DFrac.own q.half := rfl

theorem dfrac_own_one_op_invalid (dq : DFrac) : ¬ ✓ (DFrac.own 1 • dq) := by
  intro h
  have := DFrac.valid_own_op h
  have : (1 : Qp).val = 1 := rfl
  grind

/-! ## `Persistent` and `Timeless` of an `if` -/

instance ite_persistent {PROP : Type _} [BI PROP] (c : Prop) [Decidable c] (P Q : PROP)
    [Persistent P] [Persistent Q] : Persistent (if c then P else Q) := by
  split <;> infer_instance

instance ite_timeless {PROP : Type _} [BI PROP] (c : Prop) [Decidable c] (P Q : PROP)
    [Timeless P] [Timeless Q] : Timeless (if c then P else Q) := by
  split <;> infer_instance

section ghost
variable {GF : BundledGFunctors}

/-! ## `Fractional` -/

/-- An existential of fractional predicates whose witnesses agree is fractional. -/
theorem fractional_exists_agree {X : Type} (Φ : X → Qp → IProp GF) (hfrac : ∀ x, Fractional (Φ x))
    (hagree : ∀ x y q1 q2, Φ x q1 ∗ Φ y q2 ⊢ ⌜x = y⌝) :
    Fractional (fun q => iprop(∃ x, Φ x q)) where
  fractional p q := by
    constructor
    · iintro ⟨%x, H⟩
      icases ((hfrac x).fractional p q).1 $$ H with ⟨H1, H2⟩
      isplitl [H1]
      · iexists x; iexact H1
      · iexists x; iexact H2
    · refine (sep_exists_right.1).trans (exists_elim fun x => ?_)
      refine (sep_exists_left.1).trans (exists_elim fun y => ?_)
      refine (and_intro (hagree x y p q) .rfl).trans (pure_elim_left fun h => ?_)
      subst h
      exact ((hfrac x).fractional p q).2.trans (exists_intro (Ψ := fun x => Φ x (p + q)) x)

/-- A predicate equivalent at every fraction to a fractional one is fractional. -/
theorem fractional_of_equiv {Φ Ψ : Qp → IProp GF} (h : ∀ q, Φ q ⊣⊢ Ψ q) [hΨ : Fractional Ψ] :
    Fractional Φ where
  fractional p q :=
    (h (p + q)).trans ((hΨ.fractional p q).trans (sep_congr (h p).symm (h q).symm))

variable [AllG GF]

/-! ## Ghost variables and ghost maps -/

theorem ghostVar_half_fractional {A : Type} [Pos.Countable A] (γ : GName) (a : A) :
    Fractional (fun q : Qp => ghostVar (GF := GF) γ q.half a) where
  fractional p q := by
    rw [qp_half_add]
    exact (ghostVar_fractional γ a).fractional p.half q.half

theorem ghostMapAuth_half_fractional {K V : Type} [DecidableEq K] [Pos.Countable K]
    [Pos.Countable V] (γ : GName) (m : GMap K V) :
    Fractional (fun q : Qp => ghostMapAuth (GF := GF) γ q.half m) where
  fractional p q := by
    rw [qp_half_add]
    exact (ghostMapAuth_fractional γ m).fractional p.half q.half

/-- A ghost variable's fraction as two halves (Perennial's `ghostVar_halves` is the whole's
split, one way). -/
theorem ghostVar_split_half {A : Type} [Pos.Countable A] (γ : GName) (q : Qp) (a : A) :
    (ghostVar (GF := GF) γ q a : IProp GF) ⊣⊢ ghostVar γ q.half a ∗ ghostVar γ q.half a := by
  conv => lhs; rw [← Qp.half_add_half q]
  exact (ghostVar_fractional γ a).fractional _ _

/-- A whole ghost map authority as two halves. -/
theorem ghostMapAuth_halves {K V : Type} [DecidableEq K] [Pos.Countable K] [Pos.Countable V]
    (γ : GName) (m : GMap K V) :
    (ghostMapAuth (GF := GF) γ 1 m : IProp GF) ⊣⊢
      ghostMapAuth γ (1 : Qp).half m ∗ ghostMapAuth γ (1 : Qp).half m := by
  conv => lhs; rw [← Qp.half_add_half 1]
  exact (ghostMapAuth_fractional γ m).fractional _ _

/-- A whole ghost map element as two halves. -/
theorem ghostMapElem_halves {K V : Type} [DecidableEq K] [Pos.Countable K] [Pos.Countable V]
    (γ : GName) (k : K) (v : V) :
    (k ↪[γ] v : IProp GF) ⊣⊢ k ↪[γ]{#(1 : Qp).half} v ∗ k ↪[γ]{#(1 : Qp).half} v := by
  conv => lhs; rw [← Qp.half_add_half 1]
  exact (ghostMapElem_fractional k γ v).fractional _ _

end ghost

end EtcdGrove
end Perennial
