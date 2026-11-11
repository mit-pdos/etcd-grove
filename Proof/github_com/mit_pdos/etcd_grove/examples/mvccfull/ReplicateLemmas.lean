/-
Big separating conjunctions over `List.replicate n ()` (`Readers.lean`'s `rdStock_split`): a
fractional resource at `q` is `n` copies at `q / n`, an additive one at `n` is `n` copies at `1`,
and copies of a separating conjunction are the conjunction of copies. Lean-first.
-/
module

public import Iris.BI.BigOp.BigSepList
public import Iris.BI.Lib.Fractional
public import Perennial.Proof.sync.RWMutexGuard
public import Iris.ProofMode

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.BI.BigSepL Iris.ProofMode

section rep
variable {PROP : Type _} [BI PROP]

/-- `n` copies of `A ∗ B` are `n` copies of `A` and `n` of `B`. -/
theorem rep_sep (A B : PROP) (n : Nat) :
    ([∗list] _u ∈ List.replicate n (), iprop(A ∗ B)) ⊣⊢
      ([∗list] _u ∈ List.replicate n (), A) ∗ [∗list] _u ∈ List.replicate n (), B :=
  bigSepL_sep_eqv

/-- `k + 1` copies of `P ∗ A`, `P` persistent, are `P` and `k + 1` copies of `A`. -/
theorem rep_pers (P A : PROP) [Persistent P] [BIAffine PROP] (k : Nat) :
    (P ∗ [∗list] _u ∈ List.replicate (k + 1) (), A) ⊣⊢
      [∗list] _u ∈ List.replicate (k + 1) (), iprop(P ∗ A) := by
  induction k with
  | zero =>
    simp only [Nat.zero_add, List.replicate_one]
    constructor
    · iintro ⟨#HP, HA⟩
      iapply bigSepL_singleton.2
      icases bigSepL_singleton.1 $$ HA with HA
      iframe HA; iexact HP
    · iintro H
      icases bigSepL_singleton.1 $$ H with ⟨#HP, HA⟩
      iframe HP
      iapply bigSepL_singleton.2; iexact HA
  | succ k ih =>
    rw [List.replicate_succ]
    constructor
    · iintro ⟨#HP, HA⟩
      icases bigSepL_cons.1 $$ HA with ⟨HA, HAs⟩
      iapply bigSepL_cons.2
      isplitl [HA]
      · iframe HA; iexact HP
      iapply ih.1
      iframe HAs; iexact HP
    · iintro H
      icases bigSepL_cons.1 $$ H with ⟨⟨#HP, HA⟩, Hs⟩
      icases ih.2 $$ Hs with ⟨-, Hs⟩
      iframe HP
      iapply bigSepL_cons.2
      iframe

/-- An additive `Ψ` at `k + 1` is `k + 1` copies of `Ψ 1`. -/
theorem rep_add (Ψ : Nat → PROP) (h : ∀ a b, Ψ (a + b) ⊣⊢ Ψ a ∗ Ψ b) (k : Nat) :
    Ψ (k + 1) ⊣⊢ [∗list] _u ∈ List.replicate (k + 1) (), Ψ 1 := by
  induction k with
  | zero =>
    simp only [Nat.zero_add, List.replicate_one]
    exact (bigSepL_singleton (PROP := PROP) (Φ := fun _ _ => _) (x := ())).symm
  | succ k ih =>
    rw [List.replicate_succ, show k + 1 + 1 = 1 + (k + 1) by omega]
    constructor
    · iintro H
      icases (h 1 (k + 1)).1 $$ H with ⟨H1, Hk⟩
      iapply bigSepL_cons.2
      iframe H1
      iapply ih.1 $$ Hk
    · iintro H
      icases bigSepL_cons.1 $$ H with ⟨H1, Hk⟩
      iapply (h 1 (k + 1)).2
      iframe H1
      iapply ih.2 $$ Hk

/-- A fractional `Φ` at `(k + 1) r` is `k + 1` copies of `Φ r`. -/
theorem rep_frac (Φ : Qp → PROP) [Fractional Φ] (r : Qp) (k : Nat) :
    ∀ q : Qp, q.val = ((k : Rat) + 1) * r.val →
      (Φ q ⊣⊢ [∗list] _u ∈ List.replicate (k + 1) (), Φ r) := by
  induction k with
  | zero =>
    intro q hq
    have : q = r := Subtype.ext (by grind)
    subst this
    simp only [Nat.zero_add, List.replicate_one]
    exact (bigSepL_singleton (PROP := PROP) (Φ := fun _ _ => _) (x := ())).symm
  | succ k ih =>
    rintro ⟨q, hq⟩ hv
    obtain ⟨r, hr⟩ := r
    have hval : q - r = ((k : Rat) + 1) * r := by grind
    have hpos : (0 : Rat) < q - r := hval ▸ Rat.mul_pos (by grind) hr
    have hsum : ⟨r, hr⟩ + (⟨q - r, hpos⟩ : Qp) = ⟨q, hq⟩ := Subtype.ext (by grind)
    rw [← hsum, List.replicate_succ]
    have ih' := ih ⟨q - r, hpos⟩ hval
    constructor
    · iintro H
      icases (Fractional.fractional (Φ := Φ) ⟨r, hr⟩ ⟨q - r, hpos⟩).1 $$ H with ⟨H1, Hk⟩
      iapply bigSepL_cons.2
      iframe H1
      iapply ih'.1 $$ Hk
    · iintro H
      icases bigSepL_cons.1 $$ H with ⟨H1, Hk⟩
      iapply (Fractional.fractional (Φ := Φ) ⟨r, hr⟩ ⟨q - r, hpos⟩).2
      iframe H1
      iapply ih'.2 $$ Hk

/-- The share `q / n` taken `n` times is `q` (`n > 0`). -/
theorem div_posToQpZ_val (q : Qp) (k : Nat) :
    q.val = ((k : Rat) + 1) * (q / sync.posToQpZ ((k + 1 : Nat) : Int)).val := by
  rw [Qp.val_div, sync.posToQpZ_val _ (by omega)]
  have h0 : ((((k + 1 : Nat) : Int)) : Rat) = (k : Rat) + 1 := by push_cast; rfl
  rw [h0]
  have : (0 : Rat) < (k : Rat) + 1 := by
    have : (0 : Rat) ≤ (k : Rat) := by exact_mod_cast Nat.zero_le k
    grind
  rw [Rat.mul_div_cancel_left]; grind

end rep

end mvccfull
end EtcdGrove
end Perennial
