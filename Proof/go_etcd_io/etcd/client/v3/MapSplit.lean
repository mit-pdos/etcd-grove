/-
Big separating conjunctions over `run`'s substreams (unit W-K, K2): a substream map `M` (ids to
substreams), injective with its values among the substreams `U`, splits `U`'s conjunction into
`M`'s and the rest (`bigSepM_split_inj`, `bigSepM_join_inj`); and a choice of a witness per value
of an injective map (`bigSepM_choice_inj`). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvWatch

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace client

open Iris Iris.BI Iris.ProofMode Iris.Std

variable {GF : BundledGFunctors}

/-- An injective map's entries (`hinj`) inside a map `U` (`hU`), after an insertion. -/
private theorem ins_facts {M' : GMap w64 Loc} {X0 : w64} {ws0 : Loc} (h : M' !! X0 = none)
    (hinj : ∀ X Y ws, (<[X0 := ws0]> M') !! X = some ws → (<[X0 := ws0]> M') !! Y = some ws →
      X = Y) :
    (∀ X ws, M' !! X = some ws → (<[X0 := ws0]> M') !! X = some ws) ∧
    (∀ X, M' !! X ≠ some ws0) := by
  have hsub : ∀ X ws, M' !! X = some ws → (<[X0 := ws0]> M') !! X = some ws := by
    intro X ws hX
    have hne : X0 ≠ X := fun e => by subst e; rw [h] at hX; cases hX
    rw [GMap.lookup_insert_ne _ _ hne]; exact hX
  refine ⟨hsub, fun X hX => ?_⟩
  have := hinj X X0 ws0 (hsub X ws0 hX) (GMap.lookup_insert _ _ _)
  subst this; rw [h] at hX; cases hX

/-- **Splitting `U`'s conjunction along `M`**: `M`'s substreams, and the others (an entry of `U`
is one of `M`'s, or keeps its conjunct). -/
theorem bigSepM_split_inj (Φ : Loc → IProp GF) (U : GMap Loc Unit) :
    ∀ M : GMap w64 Loc, (∀ X ws, M !! X = some ws → U !! ws = some ()) →
    (∀ X Y ws, M !! X = some ws → M !! Y = some ws → X = Y) →
    ([∗map] ws ↦ _u ∈ U, Φ ws) ⊢ ([∗map] _X ↦ ws ∈ M, Φ ws) ∗
      ([∗map] ws ↦ _u ∈ U, ⌜∃ X, M !! X = some ws⌝ ∨ Φ ws) := by
  intro M
  induction M using LawfulFiniteMap.induction_on with
  | hemp =>
    intro _ _
    iintro H
    isplitr
    · iapply BigSepM.bigSepM_empty.2; iempintro
    iapply (BigSepM.bigSepM_mono (fun {_ _} _ => by iintro H; iright; iexact H)) $$ H
  | hins X0 ws0 M' h ih =>
    intro hU hinj
    obtain ⟨hsub, hfresh⟩ := ins_facts h hinj
    iintro HU
    icases ih (fun X ws hX => hU X ws (hsub X ws hX))
      (fun X Y ws hX hY => hinj X Y ws (hsub X ws hX) (hsub Y ws hY)) $$ HU with ⟨HM, HR⟩
    have hws0 : U !! ws0 = some () := hU X0 ws0 (GMap.lookup_insert _ _ _)
    icases (BigSepM.bigSepM_delete hws0).1 $$ HR with ⟨H0, HR⟩
    icases H0 with (%Hc | H0)
    · obtain ⟨X, hX⟩ := Hc; exact absurd hX (hfresh X)
    isplitl [H0 HM]
    · iapply (BigSepM.bigSepM_insert h).2
      iframe H0 HM
    iapply (BigSepM.bigSepM_delete hws0).2
    isplitr
    · ileft; ipureintro; exact ⟨X0, GMap.lookup_insert _ _ _⟩
    iapply (BigSepM.bigSepM_mono (fun {k _} _ => by
      iintro H
      icases H with (%Hc | H)
      · ileft; ipureintro
        obtain ⟨X, hX⟩ := Hc; exact ⟨X, hsub X k hX⟩
      · iright; iexact H)) $$ HR

/-- **Joining `M`'s conjunction back into `U`'s** (the reverse of `bigSepM_split_inj`). -/
theorem bigSepM_join_inj (Φ : Loc → IProp GF) (U : GMap Loc Unit) :
    ∀ M : GMap w64 Loc, (∀ X ws, M !! X = some ws → U !! ws = some ()) →
    (∀ X Y ws, M !! X = some ws → M !! Y = some ws → X = Y) →
    ([∗map] _X ↦ ws ∈ M, Φ ws) ∗ ([∗map] ws ↦ _u ∈ U, ⌜∃ X, M !! X = some ws⌝ ∨ Φ ws) ⊢
      [∗map] ws ↦ _u ∈ U, Φ ws := by
  intro M
  induction M using LawfulFiniteMap.induction_on with
  | hemp =>
    intro _ _
    iintro ⟨-, H⟩
    iapply (BigSepM.bigSepM_mono (fun {_ _} _ => by
      iintro H
      icases H with (%Hc | H)
      · obtain ⟨X, hX⟩ := Hc; simp [GMap.lookup_empty] at hX
      · iexact H)) $$ H
  | hins X0 ws0 M' h ih =>
    intro hU hinj
    obtain ⟨hsub, hfresh⟩ := ins_facts h hinj
    iintro ⟨HM, HR⟩
    icases (BigSepM.bigSepM_insert h).1 $$ HM with ⟨H0, HM⟩
    have hws0 : U !! ws0 = some () := hU X0 ws0 (GMap.lookup_insert _ _ _)
    icases (BigSepM.bigSepM_delete hws0).1 $$ HR with ⟨-, HR⟩
    iapply ih (fun X ws hX => hU X ws (hsub X ws hX))
      (fun X Y ws hX hY => hinj X Y ws (hsub X ws hX) (hsub Y ws hY))
    iframe HM
    iapply (BigSepM.bigSepM_delete hws0).2
    isplitl [H0]
    · iright; iexact H0
    iapply (BigSepM.bigSepM_mono (fun {k _} hk => by
      iintro H
      icases H with (%Hc | H)
      · ileft; ipureintro
        obtain ⟨X, hX⟩ := Hc
        change (<[X0 := ws0]> M') !! X = some k at hX
        have hne : X0 ≠ X := by
          intro e; subst e
          rw [GMap.lookup_insert] at hX; cases hX
          change (GMap.delete ws0 U) !! ws0 = _ at hk
          rw [GMap.lookup_delete] at hk; cases hk
        rw [GMap.lookup_insert_ne _ _ hne] at hX
        exact ⟨X, hX⟩
      · iright; iexact H)) $$ HR

/-- **A witness per value of an injective map**: from a witness for each entry, a function of the
values. -/
theorem bigSepM_choice_inj {A : Type} (d : A) (Φ : Loc → A → IProp GF) :
    ∀ M : GMap w64 Loc, (∀ X Y ws, M !! X = some ws → M !! Y = some ws → X = Y) →
    ([∗map] _X ↦ ws ∈ M, ∃ a, Φ ws a) ⊢ ∃ f : Loc → A, [∗map] _X ↦ ws ∈ M, Φ ws (f ws) := by
  intro M
  induction M using LawfulFiniteMap.induction_on with
  | hemp =>
    intro _
    iintro -
    iexists fun _ => d
    iapply BigSepM.bigSepM_empty.2; iempintro
  | hins X0 ws0 M' h ih =>
    intro hinj
    obtain ⟨hsub, hfresh⟩ := ins_facts h hinj
    iintro H
    icases (BigSepM.bigSepM_insert h).1 $$ H with ⟨⟨%a, H0⟩, HM⟩
    icases ih (fun X Y ws hX hY => hinj X Y ws (hsub X ws hX) (hsub Y ws hY)) $$ HM
      with ⟨%f, HM⟩
    iexists fun l => if l = ws0 then a else f l
    iapply (BigSepM.bigSepM_insert h).2
    simp only [↓reduceIte]
    iframe H0
    iapply (BigSepM.bigSepM_mono (fun {k ws} hk => by
      have hne : ws ≠ ws0 := fun e => by subst e; exact hfresh k hk
      simp only [hne, ↓reduceIte]
      exact .rfl)) $$ HM

/-- **A witness per key**: from a witness for each key of `U`, a function of the keys. -/
theorem bigSepM_choice_keys {A : Type} (d : A) (Φ : Loc → A → IProp GF) :
    ∀ U : GMap Loc Unit,
    ([∗map] ws ↦ _u ∈ U, ∃ a, Φ ws a) ⊢ ∃ f : Loc → A, [∗map] ws ↦ _u ∈ U, Φ ws (f ws) := by
  intro U
  induction U using LawfulFiniteMap.induction_on with
  | hemp =>
    iintro -
    iexists fun _ => d
    iapply BigSepM.bigSepM_empty.2; iempintro
  | hins ws0 u0 U' h ih =>
    iintro H
    icases (BigSepM.bigSepM_insert h).1 $$ H with ⟨⟨%a, H0⟩, HU⟩
    icases ih $$ HU with ⟨%f, HU⟩
    iexists fun l => if l = ws0 then a else f l
    iapply (BigSepM.bigSepM_insert h).2
    simp only [↓reduceIte]
    iframe H0
    iapply (BigSepM.bigSepM_mono (fun {k x} hk => by
      have hne : k ≠ ws0 := fun e => by subst e; rw [h] at hk; cases hk
      simp only [hne, ↓reduceIte]
      exact .rfl)) $$ HU

end client
end EtcdGrove
end Perennial
