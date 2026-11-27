/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/gprot/Ghost.lean (241f27e).
-/
/-
`gprot` internals — a ghost map mirroring a (finitely supported) function `f : K → Option V`,
with a persistent element for every entry of `f`. The history of the protocol model is held in
such maps; a step that only grows `f` on a finite list of keys is a ghost update.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Ghost.GhostMap

@[expose] public section

set_option linter.unusedVariables false
set_option linter.deprecated false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace github_com.hashicorp.raft
namespace gprot

section ghost
variable {GF : BundledGFunctors} [AllG GF]
variable {K V : Type} [DecidableEq K] [Pos.Countable K] [Pos.Countable V]

/-- The ghost map at `γn` mirrors `f`, and every entry of `f` has its persistent element. -/
def GMapOf (γn : GName) (f : K → Option V) : IProp GF :=
  iprop(∃ m : GMap K V, ⌜∀ k, m.lookup k = f k⌝ ∗ ghostMapAuth γn 1 m ∗
    □ (∀ k v, ⌜f k = some v⌝ → k ↪[γn]□ v))

instance GMapOf_timeless (γn : GName) (f : K → Option V) :
    Timeless (GMapOf (GF := GF) γn f) := by
  unfold GMapOf; infer_instance

theorem GMapOf_lookup (γn : GName) (f : K → Option V) (k : K) (v : V) :
    GMapOf (GF := GF) γn f ∗ k ↪[γn]□ v ⊢ GMapOf γn f ∗ ⌜f k = some v⌝ := by
  unfold GMapOf
  iintro ⟨⟨%m, %hm, Ha, #Hf⟩, #Hk⟩
  icombine Ha Hk gives %h
  isplitl [Ha]
  · iexists m; isplitr; · ipureintro; exact hm
    iframe; iexact Hf
  · ipureintro; rw [← hm]; exact h

theorem GMapOf_get (γn : GName) (f : K → Option V) (k : K) (v : V) (h : f k = some v) :
    GMapOf (GF := GF) γn f ⊢ GMapOf γn f ∗ k ↪[γn]□ v := by
  unfold GMapOf
  iintro ⟨%m, %hm, Ha, #Hf⟩
  isplitl [Ha]
  · iexists m; isplitr; · ipureintro; exact hm
    iframe; iexact Hf
  · iapply Hf; ipureintro; exact h

theorem GMapOf_congr (γn : GName) (f g : K → Option V) (h : ∀ k, f k = g k) :
    GMapOf (GF := GF) γn f ⊢ GMapOf γn g := by
  have : f = g := funext h
  subst this; exact .rfl

/-- Grow `f` to `g` at one key. -/
theorem GMapOf_insert1 (γn : GName) (f g : K → Option V) (k : K)
    (hsub : ∀ k v, f k = some v → g k = some v) (hout : ∀ k', k' ≠ k → g k' = f k') :
    GMapOf (GF := GF) γn f ⊢ |==> GMapOf γn g := by
  cases hgk : g k with
  | none =>
    have : ∀ k', f k' = g k' := by
      intro k'
      by_cases hk : k' = k
      · subst hk
        cases hfk : f k' with
        | none => rw [hgk]
        | some v => have := hsub _ _ hfk; rw [hgk] at this; cases this
      · rw [hout k' hk]
    iintro H
    imodintro
    iapply GMapOf_congr γn f g this $$ H
  | some v =>
    unfold GMapOf
    iintro ⟨%m, %hm, Ha, #Hf⟩
    cases hfk : f k with
    | some v' =>
      have hv : v' = v := by have := hsub _ _ hfk; rw [hgk] at this; cases this; rfl
      subst hv
      have : ∀ k', f k' = g k' := by
        intro k'
        by_cases hk : k' = k
        · subst hk; rw [hfk, hgk]
        · rw [hout k' hk]
      have := funext this; subst this
      imodintro
      iexists m; isplitr; · ipureintro; exact hm
      iframe; iexact Hf
    | none =>
      have hmk : m.lookup k = none := by rw [hm, hfk]
      imod ghost_map_insert_persist k v hmk $$ Ha with ⟨Ha, #Hk⟩
      imodintro
      iexists (m.insert k v)
      isplitr
      · ipureintro
        intro k'
        show (if k = k' then some v else m.lookup k') = g k'
        by_cases hk : k = k'
        · subst hk; rw [if_pos rfl, hgk]
        · rw [if_neg hk, hm, hout k' (Ne.symm hk)]
      isplitl [Ha]
      · iexact Ha
      · imodintro
        iintro %k' %v' %hk'
        by_cases hkk : k' = k
        · subst hkk
          rw [hgk] at hk'; cases hk'; iexact Hk
        · iapply Hf; ipureintro; rw [← hout k' hkk]; exact hk'

/-- Grow `f` to `g` on a finite list of keys. -/
theorem GMapOf_grow (γn : GName) (ks : List K) :
    ∀ (f g : K → Option V), (∀ k v, f k = some v → g k = some v) →
      (∀ k, k ∉ ks → g k = f k) →
      GMapOf (GF := GF) γn f ⊢ |==> GMapOf γn g := by
  induction ks with
  | nil =>
    intro f g _ hout
    iintro H; imodintro
    iapply GMapOf_congr γn f g (fun k => (hout k (by simp)).symm) $$ H
  | cons k ks ih =>
    intro f g hsub hout
    let f1 : K → Option V := fun k' => if k' = k then g k else f k'
    have h1sub : ∀ k' v, f k' = some v → f1 k' = some v := by
      intro k' v h
      by_cases hk : k' = k
      · subst hk; simp only [f1, if_pos rfl]; exact hsub _ _ h
      · simp only [f1, if_neg hk]; exact h
    have h1out : ∀ k', k' ≠ k → f1 k' = f k' := by
      intro k' hk; simp only [f1, if_neg hk]
    have h2sub : ∀ k' v, f1 k' = some v → g k' = some v := by
      intro k' v h
      by_cases hk : k' = k
      · simp only [f1, if_pos hk] at h; subst hk; exact h
      · simp only [f1, if_neg hk] at h; exact hsub _ _ h
    have h2out : ∀ k', k' ∉ ks → g k' = f1 k' := by
      intro k' hk
      by_cases hkk : k' = k
      · subst hkk; simp only [f1, if_pos rfl]
      · simp only [f1, if_neg hkk]; exact hout k' (by simp [hkk, hk])
    iintro H
    imod GMapOf_insert1 γn f f1 k h1sub h1out $$ H with H
    iapply ih f1 g h2sub h2out $$ H

theorem GMapOf_alloc :
    ⊢ |==> ∃ γn, GMapOf (GF := GF) γn (fun (_ : K) => (none : Option V)) := by
  imod ghost_map_alloc_empty (GF := GF) (K := K) (V := V) with ⟨%γn, Ha⟩
  imodintro
  iexists γn
  unfold GMapOf
  iexists ∅
  isplitr
  · ipureintro; intro k; rfl
  isplitl [Ha]
  · iexact Ha
  · imodintro
    iintro %k %v %h
    cases h

end ghost

end gprot
end github_com.hashicorp.raft

end Perennial
