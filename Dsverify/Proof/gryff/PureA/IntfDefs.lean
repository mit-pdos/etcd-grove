/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureA/IntfDefs.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit AI, internal: **the interference invariant's vocabulary** and the combinatorial core of D1
(`notes/unit-AI.md`; `interf`, `GryffProof/Pure/Agree.lean`).

Ghosts:
* a global clock `κ` (the number of steps so far);
* `rc : RecG`, `rc w q j = some t`: replica `w` first recorded instance `(q, j)` in its conflict
  table (`updateConflicts` with commands) at step `t`;
* `dg : DepG`, `dg q j = some D`: the deps instance `(q, j)` was created with (`handlePropose`).

A value with deps `D` of instance `(q, i)` is *covered* by replica `w` at a handling time `τ`, except
row `e` (`Cov`): `w` recorded `(q, i)` by `τ`, and every instance of another row (not `e`) that `w`
recorded before `τ` is in `D`. `Wp2`: two distinct coverers, the first with no exception, the second
with no exception or the first's row (the merging leader / recoverer keeps its own `deps[M]` and
ignores the replier's). `SameRow`: `deps[q] ≥ i - 1`.

`interf_core`: two values of instances of different rows with `Wp2` (and the ghost's laws: the
owner records first, one record per step and replica) depend one on the other.
-/
module

public import Dsverify.Proof.gryff.PureA.WitDefs

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pureA.AI

open Perennial Perennial.gryff.model Perennial.gryff.pure Perennial.gryff.kahn Perennial.gryff.pureA
open Perennial.gryff.pureA.AW

/-- When each replica first recorded each instance in its conflict table. -/
abbrev RecG := Fin 3 → w32 → w32 → Option Nat

/-- The creation deps of each instance. -/
abbrev DepG := w32 → w32 → Option Deps

/-- Replica `w` covers deps `D` of instance `(q, i)` at a time `τ ≤ κ`, except row `e`. -/
def Cov (rc : RecG) (κ : Nat) (q i : w32) (D : Deps) (w : Fin 3) (e : Option (Fin 3)) : Prop :=
  ∃ τ, τ ≤ κ ∧ (∃ t, rc w q i = some t ∧ t ≤ τ) ∧
    ∀ (r : Fin 3) j t, rc w (rid32 r) j = some t → t < τ → rid32 r ≠ q → e ≠ some r →
      sint.Z j ≤ sint.Z (D.at r.val)

/-- Two coverers. -/
def Wp2 (rc : RecG) (κ : Nat) (q i : w32) (D : Deps) : Prop :=
  ∃ w1 w2 e, w1 ≠ w2 ∧ Cov rc κ q i D w1 none ∧ Cov rc κ q i D w2 e ∧ (e = none ∨ e = some w1)

/-- The same-row dependency: `deps[q] ≥ i - 1`. -/
def SameRow (q i : w32) (D : Deps) : Prop := sint.Z i - 1 ≤ sint.Z (D.at q.toNat)

/-- A value's facts: same row, one coverer, two if of a STRONG status. -/
def ValI (rc : RecG) (κ : Nat) (q i : w32) (D : Deps) (st : w8) : Prop :=
  SameRow q i D ∧ (∃ w, Cov rc κ q i D w none) ∧ (Strong st → Wp2 rc κ q i D)

/-! ## Rows -/

theorem rid32_toNat (r : Fin 3) : (rid32 r).toNat = r.val := by revert r; decide

theorem rid32_inj {a b : Fin 3} (h : rid32 a = rid32 b) : a = b := by
  have := congrArg BitVec.toNat h
  rw [rid32_toNat, rid32_toNat] at this
  exact Fin.ext this

theorem fin3_pigeon (a1 a2 b1 b2 : Fin 3) (ha : a1 ≠ a2) (hb : b1 ≠ b2) :
    a1 = b1 ∨ a1 = b2 ∨ a2 = b1 ∨ a2 = b2 := by
  revert a1 a2 b1 b2; decide

theorem fin3_other (w1 w2 L R : Fin 3) (hLR : L ≠ R) (h12 : w1 ≠ w2) (h1 : ¬ (w1 = L ∨ w1 = R)) :
    w2 = L ∨ w2 = R := by
  revert w1 w2 L R; decide

/-! ## The core of D1 -/

section core
variable {rc : RecG} {κ : Nat}

/-- `w` covers `(q, i)` with an exception other than `R`. -/
def Good (rc : RecG) (κ : Nat) (q i : w32) (D : Deps) (R w : Fin 3) : Prop :=
  ∃ e, Cov rc κ q i D w e ∧ e ≠ some R

theorem rec_of_good {q i : w32} {D : Deps} {R w : Fin 3} (g : Good rc κ q i D R w) :
    ∃ t, rc w q i = some t := by
  obtain ⟨e, ⟨τ, -, ⟨t, ht, -⟩, -⟩, -⟩ := g
  exact ⟨t, ht⟩

/-- A good coverer of `x` that misses `y`: it recorded `x` strictly before `y`. -/
theorem lt_of_good (inj : ∀ w q j q' j' t, rc w q j = some t → rc w q' j' = some t → q = q' ∧ j = j')
    {L R w : Fin 3} (hLR : L ≠ R) {ix iy : w32} {D : Deps}
    (nx : ¬ sint.Z iy ≤ sint.Z (D.at R.val)) (g : Good rc κ (rid32 L) ix D R w) :
    ∃ tx, rc w (rid32 L) ix = some tx ∧ ∀ ty, rc w (rid32 R) iy = some ty → tx < ty := by
  obtain ⟨e, ⟨τ, -, ⟨tx, h1, h2⟩, h3⟩, he⟩ := g
  refine ⟨tx, h1, fun ty hy => ?_⟩
  have hq : rid32 R ≠ rid32 L := fun h => hLR (rid32_inj h).symm
  have hle : tx ≤ ty := Nat.le_of_not_lt fun hlt => nx (h3 R iy ty hy (Nat.lt_of_lt_of_le hlt h2) hq he)
  rcases Nat.lt_or_eq_of_le hle with h | h
  · exact h
  · subst h
    exact absurd (rid32_inj (inj _ _ _ _ _ _ h1 hy).1) hLR

/-- A pair has a good member among the two rows. -/
theorem good_rows {L R : Fin 3} (hLR : L ≠ R) {ix : w32} {D : Deps}
    (hW : Wp2 rc κ (rid32 L) ix D) : ∃ a, (a = L ∨ a = R) ∧ Good rc κ (rid32 L) ix D R a := by
  obtain ⟨w1, w2, e, h12, c1, c2, he⟩ := hW
  by_cases h1 : w1 = L ∨ w1 = R
  · exact ⟨w1, h1, none, c1, by simp⟩
  · refine ⟨w2, fin3_other w1 w2 L R hLR h12 h1, e, c2, fun e' => ?_⟩
    subst e'
    rcases he with he | he
    · cases he
    · cases he; exact h1 (Or.inr rfl)

/-- A member of a pair is good, or `R` is. -/
theorem good_or_R {L R : Fin 3} {ix : w32} {D : Deps} {w1 w2 : Fin 3} {e : Option (Fin 3)}
    (c1 : Cov rc κ (rid32 L) ix D w1 none) (c2 : Cov rc κ (rid32 L) ix D w2 e)
    (he : e = none ∨ e = some w1) {w : Fin 3} (hw : w = w1 ∨ w = w2) :
    Good rc κ (rid32 L) ix D R w ∨ Good rc κ (rid32 L) ix D R R := by
  rcases hw with rfl | rfl
  · exact Or.inl ⟨none, c1, by simp⟩
  · by_cases h : e = some R
    · subst h
      rcases he with he | he
      · cases he
      · cases he; exact Or.inr ⟨none, c1, by simp⟩
    · exact Or.inl ⟨e, c2, h⟩

/-- If `R` (the owner of `y`) is a good coverer of `x` (missing `y`), no member of `y`'s rows is a
good coverer of `y` missing `x`. -/
theorem owner_good_contra
    (own : ∀ w r j t, rc w (rid32 r) j = some t → ∃ t0, rc r (rid32 r) j = some t0 ∧ t0 ≤ t)
    (inj : ∀ w q j q' j' t, rc w q j = some t → rc w q' j' = some t → q = q' ∧ j = j')
    {L R : Fin 3} (hLR : L ≠ R) {ix iy : w32} {Dx Dy : Deps}
    (nx : ¬ sint.Z iy ≤ sint.Z (Dx.at R.val)) (ny : ¬ sint.Z ix ≤ sint.Z (Dy.at L.val))
    (gR : Good rc κ (rid32 L) ix Dx R R) {b : Fin 3} (hb : b = L ∨ b = R)
    (gb : Good rc κ (rid32 R) iy Dy L b) : False := by
  obtain ⟨tx, hx, kx⟩ := lt_of_good inj hLR nx gR
  obtain ⟨tyb, hyb, ky⟩ := lt_of_good inj (Ne.symm hLR) ny gb
  obtain ⟨ty0, hy0, ey0⟩ := own b R iy tyb hyb
  have l1 := kx ty0 hy0
  have hbx : ∃ t', rc b (rid32 L) ix = some t' ∧ t' ≤ tx := by
    rcases hb with rfl | rfl
    · exact own R b ix tx hx
    · exact ⟨tx, hx, Nat.le_refl _⟩
  obtain ⟨t', ht', et'⟩ := hbx
  have l2 := ky t' ht'
  omega

/-- **The core of D1** (instances of different rows). -/
theorem interf_core
    (own : ∀ w r j t, rc w (rid32 r) j = some t → ∃ t0, rc r (rid32 r) j = some t0 ∧ t0 ≤ t)
    (inj : ∀ w q j q' j' t, rc w q j = some t → rc w q' j' = some t → q = q' ∧ j = j')
    {L R : Fin 3} (hLR : L ≠ R) {ix iy : w32} {Dx Dy : Deps}
    (hx : Wp2 rc κ (rid32 L) ix Dx) (hy : Wp2 rc κ (rid32 R) iy Dy) :
    sint.Z iy ≤ sint.Z (Dx.at R.val) ∨ sint.Z ix ≤ sint.Z (Dy.at L.val) := by
  refine Classical.byContradiction fun hn => ?_
  have nx : ¬ sint.Z iy ≤ sint.Z (Dx.at R.val) := fun h => hn (Or.inl h)
  have ny : ¬ sint.Z ix ≤ sint.Z (Dy.at L.val) := fun h => hn (Or.inr h)
  have cR : Good rc κ (rid32 L) ix Dx R R → False := fun gR => by
    obtain ⟨b, hb, gb⟩ := good_rows (Ne.symm hLR) hy
    exact owner_good_contra own inj hLR nx ny gR (hb.symm) gb
  have cL : Good rc κ (rid32 R) iy Dy L L → False := fun gL => by
    obtain ⟨a, ha, ga⟩ := good_rows hLR hx
    exact owner_good_contra own inj (Ne.symm hLR) ny nx gL ha.symm ga
  obtain ⟨a1, a2, ea, ha, ca1, ca2, hea⟩ := hx
  obtain ⟨b1, b2, eb, hb, cb1, cb2, heb⟩ := hy
  have common : ∃ w, (w = a1 ∨ w = a2) ∧ (w = b1 ∨ w = b2) := by
    rcases fin3_pigeon a1 a2 b1 b2 ha hb with h | h | h | h
    · exact ⟨a1, Or.inl rfl, Or.inl h⟩
    · exact ⟨a1, Or.inl rfl, Or.inr h⟩
    · exact ⟨a2, Or.inr rfl, Or.inl h⟩
    · exact ⟨a2, Or.inr rfl, Or.inr h⟩
  obtain ⟨w, hwa, hwb⟩ := common
  rcases good_or_R (R := R) ca1 ca2 hea hwa with gx | gx
  · rcases good_or_R (R := L) cb1 cb2 heb hwb with gy | gy
    · obtain ⟨tx, hx1, kx⟩ := lt_of_good inj hLR nx gx
      obtain ⟨ty, hy1, ky⟩ := lt_of_good inj (Ne.symm hLR) ny gy
      have := kx ty hy1; have := ky tx hx1; omega
    · exact cL gy
  · exact cR gx

end core

end Perennial.gryff.pureA.AI
