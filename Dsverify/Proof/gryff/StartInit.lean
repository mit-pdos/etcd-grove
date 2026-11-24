/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/StartInit.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

The start's initial state of Gryff's invariant (U6): the initial maps and the pure facts
(`invFacts_init`, `connFacts_init`, `opsJoin_init`); stage 2's initial maps (`preds0`,
`budget0`, `cur0`, `claims0`).
-/
module

public import Dsverify.Proof.gryff.Proto.InvDefs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial.gryff

open proto

/-- The replica nodes' stores at the start: `(0, tag0)` for nodes 0, 1, 2. -/
def stores0 : GMap Nat (w64 × PTag) :=
  GMap.insert 0 (W64 0, tag0) (GMap.insert 1 (W64 0, tag0) (GMap.insert 2 (W64 0, tag0) ∅))

/-- The tags' values at the start: `tag0 ↦ 0`. -/
def tv0 : GMap PTag w64 := GMap.insert tag0 (W64 0) ∅

/-- The stores' lower bounds at the start: `(k, tag0)` for nodes 0, 1, 2. -/
def lbs0 : GMap (Nat × PTag) Unit :=
  GMap.insert (0, tag0) () (GMap.insert (1, tag0) () (GMap.insert (2, tag0) () ∅))

theorem stores0_lookup (k : Nat) :
    stores0.lookup k = if k < 3 then some (W64 0, tag0) else none := by
  unfold stores0
  simp only [GMap.insert]
  show (if 0 = k then _ else if 1 = k then _ else if 2 = k then _ else GMap.empty.lookup k) = _
  rcases k with _|_|_|k <;> simp [GMap.empty]

theorem tv0_lookup (t : PTag) : tv0.lookup t = if t = tag0 then some (W64 0) else none := by
  unfold tv0
  simp only [GMap.insert]
  show (if tag0 = t then _ else GMap.empty.lookup t) = _
  by_cases h : t = tag0 <;> simp [h, GMap.empty, eq_comm]

theorem lbs0_lookup (k : Nat) (t : PTag) :
    lbs0.lookup (k, t) = if k < 3 ∧ t = tag0 then some () else none := by
  unfold lbs0
  simp only [GMap.insert]
  show (if (0, tag0) = (k, t) then _ else if (1, tag0) = (k, t) then _ else
    if (2, tag0) = (k, t) then _ else GMap.empty.lookup (k, t)) = _
  by_cases h : t = tag0
  · subst h; rcases k with _|_|_|k <;> simp [GMap.empty]
  · simp [GMap.empty, Ne.symm h, h]

theorem empty_lookup {K V : Type} (k : K) : (∅ : GMap K V).lookup k = none := rfl

theorem tagLe_refl (t : PTag) : tagLe t t := Or.inr rfl

theorem median3_same (t : PTag) : median3 t t t = t := by
  unfold median3 tagMax; simp

/-- The pure facts of Gryff's invariant hold of the initial state (any turns map: no operation
is registered). -/
theorem invFacts_init (turns : GMap Int (Int × Bool)) :
    invFacts (W64 0) stores0 tv0 lbs0 ∅ [] ∅ [] ∅ turns := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · refine ⟨(W64 0, tag0), (W64 0, tag0), (W64 0, tag0), by simp [stores0_lookup],
      by simp [stores0_lookup], by simp [stores0_lookup], ?_⟩
    simp only [median3_same]
    refine ⟨by simp [tv0_lookup], ?_, ?_, by simp [tv0_lookup], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, trivial, ?_, ?_, ?_, ?_⟩
    · intro k vt h
      rw [stores0_lookup] at h; split at h <;> simp at h
      subst h; simp [tv0_lookup]
    · intro k t h
      rw [lbs0_lookup] at h; split at h
      · rename_i hk; obtain ⟨hk, rfl⟩ := hk
        exact ⟨(W64 0, tag0), by simp [stores0_lookup, hk], tagLe_refl _⟩
      · simp at h
    · intro id m h; simp at h
    · intro cid r b r' _ h; simp at h
    · intro cid r1 r2 _ h; simp at h
    · intro t v h ht; rw [tv0_lookup] at h; simp [ht] at h
    · intro id o h; simp at h
    · simp
    · simp
    · simp [replayOk]
    · intro t v h _
      rw [tv0_lookup] at h; split at h <;> simp at h
      subst h; simp [replayOk]
    · intro id1 id2 m1 m2 t h; simp at h
    · intro e h; simp at h
    · intro e a m h; simp at h
    · intro k p h; simp at h
    · intro k1 k2 p1 p2 h; simp at h
  · refine ⟨?_, ?_, ?_⟩
    · intro t v h; rw [tv0_lookup] at h; split at h
      · rename_i ht; subst ht; exact tagLe_refl _
      · simp at h
    · intro t v h ht; rw [tv0_lookup] at h; simp [ht] at h
    · intro e h; simp at h
  · refine ⟨?_, ?_, ?_⟩
    · intro k vt h; rw [stores0_lookup] at h; split at h
      · assumption
      · simp at h
    · intro k vt h; rw [stores0_lookup] at h; split at h
      · rename_i hk; simp at h; subst h; simp [lbs0_lookup, hk]
      · simp at h
    · intro cid r r' _ h; simp at h
  · intro e a h; simp at h
  · intro id m t h; simp at h

theorem opsJoin_init : opsJoin ∅ ∅ ∅ := by
  refine ⟨fun id => ?_, fun id h => ?_⟩
  · rfl
  · simp at h

/-! ## Stage 2's initial maps (D13, D14) -/

/-- Keys `0, 1, 2` at `none`: the replica ids' predictions (`γ.s2.pred`) and the replica nodes'
(`γ.s2.nodePred`) at the start. -/
def preds0 : GMap Nat (Option (List w64)) :=
  GMap.insert 0 none (GMap.insert 1 none (GMap.insert 2 none ∅))

/-- The 24 budget units at the start (keys `0 .. 23`, `γ.s2.budget`). -/
def budget0 : GMap Nat Unit := (List.range 24).foldr (fun u m => GMap.insert u () m) ∅

/-- The nine receiving cursors at `0` (`γ.s2.rxCur`). -/
def cur0 : GMap (Nat × Nat) Nat :=
  ((List.range 3).flatMap fun k => (List.range 3).map fun q => (k, q)).foldr
    (fun kq m => GMap.insert kq 0 m) ∅

/-- The claim tokens of the three replica nodes (`γ.s2.claim`). -/
def claims0 : GMap Nat Unit := GMap.insert 0 () (GMap.insert 1 () (GMap.insert 2 () ∅))

theorem connFacts_init (conns : GMap w32 (Option Nat)) : connFacts conns ∅ ∅ := by
  refine ⟨fun id h => ?_, fun hs cid r _ h => ?_⟩ <;> simp at h

end Perennial.gryff
