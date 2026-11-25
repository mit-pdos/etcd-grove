/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureA/Abstract.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit A1, internal: the abstract core of per-instance agreement (`notes/stage2-proof.md` §A,
`notes/unit-A1.md`).

One EPaxos instance `x = (L, i)`, three acceptors (`Fin 3`), ballots as integers (`sint.Z` of the
model's words). The run's history is abstracted by a ghost `Gh` (monotone along a run):
* `acc a b v`: acceptor `a` *accepted* `(b, v)` (its copy became ACCEPTED at vbal `b` with `v`:
  `handleAccept`, or the proposer accepting its own proposal);
* `prop b v`: an Accept proposal `(b, v)` was made (by `L` at ballot 0, by the recoverer owning `b`);
* `rst b`: phase 1 was restarted at ballot `b > 0` (G9: `startPhase1` from `handlePrepareReply`);
* `cre v`: `L` created the instance with value `v` (`handlePropose` → `startPhase1`, ballot 0);
* `eq a`: acceptor `a ≠ L` pre-accepted `L`'s ballot-0 PreAccept unchanged (PREACCEPTED_EQ, vbal 0);
* `fast v`: `L` committed `v` on the fast path (ballot 0).

The current state enters through `bal a`: acceptor `a`'s copy's ballot (`none`: no copy).

*Chosen*: fast-committed, or accepted at one ballot by two distinct acceptors. `chosen_unique`: under
the abstract invariant `AInv`, at most one value is chosen. The invariant's key clause is
`SafeAt` (A3), stated in a form that is stable along a run (`safeAt_evolve`): below a proposal's
ballot, no other value can ever be chosen, because two acceptors are *blocked* (ballot above, no
vote) or another value was proposed there; at ballot 0 also the fast path is blocked
(`FastNoChoice`).

`decide_safe_*` is A3's case analysis at a recovery's decision (`handlePrepareReply`, G16/G17/G22/G24),
over the recoverer's own snapshot and the deciding reply.
-/
module

public import Perennial.Std.Word

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pureA

/-- The ghost history of one instance. -/
structure Gh (V : Type) where
  acc : Fin 3 → Int → V → Prop
  prop : Int → V → Prop
  rst : Int → Prop
  cre : V → Prop
  eq : Fin 3 → Prop
  fast : V → Prop

variable {V : Type}

/-- `g'` extends `g`. -/
structure Gh.Le (g g' : Gh V) : Prop where
  acc : ∀ a b v, g.acc a b v → g'.acc a b v
  prop : ∀ b v, g.prop b v → g'.prop b v
  rst : ∀ b, g.rst b → g'.rst b
  cre : ∀ v, g.cre v → g'.cre v
  eq : ∀ a, g.eq a → g'.eq a
  fast : ∀ v, g.fast v → g'.fast v

theorem Gh.Le.refl (g : Gh V) : g.Le g := ⟨fun _ _ _ h => h, fun _ _ h => h, fun _ h => h,
  fun _ h => h, fun _ h => h, fun _ h => h⟩

theorem Gh.Le.trans {g1 g2 g3 : Gh V} (h1 : g1.Le g2) (h2 : g2.Le g3) : g1.Le g3 :=
  ⟨fun a b v h => h2.acc a b v (h1.acc a b v h), fun b v h => h2.prop b v (h1.prop b v h),
   fun b h => h2.rst b (h1.rst b h), fun v h => h2.cre v (h1.cre v h),
   fun a h => h2.eq a (h1.eq a h), fun v h => h2.fast v (h1.fast v h)⟩

/-- Acceptor `a` is blocked at ballot `b'` for value `w`: its ballot is above `b'` and it did not
accept `(b', w)`. Stable: an acceptor accepts only at ballots `≥` its ballot. -/
def Blk (g : Gh V) (bal : Fin 3 → Option Int) (a : Fin 3) (b' : Int) (w : V) : Prop :=
  ∃ B, bal a = some B ∧ b' < B ∧ ¬ g.acc a b' w

/-- `w` can never be chosen (slowly) at `b'`. -/
def SlowNoChoice (g : Gh V) (bal : Fin 3 → Option Int) (b' : Int) (w : V) : Prop :=
  (∃ u, u ≠ w ∧ g.prop b' u) ∨ ∃ a1 a2, a1 ≠ a2 ∧ Blk g bal a1 b' w ∧ Blk g bal a2 b' w

/-- `w` can never be fast-chosen (at ballot 0 by leader `L`). -/
def FastNoChoice (g : Gh V) (bal : Fin 3 → Option Int) (L : Fin 3) (w : V) : Prop :=
  (∃ v, g.cre v ∧ w ≠ v) ∨ (∃ B, bal L = some B ∧ 0 < B ∧ ∀ v, ¬ g.fast v) ∨ (∃ u, g.prop 0 u) ∨
    (∀ a, a ≠ L → ∃ B, bal a = some B ∧ 0 < B ∧ ¬ g.eq a)

/-- Nothing but `v` can be chosen below `b` (A3's conclusion for a proposal `(b, v)`). -/
def SafeAt (g : Gh V) (bal : Fin 3 → Option Int) (L : Fin 3) (b : Int) (v : V) : Prop :=
  ∀ b', 0 ≤ b' → b' < b → ∀ w, w ≠ v → SlowNoChoice g bal b' w ∧ (b' = 0 → FastNoChoice g bal L w)

/-- Nothing at all can be chosen below `b` (a restart or a no-op at `b`). -/
def SafeAll (g : Gh V) (bal : Fin 3 → Option Int) (L : Fin 3) (b : Int) : Prop :=
  ∀ b', 0 ≤ b' → b' < b → ∀ w, SlowNoChoice g bal b' w ∧ (b' = 0 → FastNoChoice g bal L w)

theorem SafeAll.safeAt {g : Gh V} {bal : Fin 3 → Option Int} {L : Fin 3} {b : Int} (h : SafeAll g bal L b)
    (v : V) : SafeAt g bal L b v := fun b' h0 h1 w _ => h b' h0 h1 w

/-- Chosen: fast-committed, or accepted at one ballot by two distinct acceptors. -/
def Chosen (g : Gh V) (v : V) : Prop :=
  g.fast v ∨ ∃ b a1 a2, a1 ≠ a2 ∧ g.acc a1 b v ∧ g.acc a2 b v

/-- The abstract invariant (the clauses `chosen_unique` needs). -/
structure AInv (g : Gh V) (bal : Fin 3 → Option Int) (L : Fin 3) : Prop where
  /-- A1: one proposal per ballot. -/
  prop_uniq : ∀ b v w, g.prop b v → g.prop b w → v = w
  /-- a vote is for a proposal -/
  acc_prop : ∀ a b v, g.acc a b v → g.prop b v
  /-- ballots are nonnegative -/
  prop_nonneg : ∀ b v, g.prop b v → 0 ≤ b
  /-- A3 -/
  prop_safe : ∀ b v, g.prop b v → SafeAt g bal L b v
  rst_safe : ∀ b, g.rst b → SafeAll g bal L b
  /-- the creation is unique -/
  cre_uniq : ∀ v w, g.cre v → g.cre w → v = w
  /-- a fast commit commits the created value, after an unchanged pre-accept, without a ballot-0
  Accept -/
  fast_cre : ∀ v, g.fast v → g.cre v
  fast_eq : ∀ v, g.fast v → ∃ a, a ≠ L ∧ g.eq a
  fast_noprop : ∀ v, g.fast v → ∀ u, ¬ g.prop 0 u

/-- Two distinct blocked acceptors and two distinct voters share a member (N = 3). -/
theorem pigeon (a1 a2 c1 c2 : Fin 3) (ha : a1 ≠ a2) (hc : c1 ≠ c2) :
    a1 = c1 ∨ a1 = c2 ∨ a2 = c1 ∨ a2 = c2 := by
  revert a1 a2 c1 c2; decide

theorem slow_vs_slow {g : Gh V} {bal : Fin 3 → Option Int} {L : Fin 3} (I : AInv g bal L)
    {b0 b1 : Int} (hb : b0 < b1) {v w : V} {a1 a2 c1 : Fin 3} (ha : a1 ≠ a2)
    (h1 : g.acc a1 b0 v) (h2 : g.acc a2 b0 v) (hc1 : g.acc c1 b1 w) : v = w := by
  refine Classical.byContradiction fun hne => ?_
  have hp := I.acc_prop _ _ _ hc1
  have h0 : 0 ≤ b0 := I.prop_nonneg _ _ (I.acc_prop _ _ _ h1)
  obtain ⟨hs, _⟩ := I.prop_safe _ _ hp b0 h0 hb v hne
  rcases hs with ⟨u, hu, hpu⟩ | ⟨d1, d2, hd, ⟨B1, _, _, hn1⟩, ⟨B2, _, _, hn2⟩⟩
  · exact hu (I.prop_uniq _ _ _ hpu (I.acc_prop _ _ _ h1))
  · rcases pigeon d1 d2 a1 a2 hd ha with h | h | h | h <;> subst h <;> contradiction

theorem fast_vs_slow {g : Gh V} {bal : Fin 3 → Option Int} {L : Fin 3} (I : AInv g bal L)
    {b : Int} {v w : V} {c1 : Fin 3} (hf : g.fast v) (hc1 : g.acc c1 b w) : v = w := by
  have hp := I.acc_prop _ _ _ hc1
  have hb0 := I.prop_nonneg _ _ hp
  rcases Int.lt_or_eq_of_le hb0 with hb | hb
  · refine Classical.byContradiction fun hne => ?_
    obtain ⟨_, hf0⟩ := I.prop_safe _ _ hp 0 (Int.le_refl 0) hb v hne
    rcases hf0 rfl with h | ⟨B, _, _, h⟩ | ⟨u, hu⟩ | h
    · obtain ⟨v', hc, hne'⟩ := h
      exact hne' (I.cre_uniq _ _ (I.fast_cre v hf) hc)
    · exact h v hf
    · exact I.fast_noprop v hf u hu
    · obtain ⟨a, haL, hea⟩ := I.fast_eq v hf
      obtain ⟨B, _, _, hn⟩ := h a haL
      exact hn hea
  · subst hb; exact absurd hp (I.fast_noprop v hf w)

/-- **At most one value is chosen.** -/
theorem chosen_unique {g : Gh V} {bal : Fin 3 → Option Int} {L : Fin 3} (I : AInv g bal L)
    {v w : V} (hv : Chosen g v) (hw : Chosen g w) : v = w := by
  rcases hv with hv | ⟨b0, a1, a2, ha, h1, h2⟩ <;> rcases hw with hw | ⟨b1, c1, c2, hc, k1, k2⟩
  · exact I.cre_uniq _ _ (I.fast_cre _ hv) (I.fast_cre _ hw)
  · exact fast_vs_slow I hv k1
  · exact (fast_vs_slow I hw h1).symm
  · rcases Int.lt_trichotomy b0 b1 with hb | hb | hb
    · exact slow_vs_slow I hb ha h1 h2 k1
    · subst hb; exact I.prop_uniq _ _ _ (I.acc_prop _ _ _ h1) (I.acc_prop _ _ _ k1)
    · exact (slow_vs_slow I hb hc k1 k2 h1).symm

/-! ## Stability of `SafeAt` along a run -/

/-- One configuration evolving into another (any number of steps): the ghost grows, copies stay and
their ballots do not decrease, and the new history respects the ballots:
* a new vote `(b, w)` at `a` is at a ballot `≥` `a`'s former ballot;
* a new unchanged pre-accept at `a` needs `a`'s former ballot `≤ 0`;
* a new fast commit needs `L`'s former ballot `≤ 0`, and the new history keeps `AInv`'s fast clauses. -/
structure Evolve (L : Fin 3) (g : Gh V) (bal : Fin 3 → Option Int) (g' : Gh V)
    (bal' : Fin 3 → Option Int) : Prop where
  le : g.Le g'
  bal_mono : ∀ a B, bal a = some B → ∃ B', bal' a = some B' ∧ B ≤ B'
  acc_new : ∀ a b w, g'.acc a b w → ¬ g.acc a b w → ∀ B, bal a = some B → B ≤ b
  eq_new : ∀ a, g'.eq a → ¬ g.eq a → ∀ B, bal a = some B → B ≤ 0
  fast_new : ∀ v, g'.fast v → ¬ g.fast v → ∀ B, bal L = some B → B ≤ 0
  fast_cre : ∀ v, g'.fast v → g'.cre v
  fast_eq : ∀ v, g'.fast v → ∃ a, a ≠ L ∧ g'.eq a
  fast_noprop : ∀ v, g'.fast v → ∀ u, ¬ g'.prop 0 u

theorem Evolve.refl {L : Fin 3} {g : Gh V} {bal : Fin 3 → Option Int} (I : AInv g bal L) :
    Evolve L g bal g bal where
  le := Gh.Le.refl g
  bal_mono _ B h := ⟨B, h, Int.le_refl B⟩
  acc_new _ _ _ h hn := absurd h hn
  eq_new _ h hn := absurd h hn
  fast_new _ h hn := absurd h hn
  fast_cre := I.fast_cre
  fast_eq := I.fast_eq
  fast_noprop := I.fast_noprop

theorem Evolve.trans {L : Fin 3} {g1 g2 g3 : Gh V} {b1 b2 b3 : Fin 3 → Option Int}
    (h1 : Evolve L g1 b1 g2 b2) (h2 : Evolve L g2 b2 g3 b3) : Evolve L g1 b1 g3 b3 where
  le := h1.le.trans h2.le
  bal_mono a B h := by
    obtain ⟨B2, h2', hle⟩ := h1.bal_mono a B h
    obtain ⟨B3, h3', hle'⟩ := h2.bal_mono a B2 h2'
    exact ⟨B3, h3', Int.le_trans hle hle'⟩
  acc_new a b w h3 hn1 B hB := by
    by_cases h2' : g2.acc a b w
    · exact h1.acc_new a b w h2' hn1 B hB
    · obtain ⟨B2, hB2, hle⟩ := h1.bal_mono a B hB
      exact Int.le_trans hle (h2.acc_new a b w h3 h2' B2 hB2)
  eq_new a h3 hn1 B hB := by
    by_cases h2' : g2.eq a
    · exact h1.eq_new a h2' hn1 B hB
    · obtain ⟨B2, hB2, hle⟩ := h1.bal_mono a B hB
      exact Int.le_trans hle (h2.eq_new a h3 h2' B2 hB2)
  fast_new v h3 hn1 B hB := by
    by_cases h2' : g2.fast v
    · exact h1.fast_new v h2' hn1 B hB
    · obtain ⟨B2, hB2, hle⟩ := h1.bal_mono L B hB
      exact Int.le_trans hle (h2.fast_new v h3 h2' B2 hB2)
  fast_cre := h2.fast_cre
  fast_eq := h2.fast_eq
  fast_noprop := h2.fast_noprop

theorem blk_evolve {L : Fin 3} {g g' : Gh V} {bal bal' : Fin 3 → Option Int} (E : Evolve L g bal g' bal')
    {a : Fin 3} {b' : Int} {w : V} (h : Blk g bal a b' w) : Blk g' bal' a b' w := by
  obtain ⟨B, hB, hlt, hn⟩ := h
  obtain ⟨B', hB', hle⟩ := E.bal_mono a B hB
  refine ⟨B', hB', Int.lt_of_lt_of_le hlt hle, fun h' => ?_⟩
  have := E.acc_new a b' w h' hn B hB
  omega

theorem slowNoChoice_evolve {L : Fin 3} {g g' : Gh V} {bal bal' : Fin 3 → Option Int}
    (E : Evolve L g bal g' bal') {b' : Int} {w : V} (h : SlowNoChoice g bal b' w) :
    SlowNoChoice g' bal' b' w := by
  rcases h with ⟨u, hu, hp⟩ | ⟨a1, a2, ha, h1, h2⟩
  · exact Or.inl ⟨u, hu, E.le.prop _ _ hp⟩
  · exact Or.inr ⟨a1, a2, ha, blk_evolve E h1, blk_evolve E h2⟩

theorem fastNoChoice_evolve {L : Fin 3} {g g' : Gh V} {bal bal' : Fin 3 → Option Int}
    (E : Evolve L g bal g' bal') {w : V} (h : FastNoChoice g bal L w) : FastNoChoice g' bal' L w := by
  rcases h with h | ⟨B, hB, hpos, hf⟩ | ⟨u, hu⟩ | h
  · obtain ⟨v, hv, hne⟩ := h
    exact Or.inl ⟨v, E.le.cre v hv, hne⟩
  · obtain ⟨B', hB', hle⟩ := E.bal_mono L B hB
    refine Or.inr (Or.inl ⟨B', hB', Int.lt_of_lt_of_le hpos hle, fun v hv => ?_⟩)
    by_cases hv0 : g.fast v
    · exact hf v hv0
    · have := E.fast_new v hv hv0 B hB; omega
  · exact Or.inr (Or.inr (Or.inl ⟨u, E.le.prop _ _ hu⟩))
  · refine Or.inr (Or.inr (Or.inr fun a ha => ?_))
    obtain ⟨B, hB, hpos, hn⟩ := h a ha
    obtain ⟨B', hB', hle⟩ := E.bal_mono a B hB
    refine ⟨B', hB', Int.lt_of_lt_of_le hpos hle, fun h' => ?_⟩
    have := E.eq_new a h' hn B hB; omega

theorem safeAt_evolve {L : Fin 3} {g g' : Gh V} {bal bal' : Fin 3 → Option Int}
    (E : Evolve L g bal g' bal') {b : Int} {v : V} (h : SafeAt g bal L b v) : SafeAt g' bal' L b v :=
  fun b' h0 h1 w hw => ⟨slowNoChoice_evolve E (h b' h0 h1 w hw).1,
    fun h2 => fastNoChoice_evolve E ((h b' h0 h1 w hw).2 h2)⟩

theorem safeAll_evolve {L : Fin 3} {g g' : Gh V} {bal bal' : Fin 3 → Option Int}
    (E : Evolve L g bal g' bal') {b : Int} (h : SafeAll g bal L b) : SafeAll g' bal' L b :=
  fun b' h0 h1 w => ⟨slowNoChoice_evolve E (h b' h0 h1 w).1,
    fun h2 => fastNoChoice_evolve E ((h b' h0 h1 w).2 h2)⟩

/-! ## New proposals and restarts keep `AInv` -/

/-- The history with a new proposal `(b, v)`, accepted by its proposer `R`. -/
def Gh.addProp (g : Gh V) (b : Int) (v : V) (R : Fin 3) : Gh V :=
  { g with acc := fun a b' u => g.acc a b' u ∨ (a = R ∧ b' = b ∧ u = v)
           prop := fun b' u => g.prop b' u ∨ (b' = b ∧ u = v) }

/-- The history with a restart at `b`. -/
def Gh.addRst (g : Gh V) (b : Int) : Gh V := { g with rst := fun b' => g.rst b' ∨ b' = b }

theorem Gh.le_addProp (g : Gh V) (b : Int) (v : V) (R : Fin 3) : g.Le (g.addProp b v R) :=
  ⟨fun _ _ _ h => Or.inl h, fun _ _ h => Or.inl h, fun _ h => h, fun _ h => h, fun _ h => h,
   fun _ h => h⟩

theorem Gh.le_addRst (g : Gh V) (b : Int) : g.Le (g.addRst b) :=
  ⟨fun _ _ _ h => h, fun _ _ h => h, fun _ h => Or.inl h, fun _ h => h, fun _ h => h, fun _ h => h⟩

/-- A proposal `(b, v)` by `R`, whose ballot is `b`, safe at `b`, the first at `b` (and, at ballot
0, before any fast commit): `AInv` holds of the extended history; the extension is an evolution. -/
theorem ainv_addProp {g : Gh V} {bal : Fin 3 → Option Int} {L R : Fin 3} {b : Int} {v : V}
    (I : AInv g bal L) (hfresh : ∀ u, ¬ g.prop b u) (hb : 0 ≤ b) (hR : bal R = some b)
    (hsafe : SafeAt g bal L b v) (hfast : b = 0 → ∀ u, ¬ g.fast u) :
    AInv (g.addProp b v R) bal L ∧ Evolve L g bal (g.addProp b v R) bal := by
  have fnp : ∀ u, g.fast u → ∀ w, ¬ (g.addProp b v R).prop 0 w := by
    intro u hu w hw
    rcases hw with hw | ⟨rfl, rfl⟩
    · exact I.fast_noprop u hu w hw
    · exact hfast rfl u hu
  have E : Evolve L g bal (g.addProp b v R) bal :=
    { le := g.le_addProp b v R
      bal_mono := fun _ B h => ⟨B, h, Int.le_refl B⟩
      acc_new := by
        intro a b' w h hn B hB
        rcases h with h | ⟨rfl, rfl, rfl⟩
        · exact absurd h hn
        · rw [hR] at hB; cases hB; exact Int.le_refl _
      eq_new := fun _ h hn => absurd h hn
      fast_new := fun _ h hn => absurd h hn
      fast_cre := I.fast_cre
      fast_eq := I.fast_eq
      fast_noprop := fnp }
  refine ⟨{ prop_uniq := ?_, acc_prop := ?_, prop_nonneg := ?_, prop_safe := ?_, rst_safe := ?_,
            cre_uniq := I.cre_uniq, fast_cre := I.fast_cre, fast_eq := I.fast_eq,
            fast_noprop := fnp }, E⟩
  · intro b' u w hu hw
    rcases hu with hu | ⟨rfl, rfl⟩ <;> rcases hw with hw | ⟨h1, rfl⟩
    · exact I.prop_uniq _ _ _ hu hw
    · subst h1; exact absurd hu (hfresh u)
    · exact absurd hw (hfresh w)
    · rfl
  · intro a b' u h
    rcases h with h | ⟨_, rfl, rfl⟩
    · exact Or.inl (I.acc_prop _ _ _ h)
    · exact Or.inr ⟨rfl, rfl⟩
  · intro b' u h
    rcases h with h | ⟨rfl, _⟩
    · exact I.prop_nonneg _ _ h
    · exact hb
  · intro b' u h
    rcases h with h | ⟨rfl, rfl⟩
    · exact safeAt_evolve E (I.prop_safe _ _ h)
    · exact safeAt_evolve E hsafe
  · intro b' h
    exact safeAll_evolve E (I.rst_safe _ h)

/-- A restart at `b`, safe at `b`: `AInv` holds of the extended history. -/
theorem ainv_addRst {g : Gh V} {bal : Fin 3 → Option Int} {L : Fin 3} {b : Int}
    (I : AInv g bal L) (hsafe : SafeAll g bal L b) :
    AInv (g.addRst b) bal L ∧ Evolve L g bal (g.addRst b) bal := by
  have E : Evolve L g bal (g.addRst b) bal :=
    { le := g.le_addRst b
      bal_mono := fun _ B h => ⟨B, h, Int.le_refl B⟩
      acc_new := fun _ _ _ h hn => absurd h hn
      eq_new := fun _ h hn => absurd h hn
      fast_new := fun _ h hn => absurd h hn
      fast_cre := I.fast_cre
      fast_eq := I.fast_eq
      fast_noprop := I.fast_noprop }
  refine ⟨{ prop_uniq := I.prop_uniq, acc_prop := I.acc_prop, prop_nonneg := I.prop_nonneg,
            prop_safe := fun b' u h => safeAt_evolve E (I.prop_safe b' u h),
            rst_safe := ?_, cre_uniq := I.cre_uniq, fast_cre := I.fast_cre, fast_eq := I.fast_eq,
            fast_noprop := I.fast_noprop }, E⟩
  intro b' h
  rcases h with h | rfl
  · exact safeAll_evolve E (I.rst_safe _ h)
  · exact safeAll_evolve E hsafe

end Perennial.gryff.pureA
