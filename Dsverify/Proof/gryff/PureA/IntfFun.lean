/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureA/IntfFun.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit AI, internal: the conflict-table functions of `epaxosrmwhandler.go` as the interference
invariant needs them.
* `updAttr_facts`: `updateAttributes` only raises deps (pointwise, signed), keeps their length,
  and (with commands) raises every row it does not skip to at least the table's entry;
* `merge_facts`: `mergeAttributes` only raises the first deps, and raises every row but the
  merging replica's own to at least the second deps' entry;
* `uc_facts`: `updateConflicts` only raises the table (`ConfLe`), and (with commands) its row
  `replica` reaches the instance; it keeps the store.
Loop lemmas: `forIn_opt_rel`, `forIn_id_rel` (a body that always yields, moves along a preorder,
and establishes a stable property at one element).
-/
module

public import Dsverify.Proof.gryff.PureA.IntfInv

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pureA.AI

open Perennial Perennial.gryff.model Perennial.gryff.pure Perennial.gryff.kahn Perennial.gryff.pureA

theorem setAt_at_same {d : Deps} {k : Nat} {x : w32} (h : k < d.length) : (d.setAt k x).at k = x := by
  simp [Deps.setAt, Deps.at, List.getD, h]

theorem setAt_at_ne {d : Deps} {k k' : Nat} {x : w32} (h : k' ≠ k) : (d.setAt k x).at k' = d.at k' := by
  simp [Deps.setAt, Deps.at, List.getD, Ne.symm h]

theorem setAt_len {d : Deps} {k : Nat} {x : w32} : (d.setAt k x).length = d.length := by
  simp [Deps.setAt]

/-- Raising entry `k` to `x > d[k]`. -/
theorem dle_setAt {d : Deps} {k : Nat} {x : w32} (h : sint.Z (d.at k) < sint.Z x) :
    DLe d (d.setAt k x) := by
  intro k'
  by_cases e : k' = k
  · subst e
    by_cases hl : k' < d.length
    · rw [setAt_at_same hl]; omega
    · have : d.setAt k' x = d := by simp [Deps.setAt, List.set_eq_of_length_le (Nat.le_of_not_lt hl)]
      rw [this]; exact Int.le_refl _
  · rw [setAt_at_ne e]; exact Int.le_refl _


/-- A loop whose body always yields, keeps `P`, moves along a preorder `Rel` keeping `Q`, and
establishes `Q` at the element `x`. -/
theorem forIn_opt_rel {α β : Type} (l : List α) (b : β) (f : α → β → Option (ForInStep β))
    (P Q : β → Prop) (Rel : β → β → Prop) (hrefl : ∀ b, Rel b b)
    (htrans : ∀ b1 b2 b3, Rel b1 b2 → Rel b2 b3 → Rel b1 b3)
    (hQQ : ∀ b b', Q b → Rel b b' → Q b') (x : α) (hP0 : P b)
    (hS : ∀ a b st, P b → f a b = some st → ∃ b', st = .yield b' ∧ P b' ∧ Rel b b' ∧ (a = x → Q b')) :
    ∀ r, forIn l b f = some r → P r ∧ Rel b r ∧ (x ∈ l → Q r) := by
  induction l generalizing b with
  | nil => intro r h; cases h; exact ⟨hP0, hrefl _, fun h => by cases h⟩
  | cons a l ih =>
    intro r h
    rw [List.forIn_cons] at h
    cases hfa : f a b with
    | none => rw [hfa] at h; cases h
    | some st =>
      obtain ⟨b', rfl, hP', hR', hQ'⟩ := hS a b _ hP0 hfa
      rw [hfa] at h
      obtain ⟨k1, k2, k3⟩ := ih b' hP' r h
      refine ⟨k1, htrans _ _ _ hR' k2, fun hx => ?_⟩
      rcases List.mem_cons.1 hx with rfl | hx'
      · exact hQQ _ _ (hQ' rfl) k2
      · exact k3 hx'

theorem raise_case {s : RState} {a : Nat} {hi0 sq : w32} {d : Deps} {ch : Bool} {P : Prop}
    (hb : 3 ≤ d.length) (hc0 : s.confAt a = some hi0) (hgt : sgt hi0 (d.at a) = true) :
    ∃ b' : w32 × Deps × Bool, ForInStep.yield (sq, d.setAt a hi0, ch) = ForInStep.yield b' ∧
      3 ≤ b'.2.1.length ∧ (DLe d b'.2.1 ∧ b'.2.1.length = d.length) ∧
      (P → a < 3 → ∀ hi, s.confAt a = some hi → sint.Z hi ≤ sint.Z (b'.2.1.at a)) := by
  simp only [sgt, slt, decide_eq_true_eq] at hgt
  refine ⟨_, rfl, by rw [setAt_len]; exact hb, ⟨dle_setAt hgt, setAt_len⟩, fun _ ha hi hh => ?_⟩
  rw [hc0] at hh; cases hh
  rw [setAt_at_same (by omega)]; exact Int.le_refl _

theorem updAttr_facts {s : RState} {cmds : List Cmd} {seq0 : w32} {deps0 : Deps} {replica : w32}
    {r : w32 × Deps × Bool} (h : updateAttributes s cmds seq0 deps0 replica = some r)
    (hl : 3 ≤ deps0.length) :
    DLe deps0 r.2.1 ∧ r.2.1.length = deps0.length ∧
    (cmds ≠ [] → ∀ k, k < 3 → ¬ (s.id ≠ replica ∧ BitVec.ofNat 32 k = replica) →
      ∀ hi, s.confAt k = some hi → sint.Z hi ≤ sint.Z (r.2.1.at k)) := by
  unfold updateAttributes at h
  rw [obind_some_iff] at h
  obtain ⟨st1, h1, h2⟩ := h
  rw [obind_some_iff] at h2
  obtain ⟨st2, -, h4⟩ := h2
  simp only [opure_some_iff] at h4
  subst h4
  have res : ∀ x : Nat, 3 ≤ st1.2.1.length ∧
      (DLe deps0 st1.2.1 ∧ st1.2.1.length = deps0.length) ∧
      (x ∈ [0, 1, 2] → x < 3 → ¬ (s.id ≠ replica ∧ BitVec.ofNat 32 x = replica) → cmds ≠ [] →
        ∀ hi, s.confAt x = some hi → sint.Z hi ≤ sint.Z (st1.2.1.at x)) := by
    intro x
    refine forIn_opt_rel _ _ _
      (fun b : w32 × Deps × Bool => 3 ≤ b.2.1.length)
      (fun b : w32 × Deps × Bool => x < 3 → ¬ (s.id ≠ replica ∧ BitVec.ofNat 32 x = replica) → cmds ≠ [] →
        ∀ hi, s.confAt x = some hi → sint.Z hi ≤ sint.Z (b.2.1.at x))
      (fun b b' : w32 × Deps × Bool => DLe b.2.1 b'.2.1 ∧ b'.2.1.length = b.2.1.length)
      (fun b => ⟨DLe.refl _, rfl⟩) (fun _ _ _ h1 h2 => ⟨h1.1.trans h2.1, h2.2.trans h1.2⟩)
      (fun b b' hq hr h3 hn hc hi hh => Int.le_trans (hq h3 hn hc hi hh) (hr.1 x)) x hl ?_ _ h1
    intro a b st hb hf
    simp only at hf
    split at hf
    · rename_i hsk
      rw [opure_some_iff] at hf; subst hf
      exact ⟨b, rfl, hb, ⟨DLe.refl _, rfl⟩, fun e _ hn => absurd (e ▸ hsk) hn⟩
    rw [obind_some_iff] at hf
    obtain ⟨st3, h3, h4⟩ := hf
    rw [opure_some_iff] at h4; subst h4
    obtain ⟨i1, i2, i3⟩ := forIn_opt_rel _ _ _
      (fun b : w32 × Deps × Bool => 3 ≤ b.2.1.length)
      (fun b : w32 × Deps × Bool => a < 3 → ∀ hi, s.confAt a = some hi → sint.Z hi ≤ sint.Z (b.2.1.at a))
      (fun b b' : w32 × Deps × Bool => DLe b.2.1 b'.2.1 ∧ b'.2.1.length = b.2.1.length)
      (fun b => ⟨DLe.refl _, rfl⟩) (fun _ _ _ h1 h2 => ⟨h1.1.trans h2.1, h2.2.trans h1.2⟩)
      (fun b b' hq hr h3 hi hh => Int.le_trans (hq h3 hi hh) (hr.1 a)) (cmds.headD default) hb (by
        intro c b st hb hf
        try simp only at hf
        opeel hf
        all_goals subst hf
        · rename_i hi0 hc0 hgt _ _ _ _
          exact raise_case hb hc0 hgt
        · rename_i hi0 hc0 hgt _ _ _ _
          exact raise_case hb hc0 hgt
        · rename_i hi0 hc0 hgt
          refine ⟨_, rfl, hb, ⟨DLe.refl _, rfl⟩, fun _ _ hi hh => ?_⟩
          rw [hc0] at hh; cases hh
          simp only [sgt, slt, decide_eq_true_eq] at hgt
          dsimp only
          omega
        · rename_i hc0
          refine ⟨_, rfl, hb, ⟨DLe.refl _, rfl⟩, fun _ _ hi hh => ?_⟩
          rw [hc0] at hh; cases hh) _ h3
    refine ⟨_, rfl, i1, i2, fun e hlt _ hc => ?_⟩
    subst e
    obtain ⟨c0, rest, rfl⟩ := List.exists_cons_of_ne_nil hc
    exact i3 (by simp) hlt
  refine ⟨(res 0).2.1.1, (res 0).2.1.2, fun hc k hk hsk hi hh => ?_⟩
  have hm : k ∈ [0, 1, 2] := by
    rcases k with _ | _ | _ | k
    · simp
    · simp
    · simp
    · omega
  exact (res k).2.2 hm hk hsk hc hi hh

theorem forIn_id_rel {α β : Type} (l : List α) (b : β) (f : α → β → Id (ForInStep β))
    (P Q : β → Prop) (Rel : β → β → Prop) (hrefl : ∀ b, Rel b b)
    (htrans : ∀ b1 b2 b3, Rel b1 b2 → Rel b2 b3 → Rel b1 b3)
    (hQQ : ∀ b b', Q b → Rel b b' → Q b') (x : α) (hP0 : P b)
    (hS : ∀ a b, P b → ∃ b', (f a b).run = .yield b' ∧ P b' ∧ Rel b b' ∧ (a = x → Q b')) :
    P (forIn l b f).run ∧ Rel b (forIn l b f).run ∧ (x ∈ l → Q (forIn l b f).run) := by
  induction l generalizing b with
  | nil => exact ⟨hP0, hrefl _, fun h => by cases h⟩
  | cons a l ih =>
    rw [List.forIn_cons]
    obtain ⟨b', hb', hP', hR', hQ'⟩ := hS a b hP0
    have e : (f a b) = ForInStep.yield b' := hb'
    rw [e]
    obtain ⟨k1, k2, k3⟩ := ih b' hP'
    refine ⟨k1, htrans _ _ _ hR' k2, fun hx => ?_⟩
    rcases List.mem_cons.1 hx with rfl | hx'
    · exact hQQ _ _ (hQ' rfl) k2
    · exact k3 hx'

theorem merge_loop (s : RState) (deps2 : Deps) (B : Bool × Deps)
    (F : Nat → Bool × Deps → Id (ForInStep (Bool × Deps))) (hl : 3 ≤ B.2.length)
    (hF : ∀ a b, 3 ≤ b.2.length → ∃ b', (F a b).run = .yield b' ∧ 3 ≤ b'.2.length ∧
      (DLe b.2 b'.2 ∧ b'.2.length = b.2.length) ∧
      (a < 3 → BitVec.ofNat 32 a ≠ s.id → sint.Z (deps2.at a) ≤ sint.Z (b'.2.at a))) :
    DLe B.2 (forIn [0, 1, 2] B F).run.2 ∧ (forIn [0, 1, 2] B F).run.2.length = B.2.length ∧
      ∀ k, k < 3 → BitVec.ofNat 32 k ≠ s.id →
        sint.Z (deps2.at k) ≤ sint.Z ((forIn [0, 1, 2] B F).run.2.at k) := by
  have res : ∀ x : Nat, 3 ≤ (forIn [0, 1, 2] B F).run.2.length ∧
      (DLe B.2 (forIn [0, 1, 2] B F).run.2 ∧ (forIn [0, 1, 2] B F).run.2.length = B.2.length) ∧
      (x ∈ [0, 1, 2] → x < 3 → BitVec.ofNat 32 x ≠ s.id →
        sint.Z (deps2.at x) ≤ sint.Z ((forIn [0, 1, 2] B F).run.2.at x)) := fun x =>
    forIn_id_rel _ _ _ (fun b : Bool × Deps => 3 ≤ b.2.length)
      (fun b : Bool × Deps => x < 3 → BitVec.ofNat 32 x ≠ s.id → sint.Z (deps2.at x) ≤ sint.Z (b.2.at x))
      (fun b b' : Bool × Deps => DLe b.2 b'.2 ∧ b'.2.length = b.2.length)
      (fun b => ⟨DLe.refl _, rfl⟩) (fun _ _ _ h1 h2 => ⟨h1.1.trans h2.1, h2.2.trans h1.2⟩)
      (fun b b' hq hr h3 hn => Int.le_trans (hq h3 hn) (hr.1 x)) x hl
      (fun a b hb => by
        obtain ⟨b', e, k1, k2, k3⟩ := hF a b hb
        exact ⟨b', e, k1, k2, fun ea => ea ▸ k3⟩)
  refine ⟨(res 0).2.1.1, (res 0).2.1.2, fun k hk hn => ?_⟩
  have hm : k ∈ [0, 1, 2] := by
    rcases k with _ | _ | _ | k
    · simp
    · simp
    · simp
    · omega
  exact (res k).2.2 hm hk hn

theorem merge_facts {s : RState} {seq1 seq2 : w32} {deps1 deps2 : Deps} (hl : 3 ≤ deps1.length) :
    DLe deps1 (mergeAttributes s seq1 deps1 seq2 deps2).2.1 ∧
    (mergeAttributes s seq1 deps1 seq2 deps2).2.1.length = deps1.length ∧
    ∀ k, k < 3 → BitVec.ofNat 32 k ≠ s.id →
      sint.Z (deps2.at k) ≤ sint.Z ((mergeAttributes s seq1 deps1 seq2 deps2).2.1.at k) := by
  unfold mergeAttributes
  dsimp only
  have body : ∀ (a : Nat) (b : Bool × Deps), 3 ≤ b.2.length → ∃ b' : Bool × Deps,
      (if BitVec.ofNat 32 a = s.id then pure (ForInStep.yield (b.fst, b.snd))
        else if b.snd.at a ≠ deps2.at a then
          if sgt (deps2.at a) (b.snd.at a) = true then
            pure (ForInStep.yield (false, b.snd.setAt a (deps2.at a)))
          else pure (ForInStep.yield (false, b.snd))
        else pure (ForInStep.yield (b.fst, b.snd)) : Id (ForInStep (Bool × Deps))).run = .yield b' ∧
      3 ≤ b'.2.length ∧ (DLe b.2 b'.2 ∧ b'.2.length = b.2.length) ∧
      (a < 3 → BitVec.ofNat 32 a ≠ s.id → sint.Z (deps2.at a) ≤ sint.Z (b'.2.at a)) := by
    intro a b hb
    split
    · rename_i he
      exact ⟨_, rfl, hb, ⟨DLe.refl _, rfl⟩, fun _ hn => absurd he hn⟩
    split
    · rename_i hne
      split
      · rename_i hgt
        simp only [sgt, slt, decide_eq_true_eq] at hgt
        refine ⟨_, rfl, by dsimp only; rw [setAt_len]; exact hb, ⟨dle_setAt hgt, setAt_len⟩,
          fun ha _ => ?_⟩
        dsimp only; rw [setAt_at_same (by omega)]; exact Int.le_refl _
      · rename_i hgt
        simp only [sgt, slt, decide_eq_true_eq] at hgt
        exact ⟨_, rfl, hb, ⟨DLe.refl _, rfl⟩, fun _ _ => by dsimp only; omega⟩
    · rename_i heq
      have e : b.snd.at a = deps2.at a := Classical.not_not.1 heq
      exact ⟨_, rfl, hb, ⟨DLe.refl _, rfl⟩, fun _ _ => by dsimp only; rw [e]; exact Int.le_refl _⟩
  split
  · split
    · simp only [Id.run_bind, Id.run_pure]
      exact merge_loop s deps2 (_, deps1) _ hl body
    · simp only [Id.run_bind, Id.run_pure]
      exact merge_loop s deps2 (_, deps1) _ hl body
  · simp only [Id.run_bind, Id.run_pure]
    exact merge_loop s deps2 (_, deps1) _ hl body

/-- The conflict table only grows. -/
def ConfLe (s s' : RState) : Prop :=
  s'.conf.length = s.conf.length ∧
    ∀ k hi, s.confAt k = some hi → ∃ hi', s'.confAt k = some hi' ∧ sint.Z hi ≤ sint.Z hi'

theorem ConfLe.refl (s : RState) : ConfLe s s := ⟨rfl, fun _ hi h => ⟨hi, h, Int.le_refl _⟩⟩
theorem ConfLe.trans {s1 s2 s3 : RState} (h1 : ConfLe s1 s2) (h2 : ConfLe s2 s3) : ConfLe s1 s3 :=
  ⟨h2.1.trans h1.1, fun k hi h => by
    obtain ⟨h', e1, l1⟩ := h1.2 k hi h
    obtain ⟨h'', e2, l2⟩ := h2.2 k h' e1
    exact ⟨h'', e2, Int.le_trans l1 l2⟩⟩

theorem confAt_set_same {l : List (Option w32)} {k : Nat} {x : Option w32} (h : k < l.length) :
    (l.set k x).getD k none = x := by
  simp [List.getD, h]

theorem confAt_set_ne {l : List (Option w32)} {k k' : Nat} {x : Option w32} (h : k' ≠ k) :
    (l.set k x).getD k' none = l.getD k' none := by
  simp [List.getD, Ne.symm h]

theorem uc_loop (s : RState) (cmds : List Cmd) (q j : w32) (F : Cmd → RState → Id (ForInStep RState))
    (hF : ∀ a t, ∃ t', (F a t).run = .yield t' ∧ (ConfLe t t' ∧ t'.tag = t.tag) ∧
      (q.toNat < s.conf.length → t.conf.length = s.conf.length →
        ∃ hi, t'.confAt q.toNat = some hi ∧ sint.Z j ≤ sint.Z hi)) :
    ConfLe s (forIn cmds s F).run ∧
    (cmds ≠ [] → q.toNat < s.conf.length →
      ∃ hi, (forIn cmds s F).run.confAt q.toNat = some hi ∧ sint.Z j ≤ sint.Z hi) ∧
    (forIn cmds s F).run.tag = s.tag := by
  have res := forIn_id_rel cmds s F (fun t => t.conf.length = s.conf.length)
    (fun t : RState => q.toNat < s.conf.length →
      ∃ hi, t.confAt q.toNat = some hi ∧ sint.Z j ≤ sint.Z hi)
    (fun t t' : RState => ConfLe t t' ∧ t'.tag = t.tag) (fun t => ⟨ConfLe.refl t, rfl⟩)
    (fun _ _ _ h1 h2 => ⟨h1.1.trans h2.1, h2.2.trans h1.2⟩)
    (fun t t' hq hr hl => by
      obtain ⟨hi, e, l⟩ := hq hl
      obtain ⟨hi', e', l'⟩ := hr.1.2 _ _ e
      exact ⟨hi', e', Int.le_trans l l'⟩) (cmds.headD default) rfl
    (fun a t ht => by
      obtain ⟨t', e, k1, k2⟩ := hF a t
      exact ⟨t', e, k1.1.1.trans ht, k1, fun _ hl => k2 hl ht⟩)
  refine ⟨res.2.1.1, fun hc hl => ?_, res.2.1.2⟩
  obtain ⟨c0, rest, rfl⟩ := List.exists_cons_of_ne_nil hc
  exact res.2.2 (by simp) hl

theorem uc_facts (s : RState) (cmds : List Cmd) (q j sq : w32) :
    ConfLe s (updateConflicts s cmds q j sq) ∧
    (cmds ≠ [] → q.toNat < s.conf.length →
      ∃ hi, (updateConflicts s cmds q j sq).confAt q.toNat = some hi ∧ sint.Z j ≤ sint.Z hi) ∧
    (updateConflicts s cmds q j sq).tag = s.tag := by
  unfold updateConflicts
  simp only [Id.run_bind, Id.run_pure]
  refine uc_loop s cmds q j _ (fun a t => ⟨_, rfl, ⟨⟨by simp, fun k hi h => ?_⟩, rfl⟩, fun hl ht => ?_⟩)
  · unfold RState.confAt at h ⊢
    dsimp only
    by_cases e : k = q.toNat
    · subst e
      by_cases hl : q.toNat < t.conf.length
      · rw [confAt_set_same hl]
        refine ⟨_, rfl, ?_⟩
        rw [h]
        dsimp only; split
        · rename_i hs; simp only [slt, decide_eq_true_eq] at hs; omega
        · exact Int.le_refl _
      · rw [List.set_eq_of_length_le (Nat.le_of_not_lt hl)]
        exact ⟨hi, h, Int.le_refl _⟩
    · rw [confAt_set_ne e]; exact ⟨hi, h, Int.le_refl _⟩
  · unfold RState.confAt
    dsimp only
    rw [confAt_set_same (by omega)]
    refine ⟨_, rfl, ?_⟩
    split
    · split
      · exact Int.le_refl _
      · rename_i hs; simp only [slt, decide_eq_true_eq] at hs; omega
    · exact Int.le_refl _

end Perennial.gryff.pureA.AI
