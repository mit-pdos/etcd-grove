/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H1/PureSC.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit H1b: the model's `shortCircuit` as an explicit loop (`loopF` of the step `scF`), for the
program proof of `GryffCoordinator.ShortCircuit` (loop over the sorted `ShortReads`).
-/
module

public import Dsverify.Proof.gryff.Model.StepGryff
public import Dsverify.Proof.gryff.H1.Defs

@[expose] public section

namespace Perennial.gryff.replica2.sc

open Perennial.gryff.model (RState Out OngoingOp sge sle shiftInts)

/-- A loop over `ks` with steps `f` (`.done`: break). -/
def loopF {α σ : Type} (f : α → σ → ForInStep σ) : List α → σ → σ
  | [], st => st
  | k :: ks, st => match f k st with
    | .done st' => st'
    | .yield st' => loopF f ks st'

theorem forIn_some {α σ : Type} (f : α → σ → ForInStep σ) :
    ∀ (ks : List α) (init : σ) (body : α → σ → Option (ForInStep σ)),
      (∀ k st, body k st = some (f k st)) → forIn ks init body = some (loopF f ks init)
  | [], init, body, _ => rfl
  | k :: ks, init, body, hb => by
    rw [List.forIn_cons, hb]
    simp only [Option.bind_eq_bind, Option.bind_some, loopF]
    cases f k init with
    | done st' => rfl
    | yield st' => exact forIn_some f ks st' body hb

/-- One iteration of `ShortCircuit`'s reads loop (key `k`; value `v`). -/
def scF (n : w32) (v : w64) (fo : Bool) (k : w32) (st : RState × List Out) :
    ForInStep (RState × List Out) :=
  if (sge k n && fo) = true then .done st else
  match st.1.ongoingReqs.get? k with
  | some o =>
    match st.1.rops.get? (shiftInts o.requestId o.clientId) with
    | some _ => .yield ({ st.1 with rops := st.1.rops.del (shiftInts o.requestId o.clientId),
                                    ongoingReqs := st.1.ongoingReqs.del k },
                        st.2 ++ [.ext (.readReply o.clientId o.requestId v 1)])
    | none => .yield st
  | none => .yield st

/-- The sorted keys and the state before the loop. -/
def scKeys (op : OngoingOp) : List w32 := op.shortReads.mergeSort (fun a b => sle a b)

def scInit (s : RState) (n : w32) (op : OngoingOp) : RState :=
  { s with ongoingReqs := s.ongoingReqs.put n { op with shortReads := scKeys op } }

theorem shortCircuit_inv (s s' : RState) (n : w32) (value : model.ValTag) (fo : Bool)
    (outs : List Out) (h : model.shortCircuit s n value fo = some (s', outs)) :
    ∃ op, s.ongoingReqs.get? n = some op ∧
      loopF (scF n value.v fo) (scKeys op) (scInit s n op, []) = (s', outs) ∧
      (fo = false → ∃ x, s'.ongoingReqs.get? n = some x) := by
  unfold model.shortCircuit at h
  split at h
  · rename_i op hop
    refine ⟨op, hop, ?_⟩
    dsimp only at h
    rw [forIn_some (scF n value.v fo)] at h
    · simp only [Option.bind_eq_bind, Option.bind_some] at h
      generalize hl : loopF (scF n value.v fo) _ _ = r at h
      cases fo with
      | true =>
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
        cases h; exact ⟨hl, fun h => by cases h⟩
      | false =>
        simp only [Bool.not_false, ↓reduceIte] at h
        split at h
        · rename_i x hx
          cases h; exact ⟨hl, fun _ => ⟨x, hx⟩⟩
        · cases h
    · intro k st
      unfold scF
      by_cases hc : (sge k n && fo) = true
      · simp only [hc, ↓reduceIte]; rfl
      · simp only [hc, Bool.false_eq_true, ↓reduceIte]
        cases h1 : st.1.ongoingReqs.get? k with
        | none => rfl
        | some o =>
          dsimp only
          cases h2 : st.1.rops.get? (shiftInts o.requestId o.clientId) <;> rfl
  · cases h

/-- The replies are appended. -/
theorem scF_outs (n : w32) (v : w64) (fo : Bool) (k : w32) (st : RState × List Out) :
    (∃ st', scF n v fo k st = .done st' ∧ st' = st) ∨
    (∃ st', scF n v fo k st = .yield st' ∧ ∃ r, st'.2 = st.2 ++ r) := by
  unfold scF
  split
  · exact Or.inl ⟨_, rfl, rfl⟩
  · split
    · split
      · exact Or.inr ⟨_, rfl, _, rfl⟩
      · exact Or.inr ⟨_, rfl, [], by simp⟩
    · exact Or.inr ⟨_, rfl, [], by simp⟩

theorem loopF_prefix (n : w32) (v : w64) (fo : Bool) :
    ∀ (ks : List w32) (st : RState × List Out), ∃ r, (loopF (scF n v fo) ks st).2 = st.2 ++ r
  | [], st => ⟨[], by simp [loopF]⟩
  | k :: ks, st => by
    simp only [loopF]
    rcases scF_outs n v fo k st with ⟨st', h, rfl⟩ | ⟨st', h, r, hr⟩
    · rw [h]; exact ⟨[], by simp⟩
    · rw [h]
      obtain ⟨r', hr'⟩ := loopF_prefix n v fo ks st'
      exact ⟨r ++ r', by rw [hr', hr]; simp⟩

/-- The step only deletes entries of `ongoingReqs`. -/
theorem scF_sub (n : w32) (v : w64) (fo : Bool) (k : w32) (st : RState × List Out)
    (st' : RState × List Out) (h : scF n v fo k st = .done st' ∨ scF n v fo k st = .yield st')
    (j : w32) (x : OngoingOp) (hx : st'.1.ongoingReqs.get? j = some x) :
    st.1.ongoingReqs.get? j = some x := by
  unfold scF at h
  split at h
  · rcases h with h | h <;> cases h; exact hx
  · split at h
    · split at h
      · rcases h with h | h <;> cases h
        simp only at hx
        rw [amap_del_get] at hx
        split at hx
        · cases hx
        · exact hx
      · rcases h with h | h <;> cases h; exact hx
    · rcases h with h | h <;> cases h; exact hx

/-- The step when the loop does not break. -/
def scY (v : w64) (k : w32) (st : RState × List Out) : RState × List Out :=
  match st.1.ongoingReqs.get? k with
  | some o =>
    match st.1.rops.get? (shiftInts o.requestId o.clientId) with
    | some _ => ({ st.1 with rops := st.1.rops.del (shiftInts o.requestId o.clientId),
                             ongoingReqs := st.1.ongoingReqs.del k },
                 st.2 ++ [.ext (.readReply o.clientId o.requestId v 1)])
    | none => st
  | none => st

theorem scF_nb (n : w32) (v : w64) (fo : Bool) (k : w32) (st : RState × List Out)
    (h : (sge k n && fo) = false) : scF n v fo k st = .yield (scY v k st) := by
  unfold scF scY
  rw [if_neg (by simp [h])]
  cases h1 : st.1.ongoingReqs.get? k with
  | none => rfl
  | some o =>
    dsimp only
    cases h2 : st.1.rops.get? (shiftInts o.requestId o.clientId) <;> rfl

/-- `shortCircuit` as the loop (both directions). -/
theorem shortCircuit_eq (s : RState) (n : w32) (value : model.ValTag) (fo : Bool) :
    model.shortCircuit s n value fo =
      match s.ongoingReqs.get? n with
      | none => none
      | some op =>
        if fo = false ∧ (loopF (scF n value.v fo) (scKeys op) (scInit s n op, [])).1.ongoingReqs.get? n = none
        then none else some (loopF (scF n value.v fo) (scKeys op) (scInit s n op, [])) := by
  unfold model.shortCircuit
  cases hop : s.ongoingReqs.get? n with
  | none => rfl
  | some op =>
    dsimp only
    rw [forIn_some (scF n value.v fo)]
    · simp only [Option.bind_eq_bind, Option.bind_some, scKeys, scInit]
      cases fo with
      | true => simp
      | false =>
        simp only [Bool.not_false, ↓reduceIte, true_and]
        split
        · rename_i x hx; rw [hx]; rfl
        · rename_i hx
          rw [if_pos (Option.eq_none_iff_forall_ne_some.2 (fun y hy => hx y hy))]
          rfl
    · intro k st
      unfold scF
      by_cases hc : (sge k n && fo) = true
      · simp only [hc, ↓reduceIte]; rfl
      · simp only [hc, Bool.false_eq_true, ↓reduceIte]
        cases h1 : st.1.ongoingReqs.get? k with
        | none => rfl
        | some o =>
          dsimp only
          cases h2 : st.1.rops.get? (shiftInts o.requestId o.clientId) <;> rfl

/-- The step with another `wops`. -/
def updW (W : model.AMap 64 model.WriteOp) (st : RState × List Out) : RState × List Out :=
  ({ st.1 with wops := W }, st.2)

theorem scF_wops (n : w32) (v : w64) (fo : Bool) (k : w32) (st : RState × List Out)
    (W : model.AMap 64 model.WriteOp) :
    scF n v fo k (updW W st) = match scF n v fo k st with
      | .done x => .done (updW W x)
      | .yield x => .yield (updW W x) := by
  unfold scF updW
  by_cases hc : (sge k n && fo) = true
  · simp only [hc, ↓reduceIte]
  · simp only [hc, Bool.false_eq_true, ↓reduceIte]
    cases h1 : st.1.ongoingReqs.get? k with
    | none => rfl
    | some o =>
      dsimp only
      cases h2 : st.1.rops.get? (shiftInts o.requestId o.clientId) <;> rfl

theorem loopF_wops (n : w32) (v : w64) (fo : Bool) (W : model.AMap 64 model.WriteOp) :
    ∀ (ks : List w32) (st : RState × List Out),
      loopF (scF n v fo) ks (updW W st) = updW W (loopF (scF n v fo) ks st)
  | [], st => rfl
  | k :: ks, st => by
    simp only [loopF, scF_wops]
    cases scF n v fo k st with
    | done x => rfl
    | yield x => exact loopF_wops n v fo W ks x

/-- `shortCircuit` does not look at `wops`. -/
theorem shortCircuit_wops (s s2 : RState) (n : w32) (value : model.ValTag) (fo : Bool)
    (o : List Out) (W : model.AMap 64 model.WriteOp)
    (h : model.shortCircuit s n value fo = some (s2, o)) :
    model.shortCircuit { s with wops := W } n value fo = some ({ s2 with wops := W }, o) := by
  rw [shortCircuit_eq] at h ⊢
  simp only at h ⊢
  split at h
  · cases h
  · rename_i op hop
    have e : scInit { s with wops := W } n op = (updW W (scInit s n op, [])).1 := rfl
    have e2 : ((scInit { s with wops := W } n op, ([] : List Out))) = updW W (scInit s n op, []) := rfl
    rw [e2, loopF_wops]
    split at h
    · cases h
    · rename_i hc
      have hr := Option.some.inj h
      rw [hr] at hc ⊢
      rw [if_neg (by simpa [updW] using hc)]
      rfl

theorem loopF_inv {α σ : Type} (f : α → σ → ForInStep σ) (P : σ → Prop)
    (h : ∀ k st st', P st → (f k st = .done st' ∨ f k st = .yield st') → P st') :
    ∀ (ks : List α) (init : σ), P init → P (loopF f ks init)
  | [], init, hi => hi
  | k :: ks, init, hi => by
    simp only [loopF]
    cases hf : f k init with
    | done st' => exact h k init st' hi (Or.inl hf)
    | yield st' => exact loopF_inv f P h ks st' (h k init st' hi (Or.inr hf))

/-- `shortCircuit` changes `rops` and `ongoingReqs` only. -/
theorem shortCircuit_frame (s s2 : RState) (n : w32) (value : model.ValTag) (fo : Bool)
    (o : List Out) (h : model.shortCircuit s n value fo = some (s2, o)) :
    s2 = { s with rops := s2.rops, ongoingReqs := s2.ongoingReqs } := by
  obtain ⟨op, -, hl, -⟩ := shortCircuit_inv s s2 n value fo o h
  have := loopF_inv (scF n value.v fo)
    (fun st => st.1 = { s with rops := st.1.rops, ongoingReqs := st.1.ongoingReqs })
    (fun k st st' hst hf => by
      unfold scF at hf
      split at hf
      · rcases hf with hf | hf <;> cases hf; exact hst
      · split at hf
        · split at hf
          · rcases hf with hf | hf <;> cases hf
            simp only
            rw [hst]
          · rcases hf with hf | hf <;> cases hf; exact hst
        · rcases hf with hf | hf <;> cases hf; exact hst)
    (scKeys op) (scInit s n op, []) rfl
  rw [hl] at this
  exact this

end Perennial.gryff.replica2.sc
