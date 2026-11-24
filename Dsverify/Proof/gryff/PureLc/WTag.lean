/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureLc/WTag.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit L-c: a write's chosen tag has `rmwc = 0` (`write_place_rmwc`): every write record's
`WriteTag` is `(ts, cid, 0)` (set only by the `Write1Reply` handler).
-/
module

public import Dsverify.Proof.gryff.PureLc.Chain

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure

open model kahn proto

/-- Every write record's `WriteTag` has `rmwc = 0`. -/
def WTag0 (s : RState) : Prop :=
  ∀ K w, s.wops.get? K = some w → ∀ t, w.writeTag = some t → t.rmwc = 0

theorem wtag0_step {r : Fin 3} {s s' : RState} {e : Ev} {o : List Out}
    (h : stepR r s e = .ok (s', o)) (hs : WTag0 s) : WTag0 s' := by
  have of_eq : s'.wops = s.wops → WTag0 s' := fun he => by unfold WTag0; rw [he]; exact hs
  cases e with
  | read => exact of_eq (stepClientRead_spec h).2.2.2.2.1
  | rmw => exact of_eq (stepClientRMW_spec h).2.2.2.2.1
  | write =>
    obtain ⟨-, -, -, -, ⟨w, -, hwt, hw⟩, -⟩ := stepClientWrite_spec h
    intro K w' hK t ht
    rw [hw, AMap.get?_put] at hK
    split at hK
    · cases hK; rw [hwt] at ht; cases ht
    · exact hs K w' hK t ht
  | msg m =>
    cases m with
    | write1 => exact of_eq (stepWrite1_spec h).1.1
    | write1Reply m =>
      obtain ⟨-, -, -, h1, -, h3⟩ := stepWrite1Reply_spec h
      intro K w' hK t ht
      by_cases hk : K = shiftInts m.requestId m.clientId
      · subst hk
        obtain ⟨w, hw, -, -, hor⟩ := h3 w' hK
        rcases hor with e | ⟨-, c, e⟩
        · rw [e] at ht; exact hs _ w hw t ht
        · rw [e] at ht; cases ht; rfl
      · rw [h1 K hk] at hK; exact hs K w' hK t ht
    | write2Reply m =>
      obtain ⟨-, -, -, h1, -, h3⟩ := stepWrite2Reply_spec h
      intro K w' hK t ht
      by_cases hk : K = shiftInts m.requestId m.clientId
      · subst hk
        obtain ⟨w, hw, -, -, e⟩ := h3 w' hK
        rw [e] at ht; exact hs _ w hw t ht
      · rw [h1 K hk] at hK; exact hs K w' hK t ht
    | _ => exact of_eq (step_fw_other h rfl).1.1
  | _ => exact of_eq (step_fw_other h rfl).1.1

/-- **A write's place has `rmwc = 0`.** -/
theorem write_place_rmwc {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) {o : Op}
    (ho : o ∈ ops l) {v : w64} (hi : o.inp = .write v) {t : model.Tag}
    (ht : place l o = some t) : t.rmwc = 0 := by
  unfold place at ht; rw [hi] at ht
  unfold writePlace firstFrom at ht
  obtain ⟨j, hj, hjt⟩ := List.exists_of_findSome?_eq_some ht
  have hjl : j < (projR l o.r).length := List.mem_range.1 (List.mem_filter.1 hj).1
  have hinv := proj_ind h o.r (fun _ s => WTag0 s) (fun K w hK => by
      simp [stOf, runP, runFrom, gNet, RState.init, AMap.get?] at hK)
    (fun _ _ _ _ _ hs ih => wtag0_step hs ih) (j + 1) (by omega)
  obtain ⟨w, hw, hwt⟩ := Option.bind_eq_some_iff.1 hjt
  exact hinv _ w hw t hwt

end Perennial.gryff.pure

namespace Perennial.gryff.pure

open model kahn proto

/-- The low half of `ShiftInts(a, b)` is `b`. -/
theorem shiftInts_low {a b a' b' : w32} (h : shiftInts a b = shiftInts a' b') : b = b' := by
  unfold shiftInts at h
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  have := congrArg (fun x => x.getLsbD k) h
  simp [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_signExtend] at this
  have h1 : k < 64 := by omega
  simpa [h1, hk] using this

/-- What the `Write1Reply` handler does to `WriteTag`s: kept, or set (at the reply's key) to
`(_, cid, 0)` with the reply's client id. -/
theorem stepWrite1Reply_wt {s s' : RState} {m : Write1ReplyM} {o : List Out}
    (h : stepWrite1Reply s m = .ok (s', o)) : ∀ K w', s'.wops.get? K = some w' →
      (∃ w, s.wops.get? K = some w ∧ w'.writeTag = w.writeTag) ∨
      (K = shiftInts m.requestId m.clientId ∧ ∃ ts, w'.writeTag = some ⟨ts, m.clientId, 0⟩) := by
  intro K w' hK
  unfold stepWrite1Reply at h
  peel h
  all_goals (cases h)
  all_goals (try (have hsc := (shortCircuit_fw ‹shortCircuit _ _ _ _ = some _›).1.1))
  all_goals (by_cases hk : K = shiftInts m.requestId m.clientId)
  all_goals (first
    | (left; exact ⟨w', hK, rfl⟩)
    | (subst hk; simp [AMap.get?_del] at hK; done)
    | (simp only [AMap.get?_del, hk, if_false, hsc] at hK; exact Or.inl ⟨w', hK, rfl⟩)
    | (subst hk; simp only [AMap.get?_put, if_true, Option.some.injEq] at hK; subst hK
       first
       | (right; exact ⟨rfl, _, rfl⟩)
       | (left; refine ⟨_, ‹_›, ?_⟩; simp_all))
    | (simp only [AMap.get?_put, hk, if_false] at hK; exact Or.inl ⟨w', hK, rfl⟩)
    | skip)

/-- Every write record's `WriteTag` carries the client id of the record's key. -/
def WCid (s : RState) : Prop :=
  ∀ K w, s.wops.get? K = some w → ∀ t, w.writeTag = some t → ∃ rid, K = shiftInts rid t.cid

theorem wcid_step {r : Fin 3} {s s' : RState} {e : Ev} {o : List Out}
    (h : stepR r s e = .ok (s', o)) (hs : WCid s) : WCid s' := by
  have of_eq : s'.wops = s.wops → WCid s' := fun he => by unfold WCid; rw [he]; exact hs
  cases e with
  | read => exact of_eq (stepClientRead_spec h).2.2.2.2.1
  | rmw => exact of_eq (stepClientRMW_spec h).2.2.2.2.1
  | write =>
    obtain ⟨-, -, -, -, ⟨w, -, hwt, hw⟩, -⟩ := stepClientWrite_spec h
    intro K w' hK t ht
    rw [hw, AMap.get?_put] at hK
    split at hK
    · cases hK; rw [hwt] at ht; cases ht
    · exact hs K w' hK t ht
  | msg m =>
    cases m with
    | write1 => exact of_eq (stepWrite1_spec h).1.1
    | write1Reply m =>
      intro K w' hK t ht
      rcases stepWrite1Reply_wt h K w' hK with ⟨w, hw, e⟩ | ⟨hk, ts, e⟩
      · rw [e] at ht; exact hs K w hw t ht
      · rw [e] at ht; cases ht; exact ⟨_, hk⟩
    | write2Reply m =>
      obtain ⟨-, -, -, h1, -, h3⟩ := stepWrite2Reply_spec h
      intro K w' hK t ht
      by_cases hk : K = shiftInts m.requestId m.clientId
      · subst hk
        obtain ⟨w, hw, -, -, e⟩ := h3 w' hK
        rw [e] at ht; exact hs _ w hw t ht
      · rw [h1 K hk] at hK; exact hs K w' hK t ht
    | _ => exact of_eq (step_fw_other h rfl).1.1
  | _ => exact of_eq (step_fw_other h rfl).1.1

/-- **A write's place carries its client id.** -/
theorem write_place_cid {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) {o : Op}
    {v : w64} (hi : o.inp = .write v) {t : model.Tag} (ht : place l o = some t) : t.cid = o.cid := by
  unfold place at ht; rw [hi] at ht
  unfold writePlace firstFrom at ht
  obtain ⟨j, hj, hjt⟩ := List.exists_of_findSome?_eq_some ht
  have hjl : j < (projR l o.r).length := List.mem_range.1 (List.mem_filter.1 hj).1
  have hinv := proj_ind h o.r (fun _ s => WCid s) (fun K w hK => by
      simp [stOf, runP, runFrom, gNet, RState.init, AMap.get?] at hK)
    (fun _ _ _ _ _ hs ih => wcid_step hs ih) (j + 1) (by omega)
  obtain ⟨w, hw, hwt⟩ := Option.bind_eq_some_iff.1 hjt
  obtain ⟨rid, hK⟩ := hinv _ w hw t hwt
  exact (shiftInts_low hK).symm

end Perennial.gryff.pure
