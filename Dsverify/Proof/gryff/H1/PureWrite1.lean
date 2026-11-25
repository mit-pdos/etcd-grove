/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H1/PureWrite1.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit H1b: the coordinator's `stepWrite1Reply` (WIP: its inversion).
-/
module

public import Dsverify.Proof.gryff.H1.PureWrite

@[expose] public section

namespace Perennial.gryff.replica2

open Perennial.gryff.model

/-- The write op after a Write1 reply carrying `vt` (counters and max value-tag). -/
def w1Upd (w : WriteOp) (vt : ValTag) : WriteOp :=
  if vt.t.gt w.maxValTag.t then
    { w with numWrite1Replies := w.numWrite1Replies + 1, maxValTag := vt,
             numWrite1Applies := if sge vt.v 0 then 1 else 0 }
  else if vt.t.eqT w.maxValTag.t && (vt.v == w.maxValTag.v && sge w.maxValTag.v 0) then
    { w with numWrite1Replies := w.numWrite1Replies + 1,
             numWrite1Applies := w.numWrite1Applies + 1 }
  else { w with numWrite1Replies := w.numWrite1Replies + 1 }

/-- The write op with its write tag set (the slow path). -/
def w1Tag (w : WriteOp) (cid : w32) : model.Tag := ⟨w.maxValTag.t.ts + 1, cid, 0⟩

/-- The slow path's write op (tag set, Write2s sent). -/
def w1Slow (w : WriteOp) (cid : w32) : WriteOp :=
  { w with writeTag := some (w1Tag w cid), sentWrite2Round := true }

/-- `stepWrite1Reply` after the op's update. -/
def w1Tail (s : RState) (m : Write1ReplyM) (w : WriteOp) : StepRes :=
  if sge w.numWrite1Replies (NHALF + 1) then
    if sge w.numWrite1Applies (NHALF + 1) then
      match shortCircuit s w.n w.maxValTag true with
      | some (s2, outs2) =>
        .ok ({ s2 with wops := s2.wops.del (shiftInts m.requestId m.clientId),
                       ongoingReqs := s2.ongoingReqs.del w.n },
             outs2 ++ [.ext (.writeReply w.clientId w.requestId 1)])
      | none => .error .dead
    else if !w.sentWrite2Round then
      match ([0, 1, 2] : List w32).mapM (fun q => sendTo q (.write2
          { requestId := w.requestId, clientId := w.clientId, k := 0,
            vt := ⟨w.writeValue, w1Tag w m.clientId⟩, replicaId := s.id })) with
      | some outs => .ok ({ s with wops := s.wops.put (shiftInts m.requestId m.clientId) (w1Slow w m.clientId) }, outs)
      | none => .error .dead
    else .ok ({ s with wops := s.wops.put (shiftInts m.requestId m.clientId) w }, [])
  else .ok ({ s with wops := s.wops.put (shiftInts m.requestId m.clientId) w }, [])

theorem stepWrite1Reply_eq (s : RState) (m : Write1ReplyM) :
    stepWrite1Reply s m = match s.wops.get? (shiftInts m.requestId m.clientId) with
      | none => .ok (s, [])
      | some w => w1Tail s m (w1Upd w m.vt) := by
  unfold stepWrite1Reply
  dsimp only
  cases hg : s.wops.get? (shiftInts m.requestId m.clientId) with
  | none => rfl
  | some w =>
    dsimp only
    simp only [w1Upd, w1Tail, w1Slow, w1Tag]
    by_cases h1 : m.vt.t.gt w.maxValTag.t = true
    · simp only [h1, ↓reduceIte]
      repeat' (first | rfl | split | (simp_all; rfl) | simp_all)
    · simp only [h1, Bool.false_eq_true, ↓reduceIte]
      by_cases h2 : m.vt.t.eqT w.maxValTag.t = true
      · by_cases h3 : (m.vt.v == w.maxValTag.v && sge w.maxValTag.v 0) = true
        · simp only [h2, h3, Bool.and_self, ↓reduceIte, Bool.true_and]
          repeat' (first | rfl | split | (simp_all; rfl) | simp_all)
        · simp only [h2, h3, Bool.true_and, Bool.false_eq_true, ↓reduceIte]
          repeat' (first | rfl | split | (simp_all; rfl) | simp_all)
      · simp only [h2, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        repeat' (first | rfl | split | (simp_all; rfl) | simp_all)

theorem w1Tail_inv (s s' : RState) (m : Write1ReplyM) (W : WriteOp) (outs : List Out)
    (h : w1Tail s m W = .ok (s', outs)) :
    (sge W.numWrite1Replies (NHALF + 1) = true ∧ sge W.numWrite1Applies (NHALF + 1) = true ∧
        ∃ s2 outs2, shortCircuit s W.n W.maxValTag true = some (s2, outs2) ∧
        s' = { s2 with wops := s2.wops.del (shiftInts m.requestId m.clientId),
                       ongoingReqs := s2.ongoingReqs.del W.n } ∧
        outs = outs2 ++ [.ext (.writeReply W.clientId W.requestId 1)]) ∨
    (sge W.numWrite1Replies (NHALF + 1) = true ∧ sge W.numWrite1Applies (NHALF + 1) = false ∧
        W.sentWrite2Round = false ∧
        ([0, 1, 2] : List w32).mapM (fun q => sendTo q (.write2
          { requestId := W.requestId, clientId := W.clientId, k := 0,
            vt := ⟨W.writeValue, w1Tag W m.clientId⟩, replicaId := s.id })) = some outs ∧
        s' = { s with wops := s.wops.put (shiftInts m.requestId m.clientId) (w1Slow W m.clientId) }) ∨
    ((sge W.numWrite1Replies (NHALF + 1) = false ∨
        (sge W.numWrite1Applies (NHALF + 1) = false ∧ W.sentWrite2Round = true)) ∧
        s' = { s with wops := s.wops.put (shiftInts m.requestId m.clientId) W } ∧ outs = []) := by
  unfold w1Tail at h
  split at h
  · rename_i hq1
    split at h
    · rename_i hq2
      split at h
      · rename_i _ s2 outs2 hsc
        cases h
        exact Or.inl ⟨hq1, hq2, s2, outs2, hsc, rfl, rfl⟩
      · cases h
    · rename_i hq2
      split at h
      · rename_i hs
        split at h
        · rename_i _ outs' hm
          cases h
          refine Or.inr (Or.inl ⟨hq1, by simpa using hq2, by simpa using hs, hm, rfl⟩)
        · cases h
      · rename_i hs
        cases h
        exact Or.inr (Or.inr ⟨Or.inr ⟨by simpa using hq2, by simpa using hs⟩, rfl, rfl⟩)
  · rename_i hq1
    cases h
    exact Or.inr (Or.inr ⟨Or.inl (by simpa using hq1), rfl, rfl⟩)

theorem stepWrite1Reply_inv (k : Fin 3) (s s' : RState) (m : Write1ReplyM) (outs : List Out)
    (h : stepR k s (.msg (.write1Reply m)) = .ok (s', outs)) :
    (s.wops.get? (shiftInts m.requestId m.clientId) = none ∧ s' = s ∧ outs = []) ∨
    ∃ w, s.wops.get? (shiftInts m.requestId m.clientId) = some w ∧
      w1Tail s m (w1Upd w m.vt) = .ok (s', outs) := by
  simp only [stepR] at h
  rw [stepWrite1Reply_eq] at h
  cases hg : s.wops.get? (shiftInts m.requestId m.clientId) with
  | none =>
    rw [hg] at h; cases h; exact Or.inl ⟨rfl, rfl, rfl⟩
  | some w =>
    rw [hg] at h; exact Or.inr ⟨w, rfl, h⟩

end Perennial.gryff.replica2
