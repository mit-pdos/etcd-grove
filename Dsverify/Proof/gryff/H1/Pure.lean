/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H1/Pure.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit H1: pure facts about the model's participant and coordinator steps.
-/
module

public import Dsverify.Proof.gryff.Replica2.Specs

@[expose] public section

namespace Perennial.gryff.replica2

open Perennial.gryff.model

theorem ovw_overwrite (s : RState) (v : w64) (t : model.Tag) :
    (s.overwrite v t).tag = (ovw s.storeVT v t).t ∧ (s.overwrite v t).val = (ovw s.storeVT v t).v ∧
    (s.overwrite v t).ongoing = s.ongoing := by
  unfold RState.overwrite ovw RState.storeVT
  split <;> simp_all

theorem stepWrite2_inv (s s' : RState) (m : Write2ProxiedM) (o1 : Out)
    (h : stepWrite2 s m = .ok (s', [o1])) :
    m.k = 0 ∧ s'.tag = (ovw s.storeVT m.vt.v m.vt.t).t ∧ s'.val = (ovw s.storeVT m.vt.v m.vt.t).v ∧
    s'.ongoing = s.ongoing.del m.clientId ∧
    sendTo m.replicaId (.write2Reply ⟨m.requestId, m.clientId,
      if s.tag.lt m.vt.t then 1 else 0⟩) = some o1 := by
  unfold stepWrite2 at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  by_cases hk : m.k = 0
  · simp only [hk, ne_eq, not_true_eq_false, ↓reduceIte] at h
    obtain ⟨h1, h2, h3⟩ := ovw_overwrite s m.vt.v m.vt.t
    split at h
    · rename_i o ho
      simp only [Except.ok.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hk, h1, h2, by simp [h3], ho⟩
    · cases h
  · simp only [hk, ne_eq, not_false_eq_true, ↓reduceIte] at h
    cases h

theorem stepRead2_inv (s s' : RState) (m : Read2ProxiedM) (o1 : Out)
    (h : stepRead2 s m = .ok (s', [o1])) :
    m.k = 0 ∧ s'.tag = (ovw s.storeVT m.vt.v m.vt.t).t ∧ s'.val = (ovw s.storeVT m.vt.v m.vt.t).v ∧
    s'.ongoing = s.ongoing ∧
    sendTo m.replicaId (.read2Reply ⟨m.requestId, m.clientId⟩) = some o1 := by
  unfold stepRead2 at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  by_cases hk : m.k = 0
  · simp only [hk, ne_eq, not_true_eq_false, ↓reduceIte] at h
    obtain ⟨h1, h2, h3⟩ := ovw_overwrite s m.vt.v m.vt.t
    split at h
    · rename_i o ho
      simp only [Except.ok.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hk, h1, h2, h3, ho⟩
    · cases h
  · simp only [hk, ne_eq, not_false_eq_true, ↓reduceIte] at h
    cases h


theorem stepRead1_inv (s s' : RState) (m : Read1ProxiedM) (o1 : Out)
    (h : stepRead1 s m = .ok (s', [o1])) :
    m.k = 0 ∧ (sge m.d.key 0 = true → m.d.key = 0) ∧
    s' = (if sge m.d.key 0 then s.overwrite m.d.vt.v m.d.vt.t else s).overwrite m.vt.v m.vt.t ∧
    sendTo m.replicaId (.read1Reply ⟨m.requestId, m.clientId, s'.id, s'.storeVT⟩) = some o1 := by
  unfold stepRead1 at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  by_cases hk : m.k = 0
  · simp only [hk, ne_eq, not_true_eq_false, ↓reduceIte] at h
    by_cases hd : sge m.d.key 0 = true
    · by_cases hd0 : m.d.key = 0
      · rw [if_pos hd, if_neg (by simpa using hd0)] at h
        split at h
        next o ho =>
          simp only [Except.ok.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨hk, fun _ => hd0, by rw [if_pos hd], ho⟩
        next => cases h
      · rw [if_pos hd, if_pos (by simpa using hd0)] at h
        cases h
    · rw [if_neg hd] at h
      split at h
      next o ho =>
        simp only [Except.ok.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨hk, fun h' => absurd h' hd, by rw [if_neg hd], ho⟩
      next => cases h
  · simp only [hk, ne_eq, not_false_eq_true, ↓reduceIte] at h
    cases h

theorem overwrite_id (s : RState) (v : w64) (t : model.Tag) : (s.overwrite v t).id = s.id ∧
    (s.overwrite v t).ongoing = s.ongoing := by
  unfold RState.overwrite; split <;> simp


/-- `OngoingWrites` after a fresh `Write1` (request `rid` of client `cid`). -/
def ongPut (ong : AMap 32 w32) (cid rid : w32) : AMap 32 w32 :=
  match ong.get? cid with
  | some r => if slt r rid then ong.put cid rid else ong
  | none => ong.put cid rid

theorem stepWrite1_inv (s s' : RState) (m : Write1ProxiedM) (outs : List Out)
    (h : stepWrite1 s m = .ok (s', outs)) :
    m.k = 0 ∧
    (((∃ r, s.ongoing.get? m.clientId = some r ∧ sgt r m.requestId = true) ∧ s' = s ∧ outs = []) ∨
     ((¬ ∃ r, s.ongoing.get? m.clientId = some r ∧ sgt r m.requestId = true) ∧
      (sge m.d.key 0 = true → m.d.key = 0) ∧ sgt m.forceWrite 0 = true ∧
      s'.tag = (if sge m.d.key 0 then s.overwrite m.d.vt.v m.d.vt.t else s).tag ∧
      s'.val = (if sge m.d.key 0 then s.overwrite m.d.vt.v m.d.vt.t else s).val ∧
      s'.ongoing = ongPut s.ongoing m.clientId m.requestId ∧
      ∃ o, outs = [o] ∧ sendTo m.replicaId (.write1Reply ⟨m.requestId, m.clientId,
        ⟨-1, (if sge m.d.key 0 then s.overwrite m.d.vt.v m.d.vt.t else s).tag⟩⟩) = some o)) := by
  have hov := overwrite_id s m.d.vt.v m.d.vt.t
  unfold stepWrite1 at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  by_cases hk : m.k = 0
  rotate_left
  · simp only [hk, ne_eq, not_false_eq_true, ↓reduceIte] at h; cases h
  simp only [hk, ne_eq, not_true_eq_false, ↓reduceIte, hov.2] at h
  refine ⟨hk, ?_⟩
  have leaf : ∀ (S1 S : RState) (o : Out)
      (hS0 : (if sge m.d.key 0 then s.overwrite m.d.vt.v m.d.vt.t else s) = S1)
      (hS1 : S.tag = S1.tag) (hS2 : S.val = S1.val)
      (hS3 : S.ongoing = ongPut s.ongoing m.clientId m.requestId)
      (hns : ¬ ∃ r, s.ongoing.get? m.clientId = some r ∧ sgt r m.requestId = true)
      (hd0 : sge m.d.key 0 = true → m.d.key = 0) (hfw : sgt m.forceWrite 0 = true)
      (ho : sendTo m.replicaId (.write1Reply ⟨m.requestId, m.clientId, ⟨-1, S1.tag⟩⟩) = some o),
      ((∃ r, s.ongoing.get? m.clientId = some r ∧ sgt r m.requestId = true) ∧ S = s ∧ [o] = []) ∨
      ((¬ ∃ r, s.ongoing.get? m.clientId = some r ∧ sgt r m.requestId = true) ∧
       (sge m.d.key 0 = true → m.d.key = 0) ∧ sgt m.forceWrite 0 = true ∧
       S.tag = (if sge m.d.key 0 then s.overwrite m.d.vt.v m.d.vt.t else s).tag ∧
       S.val = (if sge m.d.key 0 then s.overwrite m.d.vt.v m.d.vt.t else s).val ∧
       S.ongoing = ongPut s.ongoing m.clientId m.requestId ∧
       ∃ o', [o] = [o'] ∧ sendTo m.replicaId (.write1Reply ⟨m.requestId, m.clientId,
         ⟨-1, (if sge m.d.key 0 then s.overwrite m.d.vt.v m.d.vt.t else s).tag⟩⟩) = some o') := by
    intro S1 S o hS0 hS1 hS2 hS3 hns hd0 hfw ho
    subst hS0
    exact Or.inr ⟨hns, hd0, hfw, hS1, hS2, hS3, o, rfl, ho⟩
  rcases Option.eq_none_or_eq_some (s.ongoing.get? m.clientId) with hg | ⟨r, hg⟩
  rotate_left
  · simp only [hg] at h
    by_cases hs : sgt r m.requestId = true
    · simp only [hs, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at h
      exact Or.inl ⟨⟨r, hg, hs⟩, h.1.symm, h.2.symm⟩
    · simp only [hs, Bool.false_eq_true, ↓reduceIte] at h
      have hns : ¬ ∃ r', s.ongoing.get? m.clientId = some r' ∧ sgt r' m.requestId = true := by
        rintro ⟨r', hr', h'⟩; rw [hg] at hr'; cases hr'; exact hs h'
      by_cases hd : sge m.d.key 0 = true <;> by_cases hd0 : m.d.key = 0 <;>
        by_cases hlt : slt r m.requestId = true <;> by_cases hfw : sgt m.forceWrite 0 = true <;>
        simp only [hd, ne_eq, ↓reduceIte, Bool.false_eq_true] at h <;>
        simp only [hd0, hlt, hfw, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte,
          Bool.false_eq_true, Bool.not_true, Bool.not_false] at h <;>
        first
        | (cases h; done)
        | (split at h
           next o ho =>
             simp only [Except.ok.injEq, Prod.mk.injEq] at h
             obtain ⟨rfl, rfl⟩ := h
             refine leaf _ _ o (by split <;> simp_all) ?_ ?_ ?_ hns
               (by intro h'; first | exact hd0 | exact absurd h' hd) hfw ho <;>
               simp [hd, ongPut, hg, hlt, hov.2]
           next => cases h)
  · simp only [hg] at h
    have hns : ¬ ∃ r', s.ongoing.get? m.clientId = some r' ∧ sgt r' m.requestId = true := by
      rintro ⟨r', hr', -⟩; rw [hg] at hr'; cases hr'
    by_cases hd : sge m.d.key 0 = true <;> by_cases hd0 : m.d.key = 0 <;>
      by_cases hfw : sgt m.forceWrite 0 = true <;>
      simp only [hd, ne_eq, ↓reduceIte, Bool.false_eq_true] at h <;>
      simp only [hd0, hfw, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte,
        Bool.false_eq_true, Bool.not_true, Bool.not_false] at h <;>
      first
      | (cases h; done)
      | (split at h
         next o ho =>
           simp only [Except.ok.injEq, Prod.mk.injEq] at h
           obtain ⟨rfl, rfl⟩ := h
           refine leaf _ _ o (by split <;> simp_all) ?_ ?_ ?_ hns
             (by intro h'; first | exact hd0 | exact absurd h' hd) hfw ho <;>
             simp [hd, ongPut, hg, hov.2]
         next => cases h)


theorem stepRead2Reply_inv (k : Fin 3) (s s' : RState) (m : Read2ReplyM) (outs : List Out)
    (h : stepR k s (.msg (.read2Reply m)) = .ok (s', outs)) :
    (s.rops.get? (shiftInts m.requestId m.clientId) = none ∧ s' = s ∧ outs = []) ∨
    ∃ read, s.rops.get? (shiftInts m.requestId m.clientId) = some read ∧
      ((sge (read.numRead2Replies + 1) (NHALF + 1) = true ∧ ∃ rv, read.readValTag = some rv ∧
          s' = { s with ongoingReqs := s.ongoingReqs.del read.n,
                        rops := s.rops.del (shiftInts m.requestId m.clientId) } ∧
          outs = [.ext (.readReply read.clientId read.requestId rv.v 1)]) ∨
       (sge (read.numRead2Replies + 1) (NHALF + 1) = false ∧
          s' = { s with rops := s.rops.put (shiftInts m.requestId m.clientId) (
                   { read with numRead2Replies := read.numRead2Replies + 1 } : ReadOp) } ∧ outs = [])) := by
  simp only [stepR, stepRead2Reply, bind, Except.bind, pure, Except.pure] at h
  rcases Option.eq_none_or_eq_some (s.rops.get? (shiftInts m.requestId m.clientId)) with hg | ⟨read, hg⟩
  · left
    simp only [hg, Except.ok.injEq, Prod.mk.injEq] at h
    exact ⟨hg, h.1.symm, h.2.symm⟩
  · right
    refine ⟨read, hg, ?_⟩
    simp only [hg] at h
    by_cases hq : sge (read.numRead2Replies + 1) (NHALF + 1) = true
    · simp only [hq, ↓reduceIte] at h
      left
      refine ⟨hq, ?_⟩
      rcases Option.eq_none_or_eq_some read.readValTag with hr | ⟨rv, hr⟩
      · simp only [hr] at h; cases h
      · simp only [hr, Except.ok.injEq, Prod.mk.injEq] at h
        exact ⟨rv, hr, h.1.symm, h.2.symm⟩
    · simp only [hq, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at h
      right
      exact ⟨by simpa using hq, h.1.symm, h.2.symm⟩

end Perennial.gryff.replica2
