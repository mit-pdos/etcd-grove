/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H1/PureParti.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit H1d: the participant's steps keep the coordinator's and the EPaxos parts (`ppf`), and have
one output (`Read1`, `Read2`, `Write2`).
-/
module

public import Dsverify.Proof.gryff.H1.PureFrame

@[expose] public section

namespace Perennial.gryff.replica2

open Perennial.gryff.model

/-- The parts of the state a participant step keeps. -/
def ppf (s : RState) :=
  (s.id, s.maxN, s.rops, s.wops, s.ongoingReqs, s.inst, s.crtInstance, s.committedUpTo, s.conf,
    s.maxSeqK0, s.prevValTag, s.proposeQ)

theorem ppf_overwrite (s : RState) (v : w64) (t : model.Tag) : ppf (s.overwrite v t) = ppf s := by
  unfold RState.overwrite; split <;> rfl

theorem ppf_ite_overwrite (b : Bool) (s : RState) (v : w64) (t : model.Tag) :
    ppf (if b then s.overwrite v t else s) = ppf s := by
  split
  · exact ppf_overwrite _ _ _
  · rfl

theorem stepRead1_ppf (s s' : RState) (m : Read1ProxiedM) (outs : List Out)
    (h : stepRead1 s m = .ok (s', outs)) : ppf s' = ppf s ∧ ∃ o1, outs = [o1] := by
  unfold stepRead1 at h
  simp only [bind, Except.bind, pure, Except.pure, never, dead, FailM.failNever,
    FailM.failDead] at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (simp only [Except.ok.injEq, Prod.mk.injEq] at h
       obtain ⟨rfl, rfl⟩ := h
       refine ⟨?_, _, rfl⟩
       first | exact ppf_overwrite _ _ _ | simp only [ppf_overwrite, ppf_ite_overwrite])

theorem stepRead2_ppf (s s' : RState) (m : Read2ProxiedM) (outs : List Out)
    (h : stepRead2 s m = .ok (s', outs)) : ppf s' = ppf s ∧ ∃ o1, outs = [o1] := by
  unfold stepRead2 at h
  simp only [bind, Except.bind, pure, Except.pure, never, dead, FailM.failNever,
    FailM.failDead] at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (simp only [Except.ok.injEq, Prod.mk.injEq] at h
       obtain ⟨rfl, rfl⟩ := h
       refine ⟨?_, _, rfl⟩
       first | exact ppf_overwrite _ _ _ | simp only [ppf_overwrite, ppf_ite_overwrite])

theorem stepWrite2_ppf (s s' : RState) (m : Write2ProxiedM) (outs : List Out)
    (h : stepWrite2 s m = .ok (s', outs)) : ppf s' = ppf s ∧ ∃ o1, outs = [o1] := by
  unfold stepWrite2 at h
  simp only [bind, Except.bind, pure, Except.pure, never, dead, FailM.failNever,
    FailM.failDead] at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (simp only [Except.ok.injEq, Prod.mk.injEq] at h
       obtain ⟨rfl, rfl⟩ := h
       refine ⟨?_, _, rfl⟩
       exact ppf_overwrite _ _ _)

theorem stepWrite1_ppf (s s' : RState) (m : Write1ProxiedM) (outs : List Out)
    (h : stepWrite1 s m = .ok (s', outs)) : ppf s' = ppf s := by
  unfold stepWrite1 at h
  simp only [bind, Except.bind, pure, Except.pure, never, dead, FailM.failNever,
    FailM.failDead] at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (simp only [Except.ok.injEq, Prod.mk.injEq] at h
       obtain ⟨rfl, rfl⟩ := h
       first | rfl | exact ppf_overwrite _ _ _ | exact ppf_ite_overwrite _ _ _ _)

end Perennial.gryff.replica2
