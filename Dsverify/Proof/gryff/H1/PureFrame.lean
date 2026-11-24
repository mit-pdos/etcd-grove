/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H1/PureFrame.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit H1d: the coordinator's steps keep the rest of the replica's state (the participant's ongoing
writes, the id, the EPaxos part, the propose queue): `epf s' = epf s`.
-/
module

public import Dsverify.Proof.gryff.H1.PureWrite1
public import Dsverify.Proof.gryff.H1.PureRead1

@[expose] public section

namespace Perennial.gryff.replica2

open Perennial.gryff.model

/-- The parts of the state a coordinator step keeps. -/
def epf (s : RState) :=
  (s.ongoing, s.id, s.inst, s.crtInstance, s.committedUpTo, s.conf, s.maxSeqK0, s.prevValTag,
    s.proposeQ)

theorem epf_overwrite (s : RState) (v : w64) (t : model.Tag) : epf (s.overwrite v t) = epf s := by
  unfold RState.overwrite; split <;> rfl

theorem epf_shortCircuit (s s2 : RState) (n : w32) (value : model.ValTag) (fo : Bool)
    (o : List Out) (h : model.shortCircuit s n value fo = some (s2, o)) : epf s2 = epf s := by
  rw [sc.shortCircuit_frame s s2 n value fo o h]; rfl

theorem stepRead2Reply_epf (k : Fin 3) (s s' : RState) (m : Read2ReplyM) (outs : List Out)
    (h : stepR k s (.msg (.read2Reply m)) = .ok (s', outs)) : epf s' = epf s := by
  rcases stepRead2Reply_inv k s s' m outs h with ⟨-, rfl, -⟩ | ⟨read, -, ⟨-, rv, -, rfl, -⟩ | ⟨-, rfl, -⟩⟩
    <;> rfl

theorem stepWrite2Reply_epf (k : Fin 3) (s s' : RState) (m : Write2ReplyM) (outs : List Out)
    (h : stepR k s (.msg (.write2Reply m)) = .ok (s', outs)) : epf s' = epf s := by
  rcases stepWrite2Reply_inv k s s' m outs h with ⟨-, rfl, -⟩ |
    ⟨w, -, ⟨-, wt, s2, outs2, -, hsc, rfl, -⟩ | ⟨-, rfl, -⟩⟩
  · rfl
  · split at hsc
    · have := epf_shortCircuit _ _ _ _ _ _ hsc; exact this
    · cases hsc; rfl
  · rfl

theorem stepWrite1Reply_epf (k : Fin 3) (s s' : RState) (m : Write1ReplyM) (outs : List Out)
    (h : stepR k s (.msg (.write1Reply m)) = .ok (s', outs)) : epf s' = epf s := by
  rcases stepWrite1Reply_inv k s s' m outs h with ⟨-, rfl, -⟩ | ⟨w, -, hw⟩
  · rfl
  rcases w1Tail_inv s s' m _ outs hw with ⟨-, -, s2, outs2, hsc, rfl, -⟩ | ⟨-, -, -, -, rfl⟩ |
    ⟨-, rfl, -⟩
  · have := epf_shortCircuit _ _ _ _ _ _ hsc; exact this
  · rfl
  · rfl

theorem r1S_epf (s : RState) (read : ReadOp) (m : Read1ReplyM) : epf (r1S s read m) = epf s := by
  unfold r1S; split
  · exact epf_overwrite _ _ _
  · rfl

theorem stepRead1Reply_epf (k : Fin 3) (s s' : RState) (m : Read1ReplyM) (outs : List Out)
    (h : stepR k s (.msg (.read1Reply m)) = .ok (s', outs)) : epf s' = epf s := by
  rcases stepRead1Reply_inv k s s' m outs h with ⟨-, rfl, -⟩ | ⟨read, -, hc⟩
  · rfl
  rcases hc with ⟨-, rfl, -⟩ | ⟨-, ⟨-, rv, -, rfl, -⟩ | ⟨-, -, rfl, -⟩ | ⟨-, -, rv, -, -, rfl⟩⟩
  all_goals exact r1S_epf s read m

theorem stepClientWrite_epf (s s' : RState) (rid cid : w32) (v : w64) (d : Dep)
    (outs : List Out) (h : stepClientWrite s rid cid 0 v d = .ok (s', outs)) : epf s' = epf s := by
  unfold stepClientWrite at h
  simp only [bind, Except.bind, pure, Except.pure, never, disabled, dead, FailM.failNever,
    FailM.failDisabled, FailM.failDead] at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  rotate_left
  · cases h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

theorem stepClientRead_epf (s s' : RState) (rid cid : w32) (d : Dep) (outs : List Out)
    (h : stepClientRead s rid cid 0 d = .ok (s', outs)) : epf s' = epf s := by
  unfold stepClientRead at h
  simp only [bind, Except.bind, pure, Except.pure, never, disabled, dead, FailM.failNever,
    FailM.failDisabled, FailM.failDead] at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  rename_i v hv
  split at h
  rotate_left
  · cases h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have key := forIn_inv (fun (_ : List (w64 × WriteOp)) (σ : RState) => epf σ = epf s)
      _ ?step s.wops [] _ v ?init hv
  · exact key
  case init => rfl
  case step =>
    intro Lacc a σ r hP hb
    split at hb
    · split at hb
      · simp only [Except.ok.injEq] at hb
        subst hb
        exact ⟨_, rfl, hP⟩
      · cases hb
    · simp only [Except.ok.injEq] at hb
      subst hb
      exact ⟨_, rfl, hP⟩

end Perennial.gryff.replica2

namespace Perennial.gryff.replica2

open Perennial.gryff.model

theorem stepClientRead_key (s : RState) (rid cid : w32) (k : w64) (d : Dep) (r : RState × List Out)
    (h : stepClientRead s rid cid k d = .ok r) : k = 0 := by
  refine Classical.byContradiction fun hk => ?_
  unfold stepClientRead at h
  simp [never, FailM.failNever, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i hc; exact hc (Or.inl (Or.inl hk))

theorem stepClientWrite_key (s : RState) (rid cid : w32) (k v : w64) (d : Dep)
    (r : RState × List Out) (h : stepClientWrite s rid cid k v d = .ok r) : k = 0 := by
  refine Classical.byContradiction fun hk => ?_
  unfold stepClientWrite at h
  simp [never, FailM.failNever, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i hc; exact hc (Or.inl (Or.inl hk))

end Perennial.gryff.replica2
