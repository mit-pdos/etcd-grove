/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H2/PreAcceptModel.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit H2: `stepPreAccept`'s cases (pure)
-/
module

public import Dsverify.Proof.gryff.Model.Step

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.replica2

open Perennial.gryff.model

/-- `handlePreAccept`'s state after the `crtInstance` update. -/
def paS1 (s : RState) (m : PreAcceptM) : RState :=
  if sge m.inst (s.crt m.replica) then s.setCrt m.replica (m.inst + 1) else s

/-- The base and `changed` after the store's tag comparison. -/
def paBase (s1 : RState) (m : PreAcceptM) (ch0 : Bool) : ValTag × Bool :=
  if s1.tag.gt m.base.t then (s1.storeVT, true) else (m.base, ch0)

/-- `changed` (G41): the attributes differ from the PreAccept's. -/
def paCh (m : PreAcceptM) (seq : w32) (deps : Deps) : Bool :=
  (seq != m.seq).or (!depsEqual deps m.deps)

/-- The new copy. -/
def paCopy (inst : Option Copy) (m : PreAcceptM) (seq : w32) (deps : Deps) (base : ValTag)
    (status : w8) : Copy :=
  match inst with
  | some c =>
    { c with cmds := m.cmds, seq := seq, deps := deps, base := base, ballot := m.ballot,
             vbal := m.ballot, status := status }
  | none =>
    { cmds := m.cmds, ballot := m.ballot, status := status, seq := seq, deps := deps,
      base := base, lb := none, slot := m.inst, leader := m.replica, vbal := m.ballot }

/-- `uncommittedDeps`. -/
def paUnc (s1 : RState) (deps : Deps) : Bool :=
  [0, 1, 2].any (fun q => sgt (deps.at q) (s1.committedUpTo.at q))

/-- The reply's condition. -/
def paReplyCond (s1 : RState) (m : PreAcceptM) (deps : Deps) (changed : Bool) : Bool :=
  (((changed.or ([0, 1, 2].any (fun q => sgt (deps.at q) (s1.committedUpTo.at q)))).or
    (decide (m.replica ≠ m.leaderId))).or (!isInitialBallot m.ballot))

/-- `paS1` changes `crtInstance` only. -/
theorem paS1_eq (s : RState) (m : PreAcceptM) :
    paS1 s m = { s with crtInstance := (paS1 s m).crtInstance } := by
  unfold paS1; split <;> rfl

theorem paS1_len (s : RState) (m : PreAcceptM) :
    (paS1 s m).crtInstance.length = s.crtInstance.length := by
  unfold paS1; split
  · simp [RState.setCrt]
  · rfl

@[simp] theorem paS1_inst (s : RState) (m : PreAcceptM) : (paS1 s m).inst = s.inst := by
  unfold paS1; split <;> rfl
@[simp] theorem paS1_confAt (s : RState) (m : PreAcceptM) : (paS1 s m).confAt = s.confAt := by
  unfold paS1; split <;> rfl
@[simp] theorem paS1_conf (s : RState) (m : PreAcceptM) : (paS1 s m).conf = s.conf := by
  unfold paS1; split <;> rfl
@[simp] theorem paS1_maxSeqK0 (s : RState) (m : PreAcceptM) : (paS1 s m).maxSeqK0 = s.maxSeqK0 := by
  unfold paS1; split <;> rfl
@[simp] theorem paS1_committedUpTo (s : RState) (m : PreAcceptM) :
    (paS1 s m).committedUpTo = s.committedUpTo := by
  unfold paS1; split <;> rfl
@[simp] theorem paS1_prevValTag (s : RState) (m : PreAcceptM) :
    (paS1 s m).prevValTag = s.prevValTag := by
  unfold paS1; split <;> rfl
@[simp] theorem paS1_id (s : RState) (m : PreAcceptM) : (paS1 s m).id = s.id := by
  unfold paS1; split <;> rfl
@[simp] theorem paS1_tag (s : RState) (m : PreAcceptM) : (paS1 s m).tag = s.tag := by
  unfold paS1; split <;> rfl
@[simp] theorem paS1_val (s : RState) (m : PreAcceptM) : (paS1 s m).val = s.val := by
  unfold paS1; split <;> rfl
@[simp] theorem paS1_storeVT (s : RState) (m : PreAcceptM) : (paS1 s m).storeVT = s.storeVT := by
  unfold paS1; split <;> rfl

set_option hygiene false in
/-- The common tail of `stepPreAccept_cases`'s cases. -/
local macro "pa_tail" : tactic => `(tactic| (
  rcases hu : updateAttributes (paS1 s m) m.cmds m.seq m.deps m.replica with _ | ⟨seq, deps, ch0⟩
  · simp [hu] at h
  simp only [hu] at h
  rcases hh : m.cmds.head? with _ | c0
  · simp [hh] at h
  simp only [hh] at h
  have hne : m.cmds ≠ [] := by intro e; simp [e] at hh
  refine ⟨seq, deps, ch0, rfl, hne, ?_⟩
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (simp [bind, Except.bind] at h; done)
    | (obtain ⟨h1, h2⟩ := Prod.mk.inj (Except.ok.inj h)
       subst h1 h2
       first
         | (left; refine ⟨_, _, rfl, ?_, ?_, rfl, rfl⟩ <;> simp_all; done)
         | (right; refine ⟨by simp_all, _, ?_, rfl, ?_⟩ <;> simp_all [paBase, paCopy, paReplyCond, paCh]))))

theorem stepPreAccept_cases (s s' : RState) (outs : List Out) (m : PreAcceptM)
    (h : stepPreAccept s m = .ok (s', outs)) :
    cmdsOk m.cmds = true ∧ inBox m.replica m.inst = true ∧
    ((∃ c, s.inst m.replica m.inst = some c ∧
        (c.status = St.COMMITTED ∨ c.status = St.ACCEPTED ∨ c.status = St.EXECUTED) ∧
        s' = s ∧ outs = []) ∨
     (¬ (∃ c, s.inst m.replica m.inst = some c ∧
        (c.status = St.COMMITTED ∨ c.status = St.ACCEPTED ∨ c.status = St.EXECUTED)) ∧
      ∃ seq deps ch0, updateAttributes (paS1 s m) m.cmds m.seq m.deps m.replica =
          some (seq, deps, ch0) ∧ m.cmds ≠ [] ∧
        ((∃ c o, s.inst m.replica m.inst = some c ∧ slt m.ballot c.ballot = true ∧
            sendPeer (paS1 s m) m.leaderId (.preAcceptReply
              ⟨m.replica, m.inst, FALSE, c.ballot, c.seq, c.deps, c.base⟩) = some o ∧
            s' = paS1 s m ∧ outs = [o]) ∨
         ((∀ c, s.inst m.replica m.inst = some c → slt m.ballot c.ballot = false) ∧
          ∃ o, s' = updateConflicts ((paS1 s m).setInst m.replica m.inst
                (paCopy (s.inst m.replica m.inst) m seq deps (paBase (paS1 s m) m (paCh m seq deps)).1
                  (if (paBase (paS1 s m) m (paCh m seq deps)).2 then St.PREACCEPTED else St.PREACCEPTED_EQ)))
                m.cmds m.replica m.inst m.seq ∧ outs = [o] ∧
            (if paReplyCond (paS1 s m) m deps (paBase (paS1 s m) m (paCh m seq deps)).2 then
              sendPeer s' m.leaderId (.preAcceptReply
                ⟨m.replica, m.inst, TRUE, m.ballot, seq, deps, (paBase (paS1 s m) m (paCh m seq deps)).1⟩) = some o
             else sendPeer s' m.leaderId (.preAcceptOK ⟨m.inst⟩) = some o))))) := by
  unfold stepPreAccept at h
  have hok : cmdsOk m.cmds = true := by
    cases hc : cmdsOk m.cmds
    · simp only [hc] at h; simp at h; cases h
    · rfl
  have hbox : inBox m.replica m.inst = true := by
    cases hc : inBox m.replica m.inst
    · simp only [hok, hc] at h; simp at h; cases h
    · rfl
  simp only [hok, hbox, Bool.not_true] at h
  refine ⟨hok, hbox, ?_⟩
  by_cases hearly : ∃ c, s.inst m.replica m.inst = some c ∧
      (c.status = St.COMMITTED ∨ c.status = St.ACCEPTED ∨ c.status = St.EXECUTED)
  · obtain ⟨c, hc, hst⟩ := hearly
    left
    refine ⟨c, hc, hst, ?_⟩
    simp only [hc] at h
    rcases hst with hst | hst | hst <;> simp [hst] at h <;>
      (obtain ⟨h1, h2⟩ := Prod.mk.inj (Except.ok.inj h); exact ⟨h1.symm, h2.symm⟩)
  · right
    refine ⟨hearly, ?_⟩
    have hjp : ∀ c, s.inst m.replica m.inst = some c →
        ¬ (c.status = St.COMMITTED ∨ c.status = St.ACCEPTED ∨ c.status = St.EXECUTED) :=
      fun c hc hst => hearly ⟨c, hc, hst⟩
    rcases hc : s.inst m.replica m.inst with _ | c
    · simp only [hc, Bool.false_eq_true, ↓reduceIte] at h
      split at h
      · rw [show s.setCrt m.replica (m.inst + 1) = paS1 s m by simp [paS1, *]] at h
        pa_tail
      · rw [← (show paS1 s m = s by simp [paS1, *])] at h
        pa_tail
    · have hns := hjp c hc
      simp only [hc, hns, Bool.false_eq_true, ↓reduceIte] at h
      split at h
      · rw [show s.setCrt m.replica (m.inst + 1) = paS1 s m by simp [paS1, *]] at h
        pa_tail
      · rw [← (show paS1 s m = s by simp [paS1, *])] at h
        pa_tail

end Perennial.gryff.replica2
