/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureA/StepPreAcceptCases.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit A1c, internal: the succeeding paths of `stepPreAccept` (`stepPreAccept_cases`): an early
return (the copy is ACCEPTED/COMMITTED/EXECUTED), a NACK (the copy's ballot is above the message's),
or the update of the copy (`PAUpd`: G41's equality-based status, the reply or the PreAcceptOK).
-/
module

public import Dsverify.Proof.gryff.PureA.StepPreAcceptFrame

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pureA.SPA

open Perennial Perennial.gryff.model Perennial.gryff.pure Perennial.gryff.kahn

def Bump (s : RState) (m : PreAcceptM) (s1 : RState) : Prop :=
  s1 = s ∨ (sge m.inst (s.crt m.replica) = true ∧ s1 = s.setCrt m.replica (m.inst + 1))

def SendP (s : RState) (q : w32) (msg : Msg) (x : Out) : Prop :=
  q ≠ s.id ∧ ∃ d, dstOf q = some d ∧ x = .send d msg

theorem sendP_of {s t : RState} {q : w32} {msg : Msg} {x : Out} (h : sendPeer t q msg = some x)
    (e : t.id = s.id) : SendP s q msg x := by
  unfold sendPeer at h
  split at h
  · cases h
  · rename_i hne
    unfold sendTo at h
    obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.1 h
    exact ⟨e ▸ hne, d, hd, rfl⟩

def okOf (m : PreAcceptM) (cp : Copy) : PreAcceptReplyM :=
  { replica := m.replica, inst := m.inst, ok := TRUE, ballot := m.ballot, seq := cp.seq,
    deps := cp.deps, base := cp.base }

abbrev isCAE (c : Copy) : Prop := c.status = St.COMMITTED ∨ c.status = St.ACCEPTED ∨ c.status = St.EXECUTED

structure PAUpd (s : RState) (m : PreAcceptM) (s1 : RState) (cp : Copy) (x : Out) : Prop where
  ua : ∃ ch, updateAttributes s1 m.cmds m.seq m.deps m.replica = some (cp.seq, cp.deps, ch)
  cmds : cp.cmds = m.cmds
  ballot : cp.ballot = m.ballot
  vbal : cp.vbal = m.ballot
  base : (s1.tag.gt m.base.t = false ∧ cp.base = m.base) ∨
    (s1.tag.gt m.base.t = true ∧ cp.base = s1.storeVT)
  st1 : cp.status = St.PREACCEPTED ∨ cp.status = St.PREACCEPTED_EQ
  st2 : cp.status = St.PREACCEPTED_EQ →
    cp.seq = m.seq ∧ depsEqual cp.deps m.deps = true ∧ s1.tag.gt m.base.t = false
  st3 : cp.seq = m.seq → depsEqual cp.deps m.deps = true → s1.tag.gt m.base.t = false →
    cp.status = St.PREACCEPTED_EQ
  old : s.inst m.replica m.inst = none ∨ ∃ c, s.inst m.replica m.inst = some c ∧ ¬ isCAE c ∧
    slt m.ballot c.ballot = false ∧ cp.lb = c.lb
  out : SendP s m.leaderId (.preAcceptReply (okOf m cp)) x ∨
    (cp.status = St.PREACCEPTED_EQ ∧ m.replica = m.leaderId ∧ isInitialBallot m.ballot = true ∧
      SendP s m.leaderId (.preAcceptOK { inst := m.inst }) x)

def nackOf (m : PreAcceptM) (c : Copy) : PreAcceptReplyM :=
  { replica := m.replica, inst := m.inst, ok := FALSE, ballot := c.ballot, seq := c.seq,
    deps := c.deps, base := c.base }

def PACases (s : RState) (m : PreAcceptM) (s' : RState) (o : List Out) : Prop :=
  (s' = s ∧ o = []) ∨
  (∃ s1 c x, Bump s m s1 ∧ s.inst m.replica m.inst = some c ∧ ¬ isCAE c ∧
      slt m.ballot c.ballot = true ∧ s' = s1 ∧ o = [x] ∧ SendP s m.leaderId (.preAcceptReply (nackOf m c)) x) ∨
  (∃ s1 cp x, Bump s m s1 ∧ s' = updateConflicts (s1.setInst m.replica m.inst cp) m.cmds m.replica m.inst m.seq ∧
      o = [x] ∧ PAUpd s m s1 cp x)

theorem or_ff {x y : Bool} (h1 : (or x y) = false) (h2 : x = true) : False := by
  subst h2; simp at h1

theorem tor_ff {y : Bool} (h1 : (or true y) = false) : False := by simp at h1

theorem st_pe : St.PREACCEPTED ≠ St.PREACCEPTED_EQ := by decide

theorem nt {b : Bool} (h : ¬ b = true) : b = false := by simpa using h

theorem chg_false {a b : w32} {d : Bool} (h : ¬ (or (bne a b) (not d)) = true) : a = b ∧ d = true := by
  simpa using h

theorem chg_true {a b : w32} {d : Bool} (h : (or (bne a b) (not d)) = true) (e1 : a = b) (e2 : d = true) :
    False := by
  subst e1; simp [e2] at h

theorem rep_false {x y z : Bool} {p : Prop} [Decidable p] (h : ¬ (or (or (or x y) (decide p)) (not z)) = true) :
    x = false ∧ ¬ p ∧ z = true := by
  simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true', not_or] at h
  exact ⟨by simpa using h.1.1.1, h.1.2, by simpa using h.2⟩

theorem uc_id (t : RState) (cmds : List Cmd) (q i sq : w32) :
    (updateConflicts t cmds q i sq).id = t.id := (updateConflicts_inst _ _ _ _ _).2.1

set_option maxRecDepth 20000 in
theorem stepPreAccept_cases {s s' : RState} {m : PreAcceptM} {o : List Out}
    (h : stepPreAccept s m = .ok (s', o)) : inBox m.replica m.inst = true ∧ PACases s m s' o := by
  refine ⟨?_, ?_⟩
  · unfold stepPreAccept at h; peel h
    all_goals (simpa using ‹¬(!inBox _ _) = true›)
  unfold stepPreAccept at h
  rcases hc : s.inst m.replica m.inst with _ | c <;> simp only [hc] at h <;> peel h
  all_goals (cases h)
  all_goals first
    | exact absurd trivial ‹¬True›
    | exact Or.inl ⟨rfl, rfl⟩
    | (refine Or.inr (Or.inl ⟨_, c, _, ?_, hc, asm, asm, rfl, rfl, ?_⟩)
       · first | exact Or.inl rfl | exact Or.inr ⟨asm, rfl⟩
       · refine sendP_of ‹sendPeer _ _ _ = some _› ?_; rfl)
    | (refine Or.inr (Or.inr ⟨_, _, _, ?_, rfl, rfl, ?_⟩)
       · first | exact Or.inl rfl | exact Or.inr ⟨asm, rfl⟩
       · refine { ua := ⟨_, asm⟩, cmds := rfl, ballot := rfl, vbal := rfl, base := ?_, st1 := ?_,
                  st2 := ?_, st3 := ?_, old := ?_, out := ?_ }
         · first | exact Or.inl ⟨nt asm, rfl⟩ | exact Or.inr ⟨asm, rfl⟩
         · first | exact Or.inl rfl | exact Or.inr rfl
         · intro he
           first
             | exact absurd he st_pe
             | exact ⟨(chg_false asm).1, (chg_false asm).2, nt asm⟩
         · intro e1 e2 e3
           first
             | rfl
             | exact absurd (e3.symm.trans asm) Bool.false_ne_true
             | exact (chg_true asm e1 e2).elim
         · first | exact Or.inl asm | exact Or.inr ⟨_, hc, asm, nt asm, rfl⟩
         · first
             | (left; refine sendP_of ‹sendPeer _ _ _ = some _› ?_; exact uc_id _ _ _ _ _)
             | (have k := rep_false asm
                first
                  | (right; refine ⟨rfl, Classical.not_not.1 k.2.1, k.2.2, ?_⟩
                     refine sendP_of ‹sendPeer _ _ _ = some _› ?_; exact uc_id _ _ _ _ _)
                  | exact (tor_ff k.1).elim
                  | exact Bool.noConfusion k.1
                  | exact (or_ff k.1 asm).elim
                  | exact absurd (k.1.symm.trans asm) Bool.false_ne_true))
end Perennial.gryff.pureA.SPA
