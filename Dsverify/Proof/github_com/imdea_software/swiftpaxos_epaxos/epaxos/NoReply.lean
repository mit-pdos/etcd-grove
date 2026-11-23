/-
The handlers' outputs carry no client reply (only the executor's `execCmdAt` replies).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.State

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

def Out.isReply : Out → Bool
  | .reply _ _ => true
  | _ => false

/-- No client reply among the outputs. -/
def noRep (outs : List Out) : Prop := ∀ o ∈ outs, o.isReply = false

theorem noRep_nil : noRep [] := by simp [noRep]

theorem noRep_cons {o : Out} {os : List Out} (h : o.isReply = false) (hs : noRep os) :
    noRep (o :: os) := by
  intro o' ho'; rcases List.mem_cons.mp ho' with rfl | ho'
  · exact h
  · exact hs o' ho'

theorem noRep_ite {c : Prop} [Decidable c] {a b : RState × List Out} (ha : noRep a.2)
    (hb : noRep b.2) : noRep (if c then a else b).2 := by
  split
  · exact ha
  · exact hb

theorem noRep_append {os os' : List Out} (h : noRep os) (h' : noRep os') : noRep (os ++ os') := by
  intro o ho; rcases List.mem_append.mp ho with ho | ho
  · exact h o ho
  · exact h' o ho

theorem startPhase1_noRep (σ : RState) (cmds : List WCmd) (x : InstId) (replica n ballot : w32)
    (ps : Option (List Proposal)) : noRep (startPhase1 σ cmds x replica n ballot ps).2 := by
  simp [startPhase1, noRep, Out.isReply]

theorem nackBranch_noRep (σ : RState) (x : InstId) (inst : InstRec) (lb : LbRec) :
    noRep (nackBranch σ x inst lb).2 := by
  unfold nackBranch
  dsimp only
  repeat' split
  all_goals ((try dsimp only); first
    | exact startPhase1_noRep _ _ _ _ _ _ _
    | (repeat' first | exact noRep_nil | exact startPhase1_noRep _ _ _ _ _ _ _ | refine noRep_ite ?_ ?_ | refine noRep_append ?_ ?_ | refine noRep_cons rfl ?_))

theorem noRep_reprop (ps : List Proposal) : noRep (ps.map Out.repropose) := by
  intro o ho; obtain ⟨p, -, rfl⟩ := List.mem_map.mp ho; rfl

theorem noRep_ite_iff {c : Prop} [Decidable c] {a b : RState × List Out} :
    noRep (if c then a else b).2 ↔ ((c → noRep a.2) ∧ (¬ c → noRep b.2)) := by
  by_cases h : c <;> simp [h]

theorem noRep_cons_iff {o : Out} {os : List Out} : noRep (o :: os) ↔ (o.isReply = false ∧ noRep os) := by
  constructor
  · intro h; exact ⟨h o (by simp), fun o' ho' => h o' (List.mem_cons_of_mem _ ho')⟩
  · intro h; exact noRep_cons h.1 h.2

theorem noRep_append_iff {os os' : List Out} : noRep (os ++ os') ↔ (noRep os ∧ noRep os') := by
  constructor
  · intro h; exact ⟨fun o ho => h o (List.mem_append_left _ ho), fun o ho => h o (List.mem_append_right _ ho)⟩
  · intro h; exact noRep_append h.1 h.2

theorem noRep_ite' {c : Prop} [Decidable c] {a b : RState × List Out} (ha : c → noRep a.2)
    (hb : ¬ c → noRep b.2) : noRep (if c then a else b).2 := by
  split
  · exact ha ‹_›
  · exact hb ‹_›

theorem hMsg_noRep (σ : RState) (m : Msg) : noRep (hMsg σ m).2 := by
  cases m with
  | prepare p =>
    simp only [hMsg, hPrepare]
    repeat' (first | exact noRep_nil | split)
    all_goals simp only [noRep_ite_iff, nackBranch_noRep, startPhase1_noRep, noRep_nil, noRep_cons_iff, noRep_append_iff, noRep_reprop, Out.isReply, and_true, true_and, implies_true]
  | prepareReply p =>
    simp only [hMsg, hPrepareReply]
    repeat' (first | exact noRep_nil | split)
    all_goals simp only [noRep_ite_iff, nackBranch_noRep, startPhase1_noRep, noRep_nil, noRep_cons_iff, noRep_append_iff, noRep_reprop, Out.isReply, and_true, true_and, implies_true]
  | preAccept p =>
    simp only [hMsg, hPreAccept]
    repeat' (first | exact noRep_nil | split)
    all_goals simp only [noRep_ite_iff, nackBranch_noRep, startPhase1_noRep, noRep_nil, noRep_cons_iff, noRep_append_iff, noRep_reprop, Out.isReply, and_true, true_and, implies_true]
  | preAcceptReply p =>
    simp only [hMsg, hPreAcceptReply]
    repeat' (first | exact noRep_nil | split)
    all_goals simp only [noRep_ite_iff, nackBranch_noRep, startPhase1_noRep, noRep_nil, noRep_cons_iff, noRep_append_iff, noRep_reprop, Out.isReply, and_true, true_and, implies_true]
  | accept p =>
    simp only [hMsg, hAccept]
    repeat' (first | exact noRep_nil | split)
    all_goals simp only [noRep_ite_iff, nackBranch_noRep, startPhase1_noRep, noRep_nil, noRep_cons_iff, noRep_append_iff, noRep_reprop, Out.isReply, and_true, true_and, implies_true]
  | acceptReply p =>
    simp only [hMsg, hAcceptReply]
    split; · exact noRep_nil
    split; · exact noRep_nil
    simp only [noRep_ite_iff, nackBranch_noRep, startPhase1_noRep, noRep_nil, noRep_cons_iff, noRep_append_iff, noRep_reprop, Out.isReply, and_true, true_and, implies_true]
  | commit p =>
    simp only [hMsg, hCommit]
    repeat' (first | exact noRep_nil | split)
    all_goals simp only [noRep_ite_iff, nackBranch_noRep, startPhase1_noRep, noRep_nil, noRep_cons_iff, noRep_append_iff, noRep_reprop, Out.isReply, and_true, true_and, implies_true]
  | tryPreAccept p => simp [hMsg, hTryPreAccept, noRep]
  | tryPreAcceptReply p => simp [hMsg, hTryPreAcceptReply, noRep]
  | beacon _ => simp [hMsg, noRep]
  | beaconReply _ => simp [hMsg, noRep]

theorem hRecover_noRep (σ : RState) (x : InstId) : noRep (hRecover σ x).2 := by
  simp only [hRecover]
  simp only [noRep_ite_iff, nackBranch_noRep, startPhase1_noRep, noRep_nil, noRep_cons_iff, noRep_append_iff, noRep_reprop, Out.isReply, and_true, true_and, implies_true]

theorem hPropose_noRep (σ : RState) (batch : List Proposal) : noRep (hPropose σ batch).2 := by
  unfold hPropose; split
  · simp [noRep]
  · intro o ho
    simp only [List.mem_cons] at ho
    rcases ho with rfl | ho
    · rfl
    · exact startPhase1_noRep _ _ _ _ _ _ _ o ho

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model
