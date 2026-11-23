/-
Pure facts about the model's handlers (`Epaxos/Model/State.lean`) that the heap proofs use:
each handler's result as a record update of its input, branch by branch.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Inv

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open model

theorem upd_self {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) (h : f a = b) :
    model.upd f a b = f := by
  funext a'; unfold model.upd; split <;> simp_all

namespace model

theorem RState.eta_inst (σ : RState) : { σ with inst := σ.inst } = σ := by cases σ; rfl

theorem getOrDefault_fst (σ : RState) (x : InstId) :
    (getOrDefault σ x).1 = { σ with inst := upd σ.inst x (some (getOrDefault σ x).2) } := by
  unfold getOrDefault
  rcases h : σ.inst x with _ | w
  · rfl
  · simp only
    rw [upd_self _ _ _ h]

theorem getOrDefault_snd_inst (σ σ' : RState) (x : InstId) (h : σ.inst = σ'.inst) :
    (getOrDefault σ x).2 = (getOrDefault σ' x).2 := by
  unfold getOrDefault; rw [h]; split <;> rfl

theorem bumpCrt_eq (σ : RState) (q : Nat) (n : w32) :
    bumpCrt σ q n = { σ with crtInstance := (bumpCrt σ q n).crtInstance } := by
  unfold bumpCrt; split <;> rfl

theorem bumpRecvBallot_eq (σ : RState) (b : w32) :
    bumpRecvBallot σ b = { σ with maxRecvBallot := (bumpRecvBallot σ b).maxRecvBallot } := by
  unfold bumpRecvBallot; split <;> rfl

/-- The commit's instance record before the NOOP re-proposal test. -/
def commitW0 (σ : RState) (m : Commit) : InstRec :=
  (getOrDefault σ ⟨toN m.replica, toN m.inst⟩).2

/-- The commit handler's state after its first three statements. -/
def commitPre (σ : RState) (m : Commit) : RState :=
  { σ with crtInstance := (bumpCrt σ (toN m.replica) m.inst).crtInstance,
           maxRecvBallot := (bumpRecvBallot σ m.ballot).maxRecvBallot,
           inst := upd σ.inst ⟨toN m.replica, toN m.inst⟩ (some (commitW0 σ m)) }

theorem hCommit_pre (σ : RState) (m : Commit) :
    (getOrDefault (bumpRecvBallot (bumpCrt σ (toN m.replica) m.inst) m.ballot)
      ⟨toN m.replica, toN m.inst⟩).1 = commitPre σ m := by
  rw [getOrDefault_fst]
  have e : (getOrDefault (bumpRecvBallot (bumpCrt σ (toN m.replica) m.inst) m.ballot)
      ⟨toN m.replica, toN m.inst⟩).2 = (getOrDefault σ ⟨toN m.replica, toN m.inst⟩).2 := by
    apply getOrDefault_snd_inst
    unfold bumpRecvBallot bumpCrt; split <;> split <;> rfl
  rw [e]
  unfold commitPre commitW0 bumpRecvBallot bumpCrt
  split <;> split <;> simp_all

/-- The re-proposal step of `handleCommit` (on the record `w`). -/
def commitRp (σ : RState) (m : Commit) (w : InstRec) : InstRec × List Out :=
  if toN m.replica = σ.id ∧ m.command.length = 1 ∧ ((m.command.head?.map (·.op)) = some opNONE) then
    match w.lb with
    | some lb =>
      match lb.clientProposals with
      | some ps => ({ w with lb := some { lb with clientProposals := none } }, ps.map Out.repropose)
      | none => (w, [])
    | none => (w, [])
  else (w, [])

/-- The committed record. -/
def commitInst (σ : RState) (m : Commit) : InstRec :=
  let w := (commitRp σ m (commitW0 σ m)).1
  { w with bal := m.ballot, vbal := m.ballot, cmds := some m.command, seq := m.seq,
           deps := m.deps, status := stCOMMITTED }

theorem hCommit_early (σ : RState) (m : Commit)
    (h : stGe (commitW0 σ m).status stCOMMITTED = true ∨ m.ballot.slt (commitW0 σ m).bal = true) :
    hCommit σ m = (commitPre σ m, []) := by
  have e := hCommit_pre σ m
  unfold commitW0 at h
  rw [getOrDefault_snd_inst σ (bumpRecvBallot (bumpCrt σ (toN m.replica) m.inst) m.ballot)
    _ (by unfold bumpRecvBallot bumpCrt; split <;> split <;> rfl)] at h
  unfold hCommit
  simp only
  rcases hg : getOrDefault (bumpRecvBallot (bumpCrt σ (toN m.replica) m.inst) m.ballot)
    ⟨toN m.replica, toN m.inst⟩ with ⟨σ3, w⟩
  rw [hg] at e h
  simp only at e h ⊢
  rcases h with h | h <;> simp [h, e]

theorem hCommit_main (σ : RState) (m : Commit)
    (h1 : stGe (commitW0 σ m).status stCOMMITTED = false)
    (h2 : m.ballot.slt (commitW0 σ m).bal = false) :
    hCommit σ m =
      (updateCommitted (updateConflicts ((commitPre σ m).setInst ⟨toN m.replica, toN m.inst⟩
          (commitInst σ m)) m.command (toN m.replica) m.inst m.seq) (toN m.replica),
        (commitRp σ m (commitW0 σ m)).2 ++
          [Out.ev (.record ⟨toN m.replica, toN m.inst⟩ m.command),
           Out.ev (.commit ⟨toN m.replica, toN m.inst⟩ m.ballot ⟨m.command, m.seq, m.deps⟩)]) := by
  have e := hCommit_pre σ m
  have hid : (bumpRecvBallot (bumpCrt σ (toN m.replica) m.inst) m.ballot).id = σ.id := by
    unfold bumpRecvBallot bumpCrt; split <;> split <;> rfl
  unfold commitInst commitRp commitW0 at *
  rw [getOrDefault_snd_inst σ (bumpRecvBallot (bumpCrt σ (toN m.replica) m.inst) m.ballot)
    _ (by unfold bumpRecvBallot bumpCrt; split <;> split <;> rfl)] at h1 h2 ⊢
  unfold hCommit
  simp only
  rcases hg : getOrDefault (bumpRecvBallot (bumpCrt σ (toN m.replica) m.inst) m.ballot)
    ⟨toN m.replica, toN m.inst⟩ with ⟨σ3, w⟩
  have hid3 : σ3.id = σ.id := by
    have := congrArg (·.1.id) hg; simp only at this; rw [← this, ← hid]
    unfold getOrDefault; split <;> rfl
  rw [hg] at e h1 h2
  simp only at e h1 h2 ⊢
  have hcid : (commitPre σ m).id = σ.id := rfl
  simp only [h1, h2, e, hid3, hcid, Bool.false_eq_true, ↓reduceIte]
  by_cases hc : toN m.replica = σ.id ∧ m.command.length = 1 ∧
      Option.map (fun x => x.op) m.command.head? = some opNONE
  · simp only [hc, and_self, ite_true]
    rcases hlb : w.lb with _ | lb
    · rfl
    · rcases hcp : lb.clientProposals with _ | ps <;> rfl
  · simp only [hc, ite_false]

/-- `updateConflicts` changes only the conflicts map, `lastScan`/`lastPut` and
`maxSeqPerKey`. -/
theorem updateConflicts_eq (σ : RState) (cmds : List WCmd) (q : Nat) (n seq : w32) :
    updateConflicts σ cmds q n seq =
      { σ with conflicts := (updateConflicts σ cmds q n seq).conflicts,
               lastScan := (updateConflicts σ cmds q n seq).lastScan,
               lastPut := (updateConflicts σ cmds q n seq).lastPut,
               maxSeqPerKey := (updateConflicts σ cmds q n seq).maxSeqPerKey } := by
  unfold updateConflicts
  induction cmds generalizing σ with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.foldl_cons]
    rw [ih]

/-- `updateConflicts`'s `lastScan`/`lastPut` depend only on them. -/
theorem updateConflicts_cls (σ σ' : RState) (cmds : List WCmd) (q : Nat) (n seq : w32)
    (h1 : σ.lastScan = σ'.lastScan) (h2 : σ.lastPut = σ'.lastPut) :
    (updateConflicts σ cmds q n seq).lastScan = (updateConflicts σ' cmds q n seq).lastScan ∧
    (updateConflicts σ cmds q n seq).lastPut = (updateConflicts σ' cmds q n seq).lastPut := by
  unfold updateConflicts
  induction cmds generalizing σ σ' with
  | nil => exact ⟨h1, h2⟩
  | cons c cs ih =>
    simp only [List.foldl_cons]
    apply ih
    · simp only [h1]
    · simp only [h2]

/-- `updateConflicts`'s maps depend only on the maps. -/
theorem updateConflicts_maps (σ σ' : RState) (cmds : List WCmd) (q : Nat) (n seq : w32)
    (h1 : σ.conflicts = σ'.conflicts) (h2 : σ.maxSeqPerKey = σ'.maxSeqPerKey) :
    (updateConflicts σ cmds q n seq).conflicts = (updateConflicts σ' cmds q n seq).conflicts ∧
    (updateConflicts σ cmds q n seq).maxSeqPerKey =
      (updateConflicts σ' cmds q n seq).maxSeqPerKey := by
  unfold updateConflicts
  induction cmds generalizing σ σ' with
  | nil => exact ⟨h1, h2⟩
  | cons c cs ih =>
    simp only [List.foldl_cons]
    apply ih
    · simp only [h1, h2]
    · simp only [h2]

theorem updateConflicts_take_succ (σ : RState) (cmds : List WCmd) (q : Nat) (n seq : w32)
    (k : Nat) (c : WCmd) (h : cmds[k]? = some c) :
    updateConflicts σ (cmds.take (k + 1)) q n seq =
      updateConflicts (updateConflicts σ (cmds.take k) q n seq) [c] q n seq := by
  unfold updateConflicts
  rw [List.take_succ, h]
  simp [List.foldl_append]

/-- `updateConflicts` on one command. -/
theorem updateConflicts_one (σ : RState) (c : WCmd) (q : Nat) (n seq : w32) :
    updateConflicts σ [c] q n seq =
      { σ with
        conflicts := upd σ.conflicts q (upd (σ.conflicts q) c.key (some
          (match σ.conflicts q c.key with
           | some p => ⟨if p.last.slt n then n else p.last,
                        if p.lastWrite.slt n ∧ c.op ≠ opGET then n else p.lastWrite⟩
           | none => ⟨n, if c.op ≠ opGET then n else W32 (-1)⟩))),
        lastScan := if c.op = opSCAN ∧ (σ.lastScan q).slt n then upd σ.lastScan q n
          else σ.lastScan,
        lastPut := if c.op = opPUT ∧ (σ.lastPut q).slt n then upd σ.lastPut q n
          else σ.lastPut,
        maxSeqPerKey := upd σ.maxSeqPerKey c.key (some
          (match σ.maxSeqPerKey c.key with
           | some s => if s.slt seq then seq else s
           | none => seq)) } := rfl

/-- `updateConflicts` touches only row `q` of the conflicts. -/
theorem updateConflicts_other_row (σ : RState) (cmds : List WCmd) (q q' : Nat) (n seq : w32)
    (h : q' ≠ q) : (updateConflicts σ cmds q n seq).conflicts q' = σ.conflicts q' := by
  unfold updateConflicts
  induction cmds generalizing σ with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.foldl_cons]
    rw [ih]; simp [upd, h]

theorem updateCommitted_eq (σ : RState) (q : Nat) :
    updateCommitted σ q = { σ with committedUpTo := (updateCommitted σ q).committedUpTo } := rfl

theorem advanceCommitted_dep (σ σ' : RState) (q : Nat) (h : σ.inst = σ'.inst) :
    ∀ fuel c, advanceCommitted σ q fuel c = advanceCommitted σ' q fuel c
  | 0, _ => rfl
  | fuel + 1, c => by
    simp only [advanceCommitted, h]
    rcases σ'.inst ⟨q, toN (c + 1)⟩ with _ | x
    · rfl
    · simp only
      split
      · exact advanceCommitted_dep σ σ' q h fuel _
      · rfl

theorem updateCommitted_dep (σ σ' : RState) (q : Nat) (h1 : σ.inst = σ'.inst)
    (h2 : σ.committedUpTo = σ'.committedUpTo) :
    (updateCommitted σ q).committedUpTo = (updateCommitted σ' q).committedUpTo := by
  simp only [updateCommitted, h2, advanceCommitted_dep σ σ' q h1]

theorem upd_upd {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b c : β) :
    upd (upd f a b) a c = upd f a c := by
  funext a'; unfold upd; split <;> rfl

/-- The state with only the committed record installed. -/
def commitIns (σ : RState) (m : Commit) : RState :=
  { σ with inst := upd σ.inst ⟨toN m.replica, toN m.inst⟩ (some (commitInst σ m)) }

/-- The committed path's final state, field by field. -/
theorem commitFinal_eq (σ : RState) (m : Commit) :
    updateCommitted (updateConflicts ((commitPre σ m).setInst ⟨toN m.replica, toN m.inst⟩
        (commitInst σ m)) m.command (toN m.replica) m.inst m.seq) (toN m.replica) =
      { σ with
        inst := upd σ.inst ⟨toN m.replica, toN m.inst⟩ (some (commitInst σ m)),
        crtInstance := (bumpCrt σ (toN m.replica) m.inst).crtInstance,
        maxRecvBallot := (bumpRecvBallot σ m.ballot).maxRecvBallot,
        conflicts := (updateConflicts σ m.command (toN m.replica) m.inst m.seq).conflicts,
        lastScan := (updateConflicts σ m.command (toN m.replica) m.inst m.seq).lastScan,
        lastPut := (updateConflicts σ m.command (toN m.replica) m.inst m.seq).lastPut,
        maxSeqPerKey := (updateConflicts σ m.command (toN m.replica) m.inst m.seq).maxSeqPerKey,
        committedUpTo := (updateCommitted (commitIns σ m) (toN m.replica)).committedUpTo } := by
  have hm := updateConflicts_maps ((commitPre σ m).setInst ⟨toN m.replica, toN m.inst⟩
    (commitInst σ m)) σ m.command (toN m.replica) m.inst m.seq rfl rfl
  have hl := updateConflicts_cls ((commitPre σ m).setInst ⟨toN m.replica, toN m.inst⟩
    (commitInst σ m)) σ m.command (toN m.replica) m.inst m.seq rfl rfl
  rw [updateCommitted_eq, updateConflicts_eq]
  simp only [hm.1, hm.2, hl.1, hl.2]
  simp [RState.setInst, commitPre, upd_upd]
  exact updateCommitted_dep _ _ _ (by simp [commitIns]) rfl

end model

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
