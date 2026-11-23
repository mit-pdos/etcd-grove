/-
Planned auxiliary conjuncts (prove phase, package `model`): the strengthenings the paper proof of
`chosenSafe`/`agreement` under recovery and the fast path needs (notes/prove-model.md, "Riskiest
step"), and the execution invariant `instDone`/`execCmd` need. Stated here so that they are
type-checked.

Status (second agent): the report facts of the last section are now the conjunct `Inv.reports`
(InvDefs.lean; `DecideProof.decAux_of` maps it to these names), and `Inv.safe` replaces the
`chosenSafe` strengthening. Superseded drafts: `paOnce` (by `paUnique`), `committedReported` +
`fastCommitFirst` (by `fastReported`), `slowExclFast` (by `accInit`, stable under steps). Still
planned (not in `Inv`): `prepReplyLast` (weakened to `reportAcc` for the decision; still the
natural form of `recLast`), `voteBallots` (derivable: `SafeProof.slowChosen_real`),
`paRecipients`, `lbValEq`, `crtBound`, `execReach`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.InvDefs

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

open github_com.imdea_software.swiftpaxos_epaxos.kvs

namespace Aux

/-- The instance a report is about. -/
def repX (m : PrepareReply) : InstId := ⟨toN m.replica, toN m.inst⟩

/-- A report (`PrepareReply` sent, or the recovering replica's own) reports the replica's *last*
vote before it: no vote of the replica for the instance lies between the reported vote and the
report; a NONE report has `vballot = -1` and no vote before it. (Strengthens
`repliesReportVotes`; needed when `maxVbal` is the chosen ballot `b`: the reply of a member of
`b`'s accept quorum is ACCEPTED, not an earlier PREACCEPTED vote at `b`.) -/
def prepReplyLast (S : Sys) : Prop :=
  ∀ r m e, S.prepReport r m e →
    (m.status = stNONE → zz m.vballot = -1) ∧
    ((isPA m.status ∨ m.status = stACCEPTED) →
      ∃ p pe : Nat, p < pe ∧
        S.hist[p]? = some (r, Event.vote (repX m) m.vballot m.status ⟨m.command, m.seq, m.deps⟩) ∧
        S.hist[pe]? = some (r, e) ∧
        ∀ q : Nat, p < q → q < pe → ∀ b st v, S.hist[q]? ≠ some (r, Event.vote (repX m) b st v))

/-- A replica that committed an instance before a report reports a committed status. -/
def committedReported (S : Sys) : Prop :=
  ∀ r m e, S.prepReport r m e → ∀ b v, S.evBefore r (.commit (repX m) b v) r e →
    isCommitted m.status

/-- A report's ballot is at most the replica's current `bal` (with `bal` monotone: the G1 fix). -/
def reportBal (S : Sys) : Prop :=
  ∀ r m e, r < nR → S.prepReport r m e →
    ∃ w, (S.rep r).inst (repX m) = some w ∧ zz m.ballot ≤ zz w.bal

/-- The leader's fast commit precedes all its reports for the instance. -/
def fastCommitFirst (S : Sys) : Prop :=
  ∀ x v m e, S.ev x.q (.fastCommit x v) → S.prepReport x.q m e → repX m = x →
    S.evBefore x.q (.fastCommit x v) x.q e

/-- Votes are at the initial ballot or at recovery ballots (`≥ N`). -/
def voteBallots (S : Sys) : Prop :=
  ∀ r x b st v, S.ev r (.vote x b st v) → b = initBal x ∨ (nR : Int) ≤ zz b

/-- At most one PREACCEPTED vote per (replica, instance, ballot), and a replica's PREACCEPTED
votes at a ballot precede its ACCEPTED votes at it. -/
def paOnce (S : Sys) : Prop :=
  (∀ r x b st st' v v', isPA st → isPA st' →
    S.ev r (.vote x b st v) → S.ev r (.vote x b st' v') → st = st' ∧ v = v') ∧
  (∀ r x b st v v', isPA st → S.evBefore r (.vote x b stACCEPTED v') r (.vote x b st v) → False)

/-- A non-leader's PREACCEPTED vote at a ballot follows the delivery to it of a PreAccept at that
ballot, from the ballot's proposer; at the initial ballot, PreAccepts go to at most `2F - 1`
distinct replicas. -/
def paRecipients (S : Sys) : Prop :=
  (∀ r x b st v, isPA st → S.ev r (.vote x b st v) → b = initBal x → r ≠ x.q →
    ∃ m : PreAccept, S.deliveredMsg x.q r (.preAccept m) ∧ m.ballot = b ∧
      (Msg.preAccept m).instOf = some x) ∧
  (∀ x (R : List Nat), R.Nodup →
    (∀ r ∈ R, ∃ m : PreAccept, Msg.preAccept m ∈ S.msgs x.q r ∧ m.ballot = initBal x ∧
      (Msg.preAccept m).instOf = some x) → R.length ≤ 2 * fR - 1)

/-- An Accept at the initial ballot (the leader's slow path) excludes the fast path's replies. -/
def slowExclFast (S : Sys) : Prop :=
  ∀ x w, S.ev x.q (.accept x (initBal x) w) → ∀ v, ¬ S.fastReplies x v

/-- An accepting bookkeeping and its accepting instance (not past its ballot) hold one value
(what makes `hAcceptReply`'s Commit carry its commit event's value: `commitMsgs`). -/
def lbValEq (S : Sys) : Prop :=
  ∀ r < nR, ∀ x w lb, (S.rep r).inst x = some w → w.lb = some lb →
    lb.status = stACCEPTED → w.status = stACCEPTED → zz w.bal ≤ zz lb.lastTriedBallot →
    w.cmds = lb.cmds ∧ w.seq = lb.seq ∧ w.deps = lb.deps

/-- Every replica's `crtInstance[q]` is at most `q`'s own, and every message about `⟨q, i⟩` has
`i ≤ crtInstance_q[q]`; `q` holds no instance of its row past it (so `hPropose`'s instance is
fresh). -/
def crtBound (S : Sys) : Prop :=
  (∀ r < nR, ∀ q < nR, zz ((S.rep r).crtInstance q) ≤ zz ((S.rep q).crtInstance q)) ∧
  (∀ fr to m x, m ∈ S.msgs fr to → m.instOf = some x → x.q < nR →
    (x.i : Int) ≤ zz ((S.rep x.q).crtInstance x.q)) ∧
  (∀ q < nR, ∀ i w, (S.rep q).inst ⟨q, i⟩ = some w → (i : Int) ≤ zz ((S.rep q).crtInstance q))

/-- Execution: what an executed instance reaches in the decided graph is executed, or is in the
component being executed, and then the executed instance is in that component's executed part. -/
def execReach (S : Sys) : Prop :=
  ∀ r < nR, ∀ y z, (S.rep r).executed y → Relation.TransGen S.dEdge y z →
    ¬ (S.rep r).executed z →
    z ∈ S.execCur r ∧ ∃ done C, sccSort (S.rep r) C = done ++ S.execCur r ∧ y ∈ done

/-! ### Report facts the recovery decision needs (`Proof/Decide.lean`, `DecAux`) -/

/-- A report's status is one a record can hold. -/
def reportStatus (S : Sys) : Prop :=
  ∀ r m e, S.prepReport r m e →
    m.status = stNONE ∨ isPA m.status ∨ m.status = stACCEPTED ∨ isCommitted m.status

/-- A NONE report has `vballot = -1`. -/
def reportNone (S : Sys) : Prop :=
  ∀ r m e, S.prepReport r m e → m.status = stNONE → zz m.vballot = -1

/-- A non-NONE report's deps have `N` entries. -/
def reportDeps (S : Sys) : Prop :=
  ∀ r m e, S.prepReport r m e → m.status ≠ stNONE → m.deps.length = nR

/-- A replica that voted ACCEPTED at a ballot at least the reported `vballot`, before the report,
reports ACCEPTED or committed (the record keeps its last vote's status). -/
def reportAcc (S : Sys) : Prop :=
  ∀ r m e, S.prepReport r m e → ∀ b u, S.evBefore r (.vote (repX m) b stACCEPTED u) r e →
    zz m.vballot ≤ zz b → m.status = stACCEPTED ∨ isCommitted m.status

/-- One pre-accept value per (replica, instance, ballot). -/
def paUnique (S : Sys) : Prop :=
  ∀ r x b st st' v v', isPA st → isPA st' → S.ev r (.vote x b st v) → S.ev r (.vote x b st' v') →
    v = v'

/-- A leader that fast-committed reports a committed status (its fast commit precedes all its
reports, and a committed record reports so). -/
def fastReported (S : Sys) : Prop :=
  ∀ x v m e, S.ev x.q (.fastCommit x v) → S.prepReport x.q m e → repX m = x → isCommitted m.status

/-- The leader's Accept at the initial ballot (its slow path) is made when no value can be
fast-chosen any more (`2F - 1` PreAccepts at most, and either at most `F` were sent or two
counted replies differ: thrifty counting). -/
def accInit (S : Sys) : Prop :=
  ∀ r x v, S.ev r (.accept x (initBal x) v) → ∀ w, S.fastBlocked x w

end Aux

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model
