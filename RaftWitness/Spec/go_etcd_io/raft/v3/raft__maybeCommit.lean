/- Port of election_proof/spec_raft__maybeCommit.v (feb5c73d4).

Lean notes: Rocq's `commit_ok` (a Prop-valued definition) is `CommitOk`.
-/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.InvRaftPhys
public import RaftWitness.Spec.go_etcd_io.raft.v3.raft__sendAppendToWitness
public import RaftWitness.Spec.go_etcd_io.raft.v3.tracker.ProgressTracker__OneLessThanQuorumInReplicationSet

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section commit_ok
variable [FfiSyntax]

/-- `CommitOk cfg ps n`: a leader in protocol state `ps` may advance its commit index to
`n` -- exactly the premises of the model's `Step.commit` other than the role: `n` is
past the current commit index and inside the log, the entry there is of the leader's
own term, and a quorum of voters has acknowledged `n` (`ackedBy`, over `matched`).
Shared with `Spec/stepLeader.lean`. -/
def CommitOk (cfg : GSet w64) (ps : PState) (n : w64) : Prop :=
  uint.Z ps.commit < uint.Z n ∧
  uint.Z n ≤ plogLastIndexZ ps.base ps.log ∧
  plogTermAt ps.base ps.log n = some ps.term ∧
  IsQuorum cfg (ackedBy ps n)

/-- `CommitOk` at a joint configuration (2026-10-13, reconfiguration stage A2): the premises
of `StepC.commit` other than the role, a joint quorum (`JQuorum`) acknowledging `n`. -/
def CommitOkC (c : CfgM) (ps : PState) (n : w64) : Prop :=
  uint.Z ps.commit < uint.Z n ∧
  uint.Z n ≤ plogLastIndexZ ps.base ps.log ∧
  plogTermAt ps.base ps.log n = some ps.term ∧
  JQuorum c (ackedBy ps n)

/-- At a simple configuration with voters, `CommitOkC` is `CommitOk`. -/
theorem CommitOkC.simple {cfg lrn : GSet w64} {ps : PState} {n : w64} (hne : cfg ≠ ∅)
    (h : CommitOkC (CfgM.simple cfg lrn) ps n) : CommitOk cfg ps n :=
  ⟨h.1, h.2.1, h.2.2.1, (JQuorum_of_out (c := CfgM.simple cfg lrn) hne rfl _).1 h.2.2.2⟩

/-- A request `maybeCommit` sends the witness (2026-10-20, witness support): to a witness `w` the
tracker reports (`OneLessThanQuorumInReplicationSet`: `OltqOk`, at the configuration `c`, the
node's epoch and peers) with the index `i`, nonzero, of an entry of the log of the leader's term
and the epoch's subterm (`raftLog.subterm`), with the halves' non-witness voters
(`sendAppendToWitness`). -/
def WAppSent (c : CfgM) (id : w64) (s : NState) (m : Msg) : Prop :=
  ∃ (w i : w64) (e : EntryM) (vs0 vs1 : List w64) (res : GMap w64 w64),
    m = wAbs (wappMsg id w s.term s.ep.sub i vs0 vs1) ∧
    ¬ OltqNone s.ep ∧ OltqOk c.incoming c.outgoing s.ep s.prvals res ∧ res !! w = some i ∧
    i ≠ W64 0 ∧
    plogEntryAt s.logst.prev (s.logst.sents ++ s.logst.uents) i = some e ∧
    e.Term' = s.term ∧ e.Subterm' = s.ep.sub ∧
    vs0 ≡ₚ GMap.elements s.ep.rs0.nwv ∧ vs1 ≡ₚ GMap.elements s.ep.rs1.nwv

end commit_ok

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `r.maybeCommit()` (`raft.maybeCommit.impl`, `Code/go_etcd_io/raft/v3.lean`;
`raft.go:773`):

    defer traceCommit(r)
    return r.raftLog.maybeCommit(entryID{term: r.Term, index: r.trk.Committed()})

`Committed()` is the quorum index of the voters' `Match` values
(`Spec/ProgressTracker__Committed.lean`); `raftLog.maybeCommit` moves `committed` there
when it is ahead, the term is non-zero and the log has `r.Term` at that index
(`Spec/raftLog__maybeCommit.lean`). The deferred `traceCommit` is a no-op.

On `true` the new commit index `N` satisfies `CommitOk` at the protocol reading of `s`:
that is `Step.commit`. The quorum is stated over `toPState s`'s `matched`, which is the
`Progress` `Match` values only for a leader -- hence `s.role = .leader`; the go code
says "This can only be called in StateLeader". `id ∈ cfg` makes the voter set
non-empty, which is what makes `Committed()` a quorum index (for an empty configuration
it is `MaxUint64`). On `false` nothing changes.

At any configuration since 2026-10-13 (reconfiguration stage A2): `CommitOkC`, a joint quorum
of the two voter halves, with no premise on the voters (an empty half has committed
everything, `MajQ`). The old statement (`id ∈ cfg`, `CommitOk cfg`) was
`raft.maybeCommit.specS`; it had no caller and is gone (2026-10-17).

(2026-10-20, witness support) First, to each witness `OneLessThanQuorumInReplicationSet`
reports, the entry at its index if it is of the leader's term and subterm
(`sendAppendToWitness`): the requests' readings `ws` are on the outbox, each a `WAppSent`, none
without a witness. -/
abbrev raft.maybeCommit.spec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState),
  s.role = .leader →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"maybeCommit")) (Val #()))
  {{ (b : Bool) (N : w64) (ws : List Msg), RET #b;
      ownRaftPhysCV c c.voters r id
        (if b then { sendMsgs s ws with logst := { s.logst with committed := N } }
         else sendMsgs s ws) ∗
      ⌜(∀ m ∈ ws, WAppSent c id s m) ∧ (c.wit = W64 0 → ws = []) ∧
        (b = true → CommitOkC c (toPState s) N)⌝ }}

end spec

end EtcdGrove
end Perennial
