/-
Port of election_proof/protocol.v, lines 4495–6250 at feb5c73d4: the refinement
obligation one rule at a time, and the refinement obligation `ownRaftGhost_step`. (On
top of `Protocol/LeaderCompleteness.lean`; the protocol facts the code needs are
`Protocol/Facts.lean`.)

Lean notes:
* Proofs are skeletons: every lemma's proof that is not done is `sorry`, on the line
  after a `-- PORT: proof` marker.
* `own_raft_ghost_step_<rule>` is `ownRaftGhost_step_<rule>` (the rule part kept in
  Rocq's snake_case: `ownRaftGhost_step_app_accept`). Rocq `Local Lemma`s are public.
* `Forall P ms` is `∀ m ∈ ms, P m`; `s <| f := v |>` is `{ s with f := v }`; `imap` is
  `List.mapIdx`; `if decide P then` is `if P then`. Rocq's `let s' := … in` in
  `own_raft_ghost_step_propose`'s statement is inlined (as `Model.lean` does in
  `Step.propose`).
* The Rocq `Local Ltac`s `destruct_ghost`, `role_ok_tac`, `lead_ok_tac`,
  `follower_votes_tac` (proof automation) are kept as comments, for the proof-filling
  port to turn into macros.
-/
import EtcdGrove.Raft.ElectionProof.Protocol.LeaderCompleteness

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI GMap go_etcd_io.raft.v3

section ghost
variable [FfiSyntax]
variable {GF : BundledGFunctors} [AllG GF] [InvGS GF]

/-! ### The refinement obligation, one rule at a time

The election rules are proved inline in `ownRaftGhost_step`; the replication rules each
have a lemma here. -/

/- Rocq:
```
Local Ltac destruct_ghost :=
  iDestruct "Hown" as (γv voted kl)
    "(%Hname & %Hidnz & Hvoted & %Hhist & #Hfrags & #Hout & #Htally & #Hlead & Hlg & %Hlok & %Hfv & #Hvrecs & %Hrok)".
```
`RoleOk` of the state a rule produces: unchanged role, vote and leader, or a follower.
```
Local Ltac role_ok_tac :=
  first
    [ assumption
    | let H1 := fresh in let H2 := fresh in
      match goal with H : role_ok _ _ |- _ => pose proof H as [H1 H2] end;
      rewrite /role_ok /psend_msgs /padopt_leader /pbecome_follower /=; split; intros ?;
      first [ congruence | done | by apply H1 | by apply H2 ] ].
```
`LeadOk` of the state a rule produces: unchanged role and leader, or a leader, or a
follower with no leader / another node as leader.
```
Local Ltac lead_ok_tac :=
  first
    [ assumption
    | rewrite /lead_ok /=; intros Hr;
      first [ by exfalso; apply Hr | assumption | congruence ] ].
```
`FollowerVotesOk` of the state a rule produces, likewise.
```
Local Ltac follower_votes_tac :=
  first
    [ assumption
    | rewrite /follower_votes_ok /=; intros Hr; first [ done | congruence ] ].
```
-/

/-- `Step.win`: allocate the term log -- recording the candidate's base and log, and
holding the leader's entry -- and acknowledge the old and the new last index. -/
theorem ownRaftGhost_step_win (γ : RaftElectionNames) (id : w64) (s : PState)
    (mt : GMap w64 w64) (ms : List Msg) :
    s.role = .candidate →
    IsQuorum γ.reCfg (granted s.votes) →
    plogLastIndexZ s.base s.log + 1 < 2 ^ 64 →
    LeaderMatchOk id s mt →
    (∀ m ∈ ms, ReplOk id (pwinState id s mt) m) →
    ⊢ ownRaftGhost (GF := GF) γ id s ==∗
      ownRaftGhost γ id (psendMsgs (pwinState id s mt)
                           ([pselfAck id (pwinState id s mt)] ++ ms)) := by
  -- PORT: proof
  sorry

/-- `Step.beat`: a heartbeat carries the leadership, a commit index the leader has, and
the `Match` it is bounded by. -/
theorem ownRaftGhost_step_beat (γ : RaftElectionNames) (id : w64) (s : PState) (ms : List Msg) :
    s.role = .leader →
    (∀ m ∈ ms, HeartbeatOk id s m) →
    ⊢ ownRaftGhost (GF := GF) γ id s ==∗ ownRaftGhost γ id (psendMsgs s ms) := by
  -- PORT: proof
  sorry

/-- `Step.sendApps`: as `Step.win`'s broadcast. -/
theorem ownRaftGhost_step_send_apps (γ : RaftElectionNames) (id : w64) (s : PState)
    (ms : List Msg) :
    s.role = .leader →
    (∀ m ∈ ms, ReplOk id s m) →
    ⊢ ownRaftGhost (GF := GF) γ id s ==∗ ownRaftGhost γ id (psendMsgs s ms) := by
  -- PORT: proof
  sorry

/-- `Step.propForward`: a proposal carries nothing. -/
theorem ownRaftGhost_step_prop_forward (γ : RaftElectionNames) (id : w64) (s : PState) (m : Msg) :
    ⊢ ownRaftGhost (GF := GF) γ id s ==∗
      ownRaftGhost γ id
        (psendMsgs s
           [Msg.mk .propose id s.lead (W64 0) m.reject
              m.index m.logterm m.commit m.rejecthint
              m.entries]) := by
  -- PORT: proof
  sorry

/-- `Step.appResp`: the new `Match` is the old one or the acknowledgement the message
carries. -/
theorem ownRaftGhost_step_app_resp (γ : RaftElectionNames) (id : w64) (s : PState) (m : Msg)
    (x : w64) :
    m.ty = .appResp →
    m.term = s.term →
    s.role = .leader →
    m.reject = false →
    s.matched !! m.src = some x →
    ⊢ isMessage (GF := GF) γ m -∗
      ownRaftGhost γ id s ==∗
      ownRaftGhost γ id
        { s with matched :=
            <[m.src := if uint.Z x < uint.Z m.index
                       then m.index else x]> s.matched } := by
  -- PORT: proof
  sorry

/-- `Step.commit`: a quorum of `Match`es at least `n` is a commit fact `cq`, which extends
the global committed log (`commit_extend`, inside the invariant) -- the node's committed
prefix is then `isCommitted`. -/
theorem ownRaftGhost_step_commit (γ : RaftElectionNames) (id : w64) (s : PState) (n : w64) :
    s.role = .leader →
    uint.Z s.commit < uint.Z n →
    uint.Z n ≤ plogLastIndexZ s.base s.log →
    plogTermAt s.base s.log n = some s.term →
    IsQuorum γ.reCfg (ackedBy s n) →
    ⊢ ownRaftGhost (GF := GF) γ id s ={⊤}=∗ ownRaftGhost γ id { s with commit := n } := by
  -- PORT: proof
  sorry

/-- `Step.appStale`: back to follower of `m.src` in the same term, and acknowledge the
commit index -- which needs no justification. -/
theorem ownRaftGhost_step_app_stale (γ : RaftElectionNames) (id : w64) (s : PState) (m : Msg) :
    m.ty = .app →
    m.src ≠ id →
    m.term = s.term →
    s.role ≠ .leader →
    ⊢ isMessage (GF := GF) γ m -∗
      ownRaftGhost γ id s ==∗
      ownRaftGhost γ id
        (psendMsgs (padoptLeader s m.src)
           [Msg.mk .appResp id m.src s.term false s.commit
              (W64 0) (W64 0) (W64 0) []]) := by
  -- PORT: proof
  sorry

/-- `Step.appReject`: back to follower of `m.src`; a rejection carries nothing. -/
theorem ownRaftGhost_step_app_reject (γ : RaftElectionNames) (id : w64) (s : PState) (m : Msg)
    (hint hintterm : w64) :
    m.ty = .app →
    m.src ≠ id →
    s.role ≠ .leader →
    ⊢ isMessage (GF := GF) γ m -∗
      ownRaftGhost γ id s ==∗
      ownRaftGhost γ id
        (psendMsgs (padoptLeader s m.src)
           [Msg.mk .appResp id m.src s.term true m.index
              hintterm (W64 0) hint []]) := by
  -- PORT: proof
  sorry

/-- `Step.heartbeat`: back to follower of `m.src`; the new commit index is the old one or
the heartbeat's, which carries `isCommittedIdx` and which the rule's premise puts within
the log. -/
theorem ownRaftGhost_step_heartbeat (γ : RaftElectionNames) (id : w64) (s : PState) (m : Msg) :
    m.ty = .heartbeat →
    m.dst = id →
    m.term = s.term →
    m.src ≠ id →
    s.role ≠ .leader →
    uint.Z m.commit ≤ plogLastIndexZ s.base s.log →
    ⊢ isMessage (GF := GF) γ m -∗
      ownRaftGhost γ id s ==∗
      ownRaftGhost γ id
        (psendMsgs
           { padoptLeader s m.src with commit := plogCommitTo s.commit m.commit }
           [Msg.plain .heartbeatResp id m.src s.term false]) := by
  -- PORT: proof
  sorry

/-- `Step.appAccept`. The new log is the old one cut at the first conflict, if any, and
the batch appended (`plogMaybeAppend_inv`); the batch is the leader's (`isMessage`'s
`leadPrefix`). So the new log has records (the old ones below the cut; the leader's
above, whose predecessor terms are the batch's, which the new log has:
`plogMaybeAppend_batch`, `plog_prefix_batch`); every justified acknowledgement of this
term is below the cut (`ackAgree_term`: the old log agrees with the leader there, and
the cut is where it does not); and the new acknowledgement of `lastnewi` is justified by
the batch itself. -/
theorem ownRaftGhost_step_app_accept (γ : RaftElectionNames) (id : w64) (s : PState) (m : Msg)
    (lastnewi : w64) (es' : List raftpb.Entry) :
    m.ty = .app →
    m.src ≠ id →
    m.term = s.term →
    s.role ≠ .leader →
    uint.Z s.commit ≤ uint.Z m.index →
    plogMaybeAppend s.base s.log
      (entryID.mk m.logterm m.index) m.entries
      = some (lastnewi, es') →
    ⊢ isMessage (GF := GF) γ m -∗
      ownRaftGhost γ id s ==∗
      ownRaftGhost γ id
        (psendMsgs
           { padoptLeader s m.src with
               log := es',
               commit := plogCommitTo s.commit
                           (if uint.Z m.commit < uint.Z lastnewi
                            then m.commit else lastnewi) }
           [Msg.mk .appResp id m.src s.term false lastnewi
              (W64 0) (W64 0) (W64 0) []]) := by
  -- PORT: proof
  sorry

/-- Freezing a batch of stamped entries into the leader's term log: their indices are
past everything in it (`leadLogOwn`'s bound) and do not wrap. Each is frozen with the
predecessor term `ptf k`. -/
theorem term_log_insert_stamped (γt : GName) (M : GMap w64 (raftpb.Entry × w64)) (T : w64)
    (L : Int) (ents : List raftpb.Entry) (ptf : Nat → w64) :
    0 ≤ L → L + (ents.length : Int) < 2 ^ 64 →
    (∀ i, (M !! i).isSome → uint.Z i ≤ L) →
    ⊢ ghostMapAuth (GF := GF) γt 1 M -∗ ([∗map] i ↦ e ∈ M, i ↪[γt]□ e) ==∗
      ∃ M' : GMap w64 (raftpb.Entry × w64),
        ghostMapAuth γt 1 M' ∗ ([∗map] i ↦ e ∈ M', i ↪[γt]□ e) ∗
        ⌜∀ i, (M' !! i).isSome → uint.Z i ≤ L + (ents.length : Int)⌝ ∗
        [∗list] k ↦ e ∈ ents.mapIdx (stamp T (W64 L)),
          e.Index' ↪[γt]□ ((e, ptf k) : raftpb.Entry × w64) := by
  -- PORT: proof
  sorry

/-- `Step.propose`: the stamped entries go into the leader's term log
(`term_log_insert_stamped`), which gives each its `isEntryR` (the first after the old
last entry, the rest after each other); the self-acknowledgement is the node's own to
allocate. (Rocq's `let s' := pappend s (imap …) in` is inlined.) -/
theorem ownRaftGhost_step_propose (γ : RaftElectionNames) (id : w64) (s : PState)
    (ents : List raftpb.Entry) :
    s.role = .leader →
    plogLastIndexZ s.base s.log + (ents.length : Int) < 2 ^ 64 →
    ⊢ ownRaftGhost (GF := GF) γ id s ==∗
      ownRaftGhost γ id
        (psendMsgs (pappend s (ents.mapIdx (stamp s.term (plastIndex s))))
          [pselfAck id (pappend s (ents.mapIdx (stamp s.term (plastIndex s))))]) := by
  -- PORT: proof
  sorry

/-- `Step.snapStale`: back to follower of `m.src`, acknowledging the commit index --
`Step.appStale`'s update. -/
theorem ownRaftGhost_step_snap_stale (γ : RaftElectionNames) (id : w64) (s : PState) (m : Msg) :
    m.ty = .snap →
    m.src ≠ id →
    m.term = s.term →
    s.role ≠ .leader →
    ⊢ isMessage (GF := GF) γ m -∗
      ownRaftGhost γ id s ==∗
      ownRaftGhost γ id
        (psendMsgs (padoptLeader s m.src)
           [Msg.mk .appResp id m.src s.term false s.commit
              (W64 0) (W64 0) (W64 0) []]) := by
  -- PORT: proof
  sorry

/-- `Step.snapFastfwd`: the new commit index is the snapshot's, which the message carries
the commit fact for and the log reaches (it has the snapshot's last entry, which the
leader's log has too). -/
theorem ownRaftGhost_step_snap_fastfwd (γ : RaftElectionNames) (id : w64) (s : PState) (m : Msg) :
    m.ty = .snap →
    m.src ≠ id →
    m.term = s.term →
    s.role ≠ .leader →
    uint.Z s.commit < uint.Z m.index →
    PlogMatches s.base s.log
      (entryID.mk m.logterm m.index) →
    ⊢ isMessage (GF := GF) γ m -∗
      ownRaftGhost γ id s ==∗
      ownRaftGhost γ id
        (psendMsgs
           { padoptLeader s m.src with commit := m.index }
           [Msg.mk .appResp id m.src s.term false m.index
              (W64 0) (W64 0) (W64 0) []]) := by
  -- PORT: proof
  sorry

/-- `Step.snapRestore`: the log is replaced by the snapshot -- no entries after the new
base, so no records to keep; the compacted prefix is the leader's full log up to the
snapshot -- and the commit index becomes the snapshot's, which the message carries the
commit fact for. No justified acknowledgement of this term is above the snapshot: the
log would then agree with the leader at the snapshot's index (`ackAgree_term`), where
the leader has the snapshot's last entry -- but the rule's premise is that the log does
not have it. Histories move to the leader's log (`hist_replace`), which disagrees with
the old log at the snapshot's index. -/
theorem ownRaftGhost_step_snap_restore (γ : RaftElectionNames) (id : w64) (s : PState) (m : Msg) :
    m.ty = .snap →
    m.src ≠ id →
    m.term = s.term →
    s.role ≠ .leader →
    uint.Z s.commit < uint.Z m.index →
    ¬ PlogMatches s.base s.log
        (entryID.mk m.logterm m.index) →
    ⊢ isMessage (GF := GF) γ m -∗
      ownRaftGhost γ id s ==∗
      ownRaftGhost γ id
        (psendMsgs
           { padoptLeader s m.src with
               base := entryID.mk m.logterm m.index,
               log := [],
               commit := m.index }
           [Msg.mk .appResp id m.src s.term false m.index
              (W64 0) (W64 0) (W64 0) []]) := by
  -- PORT: proof
  sorry

/-! ### The refinement obligation -/

theorem ownRaftGhost_step (γ : RaftElectionNames) (id : w64) (s : PState) (recv : List Msg)
    (s' : PState) :
    Step γ.reCfg id s recv s' →
    ⊢ ([∗list] m ∈ recv, isMessage (GF := GF) γ m) -∗
      ownRaftGhost γ id s ={⊤}=∗
      ownRaftGhost γ id s' := by
  -- PORT: proof
  sorry

end ghost

end EtcdGrove
end Perennial
