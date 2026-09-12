# Leader-election refinement

What `new/proof/go_etcd_io/raft/v3_proof/election_protocol.v` and
`.../election.v` are, what they prove, what they assume, and what is left.

Added 2026-09-12. Both files are reached from `new/should_build.v`.

## The claim

`raft.Step`, run on an election message, moves the raft struct from a state
refining protocol state `s` to one refining `s'`, and `s → s'` is a transition
of the protocol state machine, justified only by messages that were
legitimately on the network. That is `wp_raft__Step` in `election.v`.

The payoff is `raft_election_safety`: two nodes whose ghost state says
"leader in term t" are the same node.

## Scope

Assumed throughout, in both files:

- no pre-vote (`r.preVote = false`),
- no check-quorum (`r.checkQuorum = false`),
- no proposals (no `MsgProp` is stepped),
- no read-only requests (no `MsgReadIndex`),
- no reconfiguration, no learners — the voter set `cfg` is a fixed
  section parameter,
- node ids are nonzero, and a `MsgVote`'s `Context` is readable and is not
  the `campaignTransfer` marker (leader transfer is out of scope).

Under these, the log contributes to election only through `isUpToDate`, and
that check can only make a node **decline** to vote. Declining is always
protocol-legal, so **the log does not appear in the protocol model at all**.
A node's protocol state is `(term, vote, lead, role, votes)`.

## `election_protocol.v` — the specification side

- `nstate.t` — abstract node state; `msg.t` / `mtype.t` — abstract messages
  (`Vote`, `VoteResp`, `App`, `Heartbeat`).
- `become_follower` / `become_candidate` / `become_leader` / `record_vote`
  mirror the Go code exactly. In particular `reset(term)` clears `Vote` only
  when the term actually changes, always clears `lead` and the vote tally;
  and `RecordVote` is first-write-wins.
- `step cfg id : nstate.t → list msg.t → nstate.t → list msg.t → Prop` is the
  transition relation. It is **reflexive and transitive by construction**
  (`step_refl`, `step_trans`) so that one Go function performing several
  protocol steps (e.g. `campaign` = become candidate *and* broadcast) still
  refines a single `step`.
- Ghost state (axiomatized): `own_raft_ghost γ id s`, `is_message γ m`, and
  the one refinement obligation
  `own_raft_ghost_step : step cfg id s recv s' sent → ([∗list] recv, is_message) -∗ own_raft_ghost γ id s ={⊤}=∗ own_raft_ghost γ id s' ∗ ([∗list] sent, is_message)`.
  Plus `is_leader` / `is_leader_unique` (election safety) and
  `own_raft_ghost_is_leader`.

Constructing these is the standard "authoritative map of node states + set of
sent messages, tied by an invariant" development; it is **not** done here.

## `election.v` — the implementation side

`own_raft_phys γ r id s` is full ownership of the `raft` struct at `r` in a
state refining `s`. The important clause is that **both** outgoing queues
(`r.msgs` and `r.msgsAfterAppend`) contain only messages `γ` certifies:
`is_phys_msg`. `send` is the only place a message reaches the network, so
that is where the obligation is discharged.

### Proved (`Qed`)

- `wp_raft__send_vote` — the substantive one. A vote message reaches
  `r.msgs` (`MsgVote`) or `r.msgsAfterAppend` (`MsgVoteResp`) only if the
  caller already holds `is_message` for it.
- `wp_voteRespMsgType`.
- `mtype_of_MsgVote`, `mtype_of_MsgVoteResp`.
- The model-level composition lemmas `step_drop`,
  `step_stepdown_then_vote`, `step_stepdown_then_reject`,
  `step_record_then_win`, `step_record_then_lose`.
- `wp_raft__Step_MsgHup` (modulo `wp_raft__hup`).
- `wp_raft__Step` — the top-level dispatch, from the three per-message-type
  theorems.
- `raft_election_safety`.

### Admitted, in rough order of what to do next

1. `wp_raft__Step_MsgVote` — **partially proved**. The term preamble, the
   lease check, both pre-vote arms, the step-down (with its
   `step_higher_term` ghost transition) and the `canVote` computation are
   done; it stops at the `isUpToDate` branch. See "Where it is stuck" below.
2. `wp_raft__reset`, `wp_raft__becomeFollower/Candidate/Leader` — mechanical;
   `reset` is the only one with real work (it re-inits every `Progress`).
3. `wp_raft__poll`, `wp_raft__campaign`, `wp_raft__hup`.
4. `wp_stepCandidate_MsgVoteResp`, then `wp_raft__Step_MsgVoteResp`.

### Trust boundary (`Section helper_axioms`)

Axiomatized because election does not reason about them: `own_raftLog` and
its four methods, `own_tracker` and `ResetVotes`/`RecordVote`/`TallyVotes`,
`promotable`, `hasUnappliedConfChanges`, the voter-id enumeration,
`is_Logger` + `wp_Logger__logf`, `own_raft_misc`, and the five `traceX`
functions.

Two deliberate choices there:

- `wp_Logger__logf` covers only the **non-panicking** methods
  (`log_methods`). `Panic`/`Panicf` do not return, so a path reaching one has
  to be shown unreachable rather than assumed away. (This is why
  `wp_raft__send_vote` needs `m.To ≠ id` for a `MsgVote`: `send` panics on a
  self-addressed non-response.)
- `own_raft_misc` is indexed by the three struct fields it actually covers
  (`readStates`, `readOnly`, `pendingReadIndexMessages`), not by the whole
  `raft.raft.t`. An earlier version indexed it by the struct and needed an
  `own_raft_misc rv -∗ own_raft_misc rv'` axiom to survive any field update —
  which is strong enough to be worthless. Do not reintroduce that.

## Where `wp_raft__Step_MsgVote` is stuck

At the `send` of the granted vote response. The ghost step
(`step_grant_vote`) goes through and produces
`is_message γ (msg.mk mtype.VoteResp id m.From m.Term false)`; the physical
message `send` is called with is the literal
`Message{To := m.From; Term := m.Term; Type := MsgVoteResp}`. These *should*
be the same after `iota`, but `iFrame` refuses to place the hypothesis into
`wp_raft__send_vote`'s `#Hm` slot, and it still refuses after the
precondition was restated in explicit `msg.mk` form rather than
`abs_msg ty (m <| From' := id |>)`.

Not diagnosed. Next thing to try: print the residual precondition goal (use
`wp_apply (... with "[Hphys Hgrant]")` so it becomes a separate goal) and
compare it against `Hgrant` term-by-term — the mismatch is probably in a
field that is *not* one of the five the eye is drawn to.

Note the goal order `wp_apply` produces here is
`[pure premises] [continuation] [resource]`, which is why putting `{ }`
blocks for the premises leaves you focused on the continuation with evars in
`Hphys`, not on the resource goal. That cost an hour; do not be fooled by it.

## Working on this file

`election.v` is ~900 lines and a cold check is ~3 minutes, so use
`rocq-warm` (<https://github.com/zeldovich/rocq-warm>): it keeps a `rocq
repl` warm and replays only from the edit onwards (1–20s in practice). See
[gotchas.md](gotchas.md) for the flags this repo needs.
