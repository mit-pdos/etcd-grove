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

It also owns `own_progresses r.trk.Progress` — the tracker's `Progress` map
and its contents. That is a separate heap object from the struct, so
`r ↦ rv` does not cover it, and `becomeLeader` writes to it. See the trust
boundary below.

### Proved (`Qed`)

- `wp_raft__send_vote` — the substantive one. A vote message reaches
  `r.msgs` (`MsgVote`) or `r.msgsAfterAppend` (`MsgVoteResp`) only if the
  caller already holds `is_message` for it.
- `wp_voteRespMsgType`.
- `mtype_of_MsgVote`, `mtype_of_MsgVoteResp`.
- The model-level composition lemmas `step_drop`,
  `step_stepdown_then_vote`, `step_stepdown_then_reject`,
  `step_record_then_win`, `step_record_then_lose`.
- `wp_raft__becomeFollower`, `wp_raft__becomeCandidate`,
  `wp_raft__becomeLeader` (all modulo `wp_raft__reset`, which is still
  admitted). Each is `reset` plus assignments to `lead`/`Vote`/`state`, and
  the postcondition is literally the model's role transition.
  `becomeCandidate`/`becomeLeader` also discharge the panic branch
  (`state ≠ StateLeader` / `≠ StateFollower`) from the role hypothesis, and
  `becomeLeader` additionally walks the tracker to mark its own `Progress`
  replicating and appends the empty entry.
- `wp_raft__Step_MsgHup` (modulo `wp_raft__hup`).
- `wp_raft__Step` — the top-level dispatch, from the three per-message-type
  theorems.
- `raft_election_safety`.

### Admitted, in rough order of what to do next

1. `wp_raft__Step_MsgVote` — **partially proved**. The term preamble, the
   lease check, both pre-vote arms, the step-down (with its
   `step_higher_term` ghost transition) and the `canVote` computation are
   done; it stops at the `isUpToDate` branch. See "Where it is stuck" below.
2. `wp_raft__reset` — the one the three `becomeX` proofs rest on. It is not
   mechanical: besides re-initialising every `Progress` through
   `trk.Visit` (which needs a `Visit` spec), it calls
   `resetRandomizedElectionTimeout` and `abortLeaderTransfer`, and it
   **replaces `r.readOnly` with a fresh `newReadOnly(...)`**. `own_raft_misc`
   is indexed by the old `readOnly` pointer, so finishing `reset` needs a
   `wp_newReadOnly` axiom that produces `own_raft_misc rs ro' pri` for the
   new one. That is a fine axiom to add — it is not the discredited
   `own_raft_misc rv -∗ own_raft_misc rv'` shape warned about below — but it
   is an addition, so decide it deliberately.
3. `wp_raft__poll`, `wp_raft__campaign`, `wp_raft__hup`.
4. `wp_stepCandidate_MsgVoteResp`, then `wp_raft__Step_MsgVoteResp`. This is
   the first caller of `wp_raft__becomeLeader`, so it is where the new
   `id ∈ cfg` hypothesis has to be discharged — a candidate that won an
   election is a voter, but nothing in `own_raft_phys` says so yet, so it
   will have to be threaded in from `hup`/`campaign` (which already have
   `id ∈ cfg`) or added to `own_raft_phys`.

### Trust boundary (`Section helper_axioms`)

Axiomatized because election does not reason about them: `own_raftLog` and
its four methods, `own_tracker` and `ResetVotes`/`RecordVote`/`TallyVotes`,
`promotable`, `hasUnappliedConfChanges`, the voter-id enumeration,
`is_Logger` + `wp_Logger__logf`, `own_raft_misc`, the five `traceX`
functions, and — added 2026-09-14 for `becomeLeader` — the per-peer
replication progress: `own_progresses`, `own_progress_rest`,
`wp_tracker_progress_lookup`, `wp_Progress__BecomeReplicate`.

Three deliberate choices there:

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
- The progress axioms are keyed on the **map reference** `r.trk.Progress`,
  not on the tracker location, and `own_progresses` is a conjunct of
  `own_raft_phys` rather than of `own_tracker`. The reason is the same
  "index it by what it actually covers" rule: `becomeLeader` reaches the map
  by reading the struct field (`map.lookup1 ... #(rv.trk.Progress) #id`), so
  an axiom keyed on the tracker location would have had to hand out
  `struct_field_ref ... "Progress" trk ↦ pm` — a field that `r ↦ rv`
  already covers. `own_progress` itself is a *definition*, not an axiom:
  it exposes the one field the code assigns to (`RecentActive`) as a real
  points-to and hides the rest behind `own_progress_rest`, because an
  inline field assignment cannot be stepped through an opaque predicate.
  `wp_tracker_progress_lookup` has an `i ∈ cfg` side condition (only voters
  are in the map), which is why `wp_raft__becomeLeader` now takes `id ∈ cfg`.

### A looseness in `own_raft_phys` worth knowing about

`own_raft_phys` holds **both** `r ↦ rv` — which covers the whole struct,
and `trk` is an embedded `tracker.ProgressTracker` *value*, not a pointer —
**and** `own_tracker (struct_field_ref raft.raft.t "trk" r)`. So the tracker's
bytes are claimed twice. Nothing detects this today because `own_tracker` is
an opaque axiom that need not own anything; but a real construction of
`own_tracker` that owns the `trk` field would make `own_raft_phys` provably
`False`, and every `Step` triple vacuous. Whoever discharges the tracker
axioms has to resolve this — either by having `own_tracker` own only the
parts of the field it needs and splitting `r ↦ rv` accordingly, or by
dropping `trk` from the `r ↦ rv` clause. (The same question does not arise
for `own_progresses`: the map and the `Progress` objects are separate heap
cells.)

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
