# Leader-election refinement

What `new/proof/go_etcd_io/raft/v3_proof/election_protocol.v` and
`.../election/` are, what they prove, what they assume, and what is left.

Added 2026-09-12. Restructured 2026-09-14 into one file per Go function — see
[raft-proof-map.md](raft-proof-map.md) for the file layout and
[decisions.md](decisions.md) for why. All of it is reached from
`new/should_build.v`.

**Where a spec lives.** Exactly one place per function:
`v3_proof/election/spec_<fn>.v`, holding one `Parameter`. If you find
yourself about to write a second Hoare triple for a function that already has
one, don't — see the `Step` note in [decisions.md](decisions.md).

## The claim

`raft.Step`, run on an election message, moves the raft struct from a state
refining protocol state `s` to one refining `s'`, and `s → s'` is a transition
of the protocol state machine, justified only by messages that were
legitimately on the network. That is `Step.wp_raft__Step`, specified in
`election/spec_raft__Step.v`.

The payoff is `raft_election_safety`: two nodes whose ghost state says
"leader in term t" are the same node.

## Scope

Assumed throughout:

- no pre-vote (`r.preVote = false`),
- no check-quorum (`r.checkQuorum = false`),
- no proposals (no `MsgProp` is stepped),
- no read-only requests (no `MsgReadIndex`),
- no reconfiguration, no learners — the voter set `cfg` is a fixed
  parameter (a section variable in `election_protocol.v`; an explicit binder
  on every `wp_*_body` since 2026-09-14),
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

## `election/` — the implementation side

`own_raft_phys γ r id s` is full ownership of the `raft` struct at `r` in a
state refining `s`. The important clause is that **both** outgoing queues
(`r.msgs` and `r.msgsAfterAppend`) contain only messages `γ` certifies:
`is_phys_msg`. `send` is the only place a message reaches the network, so
that is where the obligation is discharged.

The `r ↦ rv` clause covers the whole struct, `trk` included — `trk` is an
embedded `tracker.ProgressTracker` *value*, not a pointer. So `own_tracker`
must not claim those bytes as well; it is indexed by the tracker **value**
and owns only the heap that hangs off it. See the trust boundary below.

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
- `Step`: the top-level dispatch, and its `MsgHup` branch (modulo
  `wp_raft__hup`).  The three per-message-type branches are internal lemmas
  of `proof_raft__Step.v`, not separate specs — `Step` is one Go function
  and has one `Module Type`.
- `raft_election_safety`.

### Admitted, in rough order of what to do next

Each is one `proof_*.v` file; `make <that file>.vok` re-checks it in about a
minute. (`make <file>.vos` is a 2-second loop but **does not check proof
bodies** — it will accept a script that does not run.)

1. The `MsgVote` branch, now `Lemma wp_Step_MsgVote` inside
   `proof_raft__Step.v` — **partially proved**. The term preamble, the
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
4. `wp_stepCandidate_MsgVoteResp`, then the `MsgVoteResp` branch in
   `proof_raft__Step.v`. `stepCandidate` is the first caller of
   `wp_raft__becomeLeader`, so it is where the `id ∈ cfg` hypothesis has to be
   discharged — a candidate that won an election is a voter, but nothing in
   `own_raft_phys` says so. **Its spec already takes `id ∈ cfg`** (added
   2026-09-14, because inside a proof functor there is no ambient `cfg` to
   reach for), so the obligation is now on its callers: thread it in from
   `hup`/`campaign`, which already have it, or add it to `own_raft_phys`.

### Trust boundary (the `inv_*.v` files)

Since 2026-09-14 the trust base is split structurally, and the split is the
audit story:

- an **`Axiom` in an `inv_*.v` file** means *out of scope* — election does not
  reason about it and never will;
- an **`Admitted` in a `proof_*.v` file** means *in scope but unfinished*;
- a **`Parameter` in a `spec_*.v` file is neither**. It is a proof obligation
  discharged by the functor ascribed to that signature, and contributes
  nothing to `Print Assumptions`. `./etc/tcb-view.py` counts these separately;
  its `--self-check` enforces that every `spec_*.v` has exactly one and
  assumes nothing.

The out-of-scope list (was `Section helper_axioms`, now the `inv_*.v` files):

Axiomatized because election does not reason about them: `own_raftLog` and
its four methods, `own_tracker` and `ResetVotes`/`RecordVote`/`TallyVotes`,
`promotable`, `hasUnappliedConfChanges`, the voter-id enumeration,
`is_Logger` + `wp_Logger__logf`, `own_raft_misc`, the five `traceX`
functions, and — added 2026-09-14 for `becomeLeader` — the per-peer
replication progress: `own_progress_rest`, `wp_tracker_progress_lookup`,
`wp_Progress__BecomeReplicate`.

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
- **`own_tracker` is indexed by the tracker `ProgressTracker.t` *value*,
  not by its location** — same rule again. `trk` is embedded in the raft
  struct by value, so its bytes are already in the `r ↦ rv` clause of
  `own_raft_phys`; `own_tracker tv votes` owns only what `tv` points *at*:
  the map at `tv.Votes`, the map at `tv.Progress` and the `Progress` objects
  in it, and the id sets of `tv.Config`. That makes it disjoint from
  `r ↦ rv` by construction rather than by hope. See "the duplication that
  was there until 2026-09-14" below for what this replaced.

  Consequences to know when using the tracker specs:

  - A method that *mutates* the tracker also needs its location, so
    `ResetVotes` / `RecordVote` / `TallyVotes` take `trk ↦ tv` alongside
    `own_tracker tv votes`. `ResetVotes` assigns a fresh map to `p.Votes`,
    so it returns `trk ↦ (tv <| Votes' := votesRef |>)` and an
    `own_tracker` at the new value; the other two return `tv` unchanged.
  - A caller holding the whole struct splits that one field out with
    `iEval (rewrite typed_pointsto_unseal /typed_pointsto_wrap /=) in "Hr"`,
    which turns `r ↦ rv` into the named conjunction of its field points-tos
    (that *is* the definition — see the `TypedPointsto` instance in
    `new/generatedproof/go_etcd_io/raft/v3.v`). `wp_auto` does not need this;
    it reads and writes fields through the whole-struct points-to using the
    generated `AccessStrict` instances. Only an explicit `wp_apply` of a
    lemma that wants `trk ↦ tv` does.
  - `wp_raft__promotable` and `wp_campaign_peer_ids` are now stated against
    the struct and the tracker value they actually read, instead of against
    unrelated parameters. `wp_campaign_peer_ids`'s receiver is
    `trk.[ProgressTracker.t, "Config"].[Config.t, "Voters"]`, which is what
    `campaign` calls `IDs` on.
- `own_progress` is a *definition*, not an axiom: it exposes the one field
  the code assigns to (`RecentActive`) as a real points-to and hides the
  rest behind `own_progress_rest`, because an inline field assignment cannot
  be stepped through an opaque predicate.
  `wp_tracker_progress_lookup` takes `own_tracker tv votes`, reads the map
  reference out of `tv`, and hands back one `Progress` plus the wand to put
  it back. Its `i ∈ cfg` side condition (only voters are in the map) is why
  `wp_raft__becomeLeader` takes `id ∈ cfg`.

### The duplication that was there until 2026-09-14

Worth recording because the shape is easy to reintroduce. `own_tracker` used
to be indexed by a **location**, and `own_raft_phys` instantiated it at
`struct_field_ref raft.raft.t "trk" r` while *also* holding `r ↦ rv`. Since
`trk` is embedded by value, `r ↦ rv` unfolds to a conjunction that includes
`r.[raft.raft.t, "trk"] ↦ rv.(trk')` — so the tracker's bytes were claimed
twice. Nothing detected it, because `own_tracker` was an opaque axiom that
need not own anything; but any real construction of `own_tracker` that owned
the field would have made `own_raft_phys` provably `False` and every `Step`
triple vacuous. The same axiom set also used one `loc` as both "the tracker"
(in `own_tracker trk votes`) and "the tracker's `Voters` field" (as the
`*quorum.JointConfig` receiver of `IDs`), which cannot both be true.

Re-indexing by the value fixed all of it and removed a conjunct from
`own_raft_phys`: the separate `own_progresses` predicate that the
`becomeLeader` proof had needed is now just part of `own_tracker`.

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

## Working on these files

Since the split there is no big file to re-check: each function is its own
`proof_*.v`, and `make <it>.vok` is about a minute. That is the main practical
payoff of the layout — the monolithic `election.v` took upwards of twelve.

- `make <file>.vos` — ~2s, checks statements, signatures and module structure.
  **It does not check proof bodies**, so it will happily accept a proof script
  that does not run. Never finish on a `.vos` alone.
- `make <file>.vok` — the real check, against `.vos` dependencies.
- Do **not** reach for `.vo`: nothing in the tree has `.vo` dependencies, so
  `make x.vo` starts building all of Perennial.
- `rocq-warm` (<https://github.com/zeldovich/rocq-warm>) still helps for a
  long single proof; see [gotchas.md](gotchas.md) for the flags this repo
  needs.

### Things that bite in this layout

- **`Collection W` is section-scoped, the `Set` that names it is not.** A
  closed lemma after `End <section>` fails with `Unknown variable: W`.
  `proof_raft__Step.v` restores `Set Default Proof Using "Type"` after its
  section for exactly this reason.
- **Implicits are not inferred through a folded `_body`**, so every
  `link_*.v` ends with `Arguments <Fn>.wp_<fn> {_ _ _ _ _ _ _ _}.` Without it
  a call site fails with `The term "..." has type "w32" while it is expected
  to have type "ffi_syntax"`. Putting the `Arguments` in the `Module Type`
  is accepted but does **not** survive functor application.
- **`Require` is illegal inside a `Module` or `Section`**, and `Import` does
  not reach the proof file — a spec needing `New.proof.bytes` (for
  `wp_Equal`) must `Require Export` it.
- **A `_POSTULATES` includes only *direct* callees.** Include another
  `_POSTULATES` and you get `Error: The label ... is already declared`,
  because `reset` is reached from `Step` by two different routes.
