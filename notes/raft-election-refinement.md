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
- `step cfg id : nstate.t → list msg.t → nstate.t → Prop` is the transition
  relation. It is **reflexive and transitive by construction** (`step_refl`,
  `step_trans`) so that one Go function performing several protocol steps
  (e.g. `campaign` = become candidate *and* broadcast) still refines a single
  `step`.
- **A step has no `sent` output.** `nstate.t` has an `outbox : list msg.t`
  field, and the messages a step sends are the growth of
  `s'.(nstate.outbox)`. `step_drain` lets a node drop messages from its own
  outbox, which is what `Ready()` will do; without it the outbox could only
  grow and `own_raft_phys` could not refine past the first drain.
- Ghost state (axiomatized): `own_raft_ghost γ id s`, `is_message γ m`, the
  refinement obligation
  `own_raft_ghost_step : step cfg id s recv s' → ([∗list] recv, is_message) -∗ own_raft_ghost γ id s ={⊤}=∗ own_raft_ghost γ id s'`,
  and `own_raft_ghost_outbox : own_raft_ghost γ id s -∗ [∗list] m ∈ s.(nstate.outbox), is_message γ m`.
  Plus `is_leader` / `is_leader_unique` (election safety) and
  `own_raft_ghost_is_leader`.

Constructing these is the standard "authoritative map of node states + set of
sent messages, tied by an invariant" development; it is **not** done here.

## `election/` — the implementation side

`own_raft_phys r id s` is full ownership of the `raft` struct at `r` in a
state refining `s`. **There is no `γ`: it says nothing about ghost state.**

### The rule: no function below `Step` touches ghost state

A spec below `Step` says only which state the struct now refines and how the
outbox grew — never that the transition is *legal*. Note what
`wp_raft__becomeLeader` does **not** claim: `step_win` requires
`is_quorum (granted s.votes)`, and that hypothesis appears nowhere in its
triple. Legality is discharged above.

`own_raft_ghost` therefore appears in exactly one spec, `spec_raft__Step.v`,
and `own_raft_ghost_step` is applied in exactly one proof file,
`proof_raft__Step.v`. If you find yourself adding `own_raft_ghost` to an
internal spec, something is being certified in the wrong place —
see [decisions.md](decisions.md) for the version of this that got it wrong,
and why.

### How the outbox is related to the two queues

`send` routes vote *responses* to `r.msgsAfterAppend` and everything else to
`r.msgs`; the model has one outbox, so `own_raft_phys` relates it to both:

    ⌜ s.(nstate.outbox) ≡ₚ abs_outbox msgs msgsAA ⌝

with `abs_outbox msgs msgsAA := omap abs_msg_opt msgs ++ omap abs_msg_opt msgsAA`.
Two choices to know about:

- **`omap` with a *partial* `abs_msg_opt`.** A message type the model does not
  describe drops out instead of making the abstract outbox undefined. Do not
  make `abs_msg_opt` total — `appendEntry` queues a `MsgAppResp`, which has no
  `mtype_of`, and the whole point is that it is invisible here.
- **`≡ₚ`, not `=`.** Appending to `msgs` does not append to the concatenation
  when `msgsAA` is non-empty, so equality would not survive a `send`.
  Permutation is also all the model needs. Helpers for this live in `defs.v`
  (`abs_outbox_snoc_msgs`, `abs_outbox_snoc_msgsAA`,
  `abs_outbox_snoc_msgsAA_None`).

A caller that needs to know a *pending outgoing* message is protocol-legal
reads that off `own_raft_ghost` with `own_raft_ghost_outbox`, not off
`own_raft_phys`.

The `r ↦ rv` clause covers the whole struct, `trk` included — `trk` is an
embedded `tracker.ProgressTracker` *value*, not a pointer. So `own_tracker`
must not claim those bytes as well; it is indexed by the tracker **value**
and owns only the heap that hangs off it. See the trust boundary below.

### Proved (`Qed`)

- `wp_raft__send_vote` — the substantive one, and the file that validates the
  `omap`/`≡ₚ` encoding above. A vote message reaches `r.msgs` (`MsgVote`) or
  `r.msgsAfterAppend` (`MsgVoteResp`); either way the abstract outbox grows by
  exactly that one message, so the spec is routing-agnostic and ghost-free.
- `wp_voteRespMsgType`.
- `mtype_of_MsgVote`, `mtype_of_MsgVoteResp`.
- The model-level composition lemmas `step_drop`,
  `step_stepdown_then_vote`, `step_stepdown_then_reject`,
  `step_record_then_win`, `step_record_then_lose`.
- `wp_raft__becomeFollower`, `wp_raft__becomeCandidate`,
  `wp_raft__becomeLeader`. Each is `reset` plus assignments to
  `lead`/`Vote`/`state`, and
  the postcondition is literally the model's role transition.
  `becomeCandidate`/`becomeLeader` also discharge the panic branch
  (`state ≠ StateLeader` / `≠ StateFollower`) from the role hypothesis, and
  `becomeLeader` additionally walks the tracker to mark its own `Progress`
  replicating and appends the empty entry.
- `wp_raft__reset` (2026-09-16) — see "How `reset` was proved" below.
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
2. — `wp_raft__reset` was here; **proved 2026-09-16**, see "How `reset` was
   proved" below.
3. `wp_raft__poll`, `wp_raft__campaign`, `wp_raft__hup`.
4. `wp_stepCandidate_MsgVoteResp`, then the `MsgVoteResp` branch in
   `proof_raft__Step.v`. `stepCandidate` is the first caller of
   `wp_raft__becomeLeader`, so it is where the `id ∈ cfg` hypothesis has to be
   discharged — a candidate that won an election is a voter, but nothing in
   `own_raft_phys` says so. **Its spec already takes `id ∈ cfg`** (added
   2026-09-14, because inside a proof functor there is no ambient `cfg` to
   reach for), so the obligation is now on its callers: thread it in from
   `hup`/`campaign`, which already have it, or add it to `own_raft_phys`.

### How `reset` was proved (2026-09-16)

Worth recording because it is the first proof that drives `trk.Visit`, and
because two of its three obstacles are reusable.

1. **The term branch.** The Go code tests `r.Term != term`, the model's
   `reset` keeps the vote exactly when the term is unchanged. The proof
   case-splits on `decide (term = s.(nstate.term))` and derives the value of
   `bool_decide (rv.(Term') = term)` from it. The two arms are spelled out in
   full rather than shared: they differ in the struct value (the second sets
   `Term'` and `Vote'`) and in the final pure goals, and everything that
   would let them be shared — a `Local Ltac`, a local lemma over the tail
   code — needs the frame's own names (`r`, `r_ptr`, `rv`), which Ltac1
   resolves at *definition* time and therefore cannot see.
2. **`Visit`'s caller invariant is the whole struct.** The closure reads
   `r.raftLog`, `r.trk.MaxInflight`, `r.trk.MaxInflightBytes` and `r.id`, all
   through the pointer *frame slot* the enclosing function allocated, so

       I := r_ptr ↦ r ∗ r ↦ rv' ∗ own_raftLog rv'.(raftLog')

   — note `r_ptr ↦ r`, which is easy to forget. This is exactly why
   `wp_ProgressTracker__Visit` must not ask for `trk ↦ tv`: `r ↦ rv'`
   already covers those bytes. `own_progress`'s whole-value shape is what
   lets the closure's `*pr = Progress{...}` go through, and the old
   `Inflights` object is simply dropped (the Go code leaks it too).
3. **The `trk` field could not be pulled out with the generated instance.**
   `raft_access_store_trk` fixes the field's *new* value up front, but
   `ResetVotes` only names it (`votesRef`) in its postcondition — after the
   evar for it was created, hence out of scope. `proof_raft__reset.v` adds a
   local `raft_split_trk` that hands back a ∀-quantified wand instead. Both
   this and the `iNamed`-after-unsealing correction are in
   [gotchas.md](gotchas.md).

One question the work settled: **a Goose closure literal unifies with a spec's
`#f`** with no help. `λ: "id" "pr", …` steps by the `wp_recc` pure rule to
`#(func.mk <> "id" (λ: "pr", …))`, which is literally an `IntoVal` of a
`func.t`, so `wp_apply` matches it against `visit_closure f I` directly.

`wp_newReadOnly` did **not** have to be added: it was already in
`inv_misc.v`, as an `Admitted` `Lemma` alongside `own_raft_misc_option`.

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

Plus `wp_raft__appendEmptyEntry`, which since 2026-09-15 lives in
`inv_raft_phys.v` rather than `inv_misc.v` — it has to mention
`own_raft_phys`, because `appendEntry` queues a `MsgAppResp` and the previous
version, owning only `own_raftLog`, was **false**. See
[decisions.md](decisions.md).

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

**The blocker recorded here on 2026-09-14 is gone** (2026-09-15). It was: the
ghost step `step_grant_vote` produced
`is_message γ (msg.mk mtype.VoteResp id m.From m.Term false)`, and `iFrame`
refused to place it into `wp_raft__send_vote`'s `#Hm` slot even though the two
should agree after `iota`. It was never diagnosed — **`send` no longer has an
`#Hm` slot**, so the question no longer arises. If you go looking for a
lesson here, there isn't one; the obligation moved.

What remains at that point is ordinary work: `send` the granted vote response
and perform the `r.Vote := m.From` update, then show the resulting struct
refines
`send_msgs ((become_follower s m.Term (W64 0)) <| nstate.vote := m.From |>) [VoteResp …]`.
The pure `step` fact for it is already asserted in the proof as `Hgrant`, so
what is left is matching the physical state against it — no ghost reasoning.

Still true and still worth knowing: the goal order `wp_apply` produces here is
`[pure premises] [continuation] [resource]`, so putting `{ }` blocks for the
premises leaves you focused on the continuation with evars in `Hphys`, not on
the resource goal. That cost an hour; do not be fooled by it.

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
- `rocq-warm` (<https://github.com/upamanyus/rocq-warm> — **the upamanyus
  fork**, not zeldovich's) still helps for a long single proof; see
  [gotchas.md](gotchas.md) for the flags this repo needs and what the fork
  fixes.

### Things that bite in this layout

- **`Collection W` is section-scoped, the `Set` that names it is not.** A
  closed lemma after `End <section>` fails with `Unknown variable: W`.
  `proof_raft__Step.v` restores `Set Default Proof Using "Type"` after its
  section for exactly this reason.
- **The ambient binders** (`ext … package_sem`) need care in two places: the
  `Arguments` that keeps them implicit, and the `intros` that introduces them.
  Both are written up once in [gotchas.md](gotchas.md) — short version: the
  `Arguments` goes in the `Module Type`, and proofs open with `intros_ambient`
  (`election/defs.v`), never a positional `intros`.
- **`Require` is illegal inside a `Module` or `Section`**, and `Import` does
  not reach the proof file — a spec needing `New.proof.bytes` (for
  `wp_Equal`) must `Require Export` it.
- **A `_POSTULATES` includes only *direct* callees.** Include another
  `_POSTULATES` and you get `Error: The label ... is already declared`,
  because `reset` is reached from `Step` by two different routes.

## Converting the remaining `inv_*.v` axioms (the 2026-09-16 scope rule)

The standing rule is now: the only thing this development assumes outright is
that `Step` need handle only election messages. Core raft is in scope. Things
outside the raft protocol may be assumed — `slices.Sort`, the `Logger`
interface, the tracing hooks, the RNG.

`inv_tracker.v` was converted on 2026-09-16 and is the model to copy:
ownership predicates became real `Definition`s, their method WPs became
`Admitted` `Lemma`s. That moves them from "assumed" to "in scope,
unfinished" — `./etc/tcb-view.py --summary` went 57 axioms/13 admits →
44/24, which is the accounting working as intended.

### `inv_raftlog.v` — the next one, and the one with a design decision in it

`own_raftLog` is still an `Axiom`. Converting it is **not** mechanical,
because `raftLog.storage` is a `Storage` **interface** — client-supplied, so
it is a legitimate abstraction boundary, but it has to be modelled as an
interface predicate rather than assumed away. `Storage` has six methods
(`new/code/go_etcd_io/raft/v3.v:7735`):

    Entries(lo, hi, maxSize) ([]Entry, error)
    FirstIndex() (uint64, error)
    InitialState() (HardState, ConfState, error)
    LastIndex() (uint64, error)
    Snapshot() (Snapshot, error)
    Term(i uint64) (uint64, error)

Follow the `own_AckedIndexer` pattern at `readonly.v:710`: a `Definition`
bundling a Hoare triple per method against an abstract log, persistent so it
can be shared. Then

    own_raftLog l ≜ ∃ (lv : raft.raftLog.t) (ents : list raftpb.Entry.t) …,
      l ↦ lv ∗ own_unstable lv.(unstable') ∗ is_Storage lv.(storage') … 

with `own_unstable` owning the `entries` slice and its capacity. The open
question is **what the log abstraction should be** — the election path only
needs `lastEntryID`, `isUpToDate`, `lastIndex`, `append`, and (via
`maybeSendAppend` / `hasUnappliedConfChanges`) `term`, `entries`, `scan` — but
picking an abstraction only strong enough for those will not survive contact
with log replication. Worth a decision record before writing it.

### The rest

- `inv_misc.v`: `own_raft_misc`, `wp_raft__promotable`,
  `wp_raft__hasUnappliedConfChanges` (needs `raftLog.scan`),
  `wp_campaign_peer_ids` (= `quorum`'s `JointConfig.IDs`). The four lemmas
  added on 2026-09-16 (`own_raft_misc_option`, `wp_newReadOnly`,
  `wp_raft__resetRandomizedElectionTimeout`, `wp_raft__abortLeaderTransfer`)
  are already `Admitted` `Lemma`s; the last two are nearly trivial once
  `own_raft_misc` is a definition.
- `inv_raft_phys.v`: `wp_raft__appendEmptyEntry` (→ `raftLog.append` →
  `unstable.truncateAndAppend`), and `wp_raft__bcastAppend`, which is an
  `Admitted` `Lemma` as of 2026-09-16. Its statement is deliberately weak —
  "the outbox grew by some `App`s from `id` at the current term" — matching
  the weakened `step_win`. Do not strengthen it to one-per-peer: the code
  does not do that.
- `inv_slices.v`: `wp_slices_Sort` stays an `Axiom`. There is no code to
  prove — Goose emits no body for the `cmp.Ordered` family. See
  [journal.md](journal.md) for the three ways out.
