# Where the effort actually goes when writing these proofs

Kept so the proof-development *process* can be improved, not just the proofs.
Started 2026-09-16, from direct observation of one session in which `poll`,
`hup`, `reset` and `stepCandidate` were proved and `campaign` and `Step`'s
branches were not.

The headline: **almost none of the cost is the mathematics.** The protocol
arguments are short — three or four lines of `step_*` constructor application,
usually obvious once the state is in hand. The cost is in getting the proof
*state* into a shape where those lines can be written, and that is dominated
by guess-and-check against Rocq.

## The breakdown

Rough shares of effort on the four functions that got proved, from tool-call
counts and what the agents reported:

| activity | share | notes |
|---|---|---|
| Guess-and-check on tactic behaviour | ~50% | run, read error, adjust, re-run |
| Reading generated Go-in-Rocq to find the code's real shape | ~20% | `new/code/...v` is machine-written and verbose |
| Plumbing ownership in and out of predicates | ~20% | unseal/re-seal `own_raft_phys`, field accessors |
| The actual protocol/refinement argument | ~10% | the `step` witness, quorum reasoning |

`reset` took 117 tool calls and ~40 minutes of wall clock; `campaign` took
427 tool calls and ~90 minutes and still did not finish. `poll` — the
smallest — took ~15 iterations for a 60-line proof, of which **three** were
goal inspections that each found a different wrong assumption of mine.

## What the guess-and-check is actually about

Not "which lemma do I need" (that is usually clear) but **"what will this
tactic leave behind"**:

- Does `wp_auto` step past this call, or stop in front of it? It stops for
  reasons that are not visible in the source: an unresolved `bool_decide`, a
  sealed predicate hiding the field it wants to read, a `CompositeLiteral`
  it cannot evaluate.
- How many `bool_decide`s has the program discharged at this point? This is
  what broke `Step`'s `MsgVote`: two sibling branches had discharged
  different numbers, so a shared tactic assumed the wrong shape and failed
  ~15 lines later with `iApply: cannot apply`.
- Which typeclass instance will fire? `access_strict` picks the *store*
  instance when the *load* one was wanted, and the symptom is a leftover
  goal at the end of the proof, not an error at the call.
- Is the goal a `∗` or an `∃`? `iExists` on a postcondition fails with the
  whole goal printed, burying the one-line cause.

Every one of these is answered in seconds by looking at the goal, and is
near-impossible to predict reliably from the source. **The single highest
-leverage habit is to look at the goal rather than predict it.**

## What made the difference

- **rocq-warm replays.** 0.3–30s per iteration against ~100s for
  `make .vok`, and a `Show.` is an ordinary replay in the
  [upamanyus fork](https://github.com/upamanyus/rocq-warm). This is the
  difference between 15 iterations being cheap and being a morning. Proofs
  written without it (early in the session, before the toolchain existed)
  accumulated many wrong guesses at once and were painful to debug.
- **One worked example beats prose.** Every agent that was pointed at
  `proof_raft__poll.v` reused its `access_strict` idiom immediately. The
  `gotchas.md` entry describing the same thing in words was read and
  misapplied.
- **Writing proofs blind does not work.** The first version of `poll`,
  written before Rocq was available, had an error roughly every 10 lines —
  including a helper lemma quoting residual program text that was simply
  invented. All of it was thrown away.

## Traps that cost the most, ranked

1. **A `Qed.` that does not check.** `.vos` skips opaque proofs, so a broken
   script with `Qed.` at the end compiles and greps clean. This produced a
   false "proved" report. Only `make <file>.vok` is evidence.
2. **`access_strict` instance selection** (~40 min). See
   [gotchas.md](gotchas.md).
3. **`iNamed` not firing on an unsealed `typed_pointsto`** (~40 min), and the
   first diagnosis of it was wrong — the real cause is a trailing unnamed
   `⌜l ≠ null⌝`, not that the route is unusable.
4. **Errors reported far from their cause.** A tactic that leaves the program
   un-stepped fails at the *next* `wp_apply`, which points at an innocent
   line. Several hours across the session went to this shape.
5. **A `_POSTULATES` list missing a callee.** Blocks a proof with an error
   that looks like a missing lemma. `Print Module Type` shows the truth.

## Concrete things that would help next time

- **A `Show.`-first workflow, stated as the default.** Not "inspect the goal
  if stuck" but "inspect the goal before writing the next tactic".
- **Tactics for the recurring plumbing.** Unsealing and re-sealing
  `own_raft_phys` appears in every proof and is ~10 lines each time, three
  times per function. `reset`'s three `iFrame`s over the 33-field struct are
  also most of its ~220s check time. A `raft_unseal` / `raft_reseal` pair
  would remove both the repetition and a class of error.
- **A spec-level audit for panics.** Two of the three false statements found
  in two days were about `send`: it `Panicf`s on a zero term and on a
  self-addressed non-response, and `wp_Logger__logf` deliberately excludes
  `Panicf` so those paths must be shown unreachable. A checklist item —
  *"for every `send` on this path, where does `Term ≠ 0` come from?"* — would
  have caught the false `campaign` spec before anyone tried to prove it.
- **Don't parallelise onto one checkout without private scratch dirs.** Two
  agents overwrote each other's scratch files; rocq-warm's per-file lock and
  interleaved stdout also confused them. Proof files themselves never
  collided, so the fan-out was still worth it.

## Round 2 datapoint: `campaign`, 2026-09-16

One agent, one file (430 lines), finished from a state where ~80% of the
script was already machine-checked. Three Rocq iterations, ~45 min wall clock.
Rough shares:

| activity | share |
|---|---|
| Guess-and-check on tactic behaviour | ~25% |
| Reading the generated Go-in-Rocq | ~20% |
| Plumbing ownership in and out of predicates | ~25% |
| Waiting for the checker | ~30% |
| The actual protocol argument | ~0% |

The protocol content really was zero: `campaign` refines `step_campaign`, and
the whole obligation is `cmsg <$> xs ≡ₚ [VoteResp] ++ (Vote <$> elements (cfg
∖ {[id]}))`, five lines of `Permutation`.

**The error that cost the most** was inherited, not earned: the previous run
had written down `iApply: cannot apply … "send" (# ?m)` together with a wrong
diagnosis ("`wp_auto` does not step through the composite literal; the call
site probably needs `rewrite /MsgVote bool_decide_eq_true_2`"). The real cause
was a *missing callee spec*: `campaign` calls `voteRespMsgType` to compute the
message's `Type` field, `wp_auto` stops in front of the call, and the spec was
not in `CAMPAIGN_POSTULATES`. One `wp_apply P.wp_voteRespMsgType; first done.`
fixed it. **Lesson: a recorded error message is worth keeping; a recorded
guess at its cause is worth distrusting.** When `wp_auto` stops, the first
question is "which callee is this?", answered by one `Show.`, not by
theorising about literals.

**What I should have been able to predict and could not:** that a Go
`for … range` loop variable has to be existentially quantified in the `wp_for`
invariant. `slice.for_range` allocates it outside the loop, the body assigns
it, and `iNamedAccu` freezes whatever is left in the ambient context at its
*current value*. The failure surfaces as `iFrame` not closing the invariant at
the end of every branch — three branches, three identical confusing failures.
What would have let me predict it: a one-line note next to `wp_for` in
`PERENNIAL_PROOF_REFERENCE.md` saying "everything not in your invariant is
framed at its present value; a variable the body writes must be in the
invariant". (Now in `gotchas.md`.)

**Waiting was the single largest cost, and it was self-inflicted by the
fan-out.** Three agents shared one rocq-warm daemon; sessions are 2–6 GB and
the budget is shared, so each of my checks came back `[cold, …, 250–460s]`
rather than the seconds the warm fork exists to provide. `make <file>.vok` is
~100s, is the *authoritative* check, and prints `Show.` output identically.
For a 400-line proof with other agents in the checkout, `.vok` is the better
inner loop. Corollary for planning a fan-out: either give each agent its own
checkout, or expect the warm-replay advantage to evaporate and size the work
accordingly.

**What worked:** writing the whole remaining script in one go with `Show.` at
each uncertain point, rather than one tactic per iteration. Iteration 2 was a
~90-line edit; it got through all three `send` branches and failed only at the
loop exit. At 5 min per check, batching guesses beat serialising them — the
opposite of the advice that suits a 0.3 s replay.


## Round 2 (2026-09-16, later): what parallel agents reported

Five more functions landed (`reset`, `stepCandidate`, `campaign`, `Step`'s
`MsgVote`, plus `stepFollower`/`stepLeader` on `MsgVoteResp`). Three findings
sharpen or contradict the picture above.

### The right inner loop depends on replay cost, and replay cost depends on neighbours

The `campaign` agent reported that **rocq-warm's warm replay did not help it
at all**: with several agents in one checkout the daemon evicted its 2–3 GB
session between every check, so each "replay" was a cold 250–460 s run, while
`make <file>.vok` is ~100 s and authoritative. It therefore *batched* — wrote
~90 lines with a `Show.` at each uncertain point, three iterations total — and
got through all three `send` branches in one shot.

That is the opposite of the one-tactic-at-a-time habit that suited `poll`'s
0.3 s replays, and both are right. **State the rule as: measure your replay
cost first, then pick the batch size.** Sub-second replay → one tactic at a
time. Minutes → batch, with a `Show.` at every point you are unsure.

Corollary discovered the hard way: **`Show.` does not survive `-vok`**, so
`.vok` can never be the goal-inspection loop, only the verdict. And
`proof_raft__Step.v` exceeds rocq-warm's default 4.2 GB session ceiling, so
goal inspection on the largest file needs
`ROCQ_WARM_MAX_SESSION_GB=9`. Both in [gotchas.md](gotchas.md).

### Recorded error messages are gold; recorded diagnoses are not

Two agents inherited a predecessor's unfinished script with a note giving both
the failing error *and* a guess at its cause. In both cases the error was
right and **the guess was wrong**, and the guess cost real time:

- `campaign`'s note blamed a `CompositeLiteral`; the actual cause was
  `wp_auto` parked in front of a `voteRespMsgType` call whose spec was missing
  from the postulates list. One `Show.` would have shown it.
- `Step`'s `MsgVote` note blamed the shared reject tactic; the actual cause was
  that Goose compiles `||`/`&&` to short-circuiting `If`s, so each arm of
  `canVote` owes a *different number* of `bool_decide`s — three arms owe
  three, one owes four.

So: when preserving an unfinished proof, **record the error verbatim and the
goal, and mark any diagnosis as a guess.** The next reader should re-derive
the cause from a `Show.`, not inherit a theory.

### Adding a real invariant is mechanical; discovering it is missing is not

`own_raft_phys` had a comment claiming it pinned `r.step` to the role and no
such conjunct. Nothing detected that for two days — not the type checker, not
the axiom count, not a review — until a proof needed the fact and could not
get it. The tell was in plain sight: `becomeFollower`'s re-seal said
`iExists (rv <| step' := _ |>)`, and **an evar in a re-seal is where an
invariant goes to hide.** Worth grepping for.

Threading the fix through the four proofs that re-seal was then routine.

### The cheapest trust-base win was reading the generated code

Five `traceX` functions were `Axiom`s for days. Goose translates every one to
`λ: <> <>, exception_do (do: #())` — a literal no-op — so each was a two-line
proof. A sixth axiom, `wp_raftLog__hasNextOrInProgressSnapshot`, was reachable
from no proof at all and was simply deleted.

**Before assuming anything about a callee, read its translated body.** Six of
the nineteen election-path axioms cost nothing but a `grep`.

## Round 3 datapoint: `wp_campaign_peer_ids`, 2026-09-16 — a blocker found in 12 minutes

One agent, one axiom, ~10 scratch runs at 6 s each. Outcome: **not provable**,
because the translated body of `quorum.JointConfig.IDs` is stuck in the model
(Goose emits `IndexRef` on a *loaded* array value; see
[gotchas.md](gotchas.md)). Shares:

| activity | share |
|---|---|
| Stepping the program to the first stuck point | ~30% |
| Reading the framework's semantics instances to explain the stuck point | ~40% |
| Three probe lemmas that turned the explanation into evidence | ~15% |
| Writing it down | ~15% |
| The actual protocol argument | 0% |

Three things generalise:

- **The scratch-file `-vok` loop was 6 s here, not the ~56 s the `Step` agent
  measured.** Cost scales with the `.vos` closure you `Require`, so requiring
  a leaf `spec_*.v`/`postulates_*.v` rather than something under `Step` is a
  ten-fold difference. Measure it once at the start; it decides whether you
  batch. (This was written when a callee's spec lived in `inv_misc.v`; since
  2026-09-18 every callee has its own collection, so the cheap closure is
  usually the one you want anyway.)
- **"Read the callee's translated body" needs a second half: check it can
  step.** The 2026-09-16 win (five `traceX` no-ops) came from reading bodies.
  The complement is this: a body can be perfectly readable and still have no
  transition in the model. `wp_auto` to the first stuck point is the same
  six-second run and answers "is this axiom dischargeable at all?" — which is
  worth knowing *before* anyone schedules the work.
- **A negative result needs probes, not prose.** Asserting "the model has no
  rule for this" from reading `defn/array.v` would have been a guess of
  exactly the kind this file warns about. Three two-line `WP` goals —
  `IndexRef` on a loc (steps), `IndexRef` on an array value (stuck), `Index`
  on an array value (steps) — turn it into something a reader can re-run, and
  they also name the fix.

## Round 3 datapoint: `inv_tracker.v`'s `TallyVotes` and `Visit`, 2026-09-16

One agent, two `Admitted` lemmas, ~12 Rocq iterations at 10–80 s each
(`rocq compile -vok` on a scratch module — the loop `gotchas.md` recommends;
it held up). Outcome: **neither lemma was provable, and finding out why was
the work.** Both are blocked below the proof, and one of the two statements
was false.

| activity | share |
|---|---|
| Probing where the generated code stops stepping | ~45% |
| Reading `new/code/` and `new/golang/defn/` for missing instances | ~25% |
| The one piece of real proof (the tally loop) | ~20% |
| Pure Rocq (the quorum bridge lemmas) | ~10% |

### The lesson: probe the *callee chain* before writing a line of proof

Every blocker was findable in one `wp_auto` + `Show.` per callee, before any
invariant was designed. Three of the four were missing or mis-shaped steps in
the framework, not raft facts:

- `len` of a named map type (`ProgressMap`) — instance exists only at the
  literal `go.MapType`; workaround via `go.len_underlying`.
- `len` of an array type (`[7]uint64`) — **no instance anywhere**.
- `IndexRef` / `Slice` applied to a loaded array *value* where the model only
  steps on an array *location* — the defect `inv_misc.v` already wrote up for
  `JointConfig.IDs`, which also blocks `JointConfig.VoteResult` (so
  `TallyVotes`) and `Visit`'s `ids = sl[:n]`.

A five-minute "step each callee on its own and see where it parks" pass at
the start would have replaced a couple of hours. **Make it the first step for
any function whose body calls into `quorum`, or touches an array, or takes
`len` of anything whose type is a `go.Named`.**

Corollary for the trust base: the honest count of what is blocked on
*translation* rather than on proof effort is now at least three lemmas
(`wp_campaign_peer_ids`, `wp_ProgressTracker__TallyVotes`,
`wp_ProgressTracker__Visit`) plus the pre-existing
`wp_JointConfig__CommittedIndex` axiom. They share two root causes. Fixing
the array operand form in the Go fork's Goose and adding
`FuncUnfold go.len [go.ArrayType n t]` to `new/golang/defn/array.v` unblocks
all four. That is a much better use of a session than attacking them one at a
time.

### And: the falsity was in the same place as last time

`wp_ProgressTracker__Visit`'s precondition owned no part of the tracker
*struct*, so it could not read `p.Progress` through the pointer receiver. The
comment above it asserted the opposite in prose. That is the same shape as
the `r.step` entry in [STATUS.md](STATUS.md)'s table — **an invariant
promised in a comment and absent from the conjuncts** — and it is now the
second one found that way. The table's two tells (an evar in a re-seal; an
`Admitted` under a `Qed`) want a third: *a comment that argues for the
absence of a conjunct*.

Also latent, and not fixed by unblocking anything: `TallyVotes`'s
`res = VoteWon → is_quorum cfg (granted votes)` is false at `cfg = ∅`,
because `MajorityConfig.VoteResult` returns `VoteWon` outright for an empty
config while `is_quorum ∅ q` is `0 < 0`. `own_tracker` wants a
`⌜ cfg ≠ ∅ ⌝` conjunct; no proof constructs `own_tracker` from scratch, so
adding it is free.

## Round 4 datapoint: check time of `proof_raft__Step.v`, 2026-09-17

Not a proving session — a profiling one. `Step` took 45 min to `-vok`; it
now takes 9.5. Where the session's effort went:

| activity | share |
|---|---|
| Profiling: scratch lemma, `-time`, `Ltac Profiling`, `time` on isolated tactics | ~35% |
| Implementing the framework changes and getting them to parse (Ltac2/Ltac1 quotation) | ~20% |
| Waiting on `.vos` closure rebuilds (~4 min each, six of them) and `-vok` runs | ~30% |
| The A/B against the stashed old framework, and the regression it caught | ~15% |

### What the numbers say about process

- **Profile before theorising.** The first hypothesis (proof-term size and
  `Qed`) was wrong; `Qed` was 15% of the file. Two minutes of
  `Set Ltac Profiling` on one lemma pointed at typeclass search, and one
  `Set Typeclasses Debug` run said which class. Every subsequent finding
  came from a `time "name" (tac)` on an isolated tactic.
- **`assert_succeeds`/`assert_fails` + `time` is the right probe.** It
  answers "would this alternative work, and how fast" without committing.
- **A same-day A/B is worth 25 minutes of machine time.** The copied `done`
  had an extra arm that made one `//` 3000× slower; nothing else would have
  caught it, because the file still checked.
- **Do not kill processes with `pkill -f` from the agent shell.** It
  matches its own command line (exit 144) and leaves the `rocqworker` alive.
- **Never edit a `.v` while `rocq compile` is reading it.**

