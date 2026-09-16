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
