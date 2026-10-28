# Plan: specs first, proofs later

Status: proposed (2026-10-27, branch `spec-first`). Steps 1 and 2 of "Testing the plan" done (below,
"Step 1: the retrospective study", "Step 2: the checker on the known false axioms").

## Goal

Proofs are slow to write and to re-check, and a spec that changes after its proof exists costs a
re-proof, often in its callers' proofs too. This plan front-loads the discovery of the specs --
internal ones and the trust-boundary specs of the packages etcd uses -- gets confidence in them
cheaply (by tests and a few proofs), freezes them, and only then does the bulk of the proofs.

## Why: what the history shows (2026-10-27)

- 605 non-merge commits since the port began (2026-10-09) modify an existing `Spec/` file.
  The most revised: `raft__Step` 48, `NewServer` 46, `stepFollower` 29, `EtcdServer__apply` and
  `EtcdServer__applyEntries` 24 each, `stepLeader`/`stepCandidate` 21, `newRaft` 20.
- `raft__Step`'s 48 revisions are almost all scope extensions (message types, learners, joint
  configurations, PreVote, CheckQuorum, snapshots, leader transfer) and caller needs discovered
  later (the server's snapshot certificates, read-index credit, the floor raised before
  `Advance`, the sender's promise), not corrections.
- False specs exist too, found late and by hand: the axiom audit (`notes/audit.md`; D19m-p in
  `notes/decisions.md`) found trust-boundary specs false of the Go code after proofs rested on
  them.

So three causes, each with its own remedy: scope that grows a feature at a time (phase 0),
caller needs discovered bottom-up after the callee is proved (phase 1), specs nobody checked
against the code (phase 2). Step 1 below measures their shares.

## The phases

**Phase 0: scope and the top-level statement first.** Before any spec of a slice, fix the
configuration the result covers (features on or off, message types, membership changes,
snapshots, failure modes) and write the top-level theorem (e.g. the example's linearizability
adequacy). Widening later is a new, deliberate stage, not a series of spec edits.
*For a widening of code already proved* (M2, 2026-10-28): phase 0 drafts the top-level statements
and the statements of the layers it changes, not a survey of the files: M2's phase 0, decided from
a survey, was revised four times in phase 1 by drafting alone (C3, the watch store, Restore, and
delete-then-put twice).

**Phase 1: the spec skeleton, top-down.** Every function's spec written, internal and external,
every proof `sorry` (or a trust-boundary axiom), `Link.lean` generated. Then prove the *glue*:
the callers whose bodies only thread state between callees, from the callees' specs. Glue proofs
are short and are what find a missing frame, a premise the caller cannot give, or a
postcondition too weak for the caller -- before the callee's expensive proof exists.

**Phase 1b: review the specs, and iterate with the glue** (added 2026-10-27, from the pilot's
phase 1). Writing a spec and proving its callers' glue alternate per package boundary: write the
spec, prove the glue of *every* caller, review, revise; a spec is frozen only when every caller's
glue proves and the review leaves nothing in the first tier below. The review is a fresh reviewer's
(the `spec-reviewer` agent, which judges by the `spec` skill's `PRINCIPLES.md` and `examples/`), given the specs, the Go code and the callers, not the
author's conclusions; it ranks each spec that crosses a package boundary (internal helpers' specs may
mirror the code) in two tiers:

- *Requirements* (fail one and the spec is wrong): **true** of the code (phase 2's tester, then the
  proof); **sufficient for every caller** (each caller can establish the pre and gets what its proof
  needs from the post: the glue proofs check it); **faithful to concurrency** (callers that invoke it
  concurrently need persistent contracts, a once-only or exclusive use a token; and an exclusive
  requirement of the code is stated); **no unneeded premise** (each is one the code needs or one a
  stronger result needs; one that excludes a legitimate caller fails sufficiency).
- *Preferences* (among specs that pass): **abstraction** (only names the callers need: no fields,
  ghost names, helpers or other packages' internals; counted on the unfolded statement,
  `etc/gen-interface.py`); **implementation independence** (another reasonable implementation would
  satisfy it); **the weakest pre and the post no stronger than some caller needs**; **size** (the
  unfolded statement's length, binders, premises); **coupling** (other packages' predicates it
  depends on: each is a place where a change elsewhere forces this spec to change, step 1's main
  cause of churn).

*Rounds.* Repairs introduce defects (in the pilot, two of round 2's three blockers came from round 1's
repairs), so every repair is followed by another round with a fresh reviewer, until a round finds
nothing in the first tier; each later round is told what the previous repair changed (the diff) and
looks hardest there.

*Cost.* A round took about 9 minutes in the pilot (28-47 tool calls, about 170k tokens), most of it
the fresh reviewer finding and reading its context (the agent file, `CLAUDE.md`, the targets and what
they unfold to, the Go code, and above all the callers' proofs: `NewServer.lean` alone is 1800 lines);
the full `lake build` between rounds took longer (20-30 minutes). Two measures (added 2026-10-27):
- **A context bundle per round**: one generated file with the targets' unfolded statements
  (`etc/gen-interface.py`'s rendering), the Go functions they specify, the callers' call sites and the
  contracts or proof excerpts at them, and, from round 2 on, the previous repair's diff. The reviewer
  reads it first and goes to the repository only to check a claim.
- **Targeted builds during the rounds**: build only the touched modules and their importers among the
  specs and the glue (`lake build <modules>`, `etc/lean-check.py`); the full build once, before a
  commit goes to the main branch.

A round reviews a named commit; work goes on meanwhile, so the reviewer checks `HEAD` against it and
marks findings already addressed there as stale (the pilot's fourth round ranked first a finding fixed
after its snapshot).

The pilot measures whether the review pays: spec revisions found by the review, by the glue proofs,
and after the freeze.

*Measured alongside the tiers* (mechanical where possible):

| metric | what it catches | how |
|---|---|---|
| scope premises | premises restricting the configuration or workload (`AutoCompactionRetention = 0`): each a future SCOPE revision, step 1's first cause | count per spec; each must cite a phase-0 decision or an `issues/` file |
| caller burden | a missing law: callers unfold the spec's predicates or open its invariants | `unfold`/`iunfold` of the callee's definitions in callers' proofs; glue lines per call |
| law coverage | persistence, timelessness, fractions, agreement callers need and the API lacks | the laws exported next to each predicate against those callers use |
| trust exposure | axioms the spec rests on, and whether each is tested | `etc/tcb-report.py --roots`; phase 2's tester coverage of them |
| testability | how much of the spec phase 2 can check | the pure, decidable share of the pre/post; opaque predicates needing a test interpretation |
| strength margin | a post weaker than the code guarantees: a future CALLER revision, step 1's second cause | phase 2's tester with a strengthened post: if no execution refutes it, note it (strengthen only when a caller needs it) |

*The feedback loop.* The review's criteria are themselves under test:
1. every spec revision after the review (glue, phase 3, phase 4, after the freeze) records its cause
   (step 1's rubric) and the review criterion that should have caught it, or "none";
2. a "none" becomes a new or sharper criterion; a miss of an existing criterion adds an example to
   the reviewer's brief;
3. false positives count against a criterion: a finding whose change was later reverted, or that
   made a spec stronger than any caller used;
4. the criteria are re-weighted by the revisions each would have prevented, weighted by the proof
   lines those revisions touched (step 1's `proof_lines_changed`); one that never catches anything
   is dropped.
Each attributed miss becomes a principle (new or sharpened) in the `spec` skill's `PRINCIPLES.md`,
so later reviews in the repository start from it.

**Phase 2: test the specs against the Go code** (no proof).
- Canonical form: `own σ ∗ ⌜Pre σ args⌝ -∗ WP f args {r, ∃ σ', own σ' ∗ ⌜Post σ args r σ'⌝ ∗ …}`
  with `Pre`, `Post` decidable definitions on the pure records the predicates are indexed by
  (CLAUDE.md, "Records").
- A test-only Go abstraction function per record type (Go state to record, as `inflightsRingOf`
  does in Lean); trusted for testing, checked later by the proof of the representation predicate.
- Entry/exit instrumentation records `(σ, args, r, σ')` as JSON; a Lean executable evaluates the
  Lean `Pre`/`Post` on the traces (the spec itself, not a Go transcription of it). Raft already
  has the hook: `state_trace.go` (build tag), used by its TLA+ trace validation (`tla/`).
- Trace sources: raft's datadriven `testdata/` interaction tests, raft's and etcd's unit tests,
  etcd's robustness tests, Go fuzzing.
- Readings: `Post` violated: the spec is false. `Pre` violated on a trace of a normal workload:
  the spec is stronger than its real callers allow. `Pre` never satisfied: vacuous.
- Lock invariants (`Inv*`) asserted at each `Unlock`; concurrent objects checked by porcupine
  against the spec's pure model (`examples/lintest` exists); protocol-level properties keep their
  model checkers (`notes/reconfiguration-model-check.md`).
- The trust-boundary specs of other packages (bbolt, grpc, zap, the standard library) get the
  same treatment: random call sequences against the real library, checked against the axiom's pure
  model. One refuting trace is what the audit had to find by reading.

**Phase 3: a few proofs per package.** Prove fully the one or two riskiest bodies of each
package (most branching, ghost state, concurrency): they check what traces cannot -- invariant
sufficiency, the ghost design, logical atomicity. Then freeze the specs: a change after the
freeze needs a `notes/decisions.md` entry with its cause. Do an easy proof too, not only the riskiest one (the user, 2026-10-27): an easy
proof is cheap and may already find problems the review missed (a resource it cannot build, a premise
it cannot meet); measured against the hard one, it says whether the hard proof found anything more,
and so whether a hard proof per package is needed or an easy one is enough. Record for each: the time
it took, and the spec problems it found that the review and the glue had not.

*Unfolds across a package boundary* (added 2026-10-27, the user's: a client of a good spec does not
unfold its definitions). Phase 1b's caller-burden metric predicts them; phase 1's glue and phase 3's
proofs are where they show. List, for each proof, every `unfold`/`iunfold`/destructuring of a
definition of another package (its predicates, its package initializer's fact, its contracts; not
Perennial's proof-mode patterns such as `chan.blockingClausePre`). Each is a finding against that
package's API: a missing law, added to the package that owns the definition (for Perennial's, a
Perennial change, `notes/perennial-changes.md`), and the proof rewritten to use it. Unfolding a
definition of the proof's own package is normal. The pilot's two `Run` proofs had three:
`clockwork.clockOk` (now `clockOk_ok`/`clockOk_Now`/`clockOk_After`), mvcc's package fact, taken
by its 31st of 42 conjuncts (now `mvcc.ErrCompacted_target`), and Perennial's `context.isContextDef`
(`isContext_Done`, a Perennial branch). **The freeze requires the list empty**, or each remaining
unfold justified in `notes/decisions.md` (a law pending in Perennial, say).
**The freeze also requires every caller's glue** (M2, 2026-10-28), callers in planned later stages
included; a spec whose callers are not all written is "frozen pending" them. The compactor's
`compactableOk` passed five reviews and the freeze, then failed at the first glue of its real
implementation's caller in M2: the reviews had checked it against `EtcdServer.Compact.spec`, itself
an unproved `sorry`, not against `Compact`'s Go body (which reads the context's
`Value(TraceKey{})`).

**Phase 4: the remaining proofs**, against frozen specs, in parallel (independent per function,
which suits agents).

**Agents in phases 1 and 1b** (M2, 2026-10-28): a long agent drifts toward proving. Its brief says
skeleton only from the start (statements; the glue; a marked `sorry` on the failing step of anything
else) and **never deletes a finished proof**: a broken one keeps its text, with the `sorry` on the
failing step naming the commit that had the proof. (M2's S1 agent re-proved about 45 files before
S2-S4 had statements, and replaced finished proofs wholesale with `sorry`s, until redirected.)

**Not covered by testing:** the resource part of a spec (ownership, fractions, invariants,
atomicity). Only phase 1's glue proofs and phase 3's sampled proofs check it before phase 4.

**Costs.** The Go abstraction functions; decidable `Pre`/`Post` where a spec quantifies over
ghost state (a weaker test-only projection where needed); restating existing specs in the
canonical form (for the pilot slice only, at first).

## Testing the plan

1. **Retrospective study** (git history only): classify a random sample of spec revisions by
   cause, and say for each which phase would have found the need earlier. Gives the shares of the
   three causes, hence which phases are worth building. Done: below.
2. **The checker on known bugs**: replay the trust-boundary axioms later found false (the audit's
   rows, step 1's three) and the library calls with a reproduction in `issues/` through the phase-2
   checker; how many does it catch? If few, phase 2 is not worth its cost. (Narrowed to the
   trust boundary by step 1.) Done: below.
3. **A prospective pilot** (started 2026-10-27: etcd's auto-compactor, `notes/compactor-pilot-plan.md`): one unverified slice of comparable size done spec-first, compared with
   a slice done the current way (from git history: e.g. cindex, the read-index loop). Metrics:
   time to a frozen spec; spec changes after the freeze (the main one); defects found by tests vs
   by proofs; proof time after the freeze.

## Step 1: the retrospective study (2026-10-27)

**Method.** The 605 non-merge commits (2026-10-09 to 2026-10-27) that modify an existing `Spec/`
file (`git log --no-merges --diff-filter=M -- Spec`); a random sample of 64 (Python's
`random.seed(20261027); random.sample(hashes, 64)` over that list, newest first); each commit's
message, `Spec/` diff and the `notes/decisions.md` entries it names read by one of four agents with
the same rubric, which gives a primary cause, an optional secondary, the phase that would have found
the need earlier, and for a false spec the Go execution that refutes it. The data, one JSON line per
commit with the lines of `Spec/` and `Proof/` the commit changed: `notes/spec-first-study/sample.jsonl`.

Causes: SCOPE (the spec covers cases it excluded), CALLER (a caller needed more: a stronger post, a
weaker pre, a resource returned), FALSE-BEH (false of the Go code in its pure part: a concrete
execution refutes it), FALSE-RES (wrong in its resources: ownership, ghost state, invariants),
PROOF (restated for the proof or the design, same meaning for clients), INFRA (mechanical:
docstrings, renames, the Perennial pin, linter options), CODE (the Go code changed).

**Results** (64 commits; 49 classified with high confidence, 15 medium):

| cause | primary | phase that would have found it earlier |
|---|---|---|
| CALLER | 23 | P1 19, P0 2, P2 1, P3 1 |
| SCOPE | 20 | P0 19, P1 1 |
| INFRA | 11 | none |
| PROOF | 5 | P3 3, P1 1, none 1 |
| CODE | 3 | none |
| FALSE-BEH | 2 (+1 secondary) | P2 |
| FALSE-RES | 0 (3 secondary) | P1 2, P3 1 |

Of the 50 that are not INFRA or CODE: 42 (84%) are SCOPE or CALLER, which phases 0 and 1 address;
3 (6%) are false behavior, which phase 2 would have caught. The `Proof/` lines changed in the same
commits (a rough measure: such commits also do new proof work) follow the same order: SCOPE
18 472, CALLER 13 381, FALSE-BEH 294.

**The three false behaviors** (each refuted by a short execution; two of the three are
trust-boundary axioms, which no proof will ever check):
- `bfaa9ce45c`: the axiom said `pbutil.MustUnmarshalMessage` returns on any bytes; on malformed
  bytes it panics (a byte fuzzer finds it at once).
- `072b026b16`: rafthttp's `CutPeer` taken twice after `AddRemote` panics
  (`issues/etcd-rafthttp-cutpeer-twice-remote-panic.md`; a fuzzer over call sequences finds it).
- `68ceb46a40`: a key created in a txn at sub-revision 1 has sub-revision 0 after a restore (only if
  the traces record sub-revisions).

**What the sample says about the plan.**
- **Phases 0 and 1 matter most; phase 2 is narrow.** Trace testing checks that a spec is true; it
  cannot see a spec too weak for its caller, and most CALLER changes strengthen a true post
  (`Advance` keeps the term, `decodeLoop`'s error is never nil, `deleteOnce`'s `ok` implies
  `err = nil`). Build phase 2 for the trust-boundary axioms (717 of them) first, not for proved
  specs.
- **Phase 0 must fix the deployed configuration and the strongest top-level property, not just
  "a scope".** `596c72e0e6`: etcd runs raft with `CheckQuorum: true`, the proof required it off,
  so the closed theorem did not cover etcd's configuration until then (PreVote likewise).
  `e273d4457d`: the top-level property went from "a client write may fire repeatedly" to "at most
  once", which changed about 22 spec files from the client's retry interceptor down to
  `raft.Step`. Scope also shrinks (`1f26594335`: the bridge, proved, declared network;
  `19a919ec00`: leader transfer off where the network contract cannot describe `MsgTimeoutNow`).
- **Phase 1's glue proofs must be full separation-logic proofs.** The CALLER needs are mostly
  resources (a ghost fraction lent, a token threaded, ownership given back: `6e5a820e9f`,
  `38ca631867`, `bbbbfd238b`, `22473bd085`, `0d418fec3c`), not pure facts. A glue proof finds
  that something is missing; the shape of the fix is often a ghost design, phase 3's work, so
  phases 1 and 3 interleave per package rather than run in sequence.
- **A satisfiability check of preconditions** belongs in phase 1: `5239c8b0e3`'s pre could not be
  met with auth on, which composing the top-level theorem shows without any proof of a body. Some
  premises are false only in the model (`f2ac4e6c88`: `Campaign`'s `leaderRev - 1` is 0 only
  because the model's first write is revision 1): no Go trace refutes them, only the glue.
- **Causes the rubric missed**, each a few commits: replacing an axiom or opaque premise by tracked
  state to shrink the trust base (`184e97b498`, `db14efdd2e`, `28adb38f2b`); restrictions forced by
  the proof structure (`c5b96bd53a`: an auto-leave branch excluded because its proof would make the
  links mutually recursive); liveness, which no phase sees (`c01f2275b8`: the kv example's replica
  never answered requests a snapshot covered, found by a Go test).
- **Writing specs finds Go bugs before any proof**: the compaction specs (`3f2263f694`) found
  `issues/etcd-compaction-delete-then-put.md` and `issues/etcd-compaction-negative-batch-limit.md`.

**Limits.** 64 of 605 (for the large classes, about ±12 points at 95%); one agent per commit, no
second opinion; "would have found it earlier" is a counterfactual judgment. Sampling by "modifies
a `Spec/` file" also counts commits that mostly add new specs or touch only docstrings (INFRA, 11
of 64).

**Revisions to the plan from step 1.** Step 2 (the checker on known bugs) is narrowed to the
trust-boundary axioms: the audit's false rows, the three above, and the libraries' calls with
`issues/` reproductions. The pilot (step 3) measures phase 0 (is the configuration that of
deployed etcd, is the top-level property the strongest one wanted) and phase 1 (glue proofs in
full Iris, interleaved with the phase-3 proofs of the package) first.

## Step 2: the checker on the known false axioms (2026-10-27)

Two parts: a paper replay of every trust-boundary axiom known to have been false, and a working
prototype of the phase-2 checker on one library, bbolt.

**The paper replay.** The 44 axioms known false (the audit's 41, `notes/audit.md`, and step 1's
three), each classified by what would refute it: `notes/spec-first-study/step2-false-axioms.jsonl`
(one agent, the refuting execution and the generator it needs for each).

| refutable by | axioms | examples |
|---|---|---|
| a single call | 17 | `strconv.FormatUint` base 1, `MustUnmarshalMessage` on bad bytes, prometheus label counts, nil loggers and requests, `lessor.Promote` with a negative rate |
| a call sequence | 10 | bbolt's `wBkt` trio, `Cursor_kvw`, `Info_kv`; `NewBackendQuota` then `Available`; `store.Close` then `Compact`; `CutPeer` twice |
| concurrency | 1 | `SetVersionChangedNotifier`'s unlocked write (`-race`) |
| the environment | 3 | `time.Since` (a coarse clock), `NewStream` (gRPC fault injection), `monitorFileDescriptor` |
| not observable | 13 | writes to state the spec frames out (`compactRaftLog`, `snapshot`, the monitors), proposals without a permit (`raftRequestAlarm`, `Alarm`, `revokeExpiredLeases`), inconsistent only in Lean (`convert_float64_to_int64`, `dialWithBalancer`'s two) |

So 31 of 44 (70%) have a Go execution that refutes them; a frame check (the abstraction of what the
pre does not own, compared before and after the call) would add about 4 (`compactRaftLog`,
`snapshot`, `createMergedSnapshotMessage`, `monitorStorageVersion`). Existing upstream tests
already run the refuting execution of about 6 (e.g. `TestProtoUnmarshalerPanic`,
`TestV3StorageQuota*`, client_golang's invalid-label test): run against the axioms, they would have
refuted them on day one.

**The prototype: `etc/spec-test/bbolt`** (Go, 708 lines, for bbolt's 20 axioms). The specs are
both the generator and the oracle: the tester keeps the predicate instances the specs have given
out (`ownDB`, `wrTok`, `isDB`, `ownWTx`, `wBkt`, `ownCur`, ...) with their pure arguments (the data
`D`, `S`, a cursor's entries), makes at random a call whose precondition that state satisfies
(consuming its exclusive predicates; persistent ones stay), runs it on the real bbolt, and checks
the postcondition's pure part against the result; a panic refutes (a WP excludes it). A call that
does not return within 100 ms ends the run without a verdict (partial correctness allows
blocking). Each axiom is transcribed by hand from its Lean statement. Runs of 60 calls:

| statements | runs | refuted | how |
|---|---|---|---|
| current | 3000 | 28 (0.9%) | **the `wBkt` trio, still false**: a handle of a deleted, re-created bucket; `Put` panics (26), or a cursor misses the data (2) |
| current, `wBkt` corrected | 10 000 | **0** | every axiom exercised (about 600 000 calls; 272 runs blocked) |
| `DB.Info_kv` before B4b | 3000 | 2638 (88%) | `Info` after `Close` panics |
| `Bucket.Cursor_kvw` before B4b | 3000 | 282 (9%) | a `Put` while the cursor is open; the cursor sees it |
| mutant: `Seek` past an equal key | 3000 | 150 (5%) | |
| mutant: `Commit` keeps the old data | 3000 | 149 (5%) | |
| mutant: `Rollback` leaves `txLive` | 3000 | 1809 (60%) | calls on a closed transaction panic |
| mutant: a read transaction sees later commits | 3000 | 39 (1.3%) | |
| mutant: `CreateBucketIfNotExists` empties an existing bucket | 3000 | 22 (0.7%) | |
| mutant: `Delete` a no-op | 3000 | 50 (1.7%) | |
| mutant: `Begin(true)` keeps `wrTok` | 1000 | **0** | 390 runs blocked (39%, against 3%): a second writer waits |

**What step 2 says.**
- **The checker works, and catches resource errors too.** All three bbolt rows the audit found
  false were refuted, and two of them are errors in the resource part (a persistent `isDB`
  outliving `Close`, a persistent `wBkt` outliving `DeleteBucket`), which the paper replay calls
  observable only because tracking the predicates lets the tester make the call Go does not
  survive. One of them (`wBkt`) is still false in the current specs; the tester found it without
  being told, along with a Go documentation issue (`issues/bbolt-deleted-bucket-handle.md`).
- **No false alarms**: with `wBkt` corrected, 10 000 runs refute nothing, though every axiom ran.
- **Opaque predicates need no test interpretation when the specs produce them**: `isDB`, `wBkt`,
  `ownCur` are tokens a post hands out and a pre consumes. Only the environment's predicates
  (`fileHolds`, `dbCloseOk`) need one (a fresh file; a local disk).
- **What it misses**: an error whose only effect is blocking (the duplicated writer token) shows
  only as a rise in blocked runs, which partial correctness allows; a blocked-run rate well above
  the baseline is worth reporting as a warning. Concurrency is not exercised (one thread).
  Rare sequences take many runs (`wBkt`: about 1 run in 100).
- **The cost and the gap**: about 25 lines of Go per axiom, by hand, plus the pure model
  (`bktEnts`, `seekIdx`). The transcription is unchecked: a wrong transcription tests another spec.
  Specs in phase 2's canonical form (pure `Pre`/`Post` as Lean definitions) would let a generated
  checker evaluate the Lean text instead; not built.

**Revisions to the plan from step 2.** Phase 2 is worth building for the trust boundary (717
axioms, which no proof will check), as spec-guided call-sequence testing with predicate tracking,
not as checking of recorded traces alone: the sequences the specs allow are where the false
resource parts show. Next libraries by the paper replay's yield: etcd's own names-only axioms
(mvcc, lease, quota: call sequences), prometheus and `strconv`-like single calls (cheap), rafthttp.
The `wBkt` trio: fixed 2026-10-27 (handles at a generation, `notes/decisions.md`, "bbolt handles at
a generation"); the tester now runs the new statements by default (`-old-wbkt` for the old).

## Checkpoint: the compactor pilot and M2 to review round 1 (2026-10-28)

**What works.**
- *Review before proofs finds most spec problems*: the compactor's 18 of 19 first-tier revisions
  came from the reviews, before any proof (the glue the 19th; proofs and the tester none); M2's
  round 1 found 4 first-tier problems in S2-S4, none in S1, at no proof cost.
- *Drafting statements tests the design cheaply*: M2's phase-0 scope was revised four times in phase
  1 by writing statements alone; the reversal after round 1 (one family, the Go bug fixed instead of
  a compaction-mode family through the serving stack) discarded statements and stubs, not proofs.
- *The glue finds what the reviews miss*: `Compact`'s context `Value` (after five rounds), the
  `rangeResult` bound.

**What does not, yet.**
- *The freeze leaked*: one revision after it (`compactableOk`'s context, above); "0 after the
  freeze" held only while the spec's real caller did not exist. Revision: the freeze requires every
  caller's glue (phase 3, above).
- *Phase 0 from a survey underestimates a widening of proved code* (M2 is mostly that, which the
  plan was not designed for). Revision: phase 0 drafts statements (above).
- *Reviews introduce defects*: M2's future-revision defect came from the compactor's first review
  repair ("any revision" instead of "a revision the store reached"), as round 2 of the pilot saw.
  The rule stands: a round after every repair, looking hardest at what changed.
- *Reviews trusted unproved specs*: a sharpened principle (`.claude/skills/spec/PRINCIPLES.md`,
  "Complete": a contract against its implementation's Go body when that implementation's spec is
  unproved).
- *Execution*: agents drifted to proving and deleted finished proofs. Revision: the agents' brief
  (phase 4, above).
- *Cost*: a round is about 10-15 minutes of agent time plus long builds, and M2 needed many of the
  user's decisions (eight so far): cheaper than re-proofs, not free.

**The comparison** (step 3's main metric): spec revisions after the freeze, 1 for the compactor (by
M2's glue), against about 5 for the read-index baseline over two weeks; not yet fair (hours against
weeks, and M2 not finished).
