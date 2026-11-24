# Spec-first: the phases of a stage

A **stage** is one increment of the result. Usually there is one: the challenge's goal; a later stage
is work continued from an earlier one (a new session on the same goal). Each stage goes through five phases in order, and
each leaves a committed record (below, "Phase records"): a phase without its record did not happen.

**What spec-first fixes before proving, and what it does not.** Before any proof, the stage fixes its
**interface**: the hub statements and their slots (`HUBS.md`), the bodies of
the invariants that cross packages, and the spec of every function called across a package boundary.
These are what a late change is expensive in: every package's proofs are built on them. A package's
**internal** specs (functions called only inside it, helper lemmas, model laws) are written and
proved together, by the agent proving that package, and change freely while it proves: a wrong
internal statement is found by the prover in minutes and costs only its own proofs. The exception is
the invariant of an object shared across threads: its gaps take rounds to find (Prove, below).

*Why this line.* In paired runs (four stages of two systems; spec-first against the same agent
without it), the earlier form of this file, which froze every internal spec and added
Test and Probe phases before the freeze, spent longer before its freeze than the other arm spent on
the whole stage, every time (144 vs 87 min, 87 vs 63, 123 vs 91, 194 vs 139), and still changed
internal frozen statements after it (overflow premises, `timeless` claims, a mutex invariant: things
only a proof finds). The other arm's wrong statements were all caught by its prover and fixed
locally in minutes. Both arms found the same bugs in the targets. Proving itself was not slower
after a freeze: the cost was the serial work before it.

**The proof gate.** No proof agent is started before the interface is frozen:

```
git rev-parse -q --verify refs/tags/stageN-frozen || echo "NOT FROZEN: no proof agents"
```

Run it before every batch of proof agents and put its output in the batch's brief.

| phase | does | exits when |
|---|---|---|
| **Scope** | reads the given statement and premises; records what they cover; runs the test and the bug read | the scope record is committed |
| **Interface** | the hub statements and slots, the cross-package invariants in full, the cross-package specs; `sorry` bodies; builds | it builds |
| **Review** | one fresh reviewer round on the interface; repairs; a check of the first-tier repairs | no first-tier finding left |
| **Freeze** | fixes the interface; attacks every new hypothesis | the user approves (or the logged decision); the tag `stageN-frozen` |
| **Prove** | per package, in parallel: internal specs and proofs, top functions first, then riskiest | no `sorry` and no hypothesis of yours left on the goal's path (`CHALLENGE.md`, "Done") |

## Scope

In a challenge the top-level statement, its premises and the program it is about are given
(`CHALLENGE.md`): Scope does not choose them, and nothing you learn changes them. It records what
they mean, so that every later statement is written against the right target:

- **The configuration** the program covers: the machines, what the orchestrator chooses at random
  and over which ranges, the workload, the faults the network model allows (`NET.md`), and what the
  statement leaves out (crashes, liveness, configurations outside the ranges). Read it off the Go,
  not the prose.
- **The premises**: each class the statement takes, what it asserts, which calls of the program it
  covers; and whether each holds of the real library as you read it (`CHALLENGE.md`, the premise
  rules). A premise you believe false or too weak for the program is a finding now, not after the
  proofs.
- **What every case breaks**: list the paths the program can take that the obvious invariant rules
  out (a leader change, a recovery, a retried read, an unknown write, a configuration the
  orchestrator may choose): each is a design decision better made now than in the middle of the
  interface's plumbing.
- **Bugs in the target**: read the in-scope code for bugs, and write each finding's failing Go test
  (`TRUST.md`, "Findings"). Then a **stress test with direct checks** (required, timeboxed to about 20
  minutes of agent time): run the in-scope configuration many times under randomized schedules and
  `-race`, and check the replication invariants directly, not only the history: each request takes
  effect at most once, the replicas' executed sequences are prefixes of one another, every reply
  answers its request. A bug that shows in a short client history only rarely shows at once in these
  checks. (In one paired run, a duplicate execution that reading missed was found by such a check
  within half an hour in one arm, and by the other arm's protocol proof after its freeze, three
  times later.) Long open-ended Go bug hunts beyond this are not needed.
  Phrase a bug read, and any brief for an agent doing one, as a correctness review: check the
  protocol's safety properties (agreement, linearizability, the invariants the design will state)
  against the code, and name the properties and the code paths to check. Do not phrase it as a
  search for inputs or schedules that crash the program, and do not list crash classes (nil
  dereferences, out-of-range indexes, integer underflow, and the like): such briefs read as
  vulnerability hunting and can trip the model's safety classifier (in one run a bug-read agent
  was stopped, and the session fell back to an older model for the rest of the run). Crashes in scope are caught anyway: the driver's checks and the proof cover every panic.

## Interface: the statements every package is proved against

One pass, by the main session or one agent, small: only what more than one package names.

- **The hub statements and slots** (`HUBS.md`).
- **Invariants written in full**: each cross-package invariant's *body* (not only its name), its
  ownership (who allocates it, who opens it, which ghost state it holds and who holds the other
  halves), and the **laws** its clients use (persistence, agreement, the facts a client extracts),
  stated with `sorry`. Judge it by `PRINCIPLES.md` (the client keeps its own invariant: TaDa; bounds
  are owned; a new mode redefines in place; laws, not unfolds).
- **The cross-package specs**: the spec of every function called across a package boundary, each
  machine's `main` (or the kit function it calls), and the client spec of the system that the
  client machines serve (`NET.md`), building with `sorry`. The goal's proof itself is written
  against them now (the start, the shares, one case per machine), with `sorry`s only below it: the
  first full build shows whether the interface can carry the goal.
- **Hypotheses attacked when written**: a new, widened or restated hypothesis gets its attack
  (`TRUST.md`, "Attacking a hypothesis") as soon as it is written, in parallel with the rest.
- **Design before plumbing**: when a change runs through shared definitions with many use sites, first
  write the design as text in the stage plan — each changed statement old → new, and for each the
  callee specs it is proved from — and have Review check that chain before any site is threaded.

It writes no package-internal spec and no proof. Keep it small: if it grows into most of the
project's statements, it has become the internal drafting it is meant to leave to the packages.

## Review: one round, then the repairs checked

A fresh reviewer (a new agent, given `PRINCIPLES.md`, the `examples/`, the interface, the Go code and
the callers — not the author's conclusions) ranks each interface statement and invariant in two tiers:

- **Requirements** (fail one and it is wrong): true of the code; sufficient for every caller; faithful
  to concurrency; no unneeded premise.
- **Preferences** (among correct ones): abstraction; implementation independence; the weakest pre and
  a post no stronger than a caller needs; size; coupling.

Rules:
- **One round**, then the first-tier findings are repaired and **one** fresh reviewer checks the repair
  diff only. Second-tier findings are decided by the main session (apply or record why not) without
  another round. More rounds found, in earlier runs, mostly what the provers found anyway, at a
  higher cost.
- **The newest abstraction** gets the reviewer's most attention: post-freeze misses cluster in it.
- **A context bundle**: one generated file with the statements unfolded, the Go functions, the callers'
  call sites. The reviewer reads it first.
- **Reviewers never build.** Repairs do, with targeted builds (`TOOLS.md`, importers).

## Freeze

The interface is fixed when Review has no first-tier finding left, **every new or restated
hypothesis has been attacked** (`TRUST.md`, "Attacking a hypothesis"), and the user approves
(when no user can answer, the agent's logged decision stands in for the approval; the freeze still
happens).

**The freeze is a tag**: an annotated tag `stageN-frozen` on the commit holding the interface, and a
`notes/decisions.md` entry naming the tag, what it freezes, the review and the attacks. After
the freeze, a change to an interface statement needs a change-log entry with its cause (below).
Internal statements are not frozen.

## Prove: per package, internal specs with their proofs, top-down, riskiest first

One agent per package (or per group of packages sharing a slot), all started at the freeze, each in
its own worktree. Each brief names the freeze tag (with the gate's output) and its package. Each agent:

- **writes its package's internal specs and proves them, top-down**, in the order that exposes
  problems first. First the package's top functions (those the interface specs name, and each
  thread's entry point) are proved end to end against stated `sorry`s for their callees and ghost
  steps: one round then shows every gap in the design. Then the `sorry`s, starting with **the step
  that must preserve the riskiest invariant in its hardest case** (the concurrent update, the
  reconfiguration, the view change, the restore): this is where an invariant's strength is checked.
  Ghost lemmas and helpers proved before the top function that uses them is stated rest on a guess.
- **designs the lifecycle first** for each object that passes between threads (`LIFECYCLE.md`), and
  writes that object's invariant in full (`PRINCIPLES.md`, Invariants) before proofs rely on it.
- **changes its internal statements freely** while proving (a premise added, a postcondition
  strengthened, a helper restated); no ceremony, a line in the package's notes. A change to the
  invariant of an object shared across threads goes through its lifecycle table first.
- **never edits an interface statement**: a change it needs goes, with the caller that needs it, to
  `notes/hub-requests.md`, and the agent goes on with a marked `sorry` at that step. The main session
  decides each request, applies the accepted ones in one commit, logs them (below) and tells every
  running agent the commit to merge.
- **lists every unfold of another package's definition** it needed: each is a missing law in that
  package's API, added there.
- **never deletes a finished proof**: a broken one keeps its text, the `sorry` on its failing step
  naming the commit where it was whole.

**Keep the critical path parallel.** The main session knows which obligations the stage's result
waits on longest. Work that does not depend on them (a library spec, another package's lemmas, a
model law) goes to another agent, not into the queue of the agent on the critical path.

**The change log** covers the interface only: every change to a frozen statement is logged in the
stage plan (old → new, why), tagged **when it is made**:

- **F** fix: the statement is false or unprovable (a review miss);
- **R** redesign: an abstraction replaced (the costliest miss);
- **W** weakening: an unnecessary premise dropped;
- **E** extension: a spec, law or vocabulary the design lacked;
- **D** decision: the user changed scope or design;
- **A** adaptation: a client restated over a changed API;
- **C** conformance: renames, moves, follow-through.

With how it was found (*proof*, *Go* reading, *user*, *check*), whether it touches a public or
trusted statement, and whether the user approved it: e.g. `[F, proof, trusted, awaits user]`. The
metric is F and R after the freeze, per interface statement.

## Phase records

Each phase's exit leaves a committed record, so that whoever reads the project (a reviewer, the user,
the next session) can see that the phase happened and what it found:

| phase | record |
|---|---|
| Scope | a `notes/decisions.md` entry: the configuration, the premises and what each covers, the cases that break the obvious invariant; the findings in `issues/` |
| Interface | a commit with every interface statement; the stage plan lists them |
| Review | `notes/review/stageN.md`: the reviewer (a fresh agent), its brief, the findings by tier, the repairs and their commits, the check of the first-tier repairs |
| Freeze | the tag `stageN-frozen` and its `notes/decisions.md` entry |
| Prove | the change log; the proof agents' briefs name the tag; each package's notes (internal changes, unfolds) |

## The feedback loop

Every post-freeze F or R to an interface statement names the review criterion that should have
caught it, or "none". A "none"
becomes a new or sharper principle in `PRINCIPLES.md`; a missed existing criterion gets an example in
`examples/`. A criterion whose findings are later reverted counts against it.

## The build budget

Builds dominate repair time once the project is large. Find the callers of a changed statement with an
importer script, not by building and reading failures; check edited files with the Lean server; one full
build per round, in the background. Each commit message says what was checked.

**One build of a shared change.** When several worktrees run at once, a change to widely imported
modules (a framework pin bump, a hub statement) merged into each of them recompiles the same modules
once per worktree. Build the main branch once after such a change lands and seed each worktree's build
directory from it (a full copy, never hard links) before building there. Full builds take turns behind
one machine-wide lock (`flock`); targeted builds and the Lean server do not take it.

**Merging takes a lock.** With several agents merging into the main branch, one can move it between
another's checks and its fast-forward. Merge from the branch's worktree under one lock held from the
check through the fast-forward: check the main branch is merged, run the checks, fast-forward.

**Wait on notifications, not on sleeps.** Run agents in the background and act when each one's
completion notification arrives; never wait for an agent with `sleep`, an `until` loop over a file or
a commit, or a fixed timeout. A finished agent's report then lands at once, not when the sleep
ends. Between notifications, do the work that does not depend on them: the next brief, the review
bundle, the decisions on hub requests already filed. (One run: 49 polls, 47 minutes with no agent
running while the main session slept.)

## Who decides

The goal and its premises are the challenge's: nobody approves a change to them, because there is
none (`CHALLENGE.md`). The user approves: each freeze; every change to a frozen statement; a fix to
the system's code. A new axiom or trusted model is never an option. The agent decides everything else and keeps
going between those points. When asking, give the options, a recommendation, and the evidence.
When no user can answer, the agent takes its recommendation and logs it as its own decision; an
approval it cannot get is replaced by that entry, never by skipping the phase it closes.

**Proceed with a veto.** Waiting for the user is the largest share of a stage's wall time, and before
the freeze a reversed decision costs statements and glue, not proofs. So a question that is not a hard
stop is not a stop: the agent takes its recommendation, records it in the stage plan as "decided by the
agent, pending the user" (options, recommendation, evidence), and goes on; the user reads these in
batches and vetoes. **Hard stops**: each freeze; a second spec family beside an existing one; a
change to a frozen statement; a declared premise you believe false or unsatisfiable, or a bug that
blocks the goal (`TRUST.md`): report it with the evidence. Everything else is decided and logged.

**Questions do not block.** An agent working in the background appends each question and each
pending decision to `questions.md` at its worktree's root (options, recommendation, what depends on
the answer) and goes on with what does not depend on it; whoever orchestrates relays the file to the
user and the answers back. It ends its turn only at a hard stop with nothing left to do that does not
depend on the answer.

*Where, and what counts as approved.* Make the stage's worktree and branch at Scope, not at the freeze,
so `questions.md` is always at the worktree's root, where every agent on the branch and the
orchestrator find it. An entry marked "approved by the user, <date>, via <session>" (or "vetoed") is
the user's decision: agents act on it without asking again. An approval given anywhere else (a dialog,
a chat) is first copied into `questions.md` in that form by whoever received it; agents act on the
file, not on relayed messages.
