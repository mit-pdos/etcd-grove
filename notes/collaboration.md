# Multi-person, multi-agent collaboration

**Status:** proposed, 2026-10-08. Nothing below is implemented yet except where it
says so; "Rollout" at the end is the order to build it in.

## The goal and the constraints

The goal is to verify all of etcd. Several people will point their agents (not
necessarily all Claude Code, not necessarily on one machine) at this repository with
a prompt as short as "Go". From that alone an agent must be able to find useful work,
avoid colliding with the others, land the result, and leave the repository in a state
the next agent can pick up from. People steer through `manual-notes.txt`; agents
coordinate through `notes/`.

The design follows from five facts:

1. **Git is the only shared medium.** Agents run on different machines, under
   different tools, with no shared filesystem or message bus. All coordination state
   is therefore files on `origin`, and a `git push` that wins or loses a race is the
   only lock.
2. **An agent remembers nothing between sessions.** Everything it needs to resume
   (what it was doing, why, how far it got) has to be in pushed commits: the task
   file and the task branch.
3. **Soundness can't depend on agents behaving well.** An agent that weakens a spec,
   adds an axiom or proves the wrong thing does damage that looks like progress.
   Machines check what they can (`lake build`, `etc/tcb-report.py --check`), and a
   human signs off on whatever changes what is trusted or claimed.
4. **The Go side is a bottleneck.** `etc/verified-code.py` (2026-10-08) shows raft at
   53.8% of Go lines verified, but etcd at 0.4%. Goose translates only 4.9% of etcd's
   lines (of `server/v3/etcdserver`'s 279 functions, only a handful). Most etcd work starts with
   translation, which happens in other repositories (Goose, Perennial's
   `etc/update-goose-new.py`, the `upamanyus/etcd` fork) and reaches this repository
   only through a Perennial pin bump.
5. **Cheap conflicts matter.** Dozens of agents editing one `STATUS.md`, one
   journal, one `Link.lean` and one `tcb-baseline.txt` would spend their time
   rebasing. The layout below gives each unit of work its own files and makes the
   shared files either generated or rarely touched.

## Who writes what

| file | written by | read by |
|---|---|---|
| `manual-notes.txt` | **people only**; agents never edit it | everyone, first |
| `notes/roadmap.md` | agents (planning tasks), people may edit | planners |
| `notes/design/<topic>.md` | agents (design tasks), people review | the tasks of that topic |
| `notes/tasks/<id>.md` | agents (create, claim, log, close) | everyone |
| `notes/STATUS.md` | agents, on landing; one section is generated | everyone, second |
| `notes/decisions.md`, `gotchas.md`, `false-statements.md`, … | agents, when a task earns it | everyone |
| `notes/questions.md` | generated from tasks in state `needs-human` | people |

`manual-notes.txt` stays free-form, so people can just write. Agents treat it as the
priority signal: a direction there outranks anything an agent invents, and a person
withdraws a direction by deleting it. An agent that wants something from a person
doesn't edit `manual-notes.txt`. It puts the question in its task file and sets the
task to `needs-human` (see below).

Main's `notes/README.md` conventions carry over: write for a stranger, use absolute
dates, record dead ends, and correct stale text in place rather than appending. The
port-era briefs (`notes/{proof,spec,protocol}-porting-task.md`,
`step-branch-task.md`) describe one-off, single-machine fan-outs that are finished;
move them to `notes/archive/` so that an agent reading `notes/` doesn't follow them.
`porting-guide.md` stays, because it is still the Rocq → Lean reference.

## The "Go" protocol

`AGENTS.md` (read by most agent tools) holds this protocol, and `CLAUDE.md` imports
it, so every tool gets the same instructions. An agent given no other instruction
does this:

0. **Sync and isolate.** `git fetch`, make a fresh worktree (or clone) on a new
   branch from `origin/lean`, and get a build (see "Build cost").
1. **Pick work** using the first rule below that yields a task. `etc/tasks.py next`
   implements the order, so agents don't each reimplement it:
   1. **`lean` is broken** (CI red, or `lake build` fails on `origin/lean`): claim or
      join the `fix-lean` task. Nothing else lands until that is fixed.
   2. **Your own person's work is unfinished**: a task `claimed` by an agent of the
      same person (same `git config user.email`) with no live session on it. Resume
      it from its branch.
   3. **A review is due**: a task in state `review` that was implemented by someone
      else's agent (see "Review").
   4. **An open task**: state `open`, all `depends` done, highest priority first
      (priority comes from the roadmap, which ranks `manual-notes.txt` directions
      first). Within a priority, prefer the task that unblocks the most others.
   5. **A stale claim**: `claimed`, with no heartbeat or push to its branch for 24 h.
      Take it over and continue from its branch.
   6. **Nothing is open**: plan. Take the highest-priority direction in
      `manual-notes.txt` (or the roadmap) that has no design doc, write the design
      doc and the tasks it breaks into, and land them. Planning is a task like any
      other (`kind: design`), so two agents don't plan the same direction.
2. **Claim** it (below), then work on the task branch, pushing at every milestone.
   The pushed branch is the handoff if the session dies.
3. **Land** it (below), close or update the task, update `STATUS.md` if anything
   moved, and release the claim.
4. **Loop** back to step 1 until the session's budget runs out. A session that ends
   mid-task pushes the branch and appends a log entry saying where it stopped.

## Tasks

One file per task, `notes/tasks/<id>.md`, so two agents never edit the same file
unless they are on the same task:

```markdown
---
id: cindex-SetConsistentIndex
title: Spec and prove cindex.consistentIndex.SetConsistentIndex
kind: proof            # proof | spec | translation | framework | design | infra | review | fix-lean
state: open            # open | claimed | review | needs-human | blocked | done | dropped
priority: 1            # 1 = a manual-notes direction; 2 = on its path; 3 = everything else
design: notes/design/consistent-index.md
depends: [goose-cindex]
claimed-by:            # "<git user.name> <host>/<session>", set by etc/tasks.py claim
heartbeat:             # ISO time; refreshed by etc/tasks.py on every push of the branch
branch:                # task/<id>
---

## Goal
What is to be true when this is done, in terms of files and theorems
(e.g. `cindex.consistentIndex.SetConsistentIndex.wp_proof` with no `sorry`).

## Context
Pointers: the design doc section, the Go source (`server/etcdserver/cindex/cindex.go:NN`),
the callees' specs, related tasks.

## Log
- 2026-10-09 (alice's agent): spec drafted; proof stuck on the backend axiom, see …
```

**Size.** A task is one landing: a few hours of agent work, typically one Go
function's spec and proof, or a small group of functions in one file. A design task
cuts its topic into tasks of that size. A proof that turns out to be larger gets
split. The agent lands what it has (a precise `sorry` beats an unpushed branch) and
creates follow-up tasks.

**States.** Only `etc/tasks.py` changes the frontmatter (claim, release, heartbeat,
done, block), so the format stays machine-checkable. CI runs `etc/tasks.py check`:
fields present, ids unique, `depends` resolvable, no cycles. The Log and body are
free text.

**Claiming.** `etc/tasks.py claim <id>` fetches, checks that the task is still
claimable, sets `claimed-by`/`heartbeat`/`branch`, commits `claim: <id>` (touching
only that file) and pushes it straight to `lean`. If the push is rejected it
rebases. If the rebase shows someone else won the claim, it picks another task;
otherwise it pushes again. Git's compare-and-swap on the branch ref is the lock. An
agent holds one claim at a time. A claim that needs a person's input moves to
`needs-human` and frees the agent for another task.

**Blocked work.** When a task hits a defect elsewhere (a false spec, a Goose
limitation, a missing framework lemma), the agent creates a task for the fix (or
finds the existing one), adds it to `depends`, sets `blocked`, and records the
evidence in the new task. This keeps diagnoses in one place, as main's `bugs/`
directory did.

## Landing

`etc/land.py` is the one way an agent lands work on `lean`:

1. Rebase the task branch onto `origin/lean`, and regenerate generated files rather
   than merging them (`etc/gen-link.py` for `Link.lean`; the generated section of
   `STATUS.md`).
2. If anything outside `notes/` changed: `lake build`, then
   `etc/tcb-report.py --check`. Either failing stops the landing.
3. If a **protected path** changed, push the branch and open a PR to `lean` for a
   person to merge, set the task to `review`, and stop. Protected paths:
   - `etc/tcb-baseline.txt`: an axiom or `sorry` was added or removed. Removing a
     `sorry` only needs a quick human look; adding an axiom is a trust decision.
   - `EtcdGrove/**/Results.lean` and the `Spec/` files of exported results: what the
     project claims.
   - `lakefile.toml`, `lake-manifest.json`: the Perennial pin (see "Cross-repo
     work").
   - `AGENTS.md`, `CLAUDE.md`, `etc/land.py`, `etc/tasks.py`, `.github/`: the rules
     themselves.
4. Otherwise push to `lean` (retrying from step 1 if the push loses a race), and mark
   the task `done` or `review`.

CI on `lean` re-runs the build and the TCB check on every push. It also fails a push
that changed a protected path outside a merged PR, which catches an agent that
bypassed `land.py`. Two individually green landings can still break `lean` together
(two agents adding the same lemma name, say). That is rare in Lean, and the
`fix-lean` rule makes it the next thing anyone does.

**Rejected: every landing through a PR with auto-merge.** Claims, heartbeats and
notes still have to be pushed directly, so a direct-push path exists anyway. A user
repository (`upamanyus/etcd-grove`) has no merge queue, so "require up to date"
would turn every landing into a rebase race in GitHub's UI. Gating only the paths
that change what is trusted puts human attention where it is worth something.

## Review

An agent's proof checks or it doesn't. The proof itself needs no review. What does
need review is whether the **statement** is right: a spec that is too weak, an axiom
that is false of the Go code, a precondition nobody can satisfy. Main's
`notes/false-statements.md` records how often this happened in the Rocq development.
So:

- Every task that adds or changes a `Spec/` file, an axiom or a trust-boundary triple
  goes to `review` when it lands. A different person's agent reviews it (rule 3 of
  "Go"). The reviewer checks the spec against the Go source and against the design
  doc, records its verdict in the task log, and either closes the task or opens a fix
  task. Main's `false-statements.md` "tells" are the checklist; port that file here
  when the first review needs it.
- People review the PRs for protected paths, and a sample of agent reviews.

## Design docs

A topic big enough to need more than a couple of tasks gets
`notes/design/<topic>.md` before any of its tasks exist. The doc states:

- **the property**, in words and then as the top-level Lean statement (draft);
- **the code**, meaning which Go functions, and their translation status from
  `etc/verified-code.py`;
- **the trust boundary**: what is axiomatized (the storage backend, the network,
  gRPC) and why that is acceptable;
- **the interfaces**: the specs other topics will rely on (for example the raft
  `Node`/`RawNode` interface that `etcdserver` consumes). An interface spec is a
  contract. Changing it after other topics depend on it is a `design` task of its
  own that names every proof it breaks;
- **the task breakdown** and dependency order;
- **the open questions**, each one either a `needs-human` task or a decision the
  doc makes and records in `decisions.md`.

## Cross-repo work

The Go code, its translation and the framework all live outside this repository:

```
upamanyus/etcd, upamanyus/etcd-raft (branch goose)    Go sources (the forks)
goose-lang/goose                                      the translator
mit-pdos/perennial (branch lean)                      etc/update-goose-new.py's package lists,
                                                      Perennial.Code.go_etcd_io (translation),
                                                      the framework, the public etcd proofs
this repository                                       pins Perennial by commit
```

A `translation` or `framework` task produces a change in one of those repositories
and then a **pin bump** here. Pin bumps are serialized: one `pin-bump` task at a
time. That task batches the upstream changes that are ready, moves the pin, fixes
whatever the move breaks, and lands through a PR (the pin is a protected path). Every
other agent then rebuilds the dependencies once.

For translation specifically, the first job on each etcd topic is a `translation`
task: find why Goose skips the target functions (an unsupported Go feature, a
dependency missing from the package list), then fix Goose, add the package, or make
a minimal, recorded edit to the fork. Each fork edit is listed in the topic's design
doc, because it changes what is verified.

## Build cost

A fresh clone builds Perennial, Iris and Batteries before it builds anything here.
CI already caches the built `.lake/packages` per pin. Publish that cache as a
downloadable artifact, with `etc/fetch-deps.sh` to fetch and unpack it, so that a new
agent starts in minutes rather than hours. Agents on one machine can share one
`.lake/packages` across worktrees by symlinking it.

Inside a task, agents check single files with `lake env lean <file>` and run the
full `lake build` once, in `land.py`. `etc/build-report.py` tracks the critical
path. As the proof grows, modules on it (today `Proof/stepLeader.lean`, 1m08s) are
worth `infra` tasks, because every landing waits on them.

## Workstreams toward all of etcd

`notes/roadmap.md` (the first planning task writes it) ranks these and keeps them
current. The ranking below follows `manual-notes.txt` as of 2026-10-08.

1. **Infrastructure for this plan** (`infra`): the Rollout below. Comes first,
   because the other workstreams run on it.
2. **etcd `cache`** (manual notes): `server`-independent and already translated in
   part (99 functions, 6 translated, 3 verified, 2 assumed, by Perennial's public
   proofs). Design doc: what the cache guarantees relative to the watched store.
3. **Consistent index** (manual notes): `etcdserver/cindex` (translated, 17
   functions, unverified) and the hooks in `server.go` that update it
   (`server.go:978`, `:2448` at etcd `f061acd09`). Design doc: the invariant
   relating the consistent index, the applied raft entries and what the backend has
   persisted, plus the known bugs it should rule out. Translation of the `server.go`
   parts is the first task.
4. **`EtcdServer.run`** (manual notes, high level): needs the raft `Node` interface
   (workstream 6) and most of `etcdserver` translated. Starts as a design doc that
   fixes the interfaces (raft below, apply/backend beside) so that 3 and 6 build
   towards it.
5. **Proof engineering** (manual notes): a proof library tuned for build time and
   for tokens per proof, as an alternative to `wp_auto`. Measure first, using
   `etc/build-report.py` and token counts of existing proofs. Then compare
   candidates on a fixed benchmark of existing proofs, and only after that migrate.
   It is a `framework` workstream, and its output may live in Perennial.
6. **Finish raft**: `confchange` (0%), `node.go` (7.9%), the rest of `rawnode.go`,
   the `raftLog.slice` `sorry`, and the `confchange.Restore` axiom. `STATUS.md`'s
   "Next" (follow the Rocq RawNode branch) belongs here, depending on decision 2
   below.
7. **The rest of etcd**, by package, in the order the roadmap's dependency graph
   gives: `mvcc`/backend (today axiomatized), `lease`, `auth`, `apply`, the v3 RPC
   layer, the client. Each starts as a `design` task.

The end-to-end statement (etcd's KV API is linearizable, given axiomatized disk and
network) should get its own design doc early, even while unprovable, so the
per-package specs are written to compose into it.

## Hotspots

- `Link.lean`: generated; always regenerate it after a rebase, never merge it.
- `STATUS.md`: its "Active work" section is generated by `etc/tasks.py status`;
  agents edit the rest by hand, on landing.
- Shared definitions (`Defs.lean`, `Inv*.lean`, `Base.lean`'s `IsPkgInit`
  instances): a change there is its own small task, landed quickly, because every
  proof downstream rebuilds and may break.
- `tcb-baseline.txt`, the pin: protected (see "Landing").
- The per-session journal of main's notes doesn't carry over. With many agents an
  append-only file is a permanent merge conflict, so the task logs are the journal.

## Decisions for the people running this

1. **Direct push to `lean` (recommended, as above) or PR-only.** If PR-only, claims
   need their own unprotected branch, and `land.py` opens auto-merge PRs instead of
   pushing.
2. **Is Lean now the primary development?** Recommended: yes, and the Rocq branches
   become read-only references. Otherwise every Rocq change needs a port and the
   two drift apart.
3. **Who can push to the upstream repositories** (`upamanyus/etcd`,
   `upamanyus/etcd-raft`, `goose-lang/goose`, `mit-pdos/perennial`)? Agents need
   either write access to a branch there or a fork the pin can point at (for
   example `upamanyus/perennial` branch `etcd-grove`, merged upstream by a person
   from time to time).
4. **Agent identity and limits**: whether each person caps their concurrent
   sessions, and whether some task kinds (design, review) are reserved for stronger
   models.

## Rollout

Each step is an `infra` task. The first is done by hand, because the task machinery
doesn't exist yet.

1. Write `AGENTS.md` (the "Go" protocol, short), point `CLAUDE.md` at it, and archive
   the port-era briefs. Add `notes/README.md` with the conventions.
2. `etc/tasks.py`: `list`, `next`, `claim`, `heartbeat`, `release`, `done`, `block`,
   `check`, `status`. Add `etc/tasks.py check` to CI.
3. `etc/land.py`, with the protected-path list, and the CI check for protected paths
   changed outside a PR.
4. Seed tasks: one `design` task per workstream 2-5 above, `roadmap`, and the
   known raft gaps of workstream 6 as `proof` tasks.
5. `etc/fetch-deps.sh` and the published dependency cache.
6. Trial with two people's agents for a few days. Then record in `decisions.md` what
   broke (claim races, stale claims, review load), and adjust before adding more
   people.
