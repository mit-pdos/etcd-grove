# Multi-person, multi-agent collaboration

**Status (2026-10-08):** in use. Built: the loop in `AGENTS.md`, the board
(`etc/tasks.py`: tasks, chat, roadmap sync, `wait`), landing (`etc/land.py`), the
protected paths (`etc/protected-paths.txt`) and CI's `board.yml`. Not yet built:
the published dependency cache ("Build cost"), seed tasks (the first agent's
roadmap sync creates them). Decisions made by the people running this are in
`decisions.md` (2026-10-08).

## The setting

The goal is to verify all of etcd. Several people run agents continuously on VMs
watching this repository, each started with little more than "Go". People steer at
two levels:

- **Big ideas** (directions, scope, what to prove, design decisions) go through
  files in the repository: `manual-notes.txt` for people's standing directions, and
  `notes/chat/` for conversations between people and agents.
- **Small questions** (how to state this lemma, why this build fails) stay between
  an agent and whoever runs its session, as with any single agent.

The design follows from five facts:

1. **Git is the only shared medium.** Agents run on different machines, under
   different tools, with no shared filesystem or message bus. All coordination state
   is files on `origin`, and a `git push` that wins or loses a race is the only lock.
2. **An agent remembers nothing between sessions.** Everything needed to resume
   (what, why, how far) is in pushed commits: the task file and the task branch.
3. **Soundness can't depend on agents behaving well.** An agent that weakens a spec,
   adds an axiom or proves the wrong thing does damage that looks like progress.
   Machines check what they can (`lake build`, `etc/tcb-report.py --check`), and a
   person signs off on whatever changes what is trusted or claimed.
4. **The Go side is a bottleneck.** `etc/verified-code.py` (2026-10-08): raft 53.8% of
   its Go lines verified, etcd 0.4%. Goose translates 4.9% of etcd's lines (of
   `server/v3/etcdserver`'s 279 functions, only a handful). Most etcd work starts with
   translation, which happens in other repositories (Goose, Perennial's
   `etc/update-goose-new.py`, the `upamanyus/etcd` fork) and arrives here only through
   a Perennial pin bump.
5. **Cheap conflicts matter.** Dozens of agents editing one shared file spend their
   time rebasing, so each unit of work has its own files, and the shared files are
   either generated or rarely touched.

## Who writes what

| file | written by | for |
|---|---|---|
| `manual-notes.txt` | **people only** (`etc/land.py` refuses agents' edits) | standing directions; the top priority signal |
| `notes/chat/<topic>.md` | people and agents, append-only | big ideas, both ways |
| `notes/roadmap.md` | agents (`roadmap-sync` tasks); people may edit | the directions ranked, each with its design doc and tasks |
| `notes/design/<topic>.md` | agents (`design` tasks) | one topic's property, code, trust boundary, interfaces, tasks |
| `notes/tasks/<id>.md` | agents, via `etc/tasks.py` for the frontmatter | one unit of work |
| `notes/STATUS.md`, `decisions.md`, … | agents, in a landing | everyone |

## The loop

`AGENTS.md` states it for the agents; `CLAUDE.md` imports it. An agent runs, until its
session ends:

1. `etc/tasks.py next --claim` picks and claims, in this order:
   1. **`lean` is broken** (the latest finished CI run failed; needs `gh`): create and
      claim a `fix-lean` task. Nothing else matters until it is fixed.
   2. **A person wrote in chat**: an open thread whose last message is a person's,
      that no agent is replying to. `chat take` marks the agent as the thread's
      `handler` for two hours, so other agents leave it alone.
   3. **`manual-notes.txt` changed**: its blob hash differs from the `manual-notes:`
      line of `notes/roadmap.md` (or there is no roadmap). The agent creates and claims
      `roadmap-sync-<hash>`: bring the roadmap in line, create a `design` task for
      each new direction, and record the new hash.
   4. **Its person's unfinished work**: a claim of the same `owner` (git
      `user.email`, which one person's agents share) with no push for 2 h.
   5. **A review**: a task in `review` that another person's agent implemented.
   6. **The best open task**: dependencies done; priority, then how many tasks it
      unblocks.
   7. **A stale claim**: anyone's, with no push for 24 h; continue from its branch.
2. Nothing to claim: if a roadmap direction has no design doc or design task, plan
   it; otherwise `etc/tasks.py wait` polls `origin` (default every 5 minutes) until
   `next` has something.
3. Work on `task/<id>`, pushing at every milestone (`etc/tasks.py heartbeat` at least
   hourly). The pushed branch is the handoff.
4. `etc/land.py`, then back to 1.

An agent holds one claim at a time; there are no per-person limits on how many agents
a person runs.

## Tasks

One file per task, `notes/tasks/<id>.md` (format: `notes/tasks/README.md`), so two
agents edit the same file only when they are on the same task.

**Size.** A task is one landing: a few hours of agent work, typically one Go
function's spec and proof, or a small group in one file. A design task cuts its topic
into tasks of that size. A proof that turns out larger gets split: land what there is
(a precise `sorry` beats an unpushed branch) and create follow-up tasks.

**States.** `open → claimed → done`, or `→ review → reviewing → done` for work whose
statement a second agent must check, `needs-human` while a person must act (merge a
protected PR), `dropped`. A task whose `depends` aren't all `done` is waiting, not a
separate state: `etc/tasks.py block <id> --on <dep>` adds the dependency and releases
the claim. Only `etc/tasks.py` changes the frontmatter, and CI runs
`etc/tasks.py check` (fields, ids, dependencies, cycles).

**Claiming.** Every state change commits only that task file on top of a fresh
`origin/lean` (git plumbing, without touching the working tree) and pushes it straight
to `lean`. A rejected push is retried against the new `origin/lean`, re-checking that
the task is still claimable, so a race has exactly one winner. Tool-written lines go
in the task's `## History` (kept last); the agent's notes go in `## Log`, above it, so
the two merge cleanly.

**Liveness** is the newer of `claimed-at` and the last push to `task/<id>`, so
heartbeats are branch pushes, not commits on `lean`. `etc/land.py` rebases the task
branch, so task-branch pushes use `--force-with-lease` against the tip last fetched:
they can rewrite the agent's own branch but never a newer push by someone else.

## Chat

`notes/chat/<topic>.md` (format: `notes/chat/README.md`): one thread per big idea,
messages appended under `### <time> · <name> [person|agent]` headers. People write by
hand (an untagged header counts as a person's) or with
`etc/tasks.py chat post --person`; agents use `etc/tasks.py chat new|take|post|resolve`,
which commits on `lean` directly like task changes. `.gitattributes` merges the files
with `union`, so concurrent appends both survive.

Agents open a thread when something needs people's judgment at the level of
direction: a proposed design ("here is what I think the cache proof should state"),
a spec of an exported result that is false, a scope decision, a translation
limitation that changes what can be verified. A thread waits on whoever didn't speak
last; `etc/tasks.py status` lists both kinds. A reply that turns a thread into work
says which tasks it created.

Why not GitHub issues or discussions: they work, but they put the coordination
outside the repository, where agents of other tools and offline readers don't see
it, and they would make the board depend on a token on every VM.

## Landing

`etc/land.py` is the one way an agent lands work on `lean`:

1. Rebase onto `origin/lean` (`--force-rebase --no-keep-empty`, which drops empty
   heartbeat commits) and regenerate `Link.lean` (`etc/gen-link.py`, which reads the
   proofs' callee hypotheses), committing it if it changed.
2. Refuse a change to `manual-notes.txt`. `etc/tasks.py check` if `notes/tasks/`
   changed. If anything outside `notes/` changed: `lake build`, then
   `etc/tcb-report.py --check`.
3. A change to a **protected path** (`etc/protected-paths.txt`: the TCB baseline,
   `Results.lean`, the protocol model, the specs of the exported results, the
   Perennial pin, the rules themselves) is pushed to the task branch and opened as a
   PR to `lean` (with `gh`; otherwise the compare URL is printed). The task goes to
   `needs-human`.
4. Otherwise push to `lean`, retrying from 1 if the push loses a race. Then close the
   task (`done`, or `review` if a `Spec/` file, an axiom or the baseline changed),
   recording the landed range, and delete its branch.

CI: `lean.yml` builds and checks the trust base on pushes that change anything
outside `notes/` (a newer push replaces a queued build); `board.yml` checks the board
and `Link.lean` on every push, and fails a push to `lean` that changed a protected
path in a commit that GitHub didn't commit (a PR merge) and that has no
`Approved-by: <person>` trailer (people pushing directly). Two individually green
landings can still break `lean` together (say, the same lemma name twice); rule 1.1
makes fixing that the next thing any agent does.

## Review

An agent's proof checks or it doesn't. What needs a second look is whether the
**statement** is right: a spec too weak to be useful, an axiom false of the Go code, a
precondition nobody can meet. `main`'s `notes/false-statements.md` shows how often
this happened in the Rocq development. So a landing that adds or changes a `Spec/` file
or an axiom goes to `review`, and another person's agent checks the statement against
the Go source and the design doc, records its verdict in the task log, and closes the
task or opens a fix task. People review the protected PRs and, from time to time, a
sample of agent reviews.

## Design docs

A topic needing more than a couple of tasks gets `notes/design/<topic>.md` first:

- **the property**, in words, then as the draft top-level Lean statement;
- **the code**: which Go functions, and their translation status (`etc/verified-code.py`);
- **the trust boundary**: what is axiomatized (the storage backend, the network, gRPC)
  and why that is acceptable;
- **the interfaces**: the specs other topics rely on (for example the raft
  `Node`/`RawNode` interface `etcdserver` consumes). An interface spec is a contract:
  changing it once others depend on it is a `design` task naming every proof it breaks;
- **the task breakdown** and dependency order;
- **the open questions**: each one a chat thread or a decision recorded in `decisions.md`.

A design doc that changes what the project will claim gets a chat thread so people
see it.

## Cross-repo work

```
upamanyus/etcd, upamanyus/etcd-raft (branch goose)    Go sources (the forks)
goose-lang/goose                                      the translator
mit-pdos/perennial (branch lean)                      etc/update-goose-new.py's package lists,
                                                      Perennial.Code.go_etcd_io (translation),
                                                      the framework, the public etcd proofs
this repository                                       pins Perennial by commit
```

A `translation` or `framework` task produces a change in one of those repositories,
then a **pin bump** here. Pin bumps are serialized: one `pin-bump` task at a time
batches the upstream changes that are ready, moves the pin, fixes what the move
breaks, and lands through a PR (the pin is protected); every other agent then
rebuilds the dependencies once. For each etcd topic the first task is usually a
`translation` task: find why Goose skips the target functions (an unsupported Go
feature, a package missing from the list), then fix Goose, add the package, or make a
minimal, recorded edit to the fork; each fork edit is listed in the topic's design
doc, because it changes what is verified. (Who may push to those repositories is
still open: see "Open questions".)

## Build cost

A fresh clone builds Perennial, Iris and Batteries before anything here. CI caches
the built `.lake/packages` per pin; publishing it (with an `etc/fetch-deps.sh`) would
let a new VM start in minutes; until then, agents on one VM share one built
`.lake/packages` across worktrees. Inside a task, agents check single files with
`lake env lean <file>`; `etc/land.py` runs the full build once. Modules on the
critical path (`etc/build-report.py`; today `Proof/stepLeader.lean`, 1m08s) are worth
`infra` tasks, since every landing waits on them.

## Workstreams toward all of etcd

`notes/roadmap.md` ranks these and keeps them current; this is the starting point,
from `manual-notes.txt` as of 2026-10-08.

1. **etcd `cache`** (manual notes): independent of `server`, and partly translated
   (99 functions: 6 translated, 3 verified, 2 assumed, by Perennial's public proofs).
2. **Consistent index** (manual notes): `etcdserver/cindex` (17 functions translated,
   none verified) and the hooks in `server.go` that update it (`server.go:978`,
   `:2448` at etcd `f061acd09`): the invariant relating the consistent index, the
   applied raft entries and what the backend persisted, and the known bugs it rules
   out. Translating the `server.go` parts comes first.
3. **`EtcdServer.run`** (manual notes, high level): needs the raft `Node` interface (6)
   and most of `etcdserver` translated. Starts as a design doc fixing the interfaces
   (raft below, apply/backend beside) so that 2 and 6 build towards it.
4. **Proof engineering** (manual notes): a proof library tuned for build time and for
   tokens per proof, instead of `wp_auto`. Measure first (`etc/build-report.py`,
   token counts of existing proofs), compare candidates on a fixed benchmark of
   existing proofs, then migrate. Likely lands partly in Perennial.
5. **Finish raft**: `confchange` (0%), `node.go` (7.9%), the rest of `rawnode.go`,
   the `raftLog.slice` `sorry`, the `confchange.Restore` axiom.
6. **The rest of etcd**, by package, in the order of the dependency graph:
   `mvcc`/backend (axiomatized today), `lease`, `auth`, `apply`, the v3 RPC layer, the
   client; each starting as a `design` task.

The end-to-end statement (etcd's KV API is linearizable, given axiomatized disk and
network) gets its own design doc early, even while unprovable, so the per-package
specs are written to compose into it.

## Hotspots

- `Link.lean`: generated from the proofs; `etc/land.py` regenerates it after every
  rebase. Never merge it by hand.
- `STATUS.md`: edited by hand in landings; keep edits small. The live board is
  `etc/tasks.py status` (also on every `board.yml` run's summary page), not a file.
- Shared definitions (`Defs.lean`, `Inv*.lean`, `Base.lean`): a change there is its
  own small task, landed quickly.
- `tcb-baseline.txt`, the pin: protected.

## Open questions

- Who can push to the upstream repositories (`upamanyus/etcd`, `upamanyus/etcd-raft`,
  `goose-lang/goose`, `mit-pdos/perennial`)? Agents need write access to a branch
  there, or a fork the pin can point at (for example `upamanyus/perennial` branch
  `etcd-grove`, merged upstream by a person from time to time).
- Whether `gh` (and a token) is on every VM: without it `next` can't see a red CI
  (an agent's own `lake build` in `land.py` still catches its own breakage), and
  `land.py` prints a compare URL instead of opening the PR.

## Rollout

1. ~~`AGENTS.md`, the loop; archive the port-era briefs; `notes/README.md`.~~ Done
   2026-10-08.
2. ~~`etc/tasks.py` (tasks, chat, roadmap sync, `wait`), `board.yml`.~~ Done 2026-10-08.
3. ~~`etc/land.py`, the protected paths and their CI check.~~ Done 2026-10-08.
4. Seed tasks: the first agent's `roadmap-sync` task writes `notes/roadmap.md` and a
   `design` task per direction; add the known raft gaps (workstream 5) as `proof`
   tasks.
5. `etc/fetch-deps.sh` and the published dependency cache.
6. Trial with two people's agents for a few days; record in `decisions.md` what broke
   (claim races, stale claims, review load, chat volume) and adjust before adding
   more people.
