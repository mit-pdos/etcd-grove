# Status

**Last updated:** 2026-09-23

This file is a snapshot of where the proof *is*. It carries no history: how
something got this way is in [journal.md](journal.md), why a design was
chosen is in [decisions.md](decisions.md), and statements that turned out to
be false of the code are in [false-statements.md](false-statements.md).

## Goal

Verify etcd using Perennial/Grove, starting with its Raft implementation.

## Where things stand

This repo (`upamanyus/etcd-grove`) is a fork of `mit-pdos/perennial`. The
Perennial framework and the Goose toolchain are inherited wholesale and are
not the object of study — the etcd proofs are.

The Go code under verification is **not in this repo**. It lives in two
forks, both on branch `goose`, wired up in `new/etc/update-goose-new.py` and
`etc/ci-goose-check.py`:

- `upamanyus/etcd-raft` → translated into `new/code/go_etcd_io/raft/`
- `upamanyus/etcd` → translated into `new/code/go_etcd_io/etcd/`

### The raft proof

`new/proof/go_etcd_io/raft/` holds two developments side by side, both
reached from `new/should_build.v`: the election proof in `election_proof/`,
and the older read-index work in `v3_proof/`. They share only `base.v`.
(The election work moved out of `v3_proof/election/` on 2026-09-22; see
[decisions.md](decisions.md).)

- `v3_proof/base.v` — `IsPkgInit` instances for the raft package and its
  dependencies. Boilerplate; grows as new packages are pulled in.
- `election_proof/protocol.v` — the **protocol model**: the abstract node
  state `nstate.t`, the transition relation `step`, the ghost state
  (`own_raft_ghost`, `is_message`, `is_vote`, `is_leader`) and
  `is_leader_unique`, the at-most-one-leader-per-term fact the model exists
  to supply — an internal lemma, not the result (see "What is proved"). The ghost state is constructed, not axiomatized:
  per-node `ghost_map`s of `term ↦ candidate`, no Iris invariant, `is_leader`
  a quorum of votes, and `own_raft_ghost_alloc` to show it is inhabited.
  **No `Axiom`, no `Admitted`.**
- `election_proof/` (332 files, flat) and `election_proof/election.v` —
  the **implementation side**. One Go function per collection of four files:
  `spec_<fn>.v` (a `Module Type` with exactly one `Parameter`, the single
  place its Hoare triple is written), `postulates_<fn>.v`, `proof_<fn>.v` (a
  functor ascribed to the signature) and `link_<fn>.v`. **78 collections.**
  Shared predicates live in `defs.v`, `inv_*.v` and `step_lemmas.v`, outside
  the module system. A function whose proof needs several files gets a
  `proof_<fn>_helpers/` directory (two today: `raft__Step`, with eight,
  and `MajorityConfig__VoteResult`).
  `election.v` is an aggregator plus `raft_election_safety`.
- `v3_proof/readonly.v` — the read-index/heartbeat protocol development.
  **Not on the election path**; nothing under `election_proof/` requires it.
  Until 2026-09-22 *nothing at all* required it, so `make ci` had never
  compiled it; `should_build.v:51` now requires it as a stopgap pending a
  clean-up of the old proofs. It checks (`-vok` clean).
- `v3_proof/protocol.v` — an axiomatized node-level interface (`is_node`,
  `node.Ready`, `node.Advance`, `node.Propose`). **Not on the election path.**

`etc/check-module-discipline.py` enforces the layout. It reads the program
expression out of each triple rather than trusting names, so it reports which
Go function a spec really specifies, and errors on a triple outside the
spec/proof shape, two triples for one function, a malformed spec file, an
incomplete collection, or a name absent from `new/code/`.

    etc/check-module-discipline.py --scope election_proof   # 5 findings, all notes/warnings
    etc/check-module-discipline.py --summary
    etc/check-module-discipline.py --selftest

Its companion `etc/tcb-report.py` views the same tree for trust rather than
structure. Both share `etc/rocqscan.py`.

### Rest of etcd

`new/proof/go_etcd_io/etcd/` carries earlier work on the client (`client/v3`,
including a leasing protocol proof), `pkg/v3`, `api/v3` protobuf packages and
`server/v3/etcdserver`. Context for the raft work, not the current focus.

## What is proved

Every Hoare triple on the election path is `Qed` — **169 lemmas**, 78
discharged signatures — except one admission signed off on for now
(below). **The result is the first of these two**; the second is an
internal lemma that nothing uses yet — a *root lemma*, in `tcb-report`'s
terms (decisions.md, 2026-09-21: what this development is for is verified
specs of Go functions):

- **`Step.wp_raft__Step`** (`election/spec_raft__Step.v`): running `Step` on
  an election message takes the physical struct from a state refining the
  protocol state `s` to one refining `s'`, and moves `own_raft_ghost` from
  `s` to `s'` at the same time, with `∃ recv, step cfg id s recv s'`.
- **`raft_election_safety`** (`election.v`): two nodes whose ghost state says
  "leader in term `t`" are the same node.

**`raft_election_safety` is code-free.** It relates two `own_raft_ghost`
assertions; `wp_raft__Step` is the only bridge to the Go code, and it is a
*single-call* triple. Nothing yet composes it into a running node or a
cluster. Read the next two sections before quoting the result.

**No spec below `Step` touches ghost state.** A callee's spec says only which
state the struct ends up refining and how the outbox grew — never that the
transition is legal. `own_raft_ghost` therefore appears in exactly one spec
and `own_raft_ghost_step` is applied in exactly one proof file. If you find
yourself adding `own_raft_ghost` to a callee, that is the thing this layout
exists to prevent.

`proof_raft__poll.v` is the worked example to imitate: short, proved from
scratch against the real code, and it demonstrates the `access_strict` idiom
for pulling one field out of `r ↦ rv`.

## The verified configuration

Everything above holds **only** under these assumptions. They are premises of
`wp_raft__Step_body` and of `own_raft_phys`, not claims about etcd.

| assumption | where |
|---|---|
| Only `MsgHup`/`MsgVote`/`MsgVoteResp` are ever passed to `Step`. Everything else is taken to be dropped by the network, so a node never *receives* `MsgApp`/`MsgHeartbeat`/`MsgSnap` and never steps down through them. Sending them is in scope and proved | `election_msg`, `spec_raft__Step.v` |
| No proposals, no read-only requests | scope |
| No reconfiguration, no learners; the voter set `cfg` is fixed, and **no `EntryConfChange` is anywhere in the log** | `HnoConfChange`, `inv_raftlog.v:139` |
| No snapshot is ever received | `Hnosnap`, `inv_raftlog.v:139` |
| No pre-vote, no check-quorum | `inv_raft_phys.v:112` |
| No leader transfer (`leadTransferee = 0`, `Context ≠ campaignTransfer`) | `spec_raft__Step.v` |
| Node ids are nonzero; `id ∈ cfg`; the ghost state's `cfg` is the physical one (`γ.(re_cfg) = cfg`) | `spec_raft__Step.v`, `own_raft_ghost` |
| A `MsgHup` cannot make the term wrap: `uint.Z s.term + 1 < 2^64` | `spec_raft__Step.v` |
| Incoming `MsgVote`/`MsgVoteResp` are addressed to this node and have `Term ≠ 0`, `From ≠ 0`. **Go checks none of these** — they are assumptions about the transport and about peers | `spec_raft__Step.v` |
| Crash safety is out of scope. `Step` is a `wp`, not a `wpc` | — |

Two of these are not restrictions a deployment can honour as written:
`HnoConfChange`, and — if you care about etcd's defaults — pre-vote and
check-quorum, both of which etcd's server turns on.

## What still needs fixing

Ranked by how much the proof's meaning depends on it. Unclaimed; pick one and
say so in the journal.

1. **`own_raft_phys` has no constructor.** There is no `newRaft` spec and no
   `is_Storage` instance (not even `MemoryStorage`), so nothing shows the
   predicate is satisfiable — and it was provably `False` once before. Until
   this exists, every triple in the development could in principle be
   vacuous. `own_raft_ghost` *is* known inhabited (`own_raft_ghost_alloc`);
   closing the same gap on the physical side is the highest-value work
   available.
2. **`HnoConfChange` is false of a real cluster.** `inv_raftlog.v:139`
   requires `Forall (λ e, Type = EntryNormal) (sents ++ uents)` — the *whole*
   log — while `RawNode.Bootstrap` (`new/code/go_etcd_io/raft/v3.v:391`)
   writes `EntryConfChange` entries at `v3.v:447`, and `StartNode` calls it.
   So `own_raft_phys` is unsatisfiable for a freshly bootstrapped node until
   compaction. Only "no conf change in `(applied, committed]`" is needed;
   weakening it is cheap and should happen.
3. **`Ready` / `advance` / `acceptReady` are unverified.** No collection
   exists. They are the only thing that drains `msgs` and `msgsAfterAppend`,
   so `step_drain` — the model rule that exists for exactly this — refines
   nothing, and nothing shows `own_raft_phys` survives a drain. This blocks
   composing `Step` into a running node.
4. **`tick` needs a scope decision.** `tickElection` calls `Step(MsgHup)`
   (`v3.v:3497`), which is covered. `tickHeartbeat` calls `Step(MsgBeat)`
   unconditionally (`v3.v:3552`); its `Step(MsgCheckQuorum)` (`v3.v:3523`) is
   guarded by `r.checkQuorum` and so is dead under the scope. Either
   `tickHeartbeat` is out of scope — a leader never heartbeats, harmless for
   safety — or `MsgBeat` needs a branch. Decide and write it down; the scope
   table above does not currently say.
5. **`isUpToDate` is unconstrained**, so a bug that makes a node grant to a
   stale candidate is invisible. Note what this does and does not cost: it is
   *not* an election-safety bug — at most one leader per term does not depend
   on log currency — so it cannot produce two leaders. It costs Leader
   Completeness, which is close to vacuous while the log only ever holds a
   leader's empty entry. Closing it needs a log model.
6. **Bring `readonly.v` and `protocol.v` into the module discipline.** Eleven
   triples are still stated loose. One is a real duplicate:
   `raft.stepLeader` has a second triple in `readonly.v` against a second
   ownership story (`own_raft`), `Admitted` with postcondition `True` and no
   users. Resolving it means deciding whether `own_raft` or `own_raft_phys`
   survives.
7. ~~Decide the top-level Raft correctness statement~~ — **decided
   2026-09-21** ([decisions.md](decisions.md)): the result is verified specs
   for the top-level Go functions, and protocol facts such as election
   safety are internal lemmas in their service. What is left of this is
   items 3 and 8.
8. **Discharge `protocol.v`'s `Section axioms`** against the translated code,
   or record why each stays an axiom. Then extend past `Propose` to the rest
   of the `node` interface.
9. Two stale comments, both misleading to an auditor: `election.v:20-23` says
   the `inv_*.v` files hold the log and tracker as `Axiom`s (they are
   definitions), and `election_proof/protocol.v:55-58` motivates including
   `App`/`Heartbeat` in the model by the higher-term step-down — true of the
   code, but under the scope above that transition is never received, so the
   rule refines nothing and a reader could take it for a discharged
   obligation.

## Trust base

**An audit is two commands, and neither substitutes for the other**:
`make` first — the only thing that checks proofs — then `etc/tcb-report.py`,
whose whole job is what the build cannot check. What each establishes, the
known gaps and the plan are in [tcb-accounting.md](tcb-accounting.md).

`etc/tcb-report.py` over the whole raft proof: **31 assumed — 23 `Axiom` and
8 `Admitted.`**, 3 of the admits signed off on for now and marked
`(* Trusted *)` — still debt; the goal is no admits. On the election path
alone: **10 `Axiom` and 1 `Admitted`**; one result, `wp_raft__Step_body`;
60 definitions, 658 lines; TCB 4.9% of the development by line.

    R=new/proof/go_etcd_io/raft      # required; the tool names no development
    etc/tcb-report.py --proof-root $R                  # summary, and which files are incomplete
    etc/tcb-report.py --proof-root $R --scope election_proof   # the cone the build reaches
    etc/tcb-report.py --proof-root $R --view assumed   # every axiom and admit, classified
    etc/tcb-report.py --proof-root $R --view surface   # results, root lemmas, what they rest on

It reports **results** (Go-function Hoare triples nothing else calls)
separately from **root lemmas** (stated facts nothing uses yet, such as
`raft_election_safety` — not results, not counted), splits the assumed
into *Hoare triples about Go code / undefined declarations / other*, and
lists any file under the proof root that the build does not reach.

**Do not count these by hand, and do not grep for them.** A grep over-counts:
doc comments quote probe lemmas ending in `Admitted.`, and `spec_*.v` files
are full of `Parameter`s.

The count of axioms is the smaller half. The **definitions** the results
reach — 60 on the election path, 658 lines — are the rest of it:
`wp_raft__Step` says nothing if `nstate.t`, `step` or `own_raft_phys` is
wrong, and none of those is an axiom.

### What the keywords mean

The *keyword* says which kind of debt and the *file name* says which
function. File kind carries no distinction.

- an **`Axiom`** means **outside the raft protocol**, and there should be very
  few. A trust-boundary triple is declared with `Axiom` inside its functor,
  which still discharges the signature's `Parameter` and still shows up in
  `Print Assumptions`;
- an **`Admitted` `Lemma`** means **in scope but unfinished**, wherever it is;
- a **`Parameter` in a `spec_*.v`** is neither — it is discharged by the
  functor ascribed to that signature, so it never reaches
  `Print Assumptions`.

The only thing the election development may assume outright is the top-level
scope. Everything in **core raft** — the log, the tracker, `Progress`,
`bcastAppend` — must be constructed and proved.

### The ten axioms on the election path

All are outside the raft protocol, and none feeds a vote or a leader
decision, so none can hide an election-safety bug.

| axiom | file | why it is outside raft |
|---|---|---|
| `is_Logger`, `is_Logger_pers`, `wp_Logger__logf` | `inv_logger.v` | client-supplied interface. Covers only the **non-panicking** methods — a path reaching `Panic`/`Panicf` must be shown unreachable |
| `own_Storage` | `inv_storage.v` | `raftLog.storage` is client-supplied; raft ships only `MemoryStorage`, for tests. A predicate, not a triple. Its contract `is_Storage` is real and constrains `Entries`, `Term`, `Snapshot` and a `< 2^61` bound on the stable last index |
| `own_big_Int`, `wp_big_NewInt`, `wp_big_Int__Int64`, `wp_rand_Int` | `inv_big.v`, `proof_big_*.v`, `proof_rand_Int.v` | `math/big` and the RNG behind `resetRandomizedElectionTimeout` |
| `wp_slices_Sort` | `proof_slices_Sort.v` | not translated. Permutation-only postcondition |
| `wp_Entry__Size` | `proof_Entry__Size.v` | protobuf-generated `raftpb` code. The one a reader may want to argue about: a library in spirit, core raft in location |

### The admission signed off on for now

`proof_raftLog__slice.v` ends `Admitted. (* Trusted *)` for one arithmetic
side condition, `|ents| + |unstable| < 2^63` at the `extend` call: Go computes
`len(dst)+len(vals)` as an `int`, and with about `2^63` unstable entries it
wraps, so the triple is false there. The bound is not derivable — `is_Storage`
gives the stable part `< 2^61` and the model bounds any one slice at `2^63` —
and it can be neither carried (an append cannot re-establish a carried bound)
nor stated as a premise (nothing at `Step` can see the log's length). The
same triple also hands the `raftLog` record back beside the page and takes
both in its wand: a strictly stronger assumption, true because a page aliases
an entry buffer, never the record. It sits on the
`hup → hasUnappliedConfChanges → slice → extend` path, which cannot reach a
`Term`/`Vote` write.

### Two things the tool cannot see

- **A framework `Admitted` under the array proofs.** `into_val_typed_array`
  (`new/golang/theory/array.v`) is `Admitted` with three `admit`s;
  `wp_JointConfig__IDs` reads a `[2]MajorityConfig` through it. Outside the
  raft tree, so `tcb-report` does not count it.
- **`Print Assumptions` is not available as a cross-check.** Over a `.vos`
  tree it under-reports — it sees axioms reachable from *statements* but not
  what opaque proofs used. Ground truth needs a full `.vo` build of
  Perennial, which nothing in this tree has.

## Working on this

**Checking your work.** `make <file>.vos` is a ~2s loop but **does not check
proof bodies** — it will accept a script that does not run. Use
`make <file>.vok` for the real check. Never claim a lemma is proved without
having seen `-vok` exit 0 on that revision. Do not reach for `.vo`: nothing
in the tree has `.vo` dependencies, so `make x.vo` starts building all of
Perennial.

**Writing against a big function.** Destructure the precondition before the
body is unfolded (`wp_start_folded as "@". iNamed "Hown". wp_start_unfold.`),
wrap a mid-body `iNamed`/`iNamedSuffix` in `wp_hidden (…)`, re-seal a big
predicate with an intro lemma rather than `iFrame "∗#%"`, and do not
`set_solver` a list membership. Each is a 10–100× difference on `Step`; see
[gotchas.md](gotchas.md).

**Inner loop: rocq-warm**, specifically the
[upamanyus fork](https://github.com/upamanyus/rocq-warm), not zeldovich's.
Replays here are 0.3–30s, and a `Show.` to inspect a goal is an ordinary
replay rather than a cold check. Pass `--allow-stale`: this tree has `.vos`
only, and without it every check is refused with exit 2. **Exit 2 is not a
verdict** and neither is **exit 130** — a Ctrl+C or a killed client stops the
work but *keeps* the session, parked at the line it reached, so interrupting
a check you no longer want is cheap. A **git worktree is its own workspace**
(rocq-warm keys the daemon on `git rev-parse --show-toplevel`), so worktrees
do not share a session table or a memory budget, only the machine.
`--rebuild` will compile stale dependencies if you would rather not pass
`--allow-stale`. See [gotchas.md](gotchas.md).

For a file low in the dependency graph, `make <file>.vok` can beat rocq-warm
outright — `election_proof/protocol.v` sits directly on `proof_prelude` and checks
in 3–5s.

**On a machine with no Rocq**, budget ~1.5h before you can check anything:
`opam switch create perennial 5.2.1`, `opam pin add -n .`,
`opam install --deps-only ./perennial.opam` (→ Rocq 9.4+alpha), then
`make -j8 TIMED=false new/proof/go_etcd_io/raft/election_proof/election.required_vos`
for the `vos` closure. **Check `opam switch list` first**: on the machine
this repo is usually worked on, Rocq is installed in the `perennial` switch
but not on a fresh shell's `PATH` — `eval "$(opam env --switch=perennial
--set-switch)"` (gotchas.md).

**Memory.** `proof_raft__Step.v` and its helpers are the expensive part of
the tree; four at once peak around 8 GB, so `-j4` is the most a 15 GB box
should run beside nothing else.

## Before you add a claim

Statements in this development have been asserted, compiled, and lived in the
tree until a proof needed the fact and could not get it — including some with
a `Qed` resting on them. A plausible-looking bookkeeping claim about
`send`/`msgs`/`msgsAfterAppend` is the shape that keeps going wrong; check it
against `raft__sendⁱᵐᵖˡ` specifically. The table, the tells to grep for, and
the two-probe check for a pointer-receiver spec are in
[false-statements.md](false-statements.md). **Read it before writing a spec or
an `Admitted`.**

**An assumption you have not tried to prove is an assumption you have not
read carefully.**

## Standing facts

- `new/code/` and `new/generatedproof/` are Goose output. **Never edit them by
  hand** and never imitate their style. Regenerate with
  `new/etc/update-goose-new.py`.
- `make ci` builds `new/should_build.vo`, which is what CI checks. A proof not
  reachable from `new/should_build.v` is not being built.
- Faster inner loop: `make vos`, or
  `make new/proof/go_etcd_io/raft/v3.required_vos` to build just what a file
  depends on. See `CONTRIBUTING.md`.
- **Every build prints a per-file time** — a `ROCQ TIME <secs> <mode> <file>`
  line as each file finishes — and records it in `.timing.sqlite3`, keyed on
  the file *and* the build mode. `make timing-report` ranks the bottlenecks;
  `make TIMING_MIN=10` prints only the slow ones.
- Both python CI jobs must stay green: run `ruff check .` and
  `ruff format --check .` before pushing a change under `etc/` or `new/etc/`.
- The Go module path here is still `github.com/mit-pdos/perennial` and the
  Rocq logical paths are still `Perennial`/`New`, on purpose — see
  [decisions.md](decisions.md).
