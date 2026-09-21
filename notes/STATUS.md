# Status

**Last updated:** 2026-09-21

## Goal

Verify etcd using Perennial/Grove, starting with its Raft implementation.

## Where things stand

This repo (`upamanyus/etcd-grove`) is a fork of `mit-pdos/perennial`, set up on
2026-09-11 for the etcd work. The Perennial framework and the Goose toolchain
are inherited wholesale and are not the object of study — the etcd proofs are.

The Go code under verification is **not in this repo**. It lives in two forks,
both on branch `goose`, wired up in `new/etc/update-goose-new.py` and
`etc/ci-goose-check.py`:

- `upamanyus/etcd-raft` → translated into `new/code/go_etcd_io/raft/`
- `upamanyus/etcd` → translated into `new/code/go_etcd_io/etcd/`

### Raft proof

`new/proof/go_etcd_io/raft/` — reached from `new/should_build.v`, so `make ci`
builds it.

- `v3_proof/base.v` (62 lines) — `IsPkgInit` instances for the raft package and
  its dependencies (raftpb, quorum, tracker, confchange, strconv, strings,
  math, big, rand, bytes). Boilerplate; grows as new packages get pulled in.
- `v3_proof/readonly.v` (955 lines) — the substantive protocol development. The
  `raft_names` ghost-state record, commit/term ghost state, the quorum-
  intersection lemmas, the reads queue (`own_reads`, `is_in_reads`,
  `try_read`), and the heartbeat-context machinery used to justify
  linearizable reads (`is_HeartbeatRequest`, `is_HeartbeatResp`,
  `is_heartbeat_ack`, `is_stale_term`).
- `v3_proof/protocol.v` (143 lines) — axiomatized node-level interface:
  `is_node`, `own_propose_message`, and WPs for `node.Ready`, `node.Advance`,
  `node.Propose`. The `Section axioms` here is the current trust boundary.
- `v3.v` (31 lines) — the public surface: `is_Node` and `wp_Node__Propose`,
  proved from `protocol.v`.
- `v3_proof/election_protocol.v` — **leader-election refinement**, protocol
  side, added 2026-09-12. The state machine, the ghost state
  (`own_raft_ghost`, `is_message`) and its refinement obligation. Since
  2026-09-15 `nstate.t` carries an `outbox` field and `step` has **no `sent`
  output** — a step's sends are the growth of `s'.(nstate.outbox)`.
- `v3_proof/election/` (192 files) and `v3_proof/election.v` — the
  implementation side. **One file per Go function**: each has `spec_<fn>.v`
  (a `Module Type` with exactly one `Parameter` — the single place its Hoare
  triple is written), `postulates_<fn>.v`, `proof_<fn>.v` (a functor ascribed
  to the signature) and `link_<fn>.v`. Shared *predicates* live in `defs.v`,
  `inv_*.v` and `step_lemmas.v`, outside the module system.
  **44 collections as of 2026-09-18**, up from 13: the 2026-09-14 refactor
  covered `Step` and its immediate callees and left 31 other Go functions
  stated as loose `Lemma`s and `Axiom`s in the `inv_*.v` files, where nothing
  stopped a second spec — and two functions had already acquired one.
  `inv_slices.v` is gone (it held one axiom and nothing else). `election.v`
  is only an aggregator plus `raft_election_safety`.
  **Listing the top level shows exactly four files per Go function**, plus
  the eight shared files and one `proof_<fn>_helpers/` directory per function
  whose proof needs several files (only `raft__Step` today, with eight). See
  [decisions.md](decisions.md) for why, and
  [raft-election-refinement.md](raft-election-refinement.md) for scope, what
  is proved, what is admitted, and the trust boundary.
- **The discipline is checked**: `etc/check-module-discipline.py`. It reads
  the program expression out of each triple rather than trusting lemma names,
  so it reports which Go function a spec really specifies, and errors on a
  triple outside the spec/proof shape, two triples for one function, a
  malformed spec file, an incomplete collection, or a name absent from
  `new/code/`. Exits non-zero, so it can gate CI.

      etc/check-module-discipline.py --scope election   # clean
      etc/check-module-discipline.py --summary
      etc/check-module-discipline.py --selftest        # the parsing contract

  Its companion is **`etc/tcb-report.py`**, which views the same tree for
  trust rather than structure: what is assumed, what is exported, and what
  those statements rest on. See "Trust base" below. The two share their
  parser, `etc/rocqscan.py`.

  With no `--scope` it checks the whole raft proof and still reports 11:
  eight in `readonly.v`, three in `protocol.v`. See "Next steps". It knows
  the toolchain and no particular package or file name, so `--proof-root`
  aims it at another development.

So: the read-index/heartbeat protocol reasoning and the election refinement
are the two developed pieces; the node interface is still axiomatized, and
per-function proofs against the translated raft code are underway only on the
election path.

### Rest of etcd

`new/proof/go_etcd_io/etcd/` carries earlier work on the client (`client/v3`,
`client/v3_proof/`, including a leasing protocol proof), `pkg/v3` (`wait`,
`idutil`), `api/v3` protobuf packages, and `server/v3/etcdserver`. This is
context for the raft work, not the current focus.

## In flight

### Closing every non-protocol admit on the election path (started 2026-09-19)

Branch `worktree-election-close-admits`. Goal: **every Hoare triple on the
election path `Qed`**, so that the only assumptions left in the raft proof
are the protocol layer — the 12 ghost-state axioms in `election_protocol.v`
(`own_raft_ghost`, `own_raft_ghost_step`, `is_leader_unique`, …) — plus the
declared trust boundary (`Logger`, `own_Storage`, `slices.Sort`, the RNG).
The ghost layer is deliberately **not** in this pass.

This table is the tracker. It is updated as items land; the journal has the
detail. "wave" is the order the work is being run in, chosen so that no two
concurrent items edit the same shared file.

| # | item | wave | status |
|---|---|---|---|
| 1 | The Goose array-indexing fix (`worktree-goose-array-index-fix`) — merged into `main` as `d0a281822` and merged here | 0 | done |
| 2 | Model: `go.len` on a nil map (`new/golang/defn/map.v` nil case, `pure_wp_map_nil_len` and a general `wp_map_len` in `theory/map.v`) | 0 | done (`theory/map.v`, `inv_tracker.v`, `proof_raft__campaign.v` at `-vok` RC=0) |
| 3 | `wp_raft__promotable` | 1 | **done** 2026-09-19 (`-vok` RC=0, no shared-file change, no new collection) |
| 4 | `wp_raft__hasUnappliedConfChanges` — target, `raftLog.scan`, and the whole `slice` sub-tree (`raftLog__slice`, `unstable__slice`, `limitSize`, `entsSize`, `extend`, both `mustCheckOutOfBounds`) Qed; `raftLog__slice` carries the one deliberate `(* Trusted *)` admit, "the log fits in memory" (see Trust base) | 1 | **done** 2026-09-20 modulo that marked admission |
| 5 | `wp_raft__resetRandomizedElectionTimeout` — **Qed** (`-vok` RC=0), with `lockedRand__Intn` Qed and `rand_Int`, `big_NewInt`, `big_Int__Int64` as trust-boundary axioms over the abstract `own_big_Int` (`inv_big.v`). Spec gained `0 < electionTimeout` (crypto/rand panics otherwise); `own_raft_phys` carries it as `HelectionTimeout`; `is_initialized` owns `globalRand` and its mutex, `ErrCompacted`, `ErrUnavailable`; `rand` has `is_rand_initialized`. `reset.v` passes the premise at the updated struct (see gotchas.md, "a pure premise about a record update") | 2 | **done** 2026-09-20 (`reset.v` call sites fixed, `-vok` RC=0) |
| 6 | `wp_JointConfig__IDs` | 1 | **done** 2026-09-20 (`-vok` RC=0; no shared-file change; carries `proof_JointConfig__IDs_helpers/map_for_range_keep.v`, see item 14) |
| 7 | `wp_ProgressTracker__Visit` — both paths of `sl[:n]` vs `make`, backwards map fill, `slices.Sort` permutation, one lent `own_progress` per id; carries its own copy of `map_for_range_keep.v` (item 14) | 1 | **done** 2026-09-20 (`-vok` RC=0, independent re-run; no shared-file change) |
| 8 | `wp_ProgressTracker__TallyVotes` — new collections `JointConfig__VoteResult`, `MajorityConfig__VoteResult` (the latter over an arbitrary component set, both `map.nil` and owned-map receivers; equivalences for Won/Lost under `s ≠ ∅`); `own_tracker`'s `Hcfg_ne` pays for the empty-config convention | 2 | **done** 2026-09-20 (`-vok` RC=0, re-checked after the tracker reshape of item 11) |
| 9 | `spec_raft__send` with `send_ok` (three clauses: vote types keep their term; `MsgApp`/`MsgHeartbeat` get `s.term` stamped; model-invisible types add nothing) | 1 | **done** 2026-09-20: `proof_raft__send.v` Qed and every caller re-checked (`campaign`, `Step`, all eight `Step` helpers, `hup`) at `-vok` RC=0 |
| 10 | `wp_raft__appendEntry` — `Axiom` → `Qed`, with six new collections (`payloadSize`, `payloadsSize`, `raft__increaseUncommittedSize`, `traceReplicate`, `unstable__truncateAndAppend`, `raftLog__append`). Three premises, all discharged by `becomeLeader` from its literal: empty `Data`, `Type = EntryNormal`, batch `< 2^61`. **No caller obligation**: the no-wrap bound is derived from `is_Storage`'s new `Hbounded` (stable last index `< 2^61`) plus the slice's own length, not carried — see decisions.md | 2 | **proved** 2026-09-20 (`-vok` RC=0 on all seven proofs, `becomeLeader`, and seven `is_Storage` dependents); commit with the final sweep |
| 11 | `wp_raft__bcastAppend` — **Qed**, with `sendAppend` Qed and new leaves `Progress__IsPaused`, `Inflights__Full`, `Progress__SentEntries`, `Progress__SentCommit`, `raftLog__entries` Qed. Reshaped the tracker predicates (see decisions.md 2026-09-20: `own_inflights_at`/`inflights_ok`, `own_progress_at`/`progress_state_ok`, read-only progress map, `visit_closure` existential in the tracker value); `is_Storage` gained `HSnapshot`; `is_initialized` gained `ErrSnapshotTemporarilyUnavailable` | 3 | **done** 2026-09-20 modulo items 15–17 (`-vok` RC=0 on the chain and on 22 dependents; whole-tree `.vos` and discipline check clean) |
| 15 | `wp_raft__maybeSendAppend` — `raftLog.term` total (`err = nil ↔ in range`); the two spec defects that then blocked it (`maybeSendSnapshot`'s contradictory precondition, `send` hiding the tracker) plus a third of the same shape (`send` also owned the log the caller must hold a page of) are repaired by item 18 | 4 | **done** 2026-09-21 |
| 18 | `own_raft_bare r id s f tv lg` (every conjunct of `own_raft_phys_at` but the tracker **and the log**, both pinned as parameters) with `own_raft_notrk` the tracker-only wrapper and `own_raft_phys_at_split : own_raft_phys_at ⊣⊢ ∃ tv, own_raft_notrk … tv ∗ own_tracker …`. `send` restated on `own_raft_bare`, `maybeSendSnapshot` on `own_raft_notrk ∗ own_progress`, `raftLog.entries`/`slice` hand `l ↦ lv` back beside the page. Ten `send` call sites: two lines each. **`wp_raft__maybeSendAppend` Qed** | 5 | **done** 2026-09-21 (`-vok` RC=0 on `inv_raft_phys.v`, `send`, `entries`, `slice`, `scan`, `maybeSendSnapshot`, `maybeSendAppend`, `sendAppend`, `bcastAppend`, `campaign`, `appendEntry`, `hasUnappliedConfChanges`, the three `Step_MsgVote` helpers, `Step`) |
| 16 | `wp_Inflights__Add` — Qed, with a new `Inflights__grow` collection (spec over the buffer pieces, premise `len(buf) < size`: with `size = 0` the `else`-arm cap does not apply and `grow` would allocate one slot past the ring). Three reachable leaves, not four: the wrap-and-grow case is dead (`len(buffer) = size` forces `next < len`) | 4 | **done** 2026-09-21 (`-vok` RC=0, independent re-run; no shared-file change) |
| 17 | `wp_raft__maybeSendSnapshot` — Qed against its current spec, with new leaves `raftLog__snapshot`, `IsEmptySnap`, `Progress__BecomeSnapshot`; `is_initialized` gained `is_new_error errSnapUnavail` (the dynamic type is a pointer type), without which `err == ErrSnapshotTemporarilyUnavailable` cannot step. Its spec is restated on `own_raft_notrk` by item 18 | 4 | **done** 2026-09-21 (`-vok` RC=0, independent re-run; `base.v` dependents re-checked) |
| 14 | Framework `theory/map.v`: `wp_map_for_range` returns the map; `wp_map_nil_for_range` and `pure_wp_map_nil_len` moved above the `K V` context so `tc_solve` can fire them; the four copied `_helpers/map_for_range_keep.v` deleted | between 2 and 3 | **done** 2026-09-20 (`map.vok` RC=0; ~90-file `.vos` rebuild RC=0; `IDs`, `Visit`, `TallyVotes`, `MajorityConfig__VoteResult`, `campaign`, `inv_tracker.v` re-checked RC=0) |
| — | Ghost layer of `election_protocol.v` (12 axioms) | — | out of scope for this pass |
| 13 | Final: `-vok` sweep of every proof-bearing file, `tcb-report`, `check-module-discipline`, notes | 6 | run 2026-09-21; see the summary below the table |

**Outcome (2026-09-21).** Every Hoare triple on the election path is `Qed`
except one deliberate, marked admission. `etc/tcb-report.py --scope election`
now counts **1 `Admitted` (trusted) and 10 `Axiom`s** against 169 Qed lemmas
and 78 discharged signatures, and every axiom is on the declared trust
boundary: `is_Logger`/`is_Logger_pers`/`wp_Logger__logf` (client `Logger`),
`own_Storage` (client `Storage`, whose contract `is_Storage` grew `Entries`,
`Hbounded`, `Snapshot` this pass), `wp_rand_Int`/`wp_big_NewInt`/`wp_big_Int__Int64`
over the abstract `own_big_Int` (the RNG and `math/big`), `wp_slices_Sort`
(not translated), and `wp_Entry__Size` (protobuf-generated `raftpb` code —
the one axiom a reader may want to argue about; it is a library in spirit
and core raft in location). The single admission is `wp_raftLog__slice_at`'s
"the log fits in memory" (Trust base). Outside this scope the protocol
layer's 12 axioms in `election_protocol.v` remain, by design of this pass.
The raft development as a whole also still carries the `readonly.v` and
`protocol.v` assumptions listed under "Next steps", which are not on the
election path.

Rules for the agents doing items 3–11, so that a shared checkout stays sane:
one `rocq` process each; edit your own collection and any *new* collections
freely; a change to a shared file (`inv_*.v`, `defs.v`, `base.v`, another
function's `spec_*.v`) is allowed only when the proof needs it, and then every
dependent is re-checked at `-vok`; nothing under `notes/`, `new/code/`,
`new/generatedproof/` is touched; no version-control commands. The
coordinator commits and writes the notes.

**The array-indexing blocker is fixed (2026-09-17)**, branch
`worktree-goose-array-index-fix` off `main`. It was three Goose bugs plus one
missing model rule, not the two the bug file had diagnosed — in particular
`len`/`cap` of an array was emitted as a *function value with no operand
applied*, so the model rule the bug file proposed would not have fixed it on
its own. `new/golang/defn/array.v` gains guarded `go.len`/`go.cap` rules for
arrays (a **TCB** change) with matching `PureWp` instances in
`new/golang/theory/array.v`. `new/code/` is regenerated: six files, every
changed line an array site. **Re-verified from a clean `.vos` slate: 101
files at `-vok`, 0 failures**, including `theory/slice.v`, `theory/map.v` and
`proof_raft__Step.v`. Details, evidence and the rejected alternatives in the
2026-09-17 [journal](journal.md) entry and [decisions.md](decisions.md).

**Leader-election refinement** — `new/proof/go_etcd_io/raft/v3_proof/`,
branch `raft-election-poll-hup`. Compiles and is reached from
`new/should_build.v`.

Thirteen Go functions are specified, one file each. **Every one is proved**
(`Qed`, each confirmed with a `-vok` run exiting 0 on that revision):
`voteRespMsgType`, `send`, `becomeFollower`, `becomeCandidate`,
`becomeLeader`, `raft_election_safety`, and — all on 2026-09-16 — **`poll`**,
**`hup`**, **`reset`**, **`stepCandidate`**, **`campaign`**,
**`stepFollower`** and **`stepLeader`** (the last two on `MsgVoteResp`, where
both are no-ops), plus **all of `Step`**: the top-level dispatch and its
`MsgHup`, `MsgVote` and `MsgVoteResp` branches.

**There is no `Admitted` left in any `proof_*.v` file.** What remains is in
the `inv_*.v` files — the predicates and helper lemmas the `proof_*.v` files
stand on — and it is listed under "Trust base" below.

`Step`'s `MsgVoteResp` branch, closed last, is the one that made
`own_raft_phys`'s `Hstepfn` conjunct necessary: all three `stepX` are
reachable from its `r.step(m)`, so without the field pinned to the role there
is nothing to apply. Its four cases:

| case | what runs | model step |
|---|---|---|
| `m.Term > r.Term` | a `VoteResp` is not `from_leader`, so `becomeFollower(m.Term, None)` rather than adopting a leader; then `stepFollower` | `step_higher_term` |
| `m.Term < r.Term` | with `checkQuorum` and `preVote` off and the type neither `MsgPreVote` nor `MsgStorageAppendResp`, only the trailing log runs | `step_refl`, `recv = []` |
| `m.Term = r.Term`, Follower/Leader | `stepFollower` / `stepLeader` only read | `step_refl` |
| `m.Term = r.Term`, Candidate | `stepCandidate` records the vote, maybe wins or loses | `step_record_then_win` / `_lose` / `step_record_vote` |

**Cost note:** `Step`'s proof is now nine files — `proof_raft__Step.v` plus
eight in **`proof_raft__Step_helpers/`** (`proof_raft__Step_MsgHup.v`,
`_MsgVote.v`, `_MsgVote_gt.v`, `_MsgVote_le.v`, `_MsgVote_lt.v`,
`_MsgVote_eq_novote.v`, `_MsgVote_eq_voted.v`, `_MsgVoteResp.v`) — that
check in **3 min 21 s wall with `make -j4`**, the
longest (`_MsgVote_gt`) 2:39 and 2.3 GB alone (2026-09-17). As one file it
was ~45 min and 11.3 GB the day before, 9.5 min after the framework fixes,
8.7 min after the walker fixes. The parts sum to ~11 min of CPU; four of
them at once peak around 8 GB, so `-j4` is the most this 15 GB box should
run beside nothing else.

**The tactic engine was the cost, not the proof (2026-09-17).** A pure step
stripped laters from every hypothesis by unfolding them; every failing
proof-mode typeclass search against the `WP` goal (so `done`, `//`,
`iPureIntro`, `iSplitR`, …) was linear in the ~500KB program term; `iFrame
"∗#%"` re-sealing a 25-conjunct predicate cost 17 s; `set_solver` on a
list-membership goal ran for minutes. The framework fixes are in
`new/golang/theory/proofmode.v` (later-free pure steps; the program text
let-bound inside `wp_apply` and `done`; `wp_hidden tac`; `wp_start_unfold`)
and the proof-side idioms in [gotchas.md](gotchas.md). `campaign` and
`reset` got 1.7× faster without being touched (same-day A/B). Details and
numbers in the 2026-09-17 [journal](journal.md) entry; the design and its
rejected alternatives in [decisions.md](decisions.md).

**Verified on 2026-09-17** (branch `perf/wp-tactics-hide-program-text`,
after the framework changes and the file split), every file individually at
`-vok` RC=0 with zero errors: all nine `proof_raft__Step*.v`, all 12 other
`proof_*.v`, every `inv_*.v`, `defs.v`, `step_lemmas.v`,
`link_raft__Step.v`, `election.v`, and the 16 `new/golang/theory/*.v` files
that have proofs. Note that this is *not* a `make ci` run — that needs a
full `.vo` build of Perennial, which nothing in this tree has.

Two things that mattered structurally:

- `reset` closing freed the three `becomeX` proofs, which had rested on it.
- `own_raft_phys` now pins `r.step` to the role (`step_func_of`), because
  `MsgVoteResp` dispatches through `r.step(m)` and the field had been
  completely unconstrained — see "Known broken" and
  [decisions.md](decisions.md). The predicate is parameterized as
  `own_raft_phys_at … f` since `becomeFollower` assigns `r.step` *before*
  `r.state` and calls `reset` in between.

`poll` is the worked example to imitate for the rest — it is short, it was
proved from scratch against the real code, and it demonstrates the
`access_strict` idiom for pulling one field out of `r ↦ rv`, which is the
thing that cost the most time. See [gotchas.md](gotchas.md).

**Restructured 2026-09-15 so that no spec below `Step` touches ghost state.**
The outbox moved into `nstate.t`; `own_raft_phys` lost its `γ` and no longer
certifies the outgoing queues; certification is read off the ghost with the
new `own_raft_ghost_outbox`. `own_raft_ghost` now appears in exactly one spec
(`Step`) and `own_raft_ghost_step` is applied in exactly one proof file. A
spec below `Step` says only which state the struct refines and how the outbox
grew — never that the transition is legal. See
[decisions.md](decisions.md) for the alternatives that were rejected.

`reset` — what the three `becomeX` proofs rested on — was closed on
2026-09-16. It is the first proof to drive `trk.Visit` with the whole raft
struct as the closure's caller invariant, and it needed one new local lemma
(`raft_split_trk`, in `proof_raft__reset.v`) because the generated
`AccessStrict` store instance cannot name a field value the call has not
produced yet. See [gotchas.md](gotchas.md) for both. The `MsgVote` blocker
recorded in
[raft-election-refinement.md](raft-election-refinement.md) on 2026-09-14 is
**gone**: it was `iFrame` refusing to fill `send`'s `#Hm` slot, and `send` no
longer has one.

**Checking your work:** `make <file>.vos` is a ~2s loop but **does not check
proof bodies** — it will accept a proof script that does not run. Use
`make <file>.vok` (~100s per function) for the real check. Do not reach for
`.vo`: nothing in the tree has `.vo` dependencies, so `make x.vo` starts
building all of Perennial. To see *where* a slow proof spends its time, put
the one lemma in a scratch file and compile it with
`rocq compile -time -vok` under `Set Ltac Profiling` — two minutes, and it
is how the 2026-09-17 speedup was found.

**Writing against a big function:** destructure the precondition before the
body is unfolded (`wp_start_folded as "@". iNamed "Hown". wp_start_unfold.`),
wrap a mid-body `iNamed`/`iNamedSuffix` in `wp_hidden (…)`, re-seal a big
predicate with an intro lemma rather than `iFrame "∗#%"`, and do not
`set_solver` a list membership. Each is a 10–100× difference on `Step`;
see [gotchas.md](gotchas.md).

For the inner loop use **rocq-warm**, and specifically the
[upamanyus fork](https://github.com/upamanyus/rocq-warm) — not zeldovich's.
Replays here are 0.3–30s, and a `Show.` to inspect a goal is an ordinary
replay rather than a cold check (that was the fork's main fix). Pass
`--allow-stale`: this tree has `.vos` only, and without it every check is
refused with exit 2. **Exit 2 is not a verdict** — it means the file could not
be checked. See [gotchas.md](gotchas.md).

**On a machine with no Rocq**, budget ~1.5h before you can check anything:
`opam switch create perennial 5.2.1`, `opam pin add -n .`,
`opam install --deps-only ./perennial.opam` (→ Rocq 9.4+alpha), then
`make -j8 TIMED=false new/proof/go_etcd_io/raft/v3_proof/election.required_vos`
for the `vos` closure.

## Trust base

As of 2026-09-15 the raft proof assumes **50 axioms and 14 `Admitted.`** (2 of
the admits deliberate, marked `(* Trusted *)` at `readonly.v:464,471`). The
one axiom added that day is `own_raft_ghost_outbox`; more importantly, one of
the 50 — `wp_raft__appendEntry`, then called `wp_raft__appendEmptyEntry` —
**stopped being a false statement**. It
owned only `own_raftLog` while the code it describes queues a `MsgAppResp`
into `r.msgsAfterAppend`. See [journal.md](journal.md).

**The scope rule changed on 2026-09-16** and this is now the governing
statement of it. The *only* thing the election development may assume
outright is the top-level one: that `Step` need handle only election
messages. Everything in **core raft** — the log, the tracker, `Progress`,
`bcastAppend`, `newReadOnly` — is in scope and must be constructed and
proved. Things genuinely outside the raft protocol may still be assumed:
`slices.Sort`, the `Logger` interface, the tracing hooks, the RNG behind
`resetRandomizedElectionTimeout`.

So the older reading of `inv_*.v` — "an `Axiom` here means out of scope" — no
longer holds for core raft. **Nor does the file kind carry the distinction
any more** (changed 2026-09-18): every triple about a Go function is in a
collection, so it is the *keyword* that says which kind of debt, and the
*file name* that says which function.

- an **`Axiom`** means **outside the raft protocol**, and there should be
  very few. A trust-boundary triple is declared with `Axiom` *inside* its
  functor — `Axiom wp_raft__appendEntry : wp_raft__appendEntry_body.` in
  `proof_raft__appendEntry.v`. Checked: that discharges the signature's
  `Parameter` and `Print Assumptions` on the instantiated module still names
  it, so nothing is hidden by the move;
- an **`Admitted` `Lemma`** means **in scope but unfinished**, wherever it is;
- a **`Parameter` in a `spec_*.v`** file is neither — it is discharged by the
  functor ascribed to that signature.

`inv_tracker.v` was converted to this shape on 2026-09-16: `own_inflights`,
`own_progress` and `own_tracker` are real **definitions**, with their seven
method lemmas `Admitted`. `inv_raftlog.v` and `inv_misc.v` still need the
same treatment — see
[raft-election-refinement.md](raft-election-refinement.md) for what each one
costs.

The **election path** carries **6 axioms**, of which **5 are legitimate**
under the scope rule:

| axiom | file | why it is outside the raft protocol |
|---|---|---|
| `is_Logger`, `is_Logger_pers`, `wp_Logger__logf` | `inv_logger.v` | the `Logger` is a client-supplied interface. Covers only the **non-panicking** methods — a path reaching `Panic`/`Panicf` has to be shown unreachable. Not a Go-function spec at all: it dispatches through `#(methods …)` on an interface value, which is why it stays with its predicate |
| `wp_slices_Sort` | `proof_slices_Sort.v` | Goose does not translate it. Permutation-only postcondition |
| `own_Storage` | `inv_storage.v` | `raftLog.storage` is a client-supplied `Storage`; raft itself ships only `MemoryStorage`, for tests. A predicate, not a triple |

The sixth, **`wp_raft__appendEntry`** (`proof_raft__appendEntry.v`), is core
raft and still owed. It was called `wp_raft__appendEmptyEntry` until
2026-09-18 — after a Go method that **does not exist**; the method it
specifies is `appendEntry`. See
[false-statements.md](false-statements.md).

**The 2026-09-18 restructure moved the trust base and did not change it.**
Counted with comments stripped, before and after: the same 6 axioms and the
same 7 `Admitted`s, now one per `proof_*.v` file named after its function —
`JointConfig__IDs`, `ProgressTracker__TallyVotes`, `ProgressTracker__Visit`,
`raft__bcastAppend`, `raft__hasUnappliedConfChanges`, `raft__promotable`,
`raft__resetRandomizedElectionTimeout`.

That is down from 13 (5 of them owed) at the start of the day. What moved:

- **`own_raftLog` is a real definition** (`inv_raftlog.v`), and its four
  methods — `lastIndex`, `lastEntryID`, `isUpToDate`,
  `hasNextOrInProgressSnapshot` — are `Qed`, along with the `unstable`
  helpers beneath them. Four axioms became zero. The `Panicf` paths in
  `lastIndex` and `term` are discharged rather than assumed: that is what
  `is_Storage` is for. `own_raftLog` exposes the entry list, so it can also
  carry "no `EntryConfChange` in the log", which is what
  `hasUnappliedConfChanges` needs.
- **`own_raft_misc` is a real definition** and `inv_misc.v` has **no axioms
  at all**.
- The five `traceX` functions are literal no-ops in the translated code
  (`λ: <> <>, exception_do (do: #())`), so each is a two-line proof.

**Read a callee's translated body before assuming anything about it.** Six
axioms went away on 2026-09-16 for almost no work, which says more about how
this was being audited than about the work.

### What is `Admitted`, and why

Seven lemmas. **The array-indexing defect that blocked three of them was
fixed on 2026-09-17**, so only one of the seven is still blocked on tooling.
The three that it blocked moved into their own collections on 2026-09-18, so
their files below are the `proof_*.v` ones, not `inv_*.v`:

| lemma | file | blocker |
|---|---|---|
| `wp_JointConfig__IDs` (was `wp_campaign_peer_ids`) | `proof_JointConfig__IDs.v` | *unblocked 2026-09-17* — the `IndexRef` steps now. What is left: `array_acc` to peel element 0 off `c`, then `wp_map_for_range` |
| `wp_ProgressTracker__TallyVotes` | `proof_ProgressTracker__TallyVotes.v` | array part unblocked; **still blocked** on `len` of a nil map ([../bugs/golang-len-of-nil-map-is-stuck.md](../bugs/golang-len-of-nil-map-is-stuck.md)). Also has a statement bug: its `VoteWon` conjunct is false at `cfg = ∅` |
| `wp_ProgressTracker__Visit` | `proof_ProgressTracker__Visit.v` | *unblocked 2026-09-17* — both the array `len` and the `sl[:n]` slice step now |
| `wp_raft__resetRandomizedElectionTimeout` | `inv_misc.v` | reaches the global RNG through `crypto/rand` and `math/big`. The RNG is outside core raft and may be assumed, but the assumption has not been written |
| `wp_raft__promotable` | `inv_misc.v` | *unblocked* — `own_raftLog` is now real. Next thing to pick up |
| `wp_raft__hasUnappliedConfChanges` | `inv_misc.v` | *unblocked* — likewise |
| `wp_raft__bcastAppend` | `inv_raft_phys.v` | log replication, not election; needs `Progress.State` and the log opened up |

Each `Admitted` carries a machine-checked prefix and a comment naming the
blocker, in the style `proof_raft__Step.v` used. Splice and continue; do not
start over.

**Do not count these by hand, and do not grep for them** — a grep
over-counts, because several doc comments quote a probe lemma ending in
`Admitted.` and the `spec_*.v` files are full of `Parameter`s. Since
2026-09-18 the counts are printed:

    etc/tcb-report.py                    # summary, and which files are incomplete
    etc/tcb-report.py --scope election
    etc/tcb-report.py --view assumed     # every axiom and admit, classified
    etc/tcb-report.py --view surface     # what the exported statements rest on

As of 2026-09-18 it reports, over the whole raft proof: **45 assumed** — 31
`Axiom` and 14 `Admitted`, of which 18 are Hoare triples about Go code, 13
are properties of the model, and 14 are opaque declarations — against **85
definitions, 651 lines**, reached from the exported statements. That last
number is the one a count of axioms misses and is the larger half of the
trust base: `raft_election_safety` says nothing if `nstate.t` or
`own_raft_ghost` is wrong, and neither is an axiom. Total 866 lines, 9.8% of
the development. On the election path alone: 6 axioms, 7 admits, 43
definitions.

**Admits rising while axioms fall is the conversion working, not a
regression** — and `--view assumed` says which is which, per file, with the
Go function each triple is about.

The 44 module-type obligations — one `Parameter` per Go function — are
**not** assumptions: each is discharged by the functor ascribed to its
signature, so none reaches `Print Assumptions`, and the tool counts them
under "not trusted" alongside the 43 internal function specs. Only one
collection, `raft__Step`, is exported. See
[decisions.md](decisions.md) for what counts as the TCB and why, including
what the tool cannot see.

**One deliberate admission on the election path: the log fits in memory.**
`proof_raftLog__slice.v` ends `Admitted. (* Trusted *)` for a single
arithmetic side condition, `|ents| + |unstable| < 2^63` at the `extend`
call: Go computes `len(dst)+len(vals)` as an `int`, and with about `2^63`
unstable entries it wraps, so the triple is false there. The bound is not
derivable — `Hbounded` gives the stable part `< 2^61` and the model bounds
any one slice at `2^63`, which sums to `2^61 + 2^63` — and it can be neither
carried (an append cannot re-establish a carried bound, decisions.md) nor
stated as a premise (nothing at `Step` can see the log's length). Same
class as the two `(* Trusted *)` overflow admits in `readonly.v`;
`tcb-report` lists it as "trusted, deliberate". Since 2026-09-21 the same triple also hands the `raftLog` record (`l ↦ lv`) back beside the page and takes both in its wand — a strictly stronger assumption, true because a page aliases an entry buffer, never the record.

**A framework `Admitted` sits under the array proofs.** `into_val_typed_array`
(`new/golang/theory/array.v`, the `IntoValTypedUnderlying` instance for
`array.t`) is `Admitted` with three `admit`s. `wp_JointConfig__IDs` reads
the `[2]MajorityConfig` value out of `trk ↦ tv` through it (the element
loads themselves go through the `Qed` `typed_pointsto_array`). It is outside
the raft tree, so `tcb-report` does not count it; it is part of what has to
be believed until someone proves it.

**`Print Assumptions` is still not available as a cross-check.** Over a
`.vos` tree it under-reports — it sees axioms reachable from *statements* but
not what opaque proofs used, so the `Admitted`s and the `wp_*` trust-boundary
axioms do not appear. Ground truth needs a full `.vo` build of Perennial,
which nothing in this tree has.

## Next steps

Unclaimed; pick one and say so in the journal.

1. **`wp_raft__promotable` and `wp_raft__hasUnappliedConfChanges`**
   (`inv_misc.v`). Both were blocked on `own_raftLog` and both are now
   unblocked: the predicate is real, it exposes the entry list, and
   `wp_raftLog__hasNextOrInProgressSnapshot` is back and `Qed`. This is the
   cheapest remaining win on the election path.
2. **Cash in the array fix** (landed 2026-09-17, see the journal). The
   translation steps now, so `wp_JointConfig__IDs`,
   `wp_ProgressTracker__Visit` and the `wp_JointConfig__CommittedIndex` axiom
   in `readonly.v` are ordinary proof work. `wp_JointConfig__IDs` is the
   cheapest: `array_acc` on `c` for element 0, then `wp_map_for_range` over
   `voters_ref`, then `wp_map_nil_for_range` at index 1.
   `wp_ProgressTracker__TallyVotes` needs
   [../bugs/golang-len-of-nil-map-is-stuck.md](../bugs/golang-len-of-nil-map-is-stuck.md)
   fixed first, and separately its `VoteWon` conjunct repaired.
3. **`wp_raft__appendEntry`** — the last core-raft axiom on the election
   path — and then `wp_raft__bcastAppend`, which is really log replication.
4. Construct `own_raft_ghost` / `is_message` rather than axiomatizing them,
   discharging `own_raft_ghost_step`, `own_raft_ghost_outbox` and
   `is_leader_unique`. Until that is done the election-safety corollary rests
   on an axiom. This is 12 of the 44 axioms, the `Section ghost` block in
   `election_protocol.v`.
5. Decide what the top-level Raft correctness statement should be (beyond
   election safety), and write it down as a decision record.
6. Discharge the `Section axioms` in `v3_proof/protocol.v` against the actual
   translated code in `new/code/go_etcd_io/raft/v3/`, or record why each axiom
   stays an axiom.
7. Extend `v3.v` past `Propose` to the rest of the `node` interface.
8. **Bring `readonly.v` and `protocol.v` into the module discipline.**
   `etc/check-module-discipline.py` lists eleven triples still
   stated loose: `ProgressTracker__IsSingleton`,
   `raft__committedEntryInCurrentTerm`, `readOnly__addRequest`,
   `readOnly__recvAck`, `JointConfig__CommittedIndex`,
   `readOnly__maybeAdvance`, `sendMsgReadIndexResponse` and `stepLeader` in
   `readonly.v`; `node__Ready`, `node__Advance`, `node__Propose` in
   `protocol.v`. The last of the `readonly.v` ones is a **real duplicate**:
   `raft.stepLeader` has a second triple there, against a second ownership
   story for the raft struct (`own_raft`), and it is `Admitted` with
   postcondition `True` and no users. Resolving that means deciding whether
   `own_raft` or `own_raft_phys` survives — see
   [false-statements.md](false-statements.md), which is the wider reason this
   is worth doing rather than a tidiness errand.

## Before you add a claim

Ten statements in this development have been asserted, compiled, and lived
in the tree until a proof needed the fact and could not get it — including
two that had a `Qed` resting on them. The table, the tells to grep for, and
the two-probe check for a pointer-receiver spec are in
[false-statements.md](false-statements.md). **Read it before writing a spec
or an `Admitted`.**

## Known broken

- **`spec_raft__campaign.v` was FALSE as written** — found 2026-09-16 while
  proving `campaign`, **fixed the same day**; the premise is in the spec and
  `campaign` is now `Qed`. Kept here for the lesson, which is not stale.

  `send` panics on a vote message whose `Term` is zero —
  `Panicf("term should be set when sending %s")` in `raft__sendⁱᵐᵖˡ` — which
  is why `wp_raft__send_vote` requires `m.(raftpb.Message.Term') ≠ W64 0`.
  `campaign` sends at `term = r.Term` *after* `becomeCandidate` has set
  `r.Term = old + 1`. So at `s.(nstate.term) = 2^64 - 1` the new term wraps
  to `0` and the real code panics, while the spec claims it returns having
  sent. `wp_Logger__logf` deliberately does not cover `Panicf`, so the proof
  genuinely cannot get past it — the falsity is detectable, and was detected.

  The fix (applied) is a no-wrap premise, `uint.Z s.(nstate.term) + 1 < 2^64`,
  on `wp_raft__campaign_body`, threaded through `wp_raft__hup_body` and into
  `spec_raft__Step.v`'s `MsgHup` hypothesis (which already has the shape
  `Type' = MsgHup → …`). It **cannot** live in `own_raft_phys`: that predicate
  has to be re-established after `becomeCandidate` increments the term, and
  `term + 1 < 2^64` does not survive its own increment.

  There is precedent for treating counter overflow as an assumption here —
  `readonly.v:589,668` carry `admit`s marked "overflow of incrementing
  value" — but this one has to be *stated*, not admitted, because it changes
  a triple that other proofs consume.

  It was the third of the ten false statements tabled above, after
  `wp_raft__appendEntry` (2026-09-15, then called
  `wp_raft__appendEmptyEntry`) and `step_win` (2026-09-16). All
  three were claims about what raft's code does to its outgoing messages. The
  pattern is worth naming: a plausible-looking bookkeeping claim about
  `send`/`msgs`/`msgsAfterAppend` is the thing this development keeps getting
  wrong, so check those against `raft__sendⁱᵐᵖˡ` specifically.

- **The Goose array-indexing defect is fixed** (2026-09-17 on
  `worktree-goose-array-index-fix`, merged into `main` 2026-09-19): Goose
  passes an array's address to `IndexRef`/`Slice`, folds `len`/`cap` of an
  array to the constant, and `new/golang/defn/array.v` has guarded
  `go.len`/`go.cap` rules. The bug file is deleted; history remembers it.
  What was left of that blocker — **`len` of a nil map has no rule** — was
  fixed on 2026-09-19 (nil case in `go.len_map`, `pure_wp_map_nil_len`).
  `bugs/` is where tooling defects go; an unfinished proof is not one.

- ~~**`ruff check` fails: 64 errors.**~~ Fixed 2026-09-19; see that day's
  second journal entry for the two that needed a decision rather than a
  keystroke. Both python CI jobs are green — `ruff check .` and
  `ruff format --check .` over 42 files, re-confirmed 2026-09-21. Keep them
  that way: run both before pushing a change under `etc/` or `new/etc/`.

## Standing facts

- `new/code/` and `new/generatedproof/` are Goose output. **Never edit them by
  hand** and never imitate their style. Regenerate with
  `new/etc/update-goose-new.py`.
- `make ci` builds `new/should_build.vo`, which is what CI checks. A proof not
  reachable from `new/should_build.v` is not being built.

- Faster inner loop: `make vos` for interface files, or
  `make new/proof/go_etcd_io/raft/v3.required_vos` to build just what a file
  depends on. See `CONTRIBUTING.md`.
- **Every build prints a per-file time** — a `ROCQ TIME <secs> <mode> <file>`
  line as each file finishes — and records it in `.timing.sqlite3`, keyed on
  the file *and* the build mode. `make timing-report` ranks the bottlenecks;
  `make TIMING_MIN=10` prints only the slow ones. Numbers from before
  2026-09-21 conflate `vo` and `vok` — see [gotchas.md](gotchas.md).
- The Go module path here is still `github.com/mit-pdos/perennial` and the Rocq
  logical paths are still `Perennial`/`New`, on purpose — see
  [decisions.md](decisions.md).
