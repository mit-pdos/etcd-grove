# Status

**Last updated:** 2026-09-17

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
- `v3_proof/election/` (51 files) and `v3_proof/election.v` (78 lines) — the
  implementation side. **Restructured 2026-09-14 into one file per Go
  function**: each has `spec_<fn>.v` (a `Module Type` with exactly one
  `Parameter` — the single place its Hoare triple is written),
  `postulates_<fn>.v`, `proof_<fn>.v` (a functor ascribed to the signature)
  and `link_<fn>.v`. Shared predicates live in `defs.v`, `inv_*.v` and
  `step_lemmas.v`, outside the module system. `election.v` is now only an
  aggregator plus `raft_election_safety`. See
  [decisions.md](decisions.md) for why, and
  [raft-election-refinement.md](raft-election-refinement.md) for scope, what
  is proved, what is admitted, and the trust boundary.

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

**Cost note:** `proof_raft__Step.v` takes **~45 minutes and 11.3 GB** to
`-vok`. Do not start a second build beside it; overlapping builds are what
killed several sessions.

**Verified on 2026-09-16 at `15fcbecd7`**, every file individually at
`-vok` RC=0 with zero errors: the four `inv_*.v` that changed, all 13
`proof_*.v`, and `election.v`. Note that this is *not* a `make ci` run —
that needs a full `.vo` build of Perennial, which nothing in this tree
has.

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
building all of Perennial.

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
the 50 — `wp_raft__appendEmptyEntry` — **stopped being a false statement**. It
owned only `own_raftLog` while the code it describes queues a `MsgAppResp`
into `r.msgsAfterAppend`. See [journal.md](journal.md).

**The scope rule changed on 2026-09-16** and this is now the governing
statement of it. The *only* thing the election development may assume
outright is the top-level one: that `Step` need handle only election
messages. Everything in **core raft** — the log, the tracker, `Progress`,
`bcastAppend`, `newReadOnly` — is in scope and must be constructed and
proved. Things genuinely outside the raft protocol may still be assumed:
`slices.Sort` (`inv_slices.v`), the `Logger` interface, the tracing hooks,
the RNG behind `resetRandomizedElectionTimeout`.

So the older reading of `inv_*.v` — "an `Axiom` here means out of scope" — no
longer holds for core raft. The trust base is now split as:

- an `Axiom` in an `inv_*.v` file means **outside the raft protocol**, and
  there should be very few;
- an `Admitted` `Lemma` anywhere means **in scope but unfinished**, whether it
  is in an `inv_*.v` file or a `proof_*.v` one;
- a `Parameter` in a `spec_*.v` file is neither — it is discharged by the
  functor ascribed to that signature.

`inv_tracker.v` was converted to this shape on 2026-09-16: `own_inflights`,
`own_progress` and `own_tracker` are real **definitions**, with their seven
method lemmas `Admitted`. `inv_raftlog.v` and `inv_misc.v` still need the
same treatment — see
[raft-election-refinement.md](raft-election-refinement.md) for what each one
costs.

As of the end of 2026-09-16 the **election path** carries **6 axioms**, of
which **5 are legitimate** under the scope rule:

| axiom | file | why it is outside the raft protocol |
|---|---|---|
| `is_Logger`, `is_Logger_pers`, `wp_Logger__logf` | `inv_logger.v` | the `Logger` is a client-supplied interface. Covers only the **non-panicking** methods — a path reaching `Panic`/`Panicf` has to be shown unreachable |
| `wp_slices_Sort` | `inv_slices.v` | Goose does not translate it. Permutation-only postcondition |
| `own_Storage` | `inv_storage.v` | `raftLog.storage` is a client-supplied `Storage`; raft itself ships only `MemoryStorage`, for tests |

The sixth, **`wp_raft__appendEmptyEntry`** (`inv_raft_phys.v`), is core raft
and still owed.

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

Seven lemmas, all in `inv_*.v`. **The array-indexing defect that blocked
three of them was fixed on 2026-09-17**, so only one of the seven is still
blocked on tooling:

| lemma | file | blocker |
|---|---|---|
| `wp_campaign_peer_ids` | `inv_misc.v` | *unblocked 2026-09-17* — the `IndexRef` steps now. What is left: `array_acc` to peel element 0 off `c`, then `wp_map_for_range` |
| `wp_ProgressTracker__TallyVotes` | `inv_tracker.v` | array part unblocked; **still blocked** on `len` of a nil map ([../bugs/golang-len-of-nil-map-is-stuck.md](../bugs/golang-len-of-nil-map-is-stuck.md)). Also has a statement bug: its `VoteWon` conjunct is false at `cfg = ∅` |
| `wp_ProgressTracker__Visit` | `inv_tracker.v` | *unblocked 2026-09-17* — both the array `len` and the `sl[:n]` slice step now |
| `wp_raft__resetRandomizedElectionTimeout` | `inv_misc.v` | reaches the global RNG through `crypto/rand` and `math/big`. The RNG is outside core raft and may be assumed, but the assumption has not been written |
| `wp_raft__promotable` | `inv_misc.v` | *unblocked* — `own_raftLog` is now real. Next thing to pick up |
| `wp_raft__hasUnappliedConfChanges` | `inv_misc.v` | *unblocked* — likewise |
| `wp_raft__bcastAppend` | `inv_raft_phys.v` | log replication, not election; needs `Progress.State` and the log opened up |

Each `Admitted` carries a machine-checked prefix and a comment naming the
blocker, in the style `proof_raft__Step.v` used. Splice and continue; do not
start over.

Count them with a grep; the axiom count is the number to watch, and admits
rising while axioms fall is the conversion working, not a regression:

    grep -rc '^Axiom\|^  Axiom' new/proof/go_etcd_io/raft --include='*.v'
    grep -rn 'Admitted\.' new/proof/go_etcd_io/raft --include='*.v'

There are also 11 module-type obligations — one `Parameter` per Go function.
Those are **not** assumptions: each is discharged by the functor ascribed to
its signature, so none reaches `Print Assumptions`.

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
   translation now steps, so `wp_campaign_peer_ids`, `wp_ProgressTracker__Visit`
   and the `wp_JointConfig__CommittedIndex` axiom in `readonly.v` are ordinary
   proof work; `TallyVotes` needs
   [../bugs/golang-len-of-nil-map-is-stuck.md](../bugs/golang-len-of-nil-map-is-stuck.md)
   fixed first, and separately its `VoteWon` conjunct repaired.
   `wp_campaign_peer_ids` is the cheapest: `array_acc` on `c` for element 0,
   then `wp_map_for_range`, then `wp_map_nil_for_range` at index 1.
3. **`wp_raft__appendEmptyEntry`** — the last core-raft axiom on the election
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

## Before you add a claim

Eight statements in this development have been asserted, compiled, and lived
in the tree until a proof needed the fact and could not get it — including
two that had a `Qed` resting on them. The table, the three tells to grep
for, and the two-probe check for a pointer-receiver spec are in
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

  It was the third of the eight false statements tabled above, after
  `wp_raft__appendEmptyEntry` (2026-09-15) and `step_win` (2026-09-16). All
  three were claims about what raft's code does to its outgoing messages. The
  pattern is worth naming: a plausible-looking bookkeeping claim about
  `send`/`msgs`/`msgsAfterAppend` is the thing this development keeps getting
  wrong, so check those against `raft__sendⁱᵐᵖˡ` specifically.

- **`len` of a nil map is stuck**, which is what is left of the old array
  blocker on `wp_ProgressTracker__TallyVotes`. Measured 2026-09-17; see
  [../bugs/golang-len-of-nil-map-is-stuck.md](../bugs/golang-len-of-nil-map-is-stuck.md).
  `bugs/` is where tooling defects go; an unfinished proof is not one.

  The array-indexing defect that used to sit here is **fixed** (2026-09-17) —
  Goose passes the array's address, `len`/`cap` of an array fold to the
  constant, and `new/golang/defn/array.v` has the `go.len`/`go.cap` rules.

- **`ruff check` fails: 64 errors.** Pre-existing on this commit, in
  `etc/*.py`, `new/etc/update-goose-new.py`, `new/experiments/gencongruence.py`
  and `new/proof/.../logatom/paradox.py` — none of it related to the etcd work.
  Ruff was bumped 0.16.0 → 0.16.5 just before the fork (commit `3352ef9a7`) and
  0.16's wider default rule set now flags these (`I001`, `UP0xx`, `PLW1510`,
  `BLE001`, …). `ruff format` passes.

  This matters now because CI never actually ran in this fork until
  2026-09-11 (every workflow triggered on `master`; the default branch is
  `main`), so the `python` job will go red on the first push. 47 of the 64 are
  `ruff --fix`-able, but **do not blind-fix**: `PLW1510` wants an explicit
  `check=` on `subprocess.run`, which changes behaviour. Fix deliberately, in
  its own commit, or pin the rule set in `pyproject.toml`'s `[tool.ruff]`.

## Standing facts

- `new/code/` and `new/generatedproof/` are Goose output. **Never edit them by
  hand** and never imitate their style. Regenerate with
  `new/etc/update-goose-new.py`.
- `make ci` builds `new/should_build.vo`, which is what CI checks. A proof not
  reachable from `new/should_build.v` is not being built.

- Faster inner loop: `make vos` for interface files, or
  `make new/proof/go_etcd_io/raft/v3.required_vos` to build just what a file
  depends on. See `CONTRIBUTING.md`.
- The Go module path here is still `github.com/mit-pdos/perennial` and the Rocq
  logical paths are still `Perennial`/`New`, on purpose — see
  [decisions.md](decisions.md).
