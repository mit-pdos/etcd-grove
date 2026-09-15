# Status

**Last updated:** 2026-09-15

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

**Leader-election refinement** — `new/proof/go_etcd_io/raft/v3_proof/`,
branch `worktree-raft-election-refinement`. Compiles and is reached from
`new/should_build.v`.

Eleven Go functions are specified, one file each. Proved: `voteRespMsgType`,
`send`, `becomeFollower`, `becomeCandidate`, `becomeLeader`, `Step` (its
dispatch and its `MsgHup` branch), and `raft_election_safety`. Five are
`Admitted`: `reset`, `poll`, `campaign`, `hup`, `stepCandidate`; plus two
`admit`-bearing branches inside `proof_raft__Step.v` (`MsgVote`, proved as far
as `isUpToDate`, and `MsgVoteResp`).

**Restructured 2026-09-15 so that no spec below `Step` touches ghost state.**
The outbox moved into `nstate.t`; `own_raft_phys` lost its `γ` and no longer
certifies the outgoing queues; certification is read off the ghost with the
new `own_raft_ghost_outbox`. `own_raft_ghost` now appears in exactly one spec
(`Step`) and `own_raft_ghost_step` is applied in exactly one proof file. A
spec below `Step` says only which state the struct refines and how the outbox
grew — never that the transition is legal. See
[decisions.md](decisions.md) for the alternatives that were rejected.

The three `becomeX` proofs rest on `wp_raft__reset`, so **`reset` is the
highest-leverage hole**, and it is less mechanical than it looks (it replaces
`r.readOnly`). Details in
[raft-election-refinement.md](raft-election-refinement.md). The `MsgVote`
blocker recorded there on 2026-09-14 is **gone**: it was `iFrame` refusing to
fill `send`'s `#Hm` slot, and `send` no longer has one.

**Checking your work:** `make <file>.vos` is a ~2s loop but **does not check
proof bodies** — it will accept a proof script that does not run. Use
`make <file>.vok` (~60s per function) for the real check. Do not reach for
`.vo`: nothing in the tree has `.vo` dependencies, so `make x.vo` starts
building all of Perennial.

## Trust base

As of 2026-09-15 the raft proof assumes **50 axioms and 14 `Admitted.`** (2 of
the admits deliberate, marked `(* Trusted *)` at `readonly.v:464,471`). The
one axiom added that day is `own_raft_ghost_outbox`; more importantly, one of
the 50 — `wp_raft__appendEmptyEntry` — **stopped being a false statement**. It
owned only `own_raftLog` while the code it describes queues a `MsgAppResp`
into `r.msgsAfterAppend`. See [journal.md](journal.md).

The trust base is split structurally:

- an `Axiom` in an `inv_*.v` file means **out of scope** (the log, the
  tracker's non-vote state, the `Logger` and tracing helpers);
- an `Admitted` in a `proof_*.v` file means **in scope but unfinished**.

There are also 11 module-type obligations — one `Parameter` per Go function.
Those are **not** assumptions: each is discharged by the functor ascribed to
its signature, so none reaches `Print Assumptions`. Print the list with

    ./etc/tcb-view.py --summary new/proof/go_etcd_io/raft

which also renders any file down to just its trust-relevant parts. It is
textual and needs no build, so it does *not* see assumptions inherited from
Perennial, Iris, or the Goose translator — see
[decisions.md](decisions.md) for what it is and is not good for.

`./etc/tcb-view.py --self-check` now also enforces the layout invariant:
every `spec_*.v` must declare exactly one `Parameter` and assume nothing.

**`Print Assumptions` is still not available as a cross-check.** Over a
`.vos` tree it under-reports — it sees axioms reachable from *statements* but
not what opaque proofs used, so the `Admitted`s and the `wp_*` trust-boundary
axioms do not appear. Ground truth needs a full `.vo` build of Perennial,
which nothing in this tree has.

## Next steps

Unclaimed; pick one and say so in the journal.

1. Finish the election refinement: `reset` (three proved lemmas rest on it),
   the `MsgVote` branch in `proof_raft__Step.v`, `poll` / `campaign` / `hup`,
   then `stepCandidate` and the `MsgVoteResp` branch. Each is now one
   `proof_*.v` file that re-checks in about a minute with `make <it>.vok`.
   See [raft-election-refinement.md](raft-election-refinement.md).
2. Construct `own_raft_ghost` / `is_message` rather than axiomatizing them,
   discharging `own_raft_ghost_step`, `own_raft_ghost_outbox` and
   `is_leader_unique`. Until that is done the election-safety corollary rests
   on an axiom. This is 12 of the 50 axioms; `./etc/tcb-view.py --summary`
   lists them under `Section ghost`.
3. Decide what the top-level Raft correctness statement should be (beyond
   election safety), and write it down as a decision record.
4. Discharge the `Section axioms` in `v3_proof/protocol.v` against the actual
   translated code in `new/code/go_etcd_io/raft/v3/`, or record why each axiom
   stays an axiom. `./etc/tcb-view.py new/proof/go_etcd_io/raft/v3_proof/protocol.v`
   shows them with nothing else in the way.
5. Extend `v3.v` past `Propose` to the rest of the `node` interface.

## Known broken

- **`./etc/tcb-view.py --self-check` reports 51 axioms against an expected
  50.** Every per-file count passes; the extra one is in
  `new/proof/go_etcd_io/raft/v3_proof/election/exp_phys_sealed.v`, an
  **untracked** experiment from an earlier session (a sealed `own_raft_phys`
  with an access-lemma API) whose header points at `journal.md` but for which
  no entry was ever written. It is not reached from `should_build.v`, so CI
  does not build it, and since 2026-09-15 it no longer compiles either — it
  references `is_phys_msg`, which the outbox change deleted. Its subject is
  moot now that `own_raft_phys` has a different shape. **Delete it, or redo
  the experiment and commit it**; it was left alone because it is someone
  else's uncommitted work. The discrepancy predates 2026-09-15 (the tables
  said 49 while the file already made it 50).

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
- `./etc/tcb-view.py` renders a `.v` file down to its trust base — theorem
  statements, the definitions they reach, and every axiom and hole — hiding
  proofs and proved helper lemmas. `--summary` for just the audit list,
  `--self-check` to verify the parser.
- Faster inner loop: `make vos` for interface files, or
  `make new/proof/go_etcd_io/raft/v3.required_vos` to build just what a file
  depends on. See `CONTRIBUTING.md`.
- The Go module path here is still `github.com/mit-pdos/perennial` and the Rocq
  logical paths are still `Perennial`/`New`, on purpose — see
  [decisions.md](decisions.md).
