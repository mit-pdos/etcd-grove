# Status

**Last updated:** 2026-09-14

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
- `v3_proof/election_protocol.v` (334 lines) and `v3_proof/election.v` (1045
  lines) — **leader-election refinement**, added 2026-09-12. The protocol
  state machine for election, the ghost state (`own_raft_ghost`,
  `is_message`) and its one refinement obligation, `own_raft_phys` for the
  raft struct, and the top-level `wp_raft__Step` triples. See
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
`new/should_build.v`. Proved: `wp_raft__send_vote` (the message-legitimacy
obligation), `wp_raft__becomeFollower` / `wp_raft__becomeCandidate` /
`wp_raft__becomeLeader` (2026-09-14), `wp_raft__Step_MsgHup`,
`wp_voteRespMsgType`, the model-level step-composition lemmas, the
`wp_raft__Step` dispatch, and `raft_election_safety`. Seven lemmas are still
`Admitted`. The three `becomeX` proofs rest on `wp_raft__reset`, which is one
of them — so `reset` is now the highest-leverage hole, and it is less
mechanical than it looks (it replaces `r.readOnly`). The other standing
target is `wp_raft__Step_MsgVote`, proved as far as the `isUpToDate` branch.
Details, the stuck point, and a **soundness looseness in `own_raft_phys`
found on 2026-09-14** are in
[raft-election-refinement.md](raft-election-refinement.md).

## Trust base

As of 2026-09-14 the raft proof assumes **50 axioms and 14 `Admitted.`** (2 of
the admits deliberate, marked `(* Trusted *)` at `readonly.v:464,471`; the other
12 are unfinished and hold 12 interior `admit.` tactics). Print the current list
with

    ./etc/tcb-view.py --summary new/proof/go_etcd_io/raft

which also renders any file down to just its trust-relevant parts. It is
textual and needs no build, so it does *not* see assumptions inherited from
Perennial, Iris, or the Goose translator — see
[decisions.md](decisions.md) for what it is and is not good for.

## Next steps

Unclaimed; pick one and say so in the journal.

1. Finish the election refinement: `wp_raft__reset` (three proved lemmas
   rest on it), `wp_raft__Step_MsgVote`, `poll` / `campaign` / `hup`, then
   `stepCandidate` and `wp_raft__Step_MsgVoteResp`. See
   [raft-election-refinement.md](raft-election-refinement.md).
2. Resolve the `own_raft_phys` double-ownership of `r.trk` described in
   [raft-election-refinement.md](raft-election-refinement.md) — it is
   harmless while `own_tracker` is an axiom and fatal once it is not, so it
   belongs with step 3 below.
3. Construct `own_raft_ghost` / `is_message` rather than axiomatizing them,
   discharging `own_raft_ghost_step` and `is_leader_unique`. Until that is
   done the election-safety corollary rests on an axiom. This is 11 of the 50
   axioms; `./etc/tcb-view.py --summary` lists them under `Section ghost`.
4. Decide what the top-level Raft correctness statement should be (beyond
   election safety), and write it down as a decision record.
5. Discharge the `Section axioms` in `v3_proof/protocol.v` against the actual
   translated code in `new/code/go_etcd_io/raft/v3/`, or record why each axiom
   stays an axiom. `./etc/tcb-view.py new/proof/go_etcd_io/raft/v3_proof/protocol.v`
   shows them with nothing else in the way.
6. Extend `v3.v` past `Propose` to the rest of the `node` interface.

## Known broken

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
