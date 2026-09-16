# Status

**Last updated:** 2026-09-16

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

Eleven Go functions are specified, one file each. Proved (`Qed`, each
confirmed with `make <file>.vok`): `voteRespMsgType`, `send`,
`becomeFollower`, `becomeCandidate`, `becomeLeader`, **`poll`** and
**`hup`** and **`reset`** (all 2026-09-16), `Step`'s dispatch and its
`MsgHup` branch, and `raft_election_safety`.

Still `Admitted` as of 2026-09-16: `campaign`, `stepCandidate`, and
the `MsgVote` / `MsgVoteResp` branches inside `proof_raft__Step.v`
(`MsgVote` is proved as far as `isUpToDate`).

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
`own_progress` and `own_tracker` are real **definitions**, with their eight
method lemmas `Admitted`. `inv_raftlog.v` and `inv_misc.v` still need the
same treatment — see [journal.md](journal.md).

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

- **`./etc/tcb-view.py --self-check` fails against a stale inventory.** Its
  `EXPECTED_AXIOMS` / `EXPECTED_ADMITS` / `EXPECTED_TOTALS` tables
  (`etc/tcb-view.py:719-759`) still say 50 axioms and 14 admits; the tree is
  at 44 and 24 after the 2026-09-16 conversion of `inv_tracker.v` from axioms
  to definitions, and after `poll`/`hup`/`stepCandidate` were proved. **The
  tool is right and the table is stale** — refresh the table, do not "fix"
  the counts. Refresh it in the same commit as any future axiom→definition
  conversion; that is what the table is for.

  The older form of this entry blamed an untracked
  `election/exp_phys_sealed.v`. That file is **gone**, so that part is
  resolved.

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
