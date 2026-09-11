# Status

**Last updated:** 2026-09-11

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

So: the read-index/heartbeat protocol reasoning is the most developed part, the
node interface is still axiomatized, and per-function proofs against the
translated raft code have barely started.

### Rest of etcd

`new/proof/go_etcd_io/etcd/` carries earlier work on the client (`client/v3`,
`client/v3_proof/`, including a leasing protocol proof), `pkg/v3` (`wait`,
`idutil`), `api/v3` protobuf packages, and `server/v3/etcdserver`. This is
context for the raft work, not the current focus.

## In flight

Nothing. The repo was just forked and set up.

## Next steps

Unclaimed; pick one and say so in the journal.

1. Decide what the top-level Raft correctness statement should be, and write it
   down as a decision record. Everything below depends on this.
2. Discharge the `Section axioms` in `v3_proof/protocol.v` against the actual
   translated code in `new/code/go_etcd_io/raft/v3/`, or record why each axiom
   stays an axiom.
3. Extend `v3.v` past `Propose` to the rest of the `node` interface.

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
- Faster inner loop: `make vos` for interface files, or
  `make new/proof/go_etcd_io/raft/v3.required_vos` to build just what a file
  depends on. See `CONTRIBUTING.md`.
- The Go module path here is still `github.com/mit-pdos/perennial` and the Rocq
  logical paths are still `Perennial`/`New`, on purpose — see
  [decisions.md](decisions.md).
