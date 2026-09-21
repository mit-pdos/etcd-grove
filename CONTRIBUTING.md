# Contributing to etcd-grove

## Project notes

Durable project context — current status, design decisions, gotchas, and a
session journal — lives in [notes/](./notes/README.md), as plain markdown. Read
[notes/STATUS.md](./notes/STATUS.md) before starting, and update the notes when
you finish. Coding agents are pointed at the same place by
[AGENTS.md](./AGENTS.md).

## Checking the raft proof's module structure

Every Hoare triple about a Go function in the etcd raft proof belongs in a
`spec_<fn>.v` / `postulates_<fn>.v` / `proof_<fn>.v` / `link_<fn>.v`
collection, so that a function has exactly one specification and nothing can
bypass it — see
[notes/decisions.md](./notes/decisions.md), "One file per function, via Rocq's
module system". `etc/check-module-discipline.py` checks it:

```
etc/check-module-discipline.py --scope election   # clean
etc/check-module-discipline.py --summary
etc/check-module-discipline.py --selftest        # the parsing contract
```

It reads the program expression out of each triple rather than trusting lemma
names, so it reports which Go function a spec really specifies, and it
cross-references the Goose output in `new/code/` to catch a spec named after a
function that does not exist. It exits non-zero on errors. The whole raft
proof is *not* clean: `readonly.v` and `protocol.v` predate the discipline.

When one function's proof needs several files, the extra ones go in
`proof_<fn>_helpers/` — so listing the top level shows exactly the four files
of each collection, and the checker errors on a helper left outside. Today
only `raft__Step` has one.

The script knows the *toolchain* — how Goose renders a call, Perennial's
`{{{ … }}}` notation, and the file-naming convention — and no particular
package, function or file name. `--proof-root` points it at another
development (it finds 24 out-of-place triples in
`new/proof/go_etcd_io/etcd`, which predates the convention), `--code-root`
at another translation, and `--scope` takes a path or the bare name of any
directory under the proof root.

## Seeing what is unproven, and how big the TCB is

`etc/tcb-report.py` answers two questions that were otherwise answered by
grepping: where the proof is incomplete, and what has to be believed for its
results to mean anything.

```
etc/tcb-report.py                        # summary + the incomplete files
etc/tcb-report.py --scope election
etc/tcb-report.py --view assumed         # every axiom and Admitted, classified
etc/tcb-report.py --view surface         # the exported statements, and what they rest on
etc/tcb-report.py --view files           # one line per file
etc/tcb-report.py --format json
etc/tcb-report.py --selftest
```

It counts three things as trusted: everything **assumed** (an `Axiom` outside
a `Module Type`, or a proof ending in `Admitted`), the **results** the
development exports, and the **definitions** those results' statements are
written in terms of — the last usually being the biggest part, and the one a
count of axioms misses. It deliberately does *not* count a `Parameter` inside
a `Module Type`, which the functor ascribed to that signature discharges, nor
the spec of a function something else in the development calls: an internal
spec is an untrusted proof artifact, since a wrong one makes its callers'
proofs fail.

"Externally facing" means nothing in the development depends on it — a
collection no other collection requires or names, or a theorem in a file
nothing requires. Go's export rule is reported next to each result, not used
to decide.

The definition count is a **lower bound**: references through a `Notation` or
found by typeclass resolution are invisible, and definitions from Perennial,
stdpp and Rocq are outside the tree and not counted, though they are trusted
too. `--view surface` prints how many names it could not resolve.

It always exits 0 — it is a viewer, not a gate. It shares its parser with
`etc/check-module-discipline.py` (`etc/rocqscan.py`, which has its own
`--selftest`), and like that script it knows the conventions and no
particular package or file name, so `--proof-root` aims it elsewhere.

## Default build

Not everything in the repo is built by default, even in CI. In order to be
compiled, a file must be `Require`d from `new/should_build.v`, which is what
`make ci` builds.

## CI notes

CI runs on pushes and PRs to `main`, nightly, and on demand
(see [.github/workflows/](.github/workflows/)).

Upstream Perennial additionally pushes a `coq/tested` branch that Rocq's own CI
builds against. That is upstream's arrangement, not ours, so the workflow for it
is not in this fork.

We skip running Qed commands in CI using
[etc/disable-qed.sh](./etc/disable-qed.sh) - see that script for details. This
reduces build times by about 10%.

## Maintaining dependencies

The dependencies are pinned to a particular commit hash (using an opam
`pin-depends` clause) to avoid breaking the
Perennial build when there are incompatible upstream changes. We use Dependabot
to do monthly checks for dependency updates (see
[.github/dependabot.yml](.github/dependabot.yml) and read the GitHub
documentation). Unlike upstream, these are **not** auto-merged: upstream's
auto-merge workflow relies on a GitHub Ruleset that gates merging on CI, which
this fork does not have, so review and merge them yourself.

## Tips for managing compilation time

The repo takes about 180 CPU minutes to compile from scratch. Compiling in
parallel with `make -j4` (or more) is significantly faster, and can cut the time down to 40-50
minutes. Incremental builds are generally much faster.

You can compile individual files by simply running `make` with the path to a
specific `.vo` output file. We often run `make new/should_build.vo` to build a
file which depends on everything in new goose that is currently maintained, for exammple.

When you make a change to a dependency, you can keep working without fully
compiling the dependency by compiling `vos` interface files, which skips proofs.
The simplest way to do this is just to run `make vos`, but you can do a more
targeted build, like `make src/program_proof/wal/proof.required_vos`, which only
builds the vos dependencies to work on the `wal/proof.v` file.

Rocq also has a feature called `vok` compilation, where Rocq compiles a file
using only `vos` files for its dependencies. The process does not produce a
self-contained `vo` file, but emits an empty `vok` file to record that checking
is complete. Similar to compiling a single `vo` file, you can build a single
`vok` file, which will be much faster at compiling the dependencies. Using `vos` and `vok` files can significantly speed up the
edit-compile-debug cycle. Note that `vok` checking isn't the same as regular
compilation - it doesn't check universe constraints.

### Per-file build times

We compile with [rocqc.py](etc/rocqc.py), a Python wrapper around `rocq
compile`. Every build reports how long each file took, as it finishes:

```
ROCQ COMPILE new/proof/go_etcd_io/raft/v3_proof/election/proof_raft__send.v
ROCQ TIME   418.79s vo  new/proof/go_etcd_io/raft/v3_proof/election/proof_raft__send.v
```

The seconds field is fixed-width, so `make ci 2>&1 | tee build.log` and then
`grep 'ROCQ TIME' build.log | sort -rn -k3` ranks a build's bottlenecks
without touching the database. `make TIMING_MIN=10 ...` prints only files
taking at least ten seconds; `make TIMED=false ...` bypasses the wrapper
entirely.

The same timings go into `.timing.sqlite3`, one row per file **per build
mode** — a file's `vo`, `vos` and `vok` builds cost very different amounts
and are kept apart. Read them back with:

```
make timing-report                                      # the vo build
make timing-report TIMING_REPORT_ARGS="--mode vok"
./etc/timing-report.py --filter raft --max-qeds 20      # or call it directly
./etc/timing-report.py --selftest
```

`timing-report.py` needs only the standard library. A compile that *fails* is
not recorded, so a broken build does not overwrite the last good timing.

Timings recorded before 2026-09-21 could not tell `vo` from `vok`, and the
database's `vo` rows from then are a mix of the two; `rocqc.py` migrates such
a database in place the next time it writes to one. `./etc/rocqc.py
--selftest` checks the wrapper against the fixtures in `etc/test_coqc/`
(those same checks are pytest tests in `etc/test_coqc.py`, but pytest is not
a dependency and no CI job runs it).

## Updating Goose output

This repo has committed versions of the output of Goose, to avoid making Goose
and all the projects involved dependencies for compilation. You should update
these using `./new/etc/update-goose-new.py`, which records exactly how to
generate the output for the various Goose projects we have (in particular, the
list of packages that should be translated), including
[upamanyus/etcd-raft](https://github.com/upamanyus/etcd-raft) and
[upamanyus/etcd](https://github.com/upamanyus/etcd).

You can run `./etc/ci-goose-check.py` to clone all the projects whose proofs are
included in this repo and re-run the translation. This is what the check-goose
CI job does.

Because the Go sources live in separate repos, a change to them is a two-commit
affair: push the Go change to the relevant fork's `goose` branch, then
re-run the update script here and commit the regenerated `new/code/` and
`new/generatedproof/` output.

## Integer templating

Some files have templates that are used to support the various integer types by
copy-pasting:

```bash
./etc/int_template.py new/proof/sync/atomic.v
./etc/int_template.py new/trusted_code/sync/atomic.v
```

## Formatting / Linting

- `python`: we run [ruff](https://github.com/astral-sh/ruff) in CI
  to lint and format all our Python code.
  Run it locally with `ruff format` and `ruff check`.
- `toml`: we run [taplo](https://taplo.tamasfe.dev/) in CI
  to format all our toml files.
  Run it locally with `taplo format`.
