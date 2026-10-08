# etcd-grove (Lean)

This branch, `lean`, verifies **etcd** — starting with its Raft implementation — in
Lean, using the Lean port of Perennial (branch `lean` of
[mit-pdos/perennial](https://github.com/mit-pdos/perennial)), which is a Lake
dependency (`lakefile.toml`, pinned in `lake-manifest.json`). The framework, the
Goose translation of etcd and etcd-raft (`Perennial.Code.go_etcd_io`,
`Perennial.GeneratedProof.go_etcd_io`) and the public etcd proofs live there; this
repository holds the etcd proofs that are not public. The goal is to verify all of
etcd.

`lean` is the primary development. It started as a port of the Rocq development on
branch `main` (`new/proof/go_etcd_io/raft/election_proof/`), which is now a read-only
reference: its notes (`git show main:notes/STATUS.md`, `false-statements.md`,
`raft-implementation-facts.md`, `gotchas.md`) still describe the raft proof's design,
the false statements found so far and what raft actually does.

Several people's agents work on this repository at once, on different machines,
coordinating only through git. **Read `notes/collaboration.md`** for how; the short
version is the loop below.

## The loop ("Go")

If you were given no other instruction ("Go"), run this loop until your session
ends. Never edit `manual-notes.txt` (people's directions to agents).

0. **Isolate.** Work in your own clone or worktree, never in a checkout another
   session uses. `git fetch origin`. Get a build: `lake build` (the dependencies take
   a long time the first time; reuse a built `.lake/packages` if your machine has
   one).
1. **Pick.** `etc/tasks.py next --claim` picks and claims the next thing, in this
   order: `lean` is broken (fix it); a person wrote in a chat thread (reply);
   `manual-notes.txt` changed (bring `notes/roadmap.md` in line with it); your
   person's unfinished task; a review of another person's spec; the best open task;
   a stale claim. It prints what it claimed and the branch to work on. If it says
   there is nothing: plan (turn a roadmap direction without a design doc into a
   `design` task) or `etc/tasks.py wait`, then go back to 1.
2. **Work** on the task branch it names (`git switch -c task/<id> origin/lean`, or
   continue the existing branch: someone may have started it). Read the task file,
   its design doc and the notes it points to first. Commit often and
   `etc/tasks.py heartbeat` at least hourly: the pushed branch is the handoff if
   your session dies, and a claim with no push for 24 h can be taken over. Write
   what you did, where you stopped and the dead ends in the task's `## Log`.
3. **Land** with `etc/land.py`. It rebases onto `origin/lean`, regenerates
   `Link.lean`, builds, checks the trust base, pushes to `lean` and closes the task
   (`done`, or `review` if it changed a spec or added an axiom). If it touched a
   protected path (`etc/protected-paths.txt`) it opens a PR for a person instead.
   Update `notes/STATUS.md` in the landing if anything moved.
4. If you can't finish: land what you have (a precise `sorry` with a comment is
   better than an unpushed branch) and `etc/tasks.py release <id> -m "<where it
   stands>"`, or `etc/tasks.py block <id> --on <other-task>` when it needs other work
   first (create that task with `etc/tasks.py new … --push`). Go back to 1.

Chat (`notes/chat/<topic>.md`, `etc/tasks.py chat …`) is for **big ideas**, between
people and agents: directions, scope, a statement that turned out false, a design
that needs a decision. Open a thread for one; when `next` hands you a thread, read
all of it and reply, or turn it into tasks and say so in the thread. Small questions
go to whoever runs your session, not the chat.

## Rules

- **Never weaken a statement to make a proof go through**: a spec in `Spec/`, an
  invariant, a result. If one looks wrong, say why in the task log, leave a `sorry`,
  and open a chat thread if it changes what the project claims.
- One Go function, one spec: `Spec/<fn>.lean` is the only place its triple is stated.
  Changing a spec others' proofs use is its own task, naming the proofs it breaks.
- Adding an axiom or a `sorry` changes the trust base: `etc/tcb-report.py --check
  --update` rewrites `etc/tcb-baseline.txt`, which is protected, so it gets a
  person's look.
- Shared definitions (`Defs.lean`, `Inv*.lean`, `Base.lean`) rebuild everything
  downstream: change them in small, separate landings.
- Don't commit generated reports (`tcb-report.py -o`, `verified-code.py -o`,
  `build-report.py`). `Link.lean` is generated but committed: never merge it by
  hand, rerun `etc/gen-link.py`.

## Read the notes first

- `notes/STATUS.md` — where the proof is.
- `notes/roadmap.md` — the directions, ranked, and which tasks serve each.
- `notes/collaboration.md` — how the work is coordinated.
- `notes/decisions.md` — why the development is the way it is.
- `notes/README.md` — what else is in `notes/`, and how to write there.

## Layout

`EtcdGrove/Raft/` mirrors the Rocq directory `new/proof/go_etcd_io/raft/election_proof/`:

- the shared definitions (`Protocol`, `Defs`, `Inv*`, `StepLemmas`), outside the
  spec/proof discipline (predicates, pure lemmas);
- `Spec/<fn>.lean`: the one Hoare triple of a Go function, as `def <fn>.spec : Prop`;
- `Proof/<fn>.lean`: `theorem <fn>.wp_proof (callee specs …) : <fn>.spec`
  (an `axiom` at the trust boundary, `sorry` if unfinished); it imports only the
  `Spec` files of its callees;
- `Link.lean` (generated by `etc/gen-link.py` from the proofs' hypotheses): links
  every proof to its callees' proofs (`theorem <T>.wp_<M> : <fn>.spec`);
  `Results.lean` states the protocol-level results.

## Trust base

`etc/tcb-report.py` reports what the proof rests on (needs `lake build`): the
`sorry`s and axioms the results depend on, the exported results (linked results no
other proof uses), and the definitions their statements are written in terms of. Run
it when you need the report; don't commit its output (`-o` writes a file), which goes
stale as the proof changes. `etc/tcb-report.py --check` exits 1 if this repository's
axioms or `sorry`s differ from `etc/tcb-baseline.txt`; when you add or remove one on
purpose, rerun with `--check --update`.

## How much is verified

`etc/verified-code.py` accounts for how much of raft's and etcd's Go code is verified
(needs `lake build` and `go`): every Go function is verified, unfinished, assumed,
translated or not translated, counted in functions and Go code lines, per package and
per file. It reads the Go sources of the forks Perennial translates (cloned into
`.lake/go-src` on first use), this repository's proofs from `.lake/tcb.json` (shared
with `etc/tcb-report.py`; `--reuse` skips re-running Lean) and Perennial's public
etcd/raft proofs from their source. It prints plain text (`--markdown` for Markdown;
`-o FILE` writes Markdown if FILE ends in `.md`). Like the TCB report, don't commit
its output.

## Proof writing

Perennial's Lean docs (in the dependency, `.lake/packages/perennial/docs/`):
`PERENNIAL_PROOF_TUTORIAL.md`, `PERENNIAL_PROOF_REFERENCE.md`, `IRIS_PROOF_MODE.md`.
`notes/porting-guide.md` maps Rocq idioms to Lean.

## Building

`lake build` (needs the `elan` toolchain in `lean-toolchain`). Inside a task, check
single files with `lake env lean <file>`; `etc/land.py` runs the full build.

`etc/build-report.py build [LAKE_ARGS…]` runs `lake build` and then reports on it:
wall and CPU time, parallelism over time, the critical path (with Lake's idle time
per step), the unlimited-cores bound, the slowest modules and where the CPU went.
CI (`.github/workflows/lean.yml`) runs the build this way and puts the report on
the run's summary page. `etc/build-report.py` alone reprints the latest report,
`--list` lists the recorded builds (`.lake/build-report/`). CI's `board.yml` checks
the task board, `Link.lean` and the protected paths on every push.
