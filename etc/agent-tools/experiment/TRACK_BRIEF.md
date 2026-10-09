# Context for the improvement tracks

We are measuring how much cheaper it gets for a *fresh* AI agent to write a new Perennial/Lean
proof when the proof tooling improves along the lines of a cost analysis of an earlier proof
effort (the google/btree proof in etcd-grove). The analysis (`COST.md`) found:

- 392 build-and-check runs, 65% with errors; ~130 "unsolved goals" errors, partly from ending a
  proof with `done` just to see the goal. Waiting on the compiler was 40–47% of wall time for
  four of seven agent groups: every check recompiles the whole file (~60 s for
  `Proof/node__iterate`), and the only way to see a goal is to make the build fail.
- ~814k output tokens, of which ~190k proof text; the rest thinking, mostly about why a tactic
  did not match. ~2.4M characters of build output fed back: Perennial goals print the whole rest
  of the function as a GooseLang term.
- Easy work that could be automated: (1) pure list facts (`take`/`drop`/subslice/`set`/length,
  sortedness, in-order contents) — most of `Lemmas/` (3,130 lines), re-derived by several agents;
  (2) Perennial tactic gaps: `wp_auto` cannot load a field through a fractional struct points-to;
  unnamed Go results block `wp_auto`; value methods called through a pointer need manual steps;
  short-circuit `&&` in loop conditions split by hand; `zero_val w64` vs `W64 0` syntactically;
  `removeOp` unfolds on one side of a goal but not the other; (3) bounds side conditions: the
  repeated `rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word, by word⟩)]` before slice and
  index steps; (4) framing mismatches in the Iris proof mode (44 errors), mostly a term not matching
  syntactically — normalising before framing would catch many; (5) boilerplate.
- What would speed it up most, in order: interactive incremental checking (goal-at-position,
  per-tactic feedback instead of whole-file rebuilds); shorter goal printing (hide the continuation
  and the GooseLang term by default); a shared list/tree lemma library with list-segment
  automation; fixing the tactic gaps; checking callee specs before agents build on them.

## The environment

Your directory (a private copy; edit freely inside it) contains:
- `EtcdGrove/Btree/`: the btree development (Defs, Model, Tree, `ListLemmas.lean`,
  `NodeLemmas.lean`, `Lemmas/*.lean`, `Spec/*.lean` (one Hoare triple per Go function),
  `Proof/*.lean` (one proof per function)). Three proofs are *challenges* for the later
  experiment and are stubs here (`Proof/items__insertAt.lean`, `Proof/items__find.lean`,
  `Proof/node__split.lean`). **Do not look for or reconstruct their original proofs** (do not read
  any other copy of the repository, git history, `../../answers`, `../../../btree-src`, or the
  `btree` worktree); the tools you build must be generic, not tailored to these three.
- `GoogleBtree/`: the Goose translation of google/btree (`Code/.../btree.lean`); `go/btree_generic.go`.
- `perennial/`: Perennial's sources and docs (`perennial/docs/PERENNIAL_PROOF_REFERENCE.md`,
  `IRIS_PROOF_MODE.md`, `PERENNIAL_PROOF_TUTORIAL.md`; tactics in
  `perennial/Perennial/Golang/Theory/{Auto,ProofMode,Mem,...}.lean`).
- Compiled libraries are shared, read-only, in `/home/ubuntu/.claude/jobs/f5d25fd8/tmp/exp/snap/`
  (LEAN_PATH order: perennial, iris, qq, batteries, btree). **Never write there.** Modules you add
  can be compiled into your own directory: e.g. `mkdir -p build && LEAN_PATH=$LEAN_PATH:$PWD/build
  lean X.lean -o build/<Module/Path>.olean -i build/<Module/Path>.ilean` (run from your dir so the
  module name is computed from the path), and put `$PWD/build` on LEAN_PATH for files importing it.
- `./check FILE.lean`: baseline whole-file check (`lean FILE`, full output). ~2 s for a stub,
  ~60 s for `Proof/node__iterate.lean`.
- `./ide`: a first version of an LSP-based tool (`./ide check FILE`, `./ide goal FILE LINE
  [--after] [--full]`): persistent `lean --server`, goal at a position, compact printing (elides the
  section variables and the GooseLang program after 14 lines). Read its source.
  Findings so far: a warm `./ide check` of an unchanged file is instant and goals at a position cost
  ~0.2 s, but a one-line edit near the end of `node__iterate` still re-elaborates for ~62 s
  (no visible reuse of tactic snapshots), and skipping the kernel (`-Ddebug.skipKernelTC=true`)
  does not help (89 s): the time is elaboration, much of it `simp` inside the WP tactics.
- Lean 4.34.1 (`~/.elan/bin`), no Mathlib; Batteries is available.

Constraints: no changes to Perennial (it is precompiled); new tactics/lemmas go in new modules
in your directory. Use `python3 -I` for scripts. Keep your total runtime reasonable (aim for ≤ 90
minutes). Clean up background processes you start (`./ide stop`).

## Deliverable

1. The tool/module/scripts, in your directory, with a short `TRACK.md` there: what it is, how an
   agent uses it (a 5–15 line usage section that can be pasted into an agent brief), and how you
   validated it.
2. Quantitative validation on the existing (non-challenge) proofs: e.g. time per check, characters
   of output per goal, number of existing occurrences a tactic replaces (and that the proofs still
   compile after the replacement, on a few files), lemmas proved automatically, etc.
3. Your final message: a concise report (≤ 500 words) with the numbers, limitations, and your
   estimate of how much the tool would save a fresh agent writing a proof like those in `Proof/`.
