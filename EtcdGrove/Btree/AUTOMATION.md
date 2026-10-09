# Does better tooling make a fresh AI cheaper at writing btree proofs?

*An experiment on the ideas of [`COST.md`](COST.md), 2026-10-09, on this tree (the btree
branch at `a4a9fbe5b`; on `lean` the btree proof has since moved to the k8s fork, at
`Proof/k8s_io/utils/third_party/forked/golang/btree/`). Tools and harness:
[`etc/agent-tools/`](../../etc/agent-tools/).*

**Result.** With the tools, fresh agents wrote the same proofs **12% faster in wall time
and waited 33% less on the compiler** (up to −25% wall time and −60% compiler wait on
the medium and hard functions), but **used 24% more input tokens** (+15% weighted by
cache pricing), because cheap checks invite many more of them (+43% checks, +25% model
turns). All 20 runs, with and without tools, produced complete proofs that pass an
independent from-scratch check. On functions this size, `COST.md`'s ideas buy speed, not
tokens; the token savings `COST.md` anticipated (huge goals, 60 s rebuilds, re-derived
list libraries) need bigger functions than a fresh agent finishes in 3–17 minutes, or a
brief that also caps how often the agent checks.

## 1. The challenges

Five btree functions whose proofs were removed (replaced by `sorry`), chosen for
different kinds of difficulty:

| challenge | original proof | what it needs |
|---|---|---|
| `items.insertAt` | 59 lines | slices: `append`, an overlapping `copy`, list arithmetic |
| `items.find` | 122 lines | a `sort.Search` closure, sortedness, `countLt` |
| `node.split` | 124 lines | node ownership, splitting items and children slices, two callees |
| `node.get` | 128 lines | recursion over the tree (strong induction), lookup lemmas |
| `node.insert` | 356 lines | recursion, `maybeSplitChild`, four branches, a lemma library |

To keep the agents from reusing the answers:
- the challenge proofs were replaced by stubs (header and statement kept), and their
  compiled modules removed from the library the agents build against (so they cannot be
  imported and `#print`ed);
- the lemmas used *only* by a challenge proof were removed from `ListLemmas.lean`,
  `Lemmas/*.lean` (and their compiled modules rebuilt): 8 for tier 1 (`insertAt_list`,
  `shiftRight_list`, five `find` lemmas, `ownNodes_take_drop`), 18 for tier 2 (16 in
  `Lemmas/Insert.lean`, 2 in `Lemmas/Read.lean`); everything else (other proofs, the rest
  of the lemma library) stayed available, as it would for a new function;
- each agent got a private copy of the sources without `.git`, was told not to read
  anything outside it, and its transcript was **audited** for every path it touched
  (the answers, the exported sources, the btree worktree, git, other runs): **0
  violations in 20 runs**;
- grading is independent of the agent: the final file is compiled from scratch with the
  plain checker, must have no errors and no `sorry`, an unchanged statement, and depend
  on no axioms beyond those of an existing btree proof.

Caveat: the original `node__insert.lean` defines, before the theorem, a local macro
`insert_tail` (the 40-line descent into a child and recursive call) that the stub kept.
All four `node.insert` agents used it (and had to reconstruct the two lemmas it calls),
so this challenge is easier than writing `node.insert` from nothing — equally for both
conditions.

## 2. The tools (`COST.md`'s ideas, implemented)

Explored in parallel by four agents (write-ups in `etc/agent-tools/experiment/tracks/`),
then merged:

| `COST.md` idea | implementation | validation on existing proofs |
|---|---|---|
| interactive, incremental checking | `ide`: a persistent Lean server; `ide upto FILE LINE` checks only up to a line (rest closed with `sorry`), `ide steps` shows what each tactic changed, `ide goal` shows a goal without breaking the build; auto-restart, timeouts | after an edit: 0.4–4.5 s vs 5–60 s for a whole-file check (`node__iterate`: 59 s → 1.9–4.5 s); found that Lean 4.34 disables incremental reuse inside `\| _ h IH =>` induction alternatives (named alternatives fix it: 70 s → 10.5 s) |
| shorter goal printing | `Tools/CompactGoals.lean` (WP programs print their next 4 statements; byte strings as `go!"items"`) + `ide` text rules (cut IH/HΦ, `--diff`) | 31 real goals: 238k → 86k characters (52k with `--diff`); errors 79k → 18k; every compact goal still showed what the next tactic needed |
| list lemma library + automation | `list_seg`, `sorted_seg` (`BtreeLib/ListAuto.lean`); `LEMMAS.md`, an index of 572 lemmas | closes 748 of 803 (93%) pure side goals harvested from the proofs; proves 68 of 175 pure library lemmas by itself |
| tactic gaps, bounds, framing | `GroveTactics.lean`: `wp_bounds`, `wp_load_frac`/`wp_auto_frac` (fractional field loads), `wp_run`, `wp_ptr_method`, `inorm`/`iframe_norm` | replaced 109 occurrences in existing proofs, 107 still compile |

The agents' brief section for the tools is `etc/agent-tools/TOOLS.md`; the baseline
condition had only the plain whole-file checker (`check-baseline`) and the same brief
otherwise.

A bug the experiment found: two treatment agents hit "(kernel) application type
mismatch" errors on proofs that the language server had accepted. Root cause: Perennial's
`word` keeps a global cache of proofs keyed by the *name* of `omega`'s auxiliary lemmas
(`_proof_1_N`), which a long-running server reuses for different goals after an edit, so
a stale proof is replayed (`Perennial/Std/Word/Cache.lean`). Batch checking (a fresh
process per check) never sees it. Fixed in the toolkit by `Tools/WordGuard.lean`
(re-checks a cached proof's type, clears the cache and retries); the proper fix belongs in
Perennial's cache (record the lemma's type, or re-check on lookup). The runs used the
toolkit before this fix.

## 3. Results

Fresh agents (Claude, same model and the same brief for both conditions), two runs per
challenge and condition, all started together on one machine (so the load was shared).
Means of the two runs:

| challenge | condition | solved | wall min | compiler wait min | checks | model turns | input tokens (M, incl. cache) | input cost (k output-equiv.) | proof lines |
|---|---|---|---|---|---|---|---|---|---|
| items.insertAt | baseline | 2/2 | 2.5 | 0.8 | 13.0 | 22 | 1.23 | 37 | 58 |
| items.insertAt | tools | 2/2 | 3.3 | 1.4 | 18.0 | 25 | 1.45 | 41 | 68 |
| items.find | baseline | 2/2 | 3.8 | 1.1 | 16.5 | 30 | 2.02 | 58 | 170 |
| items.find | tools | 2/2 | 2.9 | 0.5 | 17.0 | 26 | 1.65 | 49 | 142 |
| node.split | baseline | 2/2 | 3.4 | 1.2 | 14.0 | 26 | 2.00 | 59 | 85 |
| node.split | tools | 2/2 | 3.6 | 1.0 | 28.0 | 38 | 2.75 | 72 | 92 |
| node.get | baseline | 2/2 | 3.8 | 1.1 | 18.0 | 29 | 2.18 | 62 | 172 |
| node.get | tools | 2/2 | 2.8 | 0.4 | 22.5 | 32 | 2.30 | 63 | 143 |
| node.insert | baseline | 2/2 | 16.9 | 6.2 | 39.5 | 52 | 7.51 | 193 | 508 |
| node.insert | tools | 2/2 | 14.1 | 3.6 | 58.5 | 78 | 10.33 | 245 | 449 |

Totals over the 20 runs:

| | wall min | compiler wait min | checks | model turns | input tokens (M) | input cost (k output-equiv.) |
|---|---|---|---|---|---|---|
| baseline | 61 | 20.6 | 202 | 318 | 29.9 | 817 |
| tools | 54 | 13.7 | 288 | 399 | 37.0 | 941 |
| **tools / baseline** | **0.88** | **0.67** | **1.43** | **1.25** | **1.24** | **1.15** |

Definitions: *wall* from the agent's first to last message; *compiler wait* the summed
duration of all `check`/`ide` calls; *checks* their number; *input tokens* summed over all
model turns (each turn re-reads the context; mostly cache reads); *input cost* weights
cache reads 0.02, cache writes 0.25, fresh input 0.2 (relative to an output token); proof
lines the length of the finished file minus the stub. (The transcripts' output-token
counts were too incomplete to use; output is a small share of the cost in any case.)

## 4. Reading the results

- **The tools made agents faster where waiting mattered.** On `node.insert` (whole-file
  checks of a growing ~450-line proof) compiler wait fell from 6.2 to 3.6 minutes and
  wall time from 16.9 to 14.1; on `items.find` and `node.get` wall time fell by ~25% and
  compiler wait by ~60%. On the smallest proofs (`items.insertAt`, `node.split`) a
  whole-file check takes ~5 s and there is nothing to save.
- **But cheap checks are used more**, and every check is a model turn that re-reads the
  context: +43% checks and +25% turns overall, so cumulative input tokens grew (+24%;
  +38% on `node.insert`, +37% on `node.split`). Only `items.find` was cheaper in tokens.
  Agents with `ide upto` check after almost every few lines; with a 5–60 s whole-file
  check they batch more.
- **Proofs were somewhat shorter with the tools** on the bigger challenges (−12% to −17%
  lines on `items.find`, `node.get`, `node.insert`), from `list_seg`/`wp_bounds` replacing
  hand-written side conditions.
- **Correctness was never the bottleneck here**: every run of both conditions solved its
  challenge on the first attempt. The cost in these runs is iteration, not failure.
- **Noise**: two runs per cell; per-run differences within a cell were up to ±20%.

## 5. Recommendations

1. Keep `ide` (incremental checking, goal at a point, compact goals): the wall-time and
   compiler-wait savings are real on medium and large proofs.
2. To also save tokens, pair it with guidance that limits iteration (e.g. "write a whole
   branch, then `ide upto`; use `ide steps` once instead of repeated `upto`s"), or make a
   check cost less context (the compact output already helps).
3. Fix Perennial's `word` cache (record the auxiliary lemma's type or re-check on hit):
   any long-running Lean session (an IDE, a REPL, `ide`) can replay stale proofs.
4. Name induction alternatives (`| ind h IH =>`) in long recursive proofs so Lean's
   incremental elaboration works (`node__iterate`, `node__get` use `| _ h IH =>`).
5. To measure the bigger savings `COST.md` predicts, rerun on harder challenges
   (`node.remove`, `node.iterate`) with stubs that also drop file-local helpers, and more
   runs per cell.

## Reproducing

`etc/agent-tools/experiment/`: `setup_exp.py`/`setup_tier2.py` build the stubbed
templates, strip the challenge-only lemmas and patch a hard-linked copy of the compiled
library; `make_runs*.py` creates the run directories with their `BRIEF.md`;
`grade.py`, `audit.py`, `collect.py`, `table.py` grade, audit and tabulate;
`results/*.json` are the per-run measurements. The scripts hard-code the experiment
directory (`/home/ubuntu/.claude/jobs/f5d25fd8/tmp/exp`) and the btree worktree's build
(Perennial `copy-memmove` at `62066f0`); adjust the paths at the top of each script.
`tools-src/build.sh` compiles the tool modules (`OUT=` sets the output directory).
