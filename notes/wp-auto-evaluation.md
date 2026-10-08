# Do AI-written proofs still benefit from `wp_auto`?

*An experiment on etcd-grove's Lean raft proofs, 2026-10-08. Branch `no-wp-auto`
(based on `lean` at `5fd006691`).*

**Short answer: keep `wp_auto`, but make it explain itself.** Removing it entirely
works — every raft proof on this branch spells out every symbolic-execution step and
the build passes with `wp_auto` disabled — but the explicit proofs are 12% larger,
build 7–8% slower (39% longer wall time, through the critical-path module), and are
harder to write and maintain where control flow branches. The token cost of
`wp_auto`'s unpredictability, measured in our agent transcripts, is small (about
1.5% of proof-writing output tokens for clear-cut cases, 5–10% counted
generously), and a cost model fitted to the transcripts puts the difference between
the two styles at about ±10% of total proof cost either way. The cheapest option the
model finds is in between: a `wp_auto?` that prints the manual steps it took, and
`wp_auto` reporting where and why it stopped.

Companion notes: [`wp-auto-transcripts.md`](wp-auto-transcripts.md) (the transcript
analysis) and [`wp-auto-tradeoff.md`](wp-auto-tradeoff.md) (the cost model of verbose
vs automated proofs).

## 1. What `wp_auto` is

Perennial's `wp_auto` symbolically executes straight-line Go code: it repeatedly takes
pure steps, loads, stores and allocations of local variables, steps into the
postcondition when the expression becomes a value, unfolds blocking constants, and at
the end clears the points-to facts of dead locals. It also runs **implicitly** at the
end of `wp_apply`, `wp_if_destruct`, `wp_for`, `wp_for_post` and `wp_join … as`.
Its stopping point (a call, an `if:` on an undecided condition, a loop, an anonymous
allocation, a sealed field access) is not visible in the proof text, which is the
"unpredictability" in question.

## 2. The experiment

1. **Disable it.** `EtcdGrove/NoWpAuto.lean` (imported by every proof through
   `Raft/Base.lean`) makes an explicit `wp_auto` an error and the implicit one a no-op
   (so `wp_apply` behaves like `wp_apply +noauto`). `etc/check-no-wp-auto.sh` checks
   that no proof mentions `wp_auto`.
2. **Trace what it did.** `etc/no-wp-auto/NoWpAutoTrace.lean` replaces `wp_auto` by a
   tracer: at every run (explicit or implicit) it runs the real `wp_auto` to get the
   resulting goal, then greedily reaches the *same* goal with user-level tactics only
   (`wp_pures`, `wp_load`, `wp_store`, `wp_alloc x_ptr as x`, `wp_call`,
   `wp_func_lits`, `unfold`, and `iclear` for the dead points-to facts), and records the
   sequence with the source position. Of **3,380** runs over the whole development,
   **2,873** were reproduced exactly, **481** made no progress (implicit runs with
   nothing to do), and **26** had no manual equivalent at first; after two tracer fixes
   about **20** remained, nearly all because `wp_auto` had cleared the points-to of a
   dead local shadowed by a newer one of the same name — something a manual `iclear`
   cannot name.
3. **Splice it in.** `etc/no-wp-auto/rewrite.py` replaced each explicit `wp_auto` by its
   sequence and inserted the implicit runs' sequences after the tactic (premise bullets
   skipped, `wp_if_destruct` branches placed into their bullets, or with
   `rotate_left … rotate_right`). ~1,800 sites were placed automatically; ~180 got a
   `TODO(no-wp-auto)` comment carrying the traced sequences (`wp_join`, macros, several
   runs on one line, mismatches).
4. **Repair by hand (by agents).** Six Claude agents fixed the 79 files that still
   failed, with the TODO hints and the rule "no new automation" (no
   `repeat (first | wp_pures | wp_load …)`). The shared `wp_raft_log` macro got a fixed
   body.

Result: `lake build` passes with `wp_auto` disabled; no theorem statement or spec
changed; the trust base is unchanged (`etc/tcb-report.py --check`: 10 axioms, 0
`sorry`s).

## 3. Results

### Proof size (225 proof files)

| | with `wp_auto` | manual | change |
|---|---|---|---|
| lines | 26,609 | 28,586 | +7% |
| bytes | 1.05 MB | 1.18 MB | +12% (≈ +35k tokens over the tree) |
| `wp_auto` | 1,012 | 0 | |
| `wp_pures` | 2 | 6,023 | |
| `wp_load` | 0 | 3,226 | |
| `wp_store` | 0 | 531 | |
| `wp_alloc` | 5 | 795 | |
| `iclear` | 10 | 697 | |

Lines grow little because the steps sit on one line (`wp_pures; wp_load; wp_pures`):
an explicit `wp_auto` became ~6 steps on average, a `wp_apply`'s implicit run ~2–3
(usually `wp_pures` or `wp_pures; wp_load; wp_pures`). About 11,300 explicit steps
replace 1,012 explicit and ~2,400 implicit automation runs.

### Build time (full rebuild of EtcdGrove, same machine, back to back)

| | with `wp_auto` | manual | ratio |
|---|---|---|---|
| CPU, the 225 proof modules | 31.6 min | 34.0 min | 1.08× |
| CPU, all 427 modules | 41.1 min | 43.8 min | 1.07× |
| wall time (24 cores) | 3m23s | 4m43s | 1.39× |

The median proof module changes by 1.03×; the largest, `stepLeader` (the critical path),
by 1.34× (205 s → 276 s), hence the wall time. `wp_auto` is engineered for this (one
pass with shared substitution proofs); a sequence of separate tactics re-traverses the
goal at each step. (Other jobs were running on the machine; treat ±5% as noise.)

### What the repair cost

| | |
|---|---|
| files repaired | 79 (of 225), ~14k lines |
| agent tokens (as reported by the harness) | 1.08M in total, ~13.6k per file |
| checks (`lake env lean`) | ~280, ~3.6 per file (median 3; max 23, `RawNode__Ready`) |

This is the cost of *finishing* a mechanically derived conversion, with the traced
sequences given as hints — not of writing manual proofs from scratch. What the agents
reported as hard (consistently, across all six):

- **Branches.** `wp_auto` lets one tactic cover goals that need different step counts
  (`cases b <;> wp_auto`, `repeat (rw [h]; wp_auto)`, `wp_if_destruct` followed by a
  shared tail). Explicit steps force per-branch structure (`case'`,
  `rotate_left … rotate_right`, `focus`), and step counts per branch had to be found by
  probing (7 checks for `MsgStorageAppendResp`). `canVote`'s `||`/`&&` tree, a generic
  `repeat (any_goals cv_step)` before, became a hand-written case tree.
- **Evaluation order.** Spelled-out steps must match Goose's order exactly: `&&` as
  nested `if`s, right-to-left argument evaluation, an address load before a field-lemma
  load, a `wp_pures` between loads that look adjacent. Wrong guesses needed goal
  inspections of 100-line GooseLang terms.
- **Shadowed locals.** Inlined method calls and repeated range loops re-allocate
  `r`, `rn`, `id`, `i`; the manual proof has to rename (`wp_alloc r_ptr as r2`) or
  clear by hand. (The transcripts show the same hazard *with* `wp_auto`, example 8 in
  `wp-auto-transcripts.md`.)
- **Shared macros become brittle.** `wp_raft_log` (49 call sites) lost the `wp_pures`
  that `wp_apply`'s implicit `wp_auto` used to take; inside `try`s this failed silently
  and surfaced one step later in every caller. All six agents rediscovered it.
- **Upside.** A wrong step count fails *at that step* with a precise message ("could
  not find an allocation", "cannot apply …"), whereas a `wp_auto` that stopped early
  fails somewhere later; and straight-line code with a trace was trivial.

The agents' summary, roughly: *workable to maintain with traces, noticeably more
expensive to write from scratch, because the goal must be read at nearly every branch
point.*

## 4. What the transcripts say

From `upamanyus/etcd-grove-prompts` (74 Rocq and 11 Lean proof-writing transcripts;
details in [`wp-auto-transcripts.md`](wp-auto-transcripts.md)):

- Clear-cut `wp_auto` friction — "no progress" errors, a step after the automation
  already finished, `apply` errors the agent blamed on `wp_auto` — costs **~1.6%**
  (Rocq) and **~1.3%** (Lean) of proof-writing output tokens; a generous count
  (unattributed `apply` errors, remarks, goal inspections after automation at twice
  their detected cost) **~5%** / **~10%**. A typical episode is a one-line fix in 1–3
  turns (~300 tokens in Lean, ~960 in Rocq); the dominant pattern is a redundant
  `wp_auto` after a `wp_apply` that already ran it.
- Goal inspections land right after an automated WP tactic **3–5× more often than
  chance** — the direct signature of "I can't predict where it stopped".
- Only **~25%** of failed verifier rounds fail at a WP tactic at all; **~75%** fail in
  pure reasoning, Iris bookkeeping (`iframe`, `icases`), names or proof structure.

## 5. Verbose vs automated: the cost model

From [`wp-auto-tradeoff.md`](wp-auto-tradeoff.md): a verifier round costs ~8–13k
output-token equivalents, 86–89% of it re-reading context; an extra proof line costs
~25 output tokens. So *text is cheap and rounds are expensive*: verbosity only pays if
it saves rounds. With per-use failure rates of 1/14–1/16 for automated tactics, manual
proofs are cheaper only if a manual step fails less than **~1 in 35** (2.5× more
reliable); measured manual rates (1/13 to 1/100) straddle that, giving manual/automated
cost ratios of **0.94** (manual step fails 1/100), **0.98** (1/43) and **1.14** (1/15).
Two middle-ground options come out best:

- a **`wp_auto?`** that prints (or splices in) the manual steps it took — the tracer
  built for this experiment is a prototype — ratio **0.91**;
- **`wp_auto` reporting where and why it stopped** (the remaining expression and the
  blocking step), which makes WP repairs cheap and removes most goal inspections.

## 6. Recommendation

1. **Keep `wp_auto` on `lean`.** The benefit of removing it is within ±10% of proof
   cost on the transcript evidence, while the measured costs of removal are real: +12%
   proof text, +7–8% CPU, longer critical path, and harder branching code.
2. **Make it predictable instead:**
   - `wp_auto?` (from `etc/no-wp-auto/NoWpAutoTrace.lean`: run `wp_auto`, find the
     equivalent manual steps, print them as a "Try this" suggestion);
   - on stopping, report the head of the remaining expression and why no step applies
     (a call, an undecided `if:`, a sealed field, an anonymous allocation);
   - a softer "no progress" (warning, or success) for the implicit-run case, which is
     the largest single error class in the transcripts.
3. **Spend effort on the 75%**: the non-WP failure classes (unsolved pure goals,
   `iframe`/`icases` mismatches, names) cost more than `wp_auto` does.

## 7. Caveats

- The repair cost measures finishing a traced conversion, not writing manual proofs
  from scratch; a controlled experiment (the same functions proved twice by fresh
  agents) would settle the from-scratch question.
- The Lean transcripts are one session on another project (the bootstrap-go checker);
  manual steps are rare in them, so the manual failure rate is poorly determined.
- Build times were taken on a shared machine.
- The manual proofs are tied to the exact Goose translation: a re-translation that
  adds or removes a `let:` changes step lists that `wp_auto` absorbed.

## Reproducing

- Tracer and splicer: `etc/no-wp-auto/NoWpAutoTrace.lean`, `etc/no-wp-auto/rewrite.py`.
  To trace, import the tracer module from `Raft/Base.lean` (instead of `NoWpAuto`) on
  `5fd006691` and build with `WP_AUTO_TRACE_DIR=<dir> lake build`; then
  `rewrite.py <dir> <worktree>`.
- Check: `etc/check-no-wp-auto.sh`; build: `lake build`;
  timing: `etc/build-report.py build` on `5fd006691` and on this branch.
