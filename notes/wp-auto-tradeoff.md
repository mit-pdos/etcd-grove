# Verbose manual WP proofs vs `wp_auto`: a cost model from the transcripts

Question (2026-10-08): should the agent (a) spell out every symbolic-execution step
(`wp_pures; wp_load; …; iclear`) — longer, more predictable — or (b) rely on `wp_auto`
(also run implicitly by `wp_apply`, `wp_if_destruct`, `wp_for`, `wp_for_post`,
`wp_join`) — shorter, less predictable, possibly more verifier rounds?

Data: the proof-writing transcripts of `upamanyus/etcd-grove-prompts` (74 Rocq, 11
Lean; deduped by API message id), plus the measurements of this branch's conversion
(`notes/wp-auto-evaluation.md`). **All 513 Lean rounds are one session (2026-10-07,
porting the bootstrap-go checker), not the raft proofs.** See
`notes/wp-auto-transcripts.md` for the first analysis (error episodes, probes).

## Method

- *Edits*: Write/Edit/MultiEdit of `.v`/`.lean`, and Bash heredoc/`sed -i`/Python
  replace writes; lines added = multiset line diff.
- *Round*: a foreground verifier run (make, `rocq compile`, coqc, `lake build`,
  `lake env lean`, check scripts) whose targets include a file edited since its last
  verification (151 background runs dropped; 1,073 runs without pending edits not
  rounds). *Pass*: no error attributed to the target.
- *Tokens per round*: all assistant messages from the previous verifier result to this
  verifier call; output includes hidden thinking. *Cost* in output-token equivalents:
  output 1, fresh input 0.2, cache write 0.25, cache read 0.02.
- *Chain*: consecutive rounds on one file until its first clean verification (stands in
  for "proof unit").
- *First-error class*: regex on the first error (`wp_auto: no progress`,
  `cannot apply`, `wp_load: could not find`, `iframe`, unsolved goals, names …).
- Tactic counts per round only where the edit text is known (Rocq 419, Lean 382
  rounds). Automated: `wp_auto`, `wp_apply`, `wp_if_destruct`, `wp_for`, `wp_for_post`,
  `wp_join` (+ `iApply` in Rocq); manual: `wp_pures`, `wp_pure`, `wp_load`, `wp_store`,
  `wp_alloc`, `wp_bind`, `wp_call`, `iclear`.

## Measurements

### Rounds

| | Rocq | Lean |
|---|---|---|
| rounds | 900 | 513 |
| pass rate | 64% | 45% |
| output tokens / round (median / mean / p90) | 1,862 / 8,566 / 16.7k | 933 / 1,699 / 3,556 |
| input tokens / round (median / mean) | 457k / 2.7M | 348k / 484k |
| cost / round, output-equivalent (median / mean) | 12.8k / 80.6k | 8.4k / 12.6k |
| share of round cost that is output | 11% | 14% |

**A round's cost is mostly re-reading the context**, not writing: at ~350k tokens of
context each extra message costs ~7k output-equivalents before anything is written.

### Chains (rounds to the first clean check)

| | Rocq | Lean |
|---|---|---|
| chains finished / unfinished | 653 / 50 | 242 / 12 |
| rounds per chain (median / mean / p90) | 1 / 1.39 / 2 | 1 / 2.07 / 4 |
| first-try pass | 80% | 51% |
| P(pass): fresh round / repair round | 74% / 48% | 49% / 44% |
| cost per chain, output-equivalent (median / mean) | 20k / 104k | 16k / 25k |

### What fails (first error of failed rounds)

| class | Rocq (322) | Lean (280) |
|---|---|---|
| `wp_auto` no progress | 14.3% | 12.9% |
| `wp_apply`/`iApply` cannot apply | 10.6% | 7.5% |
| manual WP step | 0% | 2.1% |
| manual step after automation finished ("overrun") | 0% | 0.4% |
| **all WP tactics** | **25%** | **23%** |
| pure reasoning / typing | 18% | 39% |
| IPM structural (`iframe`, `icases`, `ipureintro`, …) | 9% | 21% |
| elaboration / syntax / names | 14% | 12.5% |
| proof structure (bullets, focus, Qed) | 13% | 1% |
| infrastructure / timeout | 3% | 0.4% |
| unclassified | 18% | 3% |

**WP stepping is not the bottleneck**: ~75% of failed rounds fail in reasoning that
neither strategy changes.

Per-use failure rates (attributed failures ÷ uses added in known-edit rounds):
automated tactic 1/16 (Rocq), 1/14 (Lean); manual step 0/49 (Rocq; 95% upper bound
≈1/16), 6/80 = 1/13 (Lean; CI ≈1/29–1/7). Manual steps are rare in the transcripts, so
their rate is poorly determined; the first analysis (larger denominators) found 1/43
(Rocq) and 1/100 (Lean). Usable range: **1/13 to 1/100**.

Pass rate by number of automated tactics in a round — Lean: 0 → 54%, 1–2 → 29%,
3–5 → 27%, 6–15 → 32%; Rocq: 0 → 60%, 1–2 → 67%, 3–5 → 51%, 6–15 → 46% (confounded: rounds
with WP code are harder anyway). Hazard fit (Lean): base pass 0.56, per-use failure 0.11
automated, 0.05 manual, 0.007 per other line.

### Writing and reading text

- Writing: Lean output ≈ 900 + 25 × (lines added) per round; Rocq ≈ 2.6k + 154 × lines
  (rounds ≤100 lines). Edit-only messages: 861 output tokens per 1,000 characters
  written, i.e. ~40% of an edit message's output is hidden thinking.
- Re-reading: the manual raft tree is ~10 lines (≈190 tokens) longer per file than the
  `wp_auto` tree; at cache-read weight that is ~4 output-equivalents per later message:
  negligible.

### Cost of a failure

From a failed round to the chain's pass: median 12.4k output-equivalents (Lean; mean 21k),
16.6k (Rocq; mean 52k). The repair round itself fails 56% (Lean) / 52% (Rocq) of the time.

## The model (one Lean function proof)

E[rounds] = N·(1 + (1−q)/r + q·(1−p_WP)/r_WP);
E[cost] = rounds·(C_r + O_b) + lines·t_l + thinking + probes·(C_r + 300);
p_WP = (1−a)^(A/N) (automated) or (1−m)^(k·A/N) (manual).

| parameter | value | source |
|---|---|---|
| A, automation runs per proof | 13 | 2,873 traced runs / 225 files (this branch) |
| k, manual steps per automation run | 4.1 | the no-wp-auto tree |
| N, fresh rounds per proof | 7 | 1.75 automated tactics per measured round |
| q, P(no non-WP error) per round | 0.555 | fresh pass 0.488 ÷ (13/14)^1.75 |
| a, automated failure per use | 1/14 | measured |
| m, manual failure per step | 1/100 … 1/15 | scenario |
| r = r_WP, P(repair passes) | 0.44 | measured |
| C_r, context cost per round | 7.4k | measured |
| O_b, other output per round | 900 | measured |
| t_l, output tokens per line | 25 | measured |
| lines per proof | 116 automated / 126 manual | this branch |
| t_m, thinking per extra manual step | 15 | **guess** |
| goal probes per proof | 1.5 automated / 0.75 manual | **guess** (probes follow automation 3–5× more than chance) |

### Scenarios (automated baseline: 140.7k output-equivalents, 15.2 rounds per proof)

| scenario | manual P(pass)/round | manual rounds | manual / automated cost |
|---|---|---|---|
| A. optimistic, m = 1/100 | 0.51 | 14.7 | **0.94** |
| B. middle, m = 1/43 | 0.46 | 15.5 | **0.98** |
| C. pessimistic, m = 1/15, t_m = 30, probes 1.25 | 0.33 | 17.7 | **1.14** |
| D. only load/store/alloc/iclear can fail (k = 1.9), m = 1/43 | 0.51 | 14.8 | 0.94 |
| E. Rocq-like (a = 1/16, q = 0.8, C_r = 10.9k), m = 1/43 | 0.67 | 11.8 | 1.01 |
| F. automation that reports where it stopped (r_WP = 0.8, probes 0.75) | — | — | 1.02 (automated drops to 130.7k) |
| G. a `wp_auto?` that splices in the manual steps (m = 1/200, t_m = 0) | 0.53 | 14.4 | 0.91 |

**Break-even**: manual is cheaper only if m < **1/35** per step (2.5× better than
automation's 1/14 per use); 1/16 if `wp_pures` never fails (~1.9 real decision points per
automation run); 1/62 if manual proofs need as many probes; 1/54 if automation fails
only 1/28 per use.

### Sensitivity (manual / automated cost)

| | m = 1/200 | 1/100 | 1/60 | 1/43 | 1/30 | 1/15 |
|---|---|---|---|---|---|---|
| base | 0.92 | 0.94 | 0.96 | 0.98 | 1.02 | 1.11 |
| t_m = 40 | 0.93 | 0.94 | 0.97 | 0.99 | 1.02 | 1.12 |
| C_r = 2k (small context) | 0.94 | 0.96 | 0.98 | 1.00 | 1.03 | 1.13 |
| a = 1/28 | 0.95 | 0.97 | 0.99 | 1.02 | 1.05 | 1.15 |
| a = 1/8 | 0.88 | 0.89 | 0.92 | 0.94 | 0.97 | 1.06 |
| k = 1.9 | 0.90 | 0.91 | 0.93 | 0.94 | 0.95 | 1.01 |
| q = 0.8 | 0.87 | 0.91 | 0.95 | 0.99 | 1.05 | 1.22 |
| equal probe counts | 0.96 | 0.98 | 1.00 | 1.03 | 1.06 | 1.16 |

## Conclusion

1. The choice is worth at most about **±10%** of proof cost: WP tactics are only about a
   quarter of failed rounds.
2. **Extra text is cheap; rounds are expensive.** A round costs 7–13k output-equivalents
   (mostly context re-reading); an extra line ~25 tokens; predicting ~40 extra steps at
   ~15 tokens each ~600 tokens (<0.5% of a proof).
3. The deciding number is **how often a manual step is wrong**: below ~1/35 per step,
   manual wins (more so if it also saves goal probes); the measured range (1/13–1/100)
   straddles that.
4. Better than either extreme: (G) a `wp_auto?` that prints/splices the manual steps
   (the agent writes the short form, keeps the explicit, replay-stable steps; ~9%
   cheaper); (F) automation that reports where and why it stopped (closes most of the
   gap by making WP repairs cheap and removing probes); optionally `wp_apply` without
   implicit automation by default (removes the "overrun" class). Effort is better spent
   on the larger non-WP failure classes: unsolved pure goals, `iframe`/`icases`
   mismatches, names.

## Caveats

Lean data is one session on another project; manual-step counts are small (49 Rocq, 80
Lean uses); error classes are regex-based (18% of Rocq failures unclassified; source
lines usable for ~20% of failures); pass rates by tactic count are confounded with
difficulty; "pass" includes proofs with `sorry`/admits; `sed` edits have unknown content;
background builds dropped; thinking per manual step and probe counts are guesses; the
model treats failures as independent and ignores that explicit proofs are more brittle
under changes to the Goose translation (every changed `let:` shifts the step list).
