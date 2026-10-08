# `wp_auto` in the agent transcripts (etcd-grove-prompts, synced 2026-10-07)

An analysis of the Claude Code transcripts in `upamanyus/etcd-grove-prompts`
(60 top-level sessions plus their subagents), made for the `no-wp-auto` experiment
(see `notes/wp-auto-evaluation.md`). The scripts were run in a scratch directory and
are not checked in; the method is below so the numbers can be redone.

## Method

- Each API message id is counted once: resumed sessions and forked subagents repeat
  earlier messages (without dedup the Lean totals are ~20% too high).
- A transcript's era is whichever of `.v`/`.lean` it edits more; it is "proof-writing"
  if it has at least 3 proof-file edits and 2 builds.
- An error episode starts at a build/check result with one of these errors and runs
  over the following assistant turns until a check no longer shows it (cap 12 turns;
  overlapping episodes merged). Cost: sum of output tokens (and, separately, input
  tokens incl. cache reads) over the episode's turns.
  - *noprog*: Rocq `Failed to progress.` / Lean `wp_auto: no progress` (120 of the 124
    Rocq occurrences with a location point at a 7-character span: `wp_auto`).
  - *overrun*: `<tactic>: the goal Φ … is not a GooseLang WP` (a step after the
    automation had already finished the code).
  - *apply*: `iApply`/`wp_apply: cannot apply` (ambiguous: `wp_auto` stopped
    somewhere unexpected, or the spec is wrong).
  - *manual*: `wp_load`/`wp_bind`/`wp_pure … could not find`.
  - *remark*: the agent's own text says `wp_auto` stopped/parked/already ran (noisy;
    capped at 3 turns).
- Goal inspections: tool inputs inserting `Show.`/`trace_state`/`goal.sh` whose result
  shows a goal; the tactic just before the probe is read from the preceding text.

## Corpus

| | Rocq proof | Rocq other | Lean proof | no proof edits |
|---|---|---|---|---|
| top-level sessions | 23 | 8 | 1 | 28 |
| subagents | 51 | 16 | 10 | 26 |

Rocq proof-writing: 14.9M output, 5.72B input tokens. Lean proof-writing: 1.15M
output, 352M input. The Lean sample is one session (2026-10-07) and its subagents,
porting the bootstrap-go checker proofs (same Perennial-Lean `wp_auto`), not raft.

## Error episodes (share of the proof-writing totals)

| era | kind | episodes | turns | output tok | % output | % input |
|---|---|---|---|---|---|---|
| Rocq | noprog | 126 | 590 | 216k | 1.45% | 1.74% |
| Rocq | overrun | 4 | 14 | 9.5k | 0.06% | 0.04% |
| Rocq | remark (noisy) | 34 | 90 | 60k | 0.40% | 0.33% |
| Rocq | apply, `wp_auto` named by the agent | 8 | 57 | 21k | 0.14% | 0.18% |
| Rocq | apply, unattributed | 83 | 416 | 195k | 1.31% | 1.30% |
| Rocq | manual-step errors | 9 | 29 | 10k | 0.06% | 0.13% |
| Lean | noprog | 30 | 38 | 10k | 0.87% | 2.74% |
| Lean | overrun | 10 | 16 | 5k | 0.44% | 1.03% |
| Lean | remark | 5 | 6 | 6.6k | 0.58% | 0.45% |
| Lean | apply, unattributed | 30 | 78 | 42k | 3.64% | 3.56% |
| Lean | manual-step errors | 2 | 4 | 1k | 0.08% | 0.23% |

A noprog episode is cheap: Rocq median 3 turns / ~960 output tokens (15 of 126 hit
the cap, mostly batch builds); Lean median 1 turn / ~300 tokens. The fix is nearly
always one line (delete the `wp_auto`, make it `try wp_auto`). Agents hedge:
13% of the `wp_auto`s they wrote are `try wp_auto` (496/3,679 Rocq, 76/641 Lean);
`--no-auto`/`+noauto` was used once.

## Goal inspections

- 42% (Rocq) / 49% (Lean) of probes come right after an automated WP tactic
  (`wp_auto`, `wp_apply`), 1.9% / 1.5% after a manual WP step. Automated WP tactics are
  13.7% / 15.1% of the tactics written, so probes land after automation 3–5× more often
  than chance: the proxy for "I can't predict where it stopped".
- 339 Rocq / 43 Lean probes whose result shows the goal were found (others went to
  files); ~55% / 81% of them showed a WP goal ("where did the program get to?").
- Inspections after automation cost 133k output tokens in Rocq (0.9%) and 31k in Lean
  (2.7%), probe turn plus reading turn; detection undercounts (maybe ×2).

## Performance (Rocq)

One session (395k output tokens, ~2.6% of Rocq proof output) was spent on WP-tactic
speed: 106 s in `wp_auto`'s Ltac2 walker, 74 s in 16,500 `PureWp` probes, 25 s in
failing `iClear`s; `Step` went from 45 to 9.5 minutes. Afterwards `wp_auto` (incl. the
one in `wp_apply`) was ~55% of `MsgVote`'s check time, ~100 ms per pure step over ~400
steps.

## Examples

1. "`wp_apply … as` already runs `wp_auto`, so the trailing one fails" — deleted,
   ~1k tokens, 6 turns (the most common pattern, Rocq and Lean).
2. "A `wp_auto` failed to progress, but my filter hid which line" … "`wp_apply` probably
   already stepped past it. Making those `try wp_auto`." ~0.9k tokens.
3. "`do:` is a sealed function … `wp_auto` doesn't look inside" → manual `wp_bind`
   ("could not find pattern") → "`wp_auto` already stepped past the `let`". Four chained
   episodes, ~4.4k tokens: manual stepping failed too.
4. A blocker recorded as "`wp_auto` fails to step a composite literal"; a later agent
   found the goal "parked at `@!raft.voteRespMsgType`": a missing callee spec.
   Misdiagnosis cost spread over a 322k-token agent.
5. "`wp_auto` can't step `if: ~accepted` for an opaque boolean" — really a missing spec
   premise (a proof obligation surfacing as `wp_auto` stopping), ~4.9k tokens.
6. Lean: "No `wp_auto` after `wp_apply … as`: the call already runs it" — ~300 tokens
   each, 30 such episodes.
7. Lean: `wp_auto: the goal Φ (#s, #null) is not a GooseLang WP` — deleted, 317 tokens.
8. Lean: "`wp_auto` … allocates both the Go counter `i` and the range loop's index `i`,
   which makes the Go counter's names inaccessible" — renamed the counter, ~1k tokens
   (a silent naming hazard).
9. Lean: "`wp_auto` stops before `&T{…}` … Use `wp_pures; wp_load; …; wp_alloc`"; on a
   persistent points-to its access search "picks the store instance".
10. "`wp_auto` on a stuck expression *succeeds* without progressing", yet it fails when
    there is nothing at all to step — two behaviours easy to confuse.

## Evidence for `wp_auto`

- Volume: `Step` has ~1,300 pure steps for ~140 memory operations; on `MsgVote`, 21
  `wp_auto` calls covered ~400 pure steps.
- Manual steps fail about once per 43 uses (Rocq) / 100 (Lean), `wp_auto` once per 28 /
  16 — but per Go step covered, `wp_auto` fails far less.
- Agent-written proofs refer to 429 `x_ptr`-style names with essentially no unknown-name
  errors (exception: example 8).
- The raft field lemmas are stated at exactly the expression where `wp_auto` stops
  (179 uses).

## Caveats

Most `apply` errors cannot be attributed (subagent turns usually carry no text);
episode boundaries are heuristic; inspections are undercounted; probing after the last
symbolic-execution step is also simply how one sees what comes next; the Lean data is
one day of one task. `notes/proof-effort.md` (Rocq) attributes ~50% of effort to
"guess-and-check on what a tactic will leave behind", which is broader than `wp_auto`.

## Judgment (of the transcript analysis alone)

Clear-cut `wp_auto` friction (noprog, overrun, apply errors the agent attributed to
`wp_auto`): ~1.6% of output tokens (Rocq), ~1.3% (Lean). A generous count (adding the
unattributed apply errors, remarks, and post-automation inspections at twice their
detected cost): ~5% (Rocq), ~10% (Lean). Two patterns dominate, both learnable rules:
a redundant `wp_auto` after a tactic that already ran it, and `wp_auto` stopping at a
field access, an undecided `decide`, or a callee.
