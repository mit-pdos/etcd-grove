# Track: interactive, incremental checking (`./ide`)

## What it is

`./ide` is a client for a persistent `lean --server` (one daemon per directory, started on
first use). The main additions over the first version:

- **`ide upto FILE LINE`: check a prefix.** The tool builds a cut copy of FILE in memory (an
  LSP document `FILE.upto.lean`; nothing is written to disk). The copy keeps lines 1..end of the
  tactic on LINE. Every enclosing block is then closed by `all_goals sorry` at its indentation,
  and later declarations are dropped. The copy stays open in the server, so each call
  re-elaborates only from the first changed line up to LINE. It prints the errors in lines 1..LINE
  and the goal after LINE. Two speedups apply to the copy only:
  `set_option debug.skipKernelTC true in` (the kernel check of the partial proof term is about 1 s
  per call even for `node__get`), and returning as soon as only the declaration's final phase is
  left (instantiating the term and adding it to the environment, about 2 s in `node__iterate`),
  because that phase cannot produce tactic errors.
- **`ide steps FILE FROM [TO]`: per-tactic feedback.** It prints the full state before FROM. For
  each tactic it then prints a diff against the most similar goal seen so far: `+`/`~`/`-`
  Lean and Iris hypotheses, and the new conclusion only if it changed, with the program cut to
  its first lines. It stops at the first tactic with an error and prints that error.
- **The cause of the missing reuse, and a fix.** Lean 4.34 does reuse tactic snapshots
  incrementally, but `Lean/Elab/Tactic/Induction.lean:552` turns reuse off inside a **wildcard
  alternative** `induction h using Nat.strongRecOn ... with | _ h IH =>`. Both `node__iterate` and
  `node__get` put their whole proof in such an alternative, so every edit re-elaborated the whole
  theorem. `set_option ... in`, macros, `·`, `focus`, `case` and the Perennial/Iris tactics do
  not break reuse (checked with `set_option trace.Elab.reuse true`). Naming the alternative
  (`| ind h IH =>`) fixes it. `ide upto` does the renaming in its copy by itself: it probes once
  with a wrong name and reads the expected name from Lean's error. `ide check` prints a hint
  with that name.
- **Robustness.** A dead server is detected and restarted (tested by killing it). This matters:
  another track's `pkill -f "lean --server"` hung the first version forever. A crashed file
  worker is reopened. `--timeout S` returns partial messages and says roughly how far
  elaboration got, and the server keeps working, so a rerun picks up where it left off. If a
  module in `./build` is recompiled, the documents are reopened. `ide restart [FILE]` does this by
  hand. Every call ends with an `-- elaborated in Xs` or `-- NOT finished` line. Exit codes:
  0 ok, 1 errors, 2 usage, 3 tool failure, 4 timeout.

## Usage (for an agent brief)

```
./ide upto FILE LINE      # check FILE only up to the tactic on LINE; prints errors up to LINE and the
                          # goal after it. Re-checks only what changed since your last call (≈1-4 s),
                          # whatever the size of the proof. Use it after every edit, at the line you edited
                          # or the last line you wrote. No need to end with `done`/`sorry` to see a goal.
./ide steps FILE A [B]    # per-tactic: the state before line A, then what each tactic on lines A..B
                          # changed (+/~/- hypotheses, new conclusion); stops at the first error.
./ide check FILE          # the whole file (do this once a branch is done, and at the end; authoritative,
                          # includes the kernel check). Prefer `./check FILE` only for the final run.
./ide goal FILE LINE [--after]   # state before/after LINE in the whole-file document
--full: print goals/messages uncut;  --timeout S: return after S seconds with partial results.
Write `induction ... with | ind h IH =>` (a named alternative), not `| _ h IH =>`: with `_`, Lean
re-checks the whole alternative after any edit inside it.
```

## Validation

Machine: 24 cores, shared with the other tracks (load 5–10), so the numbers are noisy (±30%).
The edit inserts `skip` before the given tactic line. "upto after edit" means: the cut copy was
warm at the end of the proof, then the file was edited and `ide upto L+1` was run. The scripts
are `exp/editbench.py` and `exp/t.py`, and the raw output is in `exp/*.out`.

| proof (lines) | `./check` cold | `ide check` after edit near start / middle / end | `ide upto` after edit near start / middle / end | `ide goal`, warm |
|---|---|---|---|---|
| items__truncate (66) | 4.7 s | 2.4 / 1.9 / 0.6 s | 0.5 / 0.4 / 0.4 s | 0.2–0.3 s |
| node__get (128, `\| _`) | 5.2 s | 3.7 / 3.3 / 3.2 s | 0.6 / 0.8 / 0.5 s | 0.3–0.4 s |
| node__insert (356, `\| ind`) | 18.3 s | 15.7 / 19.4 / 7.8 s | 1.0 / 2.7 / 4.2 s | 0.7–1.3 s |
| node__iterate (875, `\| _`) | 59 s | 60 / 63 / 70 s | 1.9 / 2.4 / 4.5 s | 0.5–1.4 s |
| node__iterate, renamed `\| ind` | — | — / 37 / **10.5 s** | 2.0 / 3.9 s | 0.6 s |

- Writing a proof in order (move the cut forward by a few tactics and call `upto`): measured
  0.6–1.3 s per step on `node__get` and 0.8–4 s on `node__iterate`. It costs the new tactics plus
  re-running the last tactic of the previous version, about 0.5 s of fixed overhead, and
  occasionally 2–6 s when a slow `word`/`simp` is re-run. Jumping 400 lines forward costs what
  those lines cost (about 25 s in iterate).
- Goal output size is unchanged: 1.2–5.7 k characters per goal with the existing compaction.
  `steps` on 15 tactics of `node__get` gave 7.2 k characters, where 15 separate goal prints would
  give about 50 k. Most steps print 1–3 lines (`+ hb : …`, `⊢ (conclusion unchanged)`).
- Checked by hand: cut points inside a `have … := by` block, on continuation lines (they are
  mapped to the start of the tactic; the report gives the span), on `· tac` bullets, and on
  `cases … with | …` alternatives. A failing tactic is reported by both `upto` and `steps`. The
  server was killed and restarted. Timeout reports were checked.

## Limitations

- The cut is based on indentation heuristics: a tactic's continuation lines are the deeper
  lines after a line that does not open a block (`by`, `=>`, `with`, `·`, `focus`, `case`, …). An
  unusual layout can produce a cut copy that does not parse, and then the parse error is
  reported. `upto` on a `with` line takes all of its alternatives.
- `upto` skips the kernel check and the final phase of the declaration, so a final
  `./ide check` or `./check` is still needed. It does not see errors that only appear when the
  declaration is complete (unsolved goals in later branches, kernel errors).
- After an error, Lean's error recovery means the state shown after it may be one where the
  failing `have` was admitted.
- `ide check` on the original file is only incremental if the proof avoids `| _` alternatives;
  the tool cannot change the user's file. Editing early in a long proof still re-checks
  everything after the edit; that is why `upto` is the command to use.
- Each document (the file, and its cut copy) has its own Lean worker with the imports loaded,
  roughly 1–2 GB each.

## Estimate for a fresh agent

In the btree effort about 40–47% of wall time was spent waiting on whole-file checks (about
60 s for `node__iterate`-sized files), and about 130 checks ended with `done` only to see a goal.
With `upto`/`steps` a check while writing a proof costs about 1–4 s instead of 5–60 s, and
showing a goal needs no failing build. For proofs of 100–900 lines that is a 5–30× reduction in
compile wait per iteration. I expect it to cut total wall time by roughly 30–40% for the larger
proofs and less for the small ones. It should also save some of the tokens spent on full
`unsolved goals` dumps, because `steps` prints diffs. The remaining costs are the final
authoritative check and thinking time.
