# Track: shorter goal printing

Goals and error messages that show what an agent needs to pick the next tactic, at about
a third of the size (a fifth with `--diff`). Nothing the next step needs is dropped; what is
cut is the rest of the program, big loop postconditions and long wand/spec hypotheses
(IH, HΦ), and each of these can be printed in full again.

## What it is

1. **`Tools/CompactGoals.lean`** (Lean side, compiled to `build/Tools/CompactGoals.olean`;
   display only, so proofs are unaffected). Importing it turns on delaborators that apply
   to goals *and* error messages:
   - `goose.pp.goStrings`: byte-list literals `[105#8, 116#8, 101#8, 109#8, 115#8]` print as
     `go!"items"`. This is exact and can be pasted back: `n.[node V, go!"items"]`,
     `methods (node.ty T).PointerType go!"get"`.
   - `goose.pp.compactWP`: `WP e {{ Φ }}` shows the next 4 statements of `e` (`.stmts`) in
     evaluation order, then `…`. `if:` branches, loop bodies and closures show 1
     statement (`.inner`), and nesting deeper than 2 (`.depth`) is `…`. The same cut
     applies to a bare program in `wp_apply: cannot apply … in evaluation position of
     <program>`.
   - `goose.pp.compactWP.post`: a big postcondition `forPostcondition s E body inv` (inside
     loops) prints as `forPostcondition …`.
   - `goose.pp.lets`: unfolded `Let`/`Lam`/`Seq` print as `let:`/`λ:`/`;;`.
   - `…` (not Lean's `⋯`) marks what the module cut. `set_option goose.pp.compactWP false`
     (or `… in <tactic>`) prints the full program.
2. **`./ide` (text side) improvements:**
   - It adds `import Tools.CompactGoals ` in front of the first `import` of the text it
     sends to the server. This is on the same line, so line numbers do not change, and
     the file on disk is untouched. `IDE_LEAN_COMPACT=0` turns it off.
   - Wand/spec hypotheses (those mentioning `-∗` or `WP`: IH, HΦ, closing wands) longer
     than 10 lines are cut to their first 6 lines, which show the binders. Pure facts and
     resources are never cut. (An earlier version also cut pure facts and hid the RHS of
     an equation; that was fixed.)
   - The 14-line program cut is skipped when the Lean side has already cut the program
     (the old cut could split the head statement).
   - The middle-of-message cut was raised from 120 to 160 lines. It is only a fallback.
   - `--diff`: hypotheses unchanged since the previous `./ide goal` on that file are
     listed by name only.
   - `./check F | ./ide compact` applies the same filter to any Lean output.
3. `./check` and `./leanc` (lean with these paths) now have `build/` on `LEAN_PATH`.
   `eval_goals.py` and `eval_errors.py` are the measurement scripts. `ide.orig` is the
   original `./ide`, kept as the baseline.

## Usage (paste into an agent brief)

```
Goals print compactly: `./ide goal FILE LINE` shows the program in WP only up to its next
few statements (`…` = the rest; the redex that runs first is always shown), struct fields
and methods as go!"name" (valid input: `n.[node V, go!"items"]`), and long IH/HΦ
hypotheses cut to their binders.
- `./ide goal FILE LINE --diff`: list hypotheses unchanged since your previous `./ide goal`
  on FILE by name only (use it for successive steps).
- `./ide goal FILE LINE --full`: no text-side cuts (whole IH/HΦ).
- Need the whole program? Write `set_option goose.pp.compactWP false in <tactic>`.
- For whole-file checks: put `import Tools.CompactGoals` at the top of the proof file
  (`./check` then prints compact errors), or pipe: `./check FILE | ./ide compact`.
```

## Validation

**Goal sizes.** 31 proof states, measured by `python3 -I eval_goals.py`: after `wp_start`,
before allocs, method calls, `wp_apply` of callee specs and of the IH, `wp_if_destruct`,
`wp_for`, inside a loop body, at `iapply HΦ`, and side goals. They come from `node__get`,
`items__truncate`, `node__insert`, `BTreeG__ReplaceOrInsert` and `node__iterate`.

| printing | chars | ≈ tokens (chars/3.5) | vs full |
|---|---|---|---|
| full (what `./check` showed agents) | 238,045 | 68,013 | 1.00 |
| original `./ide` compaction | 103,920 | 29,691 | 0.44 |
| new `./ide` text rules only | 89,972 | 25,706 | 0.38 |
| `Tools.CompactGoals` only | 114,243 | 32,641 | 0.48 |
| both (`./ide` default now) | 85,810 | 24,517 | **0.36** |
| both + `--diff` against the previous position | 52,206 | 14,916 | **0.22** |

- The `WP` part shrinks from 137k to 15k characters.
- What is left is mostly the Lean context: pure facts, all kept on purpose.
- The biggest single goal (`BTreeG__ReplaceOrInsert` after `wp_start`) goes from 21.5k to
  2.0k.

**Errors.** `python3 -I eval_errors.py` makes 11 typical mistakes, each one edit to an
existing proof: a missing `wp_auto`/`wp_pures`, a spec applied too early, a spec with the
wrong type, a failed `iframe`, `done` to see the goal, a missing bounds `rw`, a missing
frame hypothesis.

| | full | orig `./ide` | both (now) |
|---|---|---|---|
| total chars | 78,672 (1.00) | 23,780 (0.30) | 17,770 (0.23) |

- `wp_apply` "cannot apply … in evaluation position of <program>": 3.2k → 0.7k. The
  message still shows the mismatch, for example `methods (items.ty T) go!"find" #isl` in
  the spec vs `methods (items.ty T).PointerType go!"find" #n.[node V, go!"items"]` in the
  program, which calls for `wp_method_call` plus a load.
- A missing `wp_auto` in ReplaceOrInsert: 43k → 5k.
- The short messages (type mismatches, `iframe` leftovers, unsolved side goals) are
  unchanged: ~100–250 chars.

**Next tactic visible.** I checked all 31 by inspection (`scratch/show.py both`): in every
one, the compact goal still determines the next tactic of the existing proof. Examples:

| Shown at the head of the program | Next tactic |
|---|---|
| `GoAlloc` | `wp_alloc_anon` |
| `MethodResolve … go!"find"` | `wp_method_call` |
| `#(methods (items.ty T) go!"find" #isl) …` | `wp_apply wp_find` |
| `if: #found` | `wp_if_destruct` |
| `doFor` | `wp_for` |
| `![T] #(sliceIndexRef …)` | `wp_load_slice_index` |
| `(#less #item) #e.fst` | `wp_apply Hless` |
| `return:` / a value | `iapply HΦ` |

The resources needed for `iframe`/`$$ [...]` are always printed whole.

Where the compact goal hides something:
- When an `if:` condition is not the head, its call can be cut (`if: "$sw" =⟨go.bool⟩ (let:
  "$a0" := ![T] #item_ptr in …)`). It is printed once it becomes the head.
- A deeply nested head statement (a call setup made of several `let: "$aN"` lets) can be
  cut after its first lets, because those lets use up the 4-statement budget. Running
  `wp_auto`/`wp_pures` uncovers it, or `.stmts` can be raised.
- In an IH/HΦ cut to its first 6 lines, the agent must use `--full`, or read the
  spec file, to see the postcondition.

**Proofs unaffected; no cost.** `node__get`, `node__insert` and `BTreeG__ReplaceOrInsert`
compile with the import, with the same times (5.3/17.5/13.7 s with and without it).
`set_option goose.pp.compactWP false in done` prints the full program. Goal queries
through `./ide` cost the same, apart from re-loading the imports once per file.
