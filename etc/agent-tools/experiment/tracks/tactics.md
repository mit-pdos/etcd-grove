# Track: tactic gaps, bounds side conditions, framing

## What it is

`GroveTactics.lean` (module `GroveTactics`, compiled into `build/` by `./buildmod GroveTactics.lean`;
`./check` now puts `build/` on `LEAN_PATH`). No Perennial changes: new tactics on top of
Perennial's proof-mode internals (`runTacticGooseWp`, `synthAccess`, `tac_wp_load`, …).

(It is a top-level module, not `EtcdGrove/Btree/Tactics.lean`: Lean resolves `EtcdGrove.*` to the
read-only snapshot's `EtcdGrove/` directory first, so a new module under `EtcdGrove/` is not found.)

| tactic | gap it closes |
|---|---|
| `wp_bounds` | the `rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, …⟩)]` / `have hb … := by word; simp only [hb, and_self, ↓reduceIte]` before every slice index/slicing step |
| `wp_load_frac`, `wp_auto_frac` | `wp_auto` cannot load a struct field through `l ↦{dq} v` with `dq ≠ own 1` (cause: the `Access` search runs with the fraction as a metavariable and settles on the field's `DFrac.own 1` *store* instance; `wp_load_frac` takes `dq` from the hypothesis) |
| `wp_run` | `wp_auto` + `wp_alloc_anon` (unnamed Go results) + `wp_load_frac`, until nothing applies |
| `wp_ptr_method` | value method called through a pointer: `wp_method_call; wp_call; wp_auto` |
| `inorm [extra]`, `iframe_norm [extra]` | normalise the whole Iris goal (hypotheses and conclusion) before framing: `zero_val Bool`, `sint.nat (W64 0)`, `(sint.Z x).toNat`, `take`/`drop`/`map`/`++` of `[]`, `map` over `++`/`take`/`drop`/`set`/`dropLast`, `Option.getD/map/isSome` of `some`/`none`, `!true` |
| `split_ands_hyps`, `bounds_solve` | helpers: add the conjuncts of the context's conjunctions; the solver `wp_bounds` uses |
| `timed tac` | prints `timed: N ms` for `tac` |

## Usage (paste into an agent brief)

```
import GroveTactics            -- compile once: ./buildmod GroveTactics.lean
wp_bounds                      -- next `if 0 ≤ i ∧ i < len then … else Panic` : proves the condition with `word`
                               --   (uses context hyps, also conjunctions like `Hi : 0 ≤ a ∧ a < b`)
wp_bounds using exact ⟨Hi, by word⟩   -- your own proof of the condition;  `wp_bounds*`: every provable check
wp_auto_frac                   -- wp_auto that also loads `t.[S, "f"]` through `Ht : t ↦{dq} tv` (no field splitting)
wp_load_frac                   -- just that one load
wp_run                         -- wp_auto + anonymous result allocs (`wp_alloc_anon`) + fractional loads
wp_ptr_method                  -- before `wp_apply wp_find …` when Go calls a value method via a pointer (`n.items.find(…)`)
inorm                          -- normalise hyps and goal (zero_val, sint.nat 0, take/drop/map of [], Option.getD …)
inorm [lookup, List.find?_nil] -- … with extra simp lemmas;  iframe_norm [..] = inorm [..]; iframe
timed wp_bounds                -- prints the tactic's wall time
```
Do not run `inorm` while the conclusion is still a `WP` (simp would also rewrite the program).

## Validation (on copies of the existing proofs in `scratch/`; `python3 -I scratch/runall.py DIR`)

| change | sites | files | compile after replacement |
|---|---|---|---|
| bounds `rw [ite_eq_left_of_eq_true …]` → `wp_bounds` | 24 | 8 | 24/24 |
| `simp only [hb, and_self, ↓reduceIte]` → `wp_bounds` | 27 | 7 | 27/27 |
| … and the preceding `have hb … := by word` dropped (where `hb` had no other use) | 3 | 2 | 3/3 |
| `btree_fields` split (12 proofs) / explicit `Access.access` open-close (`maxItems`, `minItems`) removed, `wp_auto` → `wp_auto_frac` | 14 | 14 | 14/14 (9 needed one extra `wp_auto_frac` before a `wp_apply`) |
| `wp_alloc_anon; wp_pures; wp_alloc_anon; wp_auto` → `wp_run` | 10 | 10 | 8/10 (`min`/`max`: `wp_run` goes further, so the following `rename_i`/`irename` no longer match) |
| `wp_method_call; wp_call; wp_auto` → `wp_ptr_method` | 6 | 4 | 6/6 |
| goal `simp only`/`rw` with only normalisation lemmas → `inorm` / `inorm [rest]` | 28 (19 / 9) | 13 | 28/28 (one following `rw [show (sint.Z _).toNat = … from rfl, …]` had to drop its first lemma: `inorm` already did it) |

Total: 51 bounds checks (the one other `rw [ite_eq_left_of_eq_true …]` site, in `node__maybeSplitChild`,
is an `if` of the spec, not a bounds check, and `wp_bounds` correctly reports no bounds check).

Time per call (`timed`, from the runs above): `wp_bounds` 9–318 ms, median ≈ 70 ms (59 calls, 5.3 s
total over 15 files); `inorm` 22–102 ms; `wp_auto_frac` on `maxItems` 130 ms (whole call incl.
`wp_auto`). Whole-file check times are unchanged (e.g. `node__iterate` 60 s before and after; the
70–90 s seen in some parallel runs was machine load).

Text saved in the copies: bounds 2.2 k chars; frac 1.5 k chars + the 17-line `btree_fields` lemma
(`Lemmas/Read.lean`) no longer needed; `wp_run` 30 lines; `wp_ptr_method` 12 lines; `inorm` 1.1 k chars.

## Not done

- Short-circuit `&&` (`if: a then b else #false`): the existing proof (`node__remove`) uses a
  `wp_join (Q := …)` restating the whole frame to avoid duplicating the continuation; a generic
  tactic would need to infer that frame — not attempted. No `for … && …` loop occurs in the
  non-challenge proofs.
- `inorm` is a fixed simp set (extendable per call); it does not unfold project definitions such
  as `removeOp` or `ascRange … [] = []` unless passed as extra lemmas.
- `wp_auto_frac` stops where `wp_auto` stops; after a `wp_apply` whose internal `wp_auto` hits a
  fractional load, call it again.
