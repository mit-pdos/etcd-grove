**Tools**

*Checking.* `./ide` keeps a Lean server running for your directory, so each call re-checks only
what changed. Each call ends with `-- elaborated in Xs`. Run it from your directory:
- `./ide upto FILE LINE`: checks FILE only up to the tactic on LINE (the rest of the proof is
  cut off and closed by `sorry`) and prints the errors in lines 1..LINE and the goal after LINE.
  Use it after every edit. It takes about 1–4 s, whatever the length of the proof. You don't need
  `done` or `sorry` to see a goal.
- `./ide steps FILE A [B]`: prints the state before line A, then what each tactic on lines A..B
  changed (`+`/`~`/`-` hypotheses, new conclusion). It stops at the first failing tactic and
  prints its error. Use it when a tactic did not do what you expected.
- `./ide goal FILE LINE [--after]`: the state before (after) the tactic on LINE, in the whole file.
- `./ide check FILE`: all errors of the whole file (incremental).
- `./check FILE`: a full, from-scratch `lean FILE`. Use it as the final check; it is authoritative.
- `./ide restart [FILE]` (if something looks stale), `./ide stop` (when you are done).
  `--timeout S` returns partial results after S seconds, and the server keeps working.

Workflow: write a few tactics, then run `./ide upto FILE <last line>`. Fix the errors and repeat.
When a branch is done, run `./ide check FILE`. At the end, run `./check FILE`. (`./ide upto F 57`)

*Short goals.* Goals and errors print in compact form: a `WP` shows only the next few statements
of the program (`…` is the rest; the statement that runs next is always shown). Go names print as
`go!"items"`, which you can paste back (`n.[node V, go!"items"]`). Long IH/HΦ hypotheses are cut to
their binders. `./ide` adds this display module to its in-memory copy of the file; your file on
disk is unchanged.
- `--diff` (with `goal`/`upto`): hypotheses that are unchanged since your previous `goal`/`upto`
  on FILE are listed by name only. Example: `./ide upto F 60 --diff`.
- `--full`: no text-side cuts. For the whole program, add `set_option goose.pp.compactWP false in`
  in front of a tactic.
- With `./check`: if FILE imports `GroveTools`, errors are compact too; otherwise use
  `./check FILE | ./ide compact`.

*Incremental reuse.* Name induction alternatives: write `induction h using Nat.strongRecOn with
| ind h IH =>`, not `| _ h IH =>`. Inside a `| _` alternative, Lean re-checks the whole alternative
after every edit. `./ide upto` renames it in its copy, but `./ide check` and `./ide goal` cannot,
and `./ide check` prints the right name as a hint.

*Tactics and lemmas.* Put `import GroveTools` as the first import of the proof file. It is
precompiled; `./check` and `./ide` find it, and importing it does not slow the file down. The
sources are in `tools-src/` if you want to read them.
- `wp_bounds`: proves the bounds check of the next slice index or slicing step (the
  `if 0 ≤ i ∧ i < len then … else Panic`), replacing `rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]`.
  With your own proof: `wp_bounds using exact ⟨Hi, by word⟩`. `wp_bounds*` proves every bounds
  check it can.
- `wp_load_frac`: loads a struct field through a fractional points-to `Ht : t ↦{dq} v`, which
  `wp_auto` cannot do. `wp_auto_frac` is `wp_auto` plus such loads. After a `wp_apply`, call it
  again if it stopped at a load.
- `wp_run`: repeats `wp_auto`, allocation of unnamed Go results (`wp_alloc_anon`) and fractional
  loads until none applies.
- `wp_ptr_method`: Go calls a value method through a pointer (`n.items.find(…)`). Use it before
  `wp_apply wp_find …`; it replaces `wp_method_call; wp_call; wp_auto`.
- `inorm [extra lemmas]`: normalises the Iris hypotheses and the goal (`zero_val`,
  `sint.nat (W64 0)`, `take`/`drop`/`map` of `[]`, `Option.getD (some _)`, …).
  `iframe_norm [..]` is `inorm [..]; iframe`. Don't use them while the goal is still a `WP`.
- `list_seg`: closes pure goals about lists, slices, lengths, indices and word bounds
  (take/drop/set/++/getElem?/subslice, insert-at/remove-at arithmetic, `sint.nat`/`W64` bounds;
  it calls `word`), using the context and ignoring Iris hypotheses. It either closes the goal or
  fails and leaves the goal unchanged. Example: `have hj : sint.nat idx < cs.length := by list_seg`.
  To pass extra facts: `list_seg [hlen, countLt_le]`. Try it before `word`/`omega`, or after
  `ipureintro`. If a proof uses many `list_seg`s, write `set_option maxHeartbeats 400000 in`
  before the `theorem`.
- `sorted_seg`: proves `Sorted lt l` for `l` a piece (take/drop/sublist/`++`) of sorted lists in
  the context. Example: `have hs : Sorted o.lt (is.take i) := by sorted_seg`.
- `timed tac`: prints how long `tac` took.
- `LEMMAS.md`: an index of 572 existing lemmas (btree, `list_seg` library, Perennial lists), with
  full statements, file:line, topic and a list of duplicates. Search it before writing a lemma:
  `grep -n 'countLt' LEMMAS.md`. Regenerate it with `python3 -I etc/lemma-index.py`.

*Without the tools.* `./check FILE` (whole file, full output) still works without them. To see a
state you can still end the proof with `done` and read the error, but `./ide upto` is faster.
