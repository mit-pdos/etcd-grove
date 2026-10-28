# logkvappend: logkv plus Append, proved by adapting logkv's proof (2026-10-28, branch `logkv-eval`)

One of the four feature variants of the logkv experiment (`notes/logkv-eval.md` is the base).
`examples/lintest/logkvappend/logkvappend.go` is logkv with a second kind of write, `Append(v)`,
which appends `v` to the register's value. In the code: `Op` gets an `Append` field and
`Model.Step` an append case; the log's entries become a struct `entry{app bool; val string}`;
`Put`'s body becomes the internal `write(e entry)`, with `Put` and `Append` one-line wrappers;
`applyLoop` branches on `e.app` (`state + val` or `val`); `Apply` gets an append case; `Check`'s
generator makes clients `2 mod 4` append.

**Result**: `logkvappend_adequate` (`Proof/.../lintest/logkvappend/Adequacy.lean`) and the linked
`logkvappend.wp_Main` (`Link.lean`), both proved, no `sorry`. `#print axioms` of each is exactly
`logkv_adequate`'s / `logkv.wp_Main`'s (53 and 27 entries, compared as sets: identical), so no new
axiom. `etc/gen-init.py --check` reports every file up to date, so the copied `PkgTable.lean` is
what the plain run would generate. (`etc/tcb-report.py` and the plain `lake build` were not run:
this worktree is shared; only this package's modules were built.)

Process: the copy commit (`7ce000d05f`, logkv's `Spec/` and `Proof/` with `logkv` renamed to
`logkvappend`, byte-identical to logkvcompact's copy up to the name) and one proof commit. The
proof took one sitting with no dead ends: every file was edited once and checked, the only
iterations being Lean-level (a missing `Countable` instance, `wp_if_destruct` refusing a branch on a
record projection, an argument order).

## What changed, and why

### Specs (`Spec/`)

| Spec | Change | Required by |
|---|---|---|
| `Server.Put` | none | -- |
| `Server.Get`, `New`, `applyLoop`, `Apply`, `Model`, `Main` | none (statements byte-identical) | -- |
| `Check` | header only (the generator's description) | the feature (docs) |
| `Server.Append` (new) | `<<{ ∀∀ x, regState γ x }>> s.Append(v) @@ ∅ <<{ regState γ (x ++ v) }>>`: `Put`'s spec with the post `x ++ v` | the feature (a new function) |
| `Server.write` (new, internal) | `<<{ ∀∀ x, regState γ x }>> s.write(e) @@ ∅ <<{ regState γ (entryStep e x) }>>` | the code's refactoring (`Put`'s body moved into `write`) |

The public API changed only by addition. `Append`'s spec has the same shape as `Put`'s (the
`spec` skill: linearizability as the caller's atomic update in the triple, the shape of the
closest sibling; no ghost name or log in it). `write` is internal (only `Put` and `Append` call
it), so by the skill's scope rule its spec may mirror the code: it is stated over the Go `entry`
and `entryStep`, an internal definition. No spec reviewer was run: the one exported spec added is
`Put`'s with one term changed.

Indirectly, the vocabulary every spec is stated in changed: `regS`'s step (`regStep`), `ioOk`
and `regInOk` now describe a three-field `Op` with an append case. That is the feature itself (the
model is the spec of the register), not a choice of the base.

### Definitions and invariant (`Defs.lean`)

- **The model**: logkv's `putVal` (does the input box a write `Op{true, v}`, and of what) became
  `opOf` (the `Op` an input boxes), and `regStep` cases on its fields like `Model.Step` does:
  `Put`, then `Append` (`s ++ Val`), then the read. `putVal_boxOp` became `opOf_boxOp` (shorter);
  `regStep_put`/`regStep_get` gained the new field, `regStep_app` is new. *Feature-required* in
  substance; the reshaping (`opOf` instead of a second `appVal`) was a choice: `putVal` was
  specific to the base's one write kind. A base model written over `opOf` from the start (the step
  a function of the decoded `Op`) would have needed only the new `else if` and `regStep_app`.
- **`regS.ioOk`, `regInOk`**: `∃ b v, i = boxOp ⟨b, v⟩` became `∃ p a v, i = boxOp ⟨p, a, v⟩`
  (and a read is `p = false ∧ a = false`). *Required by the base's choice* to spell `Op` values
  positionally: stating them as `∃ o : LOp, i = boxOp o` (and the read condition on `o.Put'`,
  `o.Append'`) would have survived a new field unchanged, and so would every `obtain`/`exact` on
  them in `Model`, `Apply` and `Check`.
- **`op_intoValInj`** (an `Op` value determines its fields): one more field, five more lines of the
  same pattern. *Feature-required* (a new field), though the proof is per field boilerplate that a
  generated lemma (Goose's `GeneratedProof`) could provide; noted as a possible Perennial/Goose
  addition below.
- **The log's element type**: `Req := GoString × GName × GName` became `LEntry × …`
  (`LEntry` = the Go `entry`), the slice's `ownSliceCap GoString` became `ownSliceCap LEntry`, and
  `LEntry` needed a `Pos.Countable` instance (for the monotone list of requests) (3 lines).
  *Feature-required* (the log's Go type changed).
- **`entryStep e x`** (new): what applying an entry does to the state. **`regAu γ v P`** became
  `regAu γ e P`, its post `regState γ (entryStep e x)` instead of `regState γ v`. This is the one
  real change to the ghost design, and it is small: the writer's atomic update stored in the lock
  invariant already took the register *from any state* `x`, so making the new state depend on `x`
  only changed the term. *Feature-required.* The base's design made it cheap: the pending slot
  holds the caller's update itself (a fancy update quantified over the current state), not a
  stored "new value", so a state-dependent write fits without new ghost state.
- **Unchanged**: `regState`, `isServer`, the lock invariant `logkvappendR` (only its element type),
  `pendSlot`, `doneSlot`, the done/pending split, the saved propositions and tickets, the monotone
  list. No new ghost state, no new invariant.

### Proofs

| Proof | Change |
|---|---|
| `Server.write` (new) | logkv's `Put` proof, renamed: 3 tactic lines changed (`intro … e`, `wp_slice_literal (V := LEntry) [e]`, `let r : Req := (e, …)`); it went through on the first check |
| `Server.Put` | rewritten as glue over `write` (20 tactic lines): fire the caller's update inside `write`'s, `entryStep ⟨false, v⟩ x = v` by `simp` |
| `Server.Append` (new) | the same glue, `entryStep ⟨true, v⟩ x = x ++ v` |
| `Server.applyLoop` | the update fired at `entryStep e st` instead of `e`'s value (1 line); the code's new `if e.app` branch: case on `e.app'`, the two branches closed by one shared block (`all_goals`) that was the base's single closing block; net +6 lines |
| `Server.Apply` | a third case (append), a copy of the write case with `wp_Append`/`regStep_app` (+22 lines); the other two: the new field in patterns (`⟨b, ap, w, rfl⟩`, `regStep_put x ap w`, `⟨false, false, w, …⟩`) |
| `Model` | a third case (append) in `Step` (+12 lines); the read case's pattern gets the new field |
| `Check` | one pattern (`⟨_, _, _, rfl⟩`); the generator's new `Append: id%4 == 2` went through `wp_auto` untouched |
| `New`, `Get`, `Main`, `Adequacy`, `Results`, `Init`, `PkgTable` | none (docs only in `Adequacy`) |
| `Link` | regenerated (`etc/gen-link.py --lintest-logkvappend`), after adding `write` and `Append` and `Apply`'s new callee to `etc/link-lean-first-lintest-logkvappend.txt` |

### What carried over unchanged

All of the concurrency argument: the helping protocol (the writer's atomic update travelling to the
apply goroutine through the lock invariant and its result coming back through saved propositions
and tickets), the done/pending split, the monotone request list, the mask `∅`, the condition
variable waits, `New`, `Get`, `Main`, the adequacy proof, and the read-only `vals` in `Check`. The
hardest proof of the base (`Put`, 163 lines) carried over as `write` with three tactic lines
changed.

## What the feature cost, by cause

1. **The feature itself (unavoidable)**: the model's append case and `regStep_app`; `entryStep` and
   the `regAu` generalization; the log's element type (`Req`, `ownSliceCap`, `Countable`); the
   append branch in `applyLoop`; the new cases in `Model.Step` and `Apply`; the new `Append` spec
   and its glue proof.
2. **The code's refactoring (`Put`'s body moved into `write`)**: the new `write` spec, and `Put`'s
   proof replaced by glue. In lines this is the largest item of the raw diff (Put −140/+20, write
   +163), but it is a move: the content is the base's proof. Had the code kept two copies of the
   body, the cost would have been a second copy of the proof instead.
3. **Choices in the base (avoidable)**:
   - positional `Op` patterns `⟨b, v⟩` in `ioOk`/`regInOk` and their consumers (about 10 lines in
     `Defs`, `Model`, `Apply`, `Check`); `∃ o : LOp` with field projections would not have changed;
   - `putVal` keyed to the one write kind, rewritten as `opOf` (its lemma replaced, about 15 lines);
   - `op_intoValInj` proved field by field by hand (5 more lines per field).

   None of these touched the concurrency proof; they are all in the model's vocabulary.
4. **What the base got right for this feature**: the pending slot stores the caller's atomic update
   over *any* current state (`∃ x, regState γ x ∗ …`) rather than a value to install, and the
   linearization point is in the apply goroutine where the current state is known. A
   state-dependent write was therefore one term in `regAu`, with no new ghost state and no change
   to the invariant's structure.

## Changes outside these paths I would have made

None needed. Two general improvements noticed, not made:

- Goose's `GeneratedProof` could export, for each struct, that a value is determined by its fields
  (`go.IntoValInj` for the struct type); logkv's and logkvappend's `op_intoValInj` reprove it by
  hand per field. A Perennial/Goose change, independent of this proof.
- `wp_if_destruct` refuses a branch condition that is a record projection
  (`#rs[i].1.app'`: "no `decide` or Boolean variable"); the workaround is `cases hb : … <;> simp
  only [↓reduceIte, Bool.false_eq_true]` before `wp_auto`. A Perennial tactic improvement.

## Numbers

`git diff --stat 7ce000d05f..HEAD` on this package's paths (the proof commit, before these notes):

```
 Proof/.../logkvappend/Adequacy.lean          |   6 +-
 Proof/.../logkvappend/Check.lean             |   4 +-
 Proof/.../logkvappend/Defs.lean              | 124 ++++++++++------
 Proof/.../logkvappend/Link.lean (generated)  |  16 +-
 Proof/.../logkvappend/Model.lean             |  44 ++++--
 Proof/.../logkvappend/Server__Append.lean    |  62 ++++++++   (new)
 Proof/.../logkvappend/Server__Apply.lean     |  76 ++++++----
 Proof/.../logkvappend/Server__Put.lean       | 140 +++---------------
 Proof/.../logkvappend/Server__applyLoop.lean |  42 +++---
 Proof/.../logkvappend/Server__write.lean     | 163 +++++++++++++++++++++   (new; logkv's Put proof)
 Spec/.../logkvappend/Check.lean              |   4 +-
 Spec/.../logkvappend/Server__Append.lean     |  43 ++++++   (new)
 Spec/.../logkvappend/Server__write.lean      |  44 ++++++   (new)
 etc/link-lean-first-lintest-logkvappend.txt  |   8 +-
 14 files changed, 535 insertions(+), 241 deletions(-)
```

Counting the move as a move (`Server__write.lean` against the copy's `Server__Put.lean`: 22 lines
differ, 16 of them comments and names), the real change is about 380 inserted and 110 deleted
lines, of which roughly a third are comments and file boilerplate (the two new specs and two new
glue proofs are ~40 lines of module header each). Of the base's 22 files (1958 lines), the
adaptation touched 9 (one of them, `Spec/.../Check.lean`, only in its header); `New`, `Get`,
`Main`, `Init`, `PkgTable`, `Results` and seven of the eight specs are unchanged.
