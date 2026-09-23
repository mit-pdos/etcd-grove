# Proof performance

What makes Perennial proofs in this repo slow to check, measured rather than
guessed, and what was done about it. Newest investigation first.

## How to measure

- Per file: every build prints `ROCQ TIME`, and `.timing.sqlite3` keeps it
  (see CONTRIBUTING.md, "Per-file build times").
- Per sentence: `make <file>.vok ROCQ_ARGS="-time-file /path/out.timing"`
  writes one line per sentence, as `Chars a - b [...] t secs`. Map `a` back to
  a line with `src[:a].count('\n')+1`. Sum the lines per `Lemma` for a
  per-lemma table, or per leading tactic for a "what kind of step is slow"
  table.
- Inside a macro: `Set Ltac Profiling.` at the top of the file, then
  `Show Ltac Profile CutOff 2. Reset Ltac Profile.` after each `Qed.`.
  Ltac2 internals (most of `word`) show up only as `word`'s *local* time. To
  split them, wrap the phases in `time "label" ltac2:(word.<phase> ...)` (see
  below).
- To iterate fast on one lemma: copy the file, turn every other `Proof. … Qed.`
  into `Proof. Admitted.`, and compile the copy with `rocq compile -vok` and
  the `_RocqProject` flags. A one-lemma probe of `rwmutex.v` checks in about
  30–50 s, where the whole file takes 350 s.
- `Set Typeclasses Debug.` around one tactic shows which instances a slow
  `iFrame` explores. Do this for **one** call only, because the trace
  prints the goal: a 2 s `iFrame` produced 59k lines and took 30 s to print.
- The machine is shared with other agents, so the same unedited lemma varies
  by about ±10% from run to run. Treat smaller differences as noise.

## `new/proof/sync_proof/rwmutex.v` (2026-09-23)

**349 s → 259 s** to check (vok, one core), a 26% cut. Only the wp proofs
changed. Commit `9aa63d5d4`.

### Where the time went (before)

Time per lemma, before and after. Step lemmas are the ghost-state
`step_*` lemmas at the top of the file; wp lemmas are the program proofs:

| lemma | before (s) | after (s) |
|---|---:|---:|
| `wp_RWMutex__Lock` | 52.1 | 32.5 |
| `wp_RWMutex__RUnlock` | 36.5 | 24.6 |
| `wp_RWMutex__Unlock` | 36.5 | 27.9 |
| `wp_RWMutex__TryRLock` | 29.5 | 19.8 |
| `wp_RWMutex__RLock` | 29.0 | 16.7 |
| `step_RLock_readerCount_Add` | 27.5 | 23.6 |
| `step_rUnlockSlow_readerWait_Add` | 22.9 | 19.7 |
| `wp_RWMutex__TryLock` | 21.7 | 14.3 |
| `step_RUnlock_readerCount_Add` | 18.7 | 13.9 |
| 10 more `step_*` lemmas, `init_RWMutex`, preamble | 94.6 | 85.6 |
| **total** | **349** | **258** |

The step lemmas were not edited, so their change is noise.

Time by kind of sentence, before. There is no single hot spot, just several
costs spread across the file:

| sentence kind | total (s) | calls | avg (s) |
|---|---:|---:|---:|
| `word` | 53.7 | 40 | 1.34 |
| `iFrame` | 46.5 | 73 | 0.64 |
| `Qed` | 46.0 | 19 | 2.42 |
| compound `destruct …; word; iFrame …` (step lemmas) | 37.3 | 17 | 2.19 |
| `rwInvEnd` (close the invariant) | 26.5 | 16 | 1.65 |
| `rwStep` (apply a step lemma) | 22.0 | 11 | 2.00 |
| `rwLinearize` | 21.3 | 8 | 2.66 |
| `rwInvStart` (open the invariant) | 20.0 | 13 | 1.54 |
| `wp_auto` | 15.2 | 46 | 0.33 |

### Bottleneck 1 — bare `iFrame` / `"[$]"` next to a WP goal (fixed)

In the wp lemmas, Ltac profiling put **~40% of the time in typeclass search
under `iFrame`**. The atomic step of each operation looks like
`rwInvStart. rwAtomicStart. iFrame. …`. At that `iFrame`, the goal is the
atomic update's premise, `own_Int32 … ∗ (own_Int32 … ={∅,…}=∗ |={…}=> WP
<rest of the Go function> {{ … }})`. A bare `iFrame` tries *every* spatial
hypothesis. `Typeclasses Debug` shows each failing attempt going through
`frame_wand` → `frame_fupd` → **`frame_wp`**, and on into the WP
postcondition. That is unification against the whole remaining program, and
it is repeated about ten times to frame the one hypothesis that fits.

- `iFrame "HreaderCount_inv"` instead of `iFrame`: **2.1 s → 0.1 s per
  call**, 14 call sites.
- `rwStep` took `iMod (lem with "[$]")`. It now takes the specialization
  pattern as an argument, e.g. `rwStep step_Lock_readerCount_Add "[$Hwl
  $Hprot_inv]"`.
- `rwLinearizeStart`/`rwLinearizeEnd` framed `"[$]"` into the ghost-var
  update and into `HΦ`'s premise. They now name `Hstate_inv` /
  `Hstate2_inv` (and `Hrtok` for `RUnlock`).
- `rwInvEnd` framed into `▷ ∃ ws rs rc rw st, …` directly. Doing `iNext;
  iExists _, _, _, _, _` first, so framing fills evars instead of pushing
  every hypothesis through `frame_exist`, takes it from 1.4 s to 0.8 s.
  `iFrame "∗"` (spatial only) instead of `iFrame` made no difference.

### Bottleneck 2 — `word` (not fixed; it is framework code)

Averages 1.1–1.3 s per call, even on goals with ~8 relevant hypotheses.
`lia` is **not** the cost: timing the phases of `word.solve_unsafe`
(`src/Helpers/Word/Automation.v`) on a real goal from
`step_RLock_readerCount_Add` gave:

| phase | s |
|---|---:|
| `eliminate_word_ops` | 0.57–0.79 |
| `Z.div_mod_to_equations` | 0.14–0.17 |
| `subst_all` | 0.07–0.09 |
| `simplify_Z_constants` | 0.06–0.07 |
| `lia` | 0.03 |

`eliminate_word_ops` tries each of ~15 rewrite laws against each hypothesis
in turn (`try_rewrite_anywhere`), and restarts the whole scan after every
success. With its verbose logger on, that goal took **1,595 rewrite attempts
for 18 successful rewrites**. Clearing the unrelated non-`Prop` hypotheses
first (section variables, `γ`, …) saved under 10%, so failed attempts are
cheap. The cost is the restart-per-success structure. A fix belongs in
`Automation.v` and would speed up every file that uses `word`. It was not
attempted here, because it changes a tactic the whole repo depends on.

### Bottleneck 3 — `Qed` and per-step proof-mode overhead (not fixed)

`Qed` is ~15% (2–8 s per wp lemma). The rest is spread over proof-mode steps
that each cost 0.05–0.1 s because the context and goal are large: `iNamed`
on the invariant, `iInv`, and `iCombineNamed`. There is no single call to
remove.

### Dead ends (measured, not worth it)

- **Re-sealing `own_RWMutex_invariant` for the wp section.** The
  `#[local] Transparent` at line 87 is inside `Section protocol` and ends
  with it, so the invariant was already opaque there. No change (342 s).
- **One `iDestruct … as (?????) "(Hstate_inv & …)"` instead of
  `iNamedSuffix`** in `rwInvStart`: 0.8 s → 0.5 s per opening, but you lose
  the existential names (`reader_count` …) that `wp_RWMutex__Unlock` refers
  to. Not taken.
- **Unfolding `own_RWMutex_invariant` before `iFrame` in step lemmas:**
  0.75 s → 0.5 s per case. Too little for the churn.
- **A `clear`-non-`Prop`-hypotheses wrapper around `word`:** under 10%.
- **Hiding the program text during the atomic block.** `wp_hide_body`
  (`new/golang/theory/proofmode.v:237`) only fires when the goal *is* a
  `WP`. At an atomic step the `WP` is nested in the atomic update's
  continuation. A file-local variant that let-binds the first nested
  `wp _ _ ?e _` before `iInv` made no measurable difference *after* the
  by-name framing above: every bucket, including the untouched step lemmas,
  moved by the same +12% machine-load drift. Once nothing frames blindly,
  nothing is left unifying against the program. Not kept.
