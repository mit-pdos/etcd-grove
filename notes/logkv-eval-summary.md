# The logkv experiment: what a feature costs once the base is proved (2026-10-28)

An experiment in scalable proof development: a small program is proved end to end (phase A),
then each of four variants, each the base plus one feature, is proved by a fresh agent starting
from a renamed copy of the base proof (phase B). The cost of a feature is what phase B changed in
that copy. All agents were fresh, with the `spec` skill as of `lean` `3e99707422`; phase A did not
see the variants. Details: `notes/logkv-eval.md` (phase A), `notes/logkv-eval-{compact,snap,rw,append}.md`.

## The programs (`examples/lintest/`)

`logkv`: a register whose writes go through a lock-protected log that an apply goroutine applies
(a write takes effect in another goroutine, as in etcd's apply thread), readers reading the applied
state; `Main` checks linearizability with the `lintest` driver and porcupine. 84 lines of Go code.

| Variant | Feature | Go code lines changed |
|---|---|---|
| `logkvcompact` | log compaction: the log no longer starts at 0 | +6 −3 |
| `logkvsnap` | the state an immutable object replaced at each apply, read after unlock | +15 −12 |
| `logkvrw` | readers under a read lock (`sync.RWMutex`) | +3 −3 |
| `logkvappend` | a new operation, and a new field in the log's entries | +30 −7 |

## Results

Every program is proved end to end (`<pkg>_adequate`), with no `sorry` and the same 53 axioms as
`counter_adequate`; no agent changed anything outside its own package's files in phase B.

Phase A: 344 spec lines and 1,316 hand-written proof lines (1,143 code lines without comments), in
about 112 minutes; one change outside the package (`lintest.genSpec` gained `0 ≤ id`).

Phase B, against the renamed copy (generated `Init`/`PkgTable`/`Link` excluded; "code" excludes
comments; a moved function counts as deleted and added):

| Variant | Files changed | Lines +/− | Code lines +/− | Specs changed | Time |
|---|---|---|---|---|---|
| `logkvsnap` | 5 / 19 | +63 −39 | +42 −24 | 0 | 8 min |
| `logkvappend` | 12 / 23 | +517 −235 | +354 −155 | 3 | 11 min |
| `logkvcompact` | 9 / 19 | +124 −63 | +101 −54 | 2 | 12 min |
| `logkvrw` | 22 / 25 | +1014 −86 | +756 −53 | 8 | 19 min |

`logkvappend`'s count includes `Put`'s proof moved to the new `write` (163 lines, 3 changed);
`logkvrw`'s includes 628 lines of local copies of the driver's `Run`/`runClient` proofs (81 lines
differ from the originals), a workaround for a driver spec it was not allowed to change.

## What made features cost more than the feature

- **Invariants unpacked field by field in every proof** (`logkvsnap`: about half its changed code
  lines, including all of `Put`'s, whose logic did not change; `logkvcompact`: about 20 lines,
  including `Get`, which only reads). A named predicate per part of the lock invariant, with small
  read/update lemmas, would have kept the change in `Defs`.
- **The model matched by position** (`logkvappend`: about 30 lines): `Op` values destructured as
  `⟨b, v⟩` broke everywhere when `Op` gained a field; the input decoder recognized writes only.
- **A driver spec with no room for a thread token** (`logkvrw`: most of its cost): `lintest`'s
  `applySpec` gives the library nothing per call, and `Run` forks clients without handing them a
  token, so no `Apply` over an RWMutex reader (which needs a thread token for its reader slot) can
  meet it. The fix is in the driver: `applySpec` with the token in its pre and post.
- **A non-fractional lock invariant** (`logkvrw`): Perennial's RWMutex protects a fractional
  resource; the base's single invariant holds the writers' atomic updates, so the variant split it
  into a reader part and a writer part handed off through an Iris invariant. An RWMutex interface
  with an exclusive writer-only part would remove most of this (a Perennial change, not made).

What carried over unchanged in every variant: the register's API specs (`Put`/`Get` logically atomic
over `regState`), the model, the helping protocol (the writer's atomic update stored in the lock
invariant, fired by the apply goroutine, its result collected through saved propositions and a
ticket). The features that the base's ghost state already anticipated by its shape (a ghost request
list separate from the slice: compaction; an update over any current state: append) were cheap.

Features with a real proof obligation of their own: compaction's `start + len(log)` can wrap a
`uint64`, so the variant bounds the number of writes with time receipts; the RWMutex's reader bound
makes `threadBound ≤ 2^30` a premise, which shortens the adequacy theorem to `2^30 − 1` steps.

## As an evaluation

A phase B run is cheap (8–19 minutes) and its notes attribute each change to the feature or to a
base choice; the base-choice costs it found are the ones the snapshot work suffered at scale
(non-local invariants, interface specs lacking a resource). To train against it, compare two
versions of the guidance by running phase A with each and phase B on the same variants. Its limits:
one run per variant (agent variance unmeasured), one base proof style, small variants, and line
counts that mix proof work with comments and moves.
