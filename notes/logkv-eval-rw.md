# logkv experiment: the `logkvrw` variant (read-write mutex), 2026-10-28

The experiment (`notes/logkv-eval.md`): how much proof work a small feature costs when the base
program (`examples/lintest/logkv`, proved end to end: `logkv_adequate`) is already proved.

**The feature.** `examples/lintest/logkvrw/logkvrw.go` is `logkv` with `Server.mu` a
`sync.RWMutex` instead of a `sync.Mutex`: `Get` takes only the read lock (`RLock`/`RUnlock`), so
readers run concurrently; `Put`, `applyLoop` and the condition variable (`sync.NewCond(&s.mu)`, a
`*RWMutex` as `Locker`) use the write lock. Three lines of Go change.

**The result.** Proved end to end: `Perennial.EtcdGrove.lintest.logkvrw.logkvrw_adequate`
(`Proof/.../lintest/logkvrw/Adequacy.lean`; `Results.lean` prints its axioms), no `sorry`, no new
axiom: its `#print axioms` is the same 53 axioms as `logkv_adequate`'s (and `wp_Main`'s the same 27
as the base's), compared name by name. One thing is weaker than the base's theorem: it is about
executions of fewer than `2^30 - 1` steps, not `2^63` (below, "The thread bound").

Process: step 1 (the copy, package renamed, nothing else) is commit `b7e812e8eb`; the proof is
the commit after it.

## What changed, and why

### 1. A reader needs a reader token, and the driver gives the library none (feature + driver spec)

Perennial's `RWMutex.RLock` needs one of the lock's reader tokens (`ownRWMutex`, of which there
are `actualMaxReaders = 2^30 - 1`: more concurrent readers would overflow `readerCount`). That is
not a proof artifact: Go's lock does break with `2^30` concurrent readers. A `Get` whose spec
gives it no resource cannot take one from a finite stock without a bound on the concurrent
`Get`s, and the only such bound the logic has is the thread tokens (`threadTok`, one per live
goroutine): Perennial's `init_RWMutex_threadPool` puts the reader tokens in a thread pool that
lends one per thread token (`Perennial/Proof/sync/RWMutexThreads.lean`). This is the
`spec` skill's principle "an exclusive resource the code needs is covered by a token every caller
can supply ... a thread token is one such token" (`put.md`, critique 3).

So `Server.Get.spec` takes `threadTok` and gives it back. Its caller `Apply` is called by the
lintest driver through `applySpec` (`Proof/.../lintest/Defs.lean`), which hands the library
nothing per call; and `Run` forks its clients with `wp_fork`, which keeps each goroutine's thread
token out of reach. **No spec of `Apply` can meet `applySpec` once `Get` reads under an
`RWMutex`.** The fix belongs in the driver (below, "Changes outside my paths"); here it is a
local workaround:

- `DriverTok.lean`: `applySpecTok`, `applySpec` with the calling goroutine's `threadTok` in the
  pre and the post (weaker as a requirement on the library: an `applySpec` gives an
  `applySpecTok` by framing), and `wp_apply_commit_tok` (`ClientSteps.lean`'s
  `wp_apply_commit`, the token passed through).
- `Spec/.../logkvrw/RunTok.lean`, `runClientTok.lean` and their proofs: copies of `lintest`'s
  `Run`/`runClient` specs and proofs over `applySpecTok`. The proofs differ from the originals
  in 29 and 21 diff lines (`Run`: `wp_fork_tok_body` in place of `wp_fork`, the token given to
  `runClientTok` and returned at the goroutine's end; `runClient`: the token in the loop
  invariant and passed to each `apply`), the specs in 15 and 16 (header, names,
  `applySpecTok`). Linked in this package's `Link.lean` (`logkvrw.wp_RunTok`), with porcupine's
  `CheckOperationsVerbose` as an `@` callee; `Check` uses `RunTok` in place of `Run`.
- `Server.Apply.spec` is stated with `applySpecTok`; its proof passes the token to `Get` and
  frames it around `Put` (4 lines).

*Required by the feature?* The thread token is (any sound spec of `Get` needs a bounded-reader
argument). Having to copy the driver is the base's choice: `applySpec` was written for
`counter`/`logkv`, whose libraries need no per-goroutine resource. A driver whose `applySpec`
passed the thread token from the start (each client is a goroutine that owns one) would have
cost this variant nothing here: the copies are ~630 lines, 60% of the churn.

### 2. The thread bound (feature)

The pool needs `threadBound GF ≤ 2^30` (`init_RWMutex_threadPool`), so `New.spec`, `Check.spec`
and `Main.spec` take it as a premise, and the adequacy theorem, whose thread bound is
`T = n + 2` (`Proof/runtime/Threads.lean`), is for executions of `n < 2^30 - 1` steps instead of
`n < 2^63`. Required by the feature, given Perennial's accounting (thread tokens bounded only by
the adequacy theorem's `T`, which is tied to the execution's length): the same bound as
`watchkv`'s (`threadBound GF ≤ 2^29`). A sharper adequacy theorem would bound the live threads
of this particular program (it never has more than about seven), which Perennial's adequacy does
not offer; not attempted.

### 3. The lock invariant: fractional for the readers (feature + base invariant shape)

Perennial's guarded `RWMutex` protects a *fractional* `P q` (`Lock` gives `P 1`, `RLock`
`P rfrac`). The base's lock invariant `logkvrwR` is not fractional: its request slots hold
writers' atomic updates and postconditions (`pendSlot`, `doneSlot`). Split (`Defs.lean`):

- `rdR γ γb s q` (the `RWMutex`'s `P`): `s.state ↦{q} st`, the lock's half of the register's
  ghost variable at fraction `q`, and a new ghost variable `γb`'s half at `false`; timeless and
  `Fractional` (proved: agreement on `st` through the ghost variable). This is all a reader
  needs: its linearization point agrees with the caller's `regState` exactly as the base's did.
- `wrR γ γr s`: the rest of the base's invariant (log, `applied`, request list, slots), kept in an
  Iris invariant `wInv := γb½ true ∨ (γb½ false ∗ wrR)`: a writer, holding `rdR 1` and thus
  `γb½ false`, flips `γb` to `true` and takes `wrR` out; before unlocking it puts `wrR` back and
  flips `γb` to `false`. `logkvrwR_split`/`logkvrwR_join` relate `logkvrwR` to the two parts.
- `isServer` now holds the guard and `wInv` (`wLock`) and the pool, instead of `isMutex`.
- `WLock.lean` (new): `wp_wLock` (`Lock` gives `wLocked ∗ ▷ logkvrwR`, the base's whole
  invariant), `wp_wUnlock`, and `wLocker` (`&s.mu` is a `Locker` with that resource, for
  `Cond.Wait`). With these, **the writers' proofs are the base's**: `Put` and `applyLoop`
  changed only in the names of the lock lemmas, the destructuring of `isServer` and the Wait
  resource (12 to 17 diff lines each, of 163 and 137), plus one bullet (`· iexact HR`) where the
  premise's later is now stripped automatically. Their specs and `logkvrwR`, `pendSlot`,
  `doneSlot`, `regAu`, the model and its lemmas are unchanged.

*Required by the feature?* A fractional reader-side resource is. The `wInv`/`γb` indirection
is the cost of the base's invariant mixing reader-visible state with non-fractional writer-only
resources in one lock predicate; a base whose invariant was already `rdR 1 ∗ wrR` (the state
apart from the log) would have needed only the `wInv` part, which no `Mutex`-based base would
write. A Perennial `RWMutex` interface guarding `P q ∗ (q = 1 → W)`-style "writer-only" resources
(a fractional part for readers, an exclusive part for the writer) would remove `wInv`, `γb` and
most of `WLock.lean`: a general change worth proposing to Perennial (below).

### 4. Smaller changes

- `New`: allocates `γb`, `wInv`, and the `RWMutex` with its pool (`init_RWMutex_threadPool`)
  instead of `init_Mutex` (~30 lines of the 82); the apply goroutine is still forked with
  `wp_fork`.
- `Get`: rewritten around `RLock`/`RUnlock` and the pool (`borrow`, `giveBack`): ~45 diff lines
  of 73; the linearization-point reasoning is the base's.
- `muLocker` is `&s.mu` as a `*RWMutex`.
- `Check`/`Main`: the premise passed along, `wp_RunTok` for `wp_Run`. `Adequacy`: the bound.
- `Init.lean` and `PkgTable.lean`: unchanged copies; `etc/gen-init.py
  github_com.mit_pdos.etcd_grove.examples.lintest.logkvrw --check` and the plain `etc/gen-init.py
  --check` both report them up to date.

## What carried over unchanged

`Model` (spec and proof), the register's model and its lemmas (`regS`, `regStep_*`, the
injectivity lemmas), `regState`, `regAu`, `pendSlot`, `doneSlot`, `logkvrwR`, the specs of `Put`
and `applyLoop`, the bodies of the `Put` and `applyLoop` proofs (all the log and slot reasoning),
`Init`, `PkgTable`, the ghost-state bundle in `Adequacy`.

## Changes outside my paths I would have made

1. **`lintest`'s `applySpec` with the thread token** (`Proof/.../lintest/Defs.lean`): exactly
   `applySpecTok`, and `Run`/`runClient` proved over it (`wp_fork_tok_body` in `Run`, the token
   threaded through `runClient` and `wp_apply_commit`), as in this package's copies. Every
   existing instance (`counter`, `logkv` and the other variants) would keep its proof by framing
   the token (or by a lemma `applySpec ⊢ applySpecTok`). Why: the driver runs each `apply` on a
   goroutine of its own, which owns a thread token; withholding it makes any library that reads
   under an `RWMutex` (or anything else bounded by live threads) unprovable against the driver.
   With it, `DriverTok.lean`, `RunTok`, `runClientTok` and their link entries go away.
2. **Perennial**: a guarded `RWMutex` interface with an exclusive writer part (see 3 above), and
   `isLocker` for a `*RWMutex` through the guard (`RWMutex_guard_is_Locker`, as
   `Mutex_is_Locker`): `wLocker` is that lemma plus this package's `wInv`. To propose on its own,
   per CLAUDE.md "Changes to Perennial"; not needed for this proof.

## Numbers

`git diff --stat b7e812e8eb..HEAD -- <my paths>` (the proof commit; this note excluded): 24 files,
1035 insertions, 92 deletions. Of it:

| part | files | lines (+/-) |
|---|---|---|
| driver workaround (copies of `Run`/`runClient` over `applySpecTok`, `DriverTok`) | 5 new | +628 / -0 |
| lock split and write-lock lemmas (`Defs`, `WLock`) | 1 changed, 1 new | +263 / -12 |
| `Get` (spec and proof) | 2 | +33 / -20 |
| `New`, `Check`, `Main`, `Apply` (specs and proofs), `Adequacy`, `Results` | 10 | +75 / -38 |
| `Put`, `applyLoop` (proofs; `applyLoop`'s spec header) | 3 | +15 / -16 |
| `Link.lean` (generated), link list | 2 | +21 / -6 |

The driver copies differ from the originals by 81 diff lines in all (specs 31, proofs 50).
Without the workaround (with item 1 of the previous section done in `lintest`), the variant costs
about 400 inserted lines, three quarters of them the lock split (`Defs`, `WLock`) and the rewritten
`Get`, most of the rest comments and premise plumbing.

**Why the feature cost what it cost.** (1) The driver's library spec withholds the thread token a
reader slot needs, which forced a copy of the driver: the largest cost, and a base design choice.
(2) Perennial's `RWMutex` guards a fractional predicate, and the base's lock invariant was one
non-fractional blob: splitting it (with an invariant and a flag to hand the writer's part over)
was the main proof work, and an interface choice (Perennial's) plus an invariant-shape choice
(the base's). (3) The thread bound is intrinsic (Go's reader count), and it shortens the adequacy
theorem's execution bound to `2^30 - 1` steps through Perennial's tying of the thread bound to the
execution length. Everything about the log, the slots and linearizability carried over, because
the writer-side lemmas (`WLock.lean`) present the write lock in the base's terms.
