# Decisions (Lean port)

Why the Lean port is the way it is. Newest last. The design of the proof itself is
recorded on `main` (`notes/decisions.md`); this file only covers choices the port
had to make.

---

## The Rocq module discipline, in Lean

**2026-10-06 · accepted**

`main` gives every Go function four files (`spec_`/`postulates_`/`proof_`/`link_`)
and uses Rocq's module system for two guarantees (main's decisions.md,
2026-09-14 and 2026-09-18): one Hoare triple per Go function, a duplicate being a
build error (`Include` of two signatures with the same label), and a proof that sees
only the *specs* of its callees, never their proofs (opaque ascription), which also
keeps the proofs checking in parallel.

**Decision:** per Go function, `Spec/<fn>.lean` holds `def <fn>.spec : Prop` (the
triple, with its binders); `Proof/<fn>.lean` holds
`theorem <fn>.wp_proof (h₁ : <callee₁>.spec) … : <fn>.spec`, importing only its
callees' `Spec` files; `Link.lean` instantiates each proof with its callees'
results. Lean's global names make a second `<fn>.spec` a build error (the first
guarantee); taking the callees' specs as hypotheses, with only their `Spec` files
imported, is the second. The `postulates_` file becomes the hypothesis list.
Trust-boundary triples are `axiom <fn>.wp_proof : <fn>.spec` and unfinished ones
`sorry`, so `#print axioms` on a result separates them as `main` does with
`Axiom`/`Admitted`.

**Rejected — one file per function holding spec and proof.** Then a caller imports
its callees' proofs, which both exposes them and serializes the build.

## Build timing: a `lean` shim behind a copy of the toolchain

`etc/build-report.py` (the counterpart of `main`'s, which reads what `etc/rocqc.py`
records around each `rocq compile`) needs each module compile's start, end, CPU,
peak memory and exit status. Lake prints only a duration per job, after the fact,
and has no hook around the compiler; it runs `<sysroot>/bin/lean`, with the
sysroot from `LEAN_SYSROOT` when `LAKE_OVERRIDE_LEAN` is set.

**Decision:** `etc/timed-build.py` (until 2026-10-12 `build-report.py build`; the
report now only reads what it records) makes `.lake/build-report/sysroot/`, symlinks
to the real toolchain except `bin/lean`, a shim that runs the real `lean` under
`wait4` and appends one JSON line per compile to `.lake/build-report/<build>.jsonl`;
then it runs `lake build` with those two variables set. Lake's traces do not
depend on the `lean` path (checked: an up-to-date build stays up to date under the
shim), so the shim changes timing only by Python's start-up per compile. The
imports come from the `.setup.json` Lake writes per module (`importArts`: the
transitive imports; the last of them to finish is always a direct one, so the
critical path and the unlimited-cores bound come out the same as with direct
imports).

**Rejected — timestamping Lake's output.** `✔ [n/m] Built M (12s)` gives an end
time (when the line is read) and a duration, but not CPU or memory, and the line
can lag the compile's end.

Lake runs at most one compile per core: in the first full build of this
repository's modules on 24 cores (2026-10-08), 46s ran exactly 24 compiles and
none ran more. So the report treats the cores as Lake's job slots ("all slots
busy"), and "idle" on the critical path is a wait for a free core, Lake's own
work between compiles, or its start-up. Lean also elaborates a module's
declarations in parallel, so the report charts cores busy (each compile's CPU
spread over its run) next to compiles running.

## Build speed: the Protocol umbrella imports only what `Defs` uses

**2026-10-08 · accepted**

`Defs` imported `Protocol`, which imported the whole protocol development, so
`Defs` and everything after it waited for `StepGhost` … `Facts` (the theorems,
`Refinement` alone 23s), which ran one at a time for the first 1m10s. Only
`Model`, `Ghost` and `GhostState` are used by `Defs`/`Inv*` (checked on the
elaborated environment: which modules' constants each module's constants use);
the theorems are used by four proofs (`RawNode__Ready`, `raftLog__commitTo`,
`raft__Step`, `raft__Step/Base`) and, through `Link`, by `Results`.

**Decision:** `Protocol.lean` imports the three, those four proofs import
`Protocol.Facts`. Full build on 24 cores: 3m40s → 3m01s. No definition, statement
or axiom changed: a hash of every root statement, trusted definition (type and
body, auxiliaries included) and axiom is the same before and after.

What limits the build now, measured on that build:

* **Queueing on the critical path (~50s).** Lake has no job limit or priority:
  a compile occupies one of Lean's worker threads (one per core), and the pool
  is FIFO. When `InvRaftPhys` finishes, ~150 specs become ready at once (started
  in reverse order of registration, i.e. of the root's import list), and the
  next module of a critical chain (`Spec.stepLeader`, `InvRawnode`, then their
  proofs) queues behind them and the proofs they release: `Proof.stepLeader`
  waited 36s. **Rejected — ordering `EtcdGrove.lean` by remaining chain
  length:** it does reorder siblings (tried: `stepLeader`'s callee specs ran
  first), but the FIFO wait comes back one step later; 3m06s.
* **The tail (~30s with ≤3 compiles):** `Proof.stepLeader` (66s, 3m14s CPU) and
  `Proof.RawNode__Ready` (52s), each bounded by its longest declaration
  (`wp_stepLeader_noop`/`appresp`/`prop` ~45–50s each; `RawNode.Ready.wp_proof`
  one theorem). Only splitting those proofs into lemmas Lean elaborates in
  parallel would shorten it.
* **CPU (~39 min; what a 4-core CI runner is bound by).** See the next two
  sections: imports and interpreted tactics.

## Build speed: importing (measured; acted on in "Lean's module system" below)

**2026-10-08 · measured**

Every module pays ~2s and ~2 GiB before elaborating anything (wall / user+sys,
a file with only the import, 24-core machine otherwise idle):

| imports | wall | CPU | peak memory |
|---|---|---|---|
| nothing (`Init`) | 0.46s | 0.78s | 469 MB |
| `Batteries` | 0.99s | 1.32s | 979 MB |
| `Lean` | 1.50s | 1.86s | 1568 MB |
| `Iris` | 1.68s | 2.02s | 1599 MB |
| `Perennial` | 1.92s | 2.22s | 1911 MB |
| `Proof.go_etcd_io.raft.v3.InvRawnode` | 2.08s | 2.44s | 1990 MB |

Most of it is Lean's own `Lean` package, which Iris's and Perennial's tactics
import. The `.olean` files are `mmap`ed, not copied, but a non-`module` file
(every file here and in Perennial) imports all three parts of each module built
with Lean's module system: core Lean's public `.olean`s are 356 MB, its
`.olean.private`s (proof bodies, private declarations) 1360 MB. A `module` file
imports only the public part: `module` + `import Lean` takes 0.9s and 705 MB,
`module` + `import Iris` (Iris is all `module`s) 1.22s and 861 MB. A `module`
cannot import a non-`module` (`cannot import non-module Perennial.Proof.ProofPrelude
from module`), so this needs Perennial on the module system first, then every
file here (a `module` header and `public`/`@[expose]` where another file needs a
declaration or a `def`'s body, the specs included).

## Build speed: precompiled tactics (measured, needs Perennial)

**2026-10-08 · measured**

Perennial's and Iris's tactics run in Lean's interpreter (`interpretation` in
`-Dprofiler`: 11.2s of `RawNode__Ready`'s ~50s). `precompileModules = true` in
this repository's lakefile fails: Lake then loads each dependency as one shared
library made of the library's roots and what they import, and Perennial's root
does not reach the Goose code (`undefined symbol:
initialize_perennial_Perennial_Code_go__etcd__io_raft_v3`).

Experiment (a copy with edited dependency lakefiles): Perennial's library with
`precompileModules = true` and globs covering the Perennial modules imported
here. Lake then also builds and loads Iris, Batteries and Qq as shared
libraries; precompiling those as well made no further difference (proofs 24m54s
vs 25m06s of CPU). Clean rebuild of this repository's 402 modules, quiet machine:

| | interpreted | precompiled |
|---|---|---|
| wall | 3m01s | 2m52s |
| CPU | 39m01s | 34m48s (−11%) |
| proofs / specs CPU | 28m19s / 6m45s | 24m54s / 6m20s |
| `Proof.RawNode__Ready` | 52s | 43.5s |
| `Proof.stepLeader` | 66s | 65s |

Interpretation drops to ~0 (16ms in `RawNode__Ready`), but part of what the
profiler had charged to it was nested work (IPM instance search went from 5.4s
to 12.2s), so the gain is the 11% measured, not the ~20% `interpretation`
suggested. The cost is native code for the dependencies: building them and this
repository from scratch went from 10m44s to 13m56s; CI caches the dependencies
per pin. To adopt it, Perennial's `lakefile.toml` needs `precompileModules = true`
and a library whose modules include everything downstream imports (e.g. globs
`["Perennial.+"]`: 481 modules, of which this repository builds 242).

---

## `confchange`: translated and proved, Lean-first

**2026-10-08 · accepted**

`confchange.Restore` and `raftpb.ConfState.Equivalent` were the two axioms about core
raft code (main's notes/STATUS.md, "The fourteen axioms"), stated because the code was
not translated. `confchange` is now translated in full
(`EtcdRaft/Code/go_etcd_io/raft/v3/confchange.toml`: `translate` unrestricted) and
`Restore` proved from its callees on the voters-only, non-joint path `newRaft` and
`raft.restore` take. `Restore.spec` is unchanged, so its callers are untouched.

**Decision:** the new functions get the same discipline as the ported ones
(`Spec/<fn>.lean`, `Proof/<fn>.lean`, linked in `Link.lean`), but have no Rocq
counterpart: they are **Lean-first**. `etc/gen-link.py` reads them from
`etc/link-lean-first.txt` (`<fn>: <callees in hypothesis order>`), so `Link.lean` can
still be regenerated. Shared vocabulary (`ConfigSimple`, `addNodeCC`, `opSpec`) is in
`InvConfchange.lean`, outside the discipline like the other `Inv*` files.

**`chain` is specified higher-order.** `chain(chg, ops...)` runs closures; its spec
takes an invariant `I : Nat → Config → Loc → IProp` on the (config, progress map) pair
and, for each `i`, the triple of op `i` from `I i` to `I (i+1)` (`opSpec`). `Restore`
instantiates `I` with "the first `i` voters are in, each with an owned `Progress`" and
proves each `chg.Simple(cc)` closure's triple from `Simple`'s spec. This keeps `chain`'s
proof independent of what the ops do.

**`checkAndCopy` consumes the originals' `Progress` ownership.** Its shallow copy
`ppr := *pr` shares the `Inflights` pointer, so the copies' `ownProgress` need the
originals' inflight rings; the originals come back as bare points-tos (dropped). On this
path they are garbage anyway (`chain` replaces them), except `MakeProgressTracker`'s
empty map, which has none to lose.

**Specs are stated for the case reached, not in general** (superseded 2026-10-12, below).
`joint` only for a `nil` outgoing map, `nilAwareDelete` only for a `nil` map,
`apply`/`Simple` only for `[AddNode id]` with `id ≠ 0`, `symdiff` with a postcondition that
said only "at most 1 under the two inclusions `Simple` establishes".

**Generalized 2026-10-12: a pure model, every function for all inputs.** Each `Changer`
method's result is a pure function of the tracker's state (`InvConfchange.lean`: `CfgM`,
`CCState`, `simpleM`/`enterJointM`/`leaveJointM`/`applyM`/...), `none` exactly on its
error paths; `checkInvariants` returns `nil` iff `CfgInv`. Choices:
- the progress map is modelled by each id's `IsLearner` only (the one field `confchange`
  touches); the specs relate the result's `Progress` values to the tracker's (`ownNewPr`: a
  copy with `IsLearner` changed, or a fresh one owning its `Inflights`), and
  `ownNewPr_transfer` moves whatever the caller holds for the originals (inflight rings) to
  the copies, so the tracker's own objects are only read (any fractions);
- `symdiff` returns the exact count modulo `2^64` (`symdiffN`); `Simple`'s check is stated
  on Go's `int` (`SymdiffTooBig`), with no size premise;
- the outgoing voter map, `Learners` and `LearnersNext` are represented canonically (`nil`
  exactly when empty, `ownIdsetC`): every operation keeps them so and `checkInvariants`
  checks two of them; an empty non-`nil` `Learners` map (legal for the Go code, never
  created by it) is outside the specs. Needed so that `Restore`'s statement, which promises
  `Learners = nil`, follows from the general `Simple`;
- the old specs are replaced, not kept beside the new ones; `Restore`'s statement is
  unchanged, and its proof derives the old `Simple` statement (`Simple_votersOnly`).
Two findings: `Config.Clone` drops `AutoLeave` (`issues/raft-config-clone-autoleave.md`);
a tracker with a `nil` incoming voter map panics (`issues/raft-changer-nil-incoming.md`,
excluded by `ownCfgCC`).

**A Goose bug found on the way.** `cc := cc` (Go's loop-local-copy idiom, used twice in
`Restore`) was translated as "allocate a fresh zero `cc`, then read `cc`", i.e. the new
cell: `defineStmt` wrapped the allocations *around* the assignment it built, so a
right-hand side naming a defined variable read the fresh cell. Every closure would have
captured `NodeID = 0`, which `apply` skips, and `Restore` would have returned "removed
all voters" -- the spec was unprovable against the translation. Fixed in Perennial's
`goose/goose.go` (c35b7710d): every define statement now binds its right-hand sides
(`$r<i>`) first, then allocates the new variables, then stores, as Go evaluates the
right-hand sides before the new names are in scope. (A first fix, 43b7fc480, did this
only for right-hand sides naming a defined variable, via temporaries `$def<i>`.) The
uniform order reorders every `:=` in the translation; in the proofs a `wp_auto` (or a
`wp_pure` workaround) right after a call sometimes has nothing left to step, since the
call's `wp_apply` now also steps the allocation that follows it.

**Rejected -- requiring `voters.Nodup` in `Restore.spec`** to skip the repeated-voter
branch of `makeVoter`. The callers have it, but the spec's comment says it is not
needed and keeping the statement identical is what makes "axiom replaced by theorem"
auditable; the branch cost ~30 lines.

---

## `ConfState.Equivalent`: `reflect.DeepEqual` is the axiom, not the raft code

**2026-10-08 · accepted**

`Equivalent` (confstate.go) sorts copies of the four id slices of both `ConfState`s
and compares the results with `reflect.DeepEqual`. Goose has no model of reflection,
so the raft code is proved and `reflect.DeepEqual` on two `ConfState` values is the
axiom (`reflect` translated names-only in Perennial, like `crypto/rand`), stated as Go's
`DeepEqual` reads on this struct: fields one by one, a slice field equal iff both nil
or both non-nil with equal elements. The nil/non-nil distinction is why the proof
tracks nil-ness: `append([]uint64(nil), s...)` is `nil` for an empty `s`, so the six
empty slices come out `nil` on both sides whatever they were (`wp_slice_append_nil_empty`,
proved from Perennial's `append`/`copy` model without ownership of `s`, since the
callers only know the lengths). Sorted permutations being equal (`sorted_perm_eq`) is
what makes the voter copies `DeepEqual`.

**The closure is proved once.** `s := func(sl *[]uint64) {...}` is called eight times;
its body is copied verbatim from the translation into `sortCopyBody`, its triple proved
for a function value `f` *fixed by hypothesis* to that literal, and the stored closure is
`generalize`d to `f` before the loop, so that `wp_auto` cannot inline it. Two triples
(owned input, input only known empty) rather than one with a disjunction, so each
returns exactly what it took and the caller frames the original voter slice.

**Rejected -- strengthening the callers' premises to `= slice.nil`** for the six empty
slices (which would have let `wp_slice_append` be used). It would change `newRaft`'s
and `raft.restore`'s statements for a fact the proof can establish itself.

---

## `raftLog.slice`: the admission was the `append` model's own assumption

**2026-10-08 · accepted**

`extend` (util.go) computes `need := len(dst) + len(vals)` as a Go `int`, and its spec
required `|dst| + |vals| < 2^63`; `raftLog.slice` could not establish it (the stable
part is bounded by `2^61`, the unstable slice only by `2^63`) and admitted it, Rocq's one
`Admitted` on the election path, "the log fits in memory" (main's
notes/false-statements.md; `InvRaftlog.lean`'s `Hnowrap` comment).

**Decision:** drop the premise. When the sum reaches `2^63`, `need` wraps negative, so
`need <= cap(dst)` holds and the code takes the `append(dst, vals...)` branch; Goose's
model of `append` (`go.append`, `Perennial/Golang/Defn/Slice.lean`) begins with
`sumAssumeNoOverflowSigned`, an *assumption* that `len(dst) + len(vals)` does not
overflow -- Goose models Go's `growslice` "len out of range" panic as an assumption,
everywhere. The overflow case is therefore vacuous under the model, and the admitted
fact was that assumption restated for one call site. `extend.wp_proof` now steps into
`append` in that case and closes it from the assumption. Nothing new is trusted:
Perennial's Go semantics already were ("Not checked by Lean").

**Rejected -- carrying a `< 2^63` bound in `ownRaftLog`** (tried 2026-09-20): no
constant bound survives `appendEntry`'s `append`, for the same reason -- which is why
the model assumes it there too.

---

## ringBuffer: a persistent-item, sorted ring

**2026-10-08 · accepted**

etcd's `cache.ringBuffer[T]` (`cache/ringbuffer.go`) is the first proof about the
`EtcdCache` translation: Lean-first, generic in `T`, in the raft discipline
(`EtcdGrove/Cache/{Spec,Proof}/`, `Cache/Link.lean`, vocabulary in
`Cache/InvRingBuffer.lean`).

**Decision 1: sortedness is part of the predicate.** `ownRingBuffer` includes `RevSorted
revOf items` (revisions strictly increasing as `sint.Z`), and `Append`'s precondition is
`RevAbove` (the new revision above the newest). `Append` is the only writer, so this is
where the invariant is enforced, and the searches and iterations can then be stated
exactly: `findFirstIndexGreaterOrEqual` returns `ltCount` (the number of items `< pivot`),
the first index `≥ pivot` only because the revisions are sorted.
*Rejected:* sortedness as a premise of the searches (each caller would re-prove a fact
of the ring's history).

**Decision 2: `isItem` is persistent.** The predicate keeps `□ (… isItem e.item' v)`, and
`Append` takes `[∀ p v, Persistent (isItem p v)]`, so the ring and the caller both keep
`isItem item v` and the iteration hands it to `iter` without taking it back. The demux's
items are `*mvccpb.Event` pointers read, never written, so `p ↦□ ev` fits.
*Rejected:* owned items (`Append` would have to return the overwritten oldest item's
ownership, and the iterations would lend and reclaim each item).

**Also decided:**
- **`cap` is a parameter** of `ownRingBuffer`, not an existential: it is fixed at
  `newRingBuffer`, and `full`'s result and `Append`'s postcondition (`ringAppend cap`)
  mention it. *Rejected:* existential `cap` (then exposed by every spec anyway).
- **`cap ≤ 2^61`** is in the predicate and `newRingBuffer`'s precondition: `at` computes
  `tail + i` and `moduloIndex` adds `len(buffer)`, up to `3·cap`; past `2^63/3` that
  wraps and `at` reads the wrong slot, and Goose's `make` does not bound the length (Go's
  allocator would). *Rejected:* only the slice's `< 2^63` (the spec would be false).
- **Closure triples as `IProp`s**, like `opSpec`: `revisionOfSpec f isItem revOf` (on any
  `p` with `isItem p v`, `f p` returns `revOf v`) is stored in the predicate;
  `iterSpec iter isItem revOf vis P Q` is the loop-invariant triple of `iter` on the
  `i`-th visited item (`P i ∗ isItem p v` to `P (i+1)` on `true`, `Q` on `false`), and
  the methods end with `ownRingBuffer … ∗ (Q ∨ P vis.length)`. The closure does not get
  the ring (the method holds it while iterating). *Rejected:* the Rocq scaffolding's
  continuation form (`own_ringBuffer -∗ Φ #()` in the closure's postcondition), which
  ties the closure's triple to the caller's `Φ`.
- **The visited lists are exact sublists**: `items.drop (ltCount …)` (ascending `≥`),
  `items.take (ltCount …)` (ascending `<`), and the reverses of `items.drop/take
  (leCount …)` for the descents.
- **`moduloIndex` is specified on the struct** (`r ↦ rb`, returning `(index + len) %
  len`), not on `ownRingBuffer`: `at` has already loaded `r.buffer` when it calls it and
  needs the same struct back. `at` is specified for in-range logical indices only (Go's
  wraps others; no caller passes one).
- **Generic specs quantify `T'`/`T` inside the `∀`** (`{T'} [ZeroVal T'] [TypedPointsto
  T'] (T) [IntoValTyped T' T]`), so each `spec` is a `Prop` and `Link.lean` has the raft
  shape; `etc/gen-link.py --cache` generates it from `etc/link-lean-first-cache.txt`.


---

## store: btree as the trust boundary, ghost state under the RWMutex

**2026-10-08 · accepted**

etcd's cache `store` (`cache/store.go`, `cache/snapshot.go`) is specified and proved
Lean-first like the ring buffer (`EtcdGrove/Cache/{Spec,Proof}/`, vocabulary in
`InvStore.lean`, the btree abstraction in `InvBtree.lean`).

**Decided with the user:**
- **The btree is the trust boundary.** `k8s.io/utils/third_party/forked/golang/btree` stays
  names-only; `ownBTree T t isItem less items dq` is an `axiom` (with `ownBTree_dfractional`:
  Perennial's `DFractional`, as `typedPointsto` is), and the seven methods the store calls
  (`New`, `Clone`, `Get`, `ReplaceOrInsert`, `Delete`, `AscendGreaterOrEqual`, `AscendRange`)
  are `axiom … .wp_proof`, stated from the Go documentation over the sorted item list
  (`btFind`/`btInsert`/`btDelete`/filters), every one assuming `StrictWeakOrder less` and a
  persistent `isItem`. *Rejected:* translating the btree (copy-on-write nodes, free lists:
  a large proof for a dependency).
- **Ghost state under the RWMutex.** The lock invariant `storeLockInv s γ cap q` (Perennial's
  guarded `ownRWMutex rw P`, `P` fractional) holds a `q`-fraction of `latest.rev` and the history
  ring, of a `monoNat` on `latest.rev`, and `q/2` of a ghost variable with the abstract
  `StoreState`; the writer (`storeWriter`) holds the other half and the latest tree; readers get
  facts about *some* state with a lower bound (`storeRevLb`).
- **Errors are package variables**: `ErrNotReady` (cache) and `rpctypes.ErrFutureRev`/
  `ErrCompacted` are `globalAddr X ↦□ interface.ok e` in the packages' `IsPkgInit` facts
  (`Base.lean`), and the specs say "the returned error is the value of that variable"
  (`globalAddr X ↦□ err`, `snapErr`), not its message.

**Decided here:**
- **The map is a sorted list of `(key, *KeyValue)`** (`KvMap`), the btree's own item list:
  `kvItemIs p (k, l)` is `p ↦□ kvItem{k, l}`, so a search probe (`kv = nil`) is an item too
  (the btree's `less` closure compares probes with items), and the `KeyValue` contents are a
  separate persistent `kvAt`. *Rejected:* `(key, KeyValue value)` entries (no `isItem` for a
  probe) and a finite map (the btree's order is the list's).
- **Readers hold a token.** `RWMutex` admits at most `actualMaxReaders` readers at once, and
  Perennial's `ownRWMutex` counts them; so `Get`/`LatestRev` take `storeReader s γ cap` (one
  `ownRWMutex`) besides the persistent `isStore`, and `newStore` returns `actualMaxReaders - 1`
  of them (the writer has one). *Rejected:* a persistent `isStore` alone (it cannot pay for
  `RLock`).
- **The ring buffer is fractional.** Readers hold `P rfrac`, so `ownRingBuffer` gained a
  fraction (`dq`, default `DFrac.own 1`, `ownRingBuffer_fractional`) and its read-only
  `at`/`moduloIndex`/`findLastIndexLessOrEqual`/`DescendLessOrEqual` specs take any fraction;
  the writing specs are unchanged.
- **`Apply`'s failure path**: `applyEvents` is the code's loop as a function: batches of equal
  revision; a failed delete (missing key) stops it with the earlier batches applied (their
  snapshots appended, the revision the last one's) and the failing batch's earlier events
  applied to the latest map, with no snapshot. So "the newest snapshot is the latest map"
  (`StoreState.Synced`) is not in `StoreInv`: it holds after `Restore` and after a successful
  `Apply` (`applyResp_synced`), not after a failed one.
- **Preconditions the code relies on**: `Apply` takes events in revision order (`EvRevSorted`;
  etcd's watch guarantees it, the store does not check, and without it the ring's revisions
  would not increase); `Restore` takes `rev ≥ latest.rev` (the readers' lower bounds stay true;
  `latest.rev ≥ 0` follows); `newStore` takes `degree > 1` (`btree.New` panics) and
  `historyCapacity ≤ 2^61` (`newRingBuffer`).
- **`IsProgressNotify` and the event-type constants are translated**, not assumed:
  `client/v3.toml` translates `WatchResponse.IsProgressNotify`, `EventTypeDelete`,
  `EventTypePut`, and `etcdserverpb.toml` `ResponseHeader.GetRevision` (two more spec/proof
  pairs). *Rejected:* axioms for them (the bodies are three lines).
- **Protobuf messages through their fields only.** `kvAt`, `eventAt`, `hdrAt` are field
  points-tos (`Key`, `ModRevision`, `Type`, `Kv`, `Revision`), never a whole-message points-to:
  a message's `TypedPointsto`/`IntoValTyped` contains the opaque `state : impl.MessageState`,
  whose generated instances are `sorry` ("axiomatized type"). `InvStore.lean` also gives the
  three messages' `TypeRepr` directly (high priority), since instance search otherwise found it
  through those `IntoValTyped` instances for every field access. (Since 2026-10-09
  `impl.MessageState` is translated as a struct and those instances are proved, so this
  is no longer about the trust base; kept as it is.)


---

## watcher, notifier, ready: logs, epochs and a framed `Once`

**2026-10-09 · accepted**

Three small concurrent components of etcd's cache, specified and proved Lean-first
(`EtcdGrove/Cache/{InvWatcher,InvNotifier,InvReady,OnceFrame}.lean`, a `Spec`/`Proof` pair
per Go function). The design was decided with the user; what follows records it and what
the proofs added.

**watcher: four predicates.** `isWatcher w γ pred` (persistent: channel, `keyPred` closure,
`Once`, invariant), `watcherOpen γ sent` (exclusive, the producer's), `watcherClosed γ sent c`
(persistent), `watcherConsumer γ received` (exclusive, the consumer's). The producer (the
demux, under its lock) and the consumer (`Cache.Watch`'s goroutine) run concurrently, so
neither can know the other's progress: each holds half of its own ghost log (`γ.sent`,
`γ.recv`), the invariant the other halves, `received <+: sent`, and the values in flight
(`chanInflight`: the buffer, or the value an unbuffered send committed) are exactly the
responses `sent.drop received.length`. The receive is the atomic update `watcher_recv_au`
(what `Cache.Watch`'s `select` needs), with `wp_watcher_receive` derived from it.
- *Rejected:* Perennial's `Spsc` idiom (the same two-log shape, but only a blocking
  `spsc_send_au`, logs of channel values rather than of `RespModel`s, and a close that parks
  the producer's permission with no persistent "closed after `sent`, cancel `c`" fact: its
  AU lemmas would have had to be redone anyway); requiring `bufSize > 0` (the unbuffered
  states cost three more cases in the invariant).

**The non-blocking send's outcome.** `enqueueResponse` returns `ok` with
`enqueueResult pred r sent ok sent'`: a response the filter drops (`filterResp = none`) is
reported delivered with nothing sent; otherwise `ok → sent' = sent ++ [r']` and
`!ok → sent' = sent`. That `!ok` happens only when the buffer is full is not stated: it is
a fact about the consumer's progress, which the producer's view cannot name.
- *Rejected:* `nonblockingSendAuAlt` with a "buffer full" `Φnotready` and a persistent lower
  bound on the consumer's count (a weak fact: "full at some point"; no caller needs it yet).

**The key filter is `GoString → Bool`**, not `→ Prop`: the closure returns a Go `bool`,
and `List.filter` needs a `Bool`; a `Prop` would need classical `decide` in every statement.

**Closing through the `Once` with a frame.** Perennial's `Once.wp_Do` takes a persistent
closure triple `{P} f {Q}` with `P`, `Q` fixed at `init_Once`, so the closure cannot use the
caller's `watcherOpen`, and the caller cannot learn that *its* closure ran (and thus which
cancel response was recorded). `Once.wp_Do_frame` (`OnceFrame.lean`, proved from `isOnce`'s
definition like `wp_Do`) lends the caller's `R` to a one-shot closure spec and returns `R'`
or `R`. The `Once`'s `P` is `cancelResp ↦ nil ∗ token γ.tok`; the closing closure leaves
`cancelResp` read-only and the token in the invariant, so a second closure (after
`watcherClosed`) is refuted by the token. `Q` is "closed after some log", and `R` coming back
with `Q` contradicts `watcherOpen`.
- *Rejected:* a persistent "intent" ghost value set by the caller before `Do` (works with the
  stock `wp_Do`, but needs a third phase in the invariant); a points-to fraction instead of
  the token (Perennial has no typed points-to validity lemma for `own 1` against `□`).

**notifier and ready: epochs on broadcast channels.** Both replace a channel on every change
and close the old one, so each channel is an `ownBroadcastChan` whose broadcast proposition
is the lower bound of the *next* epoch: the notifier's `notifierLb γ (k + 1)` for the channel
installed at count `k`, ready's `readyEpochLb γ (e + 1)` for the channel of epoch `e`. A
`wait` that reads the channel at `k ≥ k0` and receives learns `k0 + 1`. `ready`'s state is
not ghost: it flips exactly when the epoch increments, so in epoch `e` it is
`readyParity e` (`e` odd), and the readers report `readySeen γ e0 b`.
- *Rejected:* a ghost history of ready states (`monoList`; the parity says the same).

**notifier's lock: tokens, not a persistent `isNotifier`.** Perennial's `RWMutex` (both its
specs) needs a token for `RLock`, so `wait` and `notify` take a `notifierHandle` (as the
store's readers do); the fractional lock invariant holds `q/2` of the current broadcast
channel's pending token, so that `notify` (with `P 1`) can close it.
- *Rejected:* the pending token in a separate invariant (closing would need it inside the
  channel's `closeAu`).

**`waitForState` is higher-order** (`readyPredSpec r pred P`, `P : Bool → Bool`, as the ring
buffer's `iterSpec`), instantiated by `WaitReady` (`id`) and `WaitNotReady` (`not`).

**`ErrCompacted.Error()`** is a package fact (`errorStringSpec`, `Base.lean`), not an axiom:
`rpctypes` is names-only and `ErrCompacted`'s dynamic type is unknown to the proof, so the
fact belongs with the variable's other initialization facts.

---

## Lean's module system (all files, here and in Perennial)

**2026-10-08 · accepted**

Importing cost every module ~2s and ~2 GiB, mostly loading the private part
(proof bodies, private declarations) of what it imports, which a non-`module` file
loads in full ("Build speed: importing" above).

**Decision:** every file is a `module`: `public import`s, then `@[expose] public
section`, so every declaration stays public and every definition's body visible,
as before; only what importers load changes. Perennial does the same (converted on
branch `lean-modules` from `lean` at 584b17c54, merged into `lean` at 2b8cb96a0 on
2026-10-09), and its Goose
translator and proofgen emit generated files in that form, so `etc/goose.py
--check` still holds. What the conversion needed besides the mechanical part:

* code run during elaboration (elaborators, delaborators, unexpanders, helpers,
  `initialize`d caches, `register_option`s read by tactics) is `meta`;
* a core simproc cannot be added to a simp set from a module (the attribute wants a
  `meta` declaration): `word` passes them at its `simp only` calls and
  `goose_wp_simp_extra` gets a local `dsimproc` wrapping `Int.reduceToNat`;
* imports a dependency makes privately are no longer visible (Perennial's
  `GMap.lean` imports `Batteries.Data.List.Perm` itself);
* a private declaration cannot appear in a public body: `private local instance`
  became `local instance` (Perennial), and the sealed `ownRaftPhys`, whose body is
  the private `ownRaftPhysDef`, is `@[no_expose]` (its body stays in its file, which
  is what the sealing meant).

Checked: every root statement, type, axiom and `sorry` of this repository and of
the Perennial definitions its statements reach (6517 entries) hashes the same as
on `lean`; 44 definition bodies (derived `DecidableEq`, `Countable`,
`typed_pointsto` instances, ...) differ, and with their proof subterms erased all 44
hash the same: the module system only compiles the proofs inside them differently.

Measured (2026-10-08, the machine shared with other builds, so no whole-build
times yet): a compile's peak memory 1.8 GiB instead of 2.8 GiB; a spec module
(almost all import) 2.1s of CPU instead of 2.6s; `import Perennial.Proof.ProofPrelude`
from a `module`, 1.3s and 0.97 GB instead of 1.75s and 1.84 GB.

## Layout by kind and Go package path

**2026-10-08 · accepted**

`EtcdRaft/`, `EtcdCache/`, `EtcdGrove/Raft/` and `EtcdGrove/Cache/` were ad hoc. **Decision:** as in
Perennial, by kind and then by Go package path, modules named after their paths:

* `Code/<pkg>`, `GeneratedProof/<pkg>`: the Goose translations (goose's
  `-lean-root PKG=`, the empty root, added to Perennial's translator for this:
  modules `Code.go_etcd_io.raft.v3`, ...);
* `Spec/<pkg>/<fn>`, `Proof/<pkg>/<fn>`: a Go function's spec and proof under its
  package, read off the spec's name (`tracker.Progress.MaybeUpdate.spec`:
  `go_etcd_io/raft/v3/tracker`; `big.NewInt.spec`: `math/big`), the file name without
  a leading `<package>_` (`tracker_NewInflights` -> `.../tracker/NewInflights.lean`);
  `etc/gen-link.py` finds a Rocq function's files by either name;
* `Proof/go_etcd_io/raft/v3/`: the Raft proof's shared definitions (`Protocol`,
  `Defs`, `Inv*`, `StepLemmas`, ...), `Link` and `Results`.
* `Proof/go_etcd_io/etcd/cache/v3/`: the same for the `cache` package's proofs
  (`Base`, `Inv*`, `OnceFrame`, `Link`); its functions' specs and proofs sit there
  too, except the btree's (`{Spec,Proof}/k8s_io/utils/third_party/forked/golang/btree/`),
  `ResponseHeader.GetRevision`'s (`.../etcd/api/v3/etcdserverpb/`) and
  `WatchResponse.IsProgressNotify`'s, the `Op` getters', `getPrefix`'s and
  `GetPrefixRangeEnd`'s (`.../etcd/client/v3/`).

One Lake library `EtcdGrove` globs the four directories (no root module). Lean
namespaces are unchanged (`Perennial.EtcdGrove.*`, `Perennial.go_etcd_io.raft.v3.*`),
so only module names and paths moved; private names embed their module, so the
check above compares them without it.

**Rejected — package path first** (`go_etcd_io/raft/v3/{Code,Spec,Proof}`): it would
need the translator to put the package before the kind, unlike Perennial.

---

## google/btree: a second proof tree, `EtcdGrove/Btree/`

**2026-10-08 · accepted**

etcd's watch cache (`etcd/cache`) keeps its snapshots in a B-tree, so the cache's proof
needs one. The cache imports `k8s.io/utils/third_party/forked/golang/btree`, a fork of
google/btree's generic `BTreeG`; this proof is of google/btree itself (`aeba20f`,
`btree_generic.go`; `btree.go` is its pre-generics twin, excluded by its build tag), the
upstream of that fork.

**Decision:** translated into `GoogleBtree/` by `etc/goose.py` (now a list of
translations), proved in `EtcdGrove/Btree/` with the Raft proof's discipline: one
`Spec/<fn>.lean` and one `Proof/<fn>.lean` per Go function, a proof importing only its
callees' specs. The predicates are in `Defs.lean`, the pure model in `Tree.lean` /
`Model.lean`.

**The top-level predicate** is `ownBTree o t dq s`: the tree at `t` holds the entries `s`
at fraction `dq` (mutations and `Clone` need `DFrac.own 1`, reads any fraction).

- **Keys, not items, are ordered.** `s : List (V × K)` pairs each Go item with a key,
  keys strictly increasing under a strict total order `o.lt`, and `o.item v k` is a
  persistent relation between an item and its key; `less` must decide `lt` on the keys
  of the items it is called with (`isLess`). The cache's items are `*kvItem`s compared by
  an immutable `key` field: there `item p k` is the persistent points-to of `p.key`, which
  a pure order on `V` could not express (the keys are only known from the heap). For an
  ordered type, `item v k := v = k` (`orderedOrder`). Requiring a strict *total* order
  costs nothing: a strict weak order on items is a total one on its classes, which the
  client takes as keys.
- **Copy-on-write ownership.** A tree owns the nodes whose `cow` is its context and
  mutates only those; `Clone` gives both trees fresh contexts, so every existing node
  becomes shared and, since every write goes through `mutableFor`, read-only forever.
  `ownNode` is per node either owned (fractional points-tos, children `ownNode` again) or
  `frozen` (persistent, with every node below frozen too and known to have a different
  context: `n.cow == cow` is a pointer comparison). `Clone` therefore needs the distinctness
  of the fresh contexts from every node's context, from the points-to validity rule.
- **The shape invariant** (`Tree.Shape`): uniform height, `len(children) = len(items) + 1`,
  non-root nodes between `d - 1` and `2d - 1` items, an internal root with an item. The
  code needs it for safety, not only for balance: a merge of children of different
  heights, or a root left without items whose only child is minimal, makes `remove` index
  out of range.

**Rejected -- `node.print`'s spec.** It is unexported debug output (only the tests call
it) through `fmt.Fprintf` and `strings.Repeat`, which Perennial has as names only; a spec
would need new trusted axioms about `fmt`, for no client.

---

## Perennial's `copy` was not Go's: now a memmove

**2026-10-08 · accepted (in Perennial's `lean` since 2026-10-09, `e9cba5d`)**

Perennial modeled `copy(dst, src)` as a front-to-back loop in place. Go's `copy` allows
overlapping slices; when `dst` starts past `src` in the same array the loop reads
elements it has already overwritten. `items.insertAt` does exactly that
(`copy(s[i+1:], s[i:])`), so under the old model insert provably corrupts the tree, and
no correct spec of it can be proved. (Every existing proof used `wp_slice_copy`, whose
separate ownership of the two slices excludes overlap, so none relied on the bad case.)

**Decision:** in Perennial, `copy` runs the old loop (`slice.copyForward`) twice, through
a fresh buffer holding all of `src`; `wp_slice_copy` keeps its statement, and
`wp_slice_copy_within` specifies a copy between two parts of one slice (`insertAt`,
`removeAt`). In Perennial's `lean` (and pinned here) since 2026-10-09.

---

## The btree proof is of the cache's fork; the cache's btree axioms are gone

**2026-10-09 · accepted** (supersedes "store: btree as the trust boundary" for the btree)

The btree proof (above) was of google/btree, while the cache uses the k8s fork
(`k8s.io/utils/third_party/forked/golang/btree`), translated names-only with seven
axiomatized specs over an axiomatized `ownBTree`.

**Decision:** the fork is translated with bodies, in the `etcd` project, and the proof
moves onto it (`Spec/`/`Proof/k8s_io/utils/third_party/forked/golang/btree/`, namespace
`btree`, so that the spec names are those the cache already used: `btree.BTree.Get.spec`,
`btree.New.spec`); google/btree's translation is dropped. One Hoare triple per Go
function: the proved spec *is* the fork's spec, and the cache's former statements become
model-level triples (`btree.<M>.modelSpec`, `InvBtree.lean`) that each store proof derives
from it on its first line (`btree.<M>.modelSpec_of`). The cache's `ownBTree` is defined
over the btree's: the store orders models (`KvEntry`, by key) by a strict *weak* order,
the btree orders keys by a strict *total* one, so the keys are the classes of the weak
order's incomparability (a quotient), and each entry is related to its model by
`isItem`. Of the axiomatized `DFractional` the store used only persistence at
`DFrac.discard` and `dq ==∗ discard`, which are proved instead.

`etc/gen-link.py --cache` links the store against the btree's results, which
`etc/gen-btree-link.py` links in the btree's own `Link.lean` (`fn: @` in
`etc/link-lean-first-cache.txt`).

**Found on the way:** the assumed `btree.New` spec asked only `1 < degree`; above `2^62`
the btree's `maxItems()` overflows and the second insert panics. `btree.New`, `newStore`
and `isStore` now require `degree <= 2^62`.

**Rejected -- keeping the cache's statements as the btree's specs** (and the proved ones as
a second triple per function): two specs per Go function, which the discipline forbids.
**Rejected -- restating the store's proofs on the btree's interface**: the model-level
triples are what the store reasons in; deriving them once keeps those proofs unchanged.

---

## demux: the delivery invariant under the lock

**2026-10-09 · accepted**

etcd's cache `demux` (`cache/demux.go`), Lean-first, one `Spec`/`Proof` pair per Go function,
vocabulary in `InvDemux.lean`. The design (decided with the user): the point of the spec is a
per-watcher delivery guarantee, an invariant of the demux's lock that every method keeps; the
methods' functional behavior is stated on an abstract state.

**Decided with the user:** the writer's state `DemuxCore` (with the ghost `stream`) and its
transitions (`initCore`, `broadcastCore`/`updResp`/`updCore`, `DemuxCore.init`), taken and
returned by `Init`/`Broadcast`/`Purge`/`Compact` with `demuxWriter`; the other goroutines
(`Register`, `Unregister`, `BroadcastProgress(To)`, `LatestRev`, resync) work from `isDemux`
and a handle; the delivery facts (`Delivered`: the events sent are the stream's from `s` to
`n`, filtered; the log ordered; progress notifications trustworthy); the registration token
with two outcomes (in a map, or closed by purge/compaction); `minRev` stated as a bound, not
the oldest revision; the overflow premise on `Broadcast`.

**Decided here:**
- **Maps.** The Go maps are Perennial `GMap Loc w64` (`ownMap`), and are *functions of the
  views*: `actOf views`/`lagOf views` (the active/lagging views' `n`). The lock's pure facts
  (`RegsOk`) are then about the views only, and an update is one ghost-map write plus the
  matching `insert`/`delete` (`actOf_insert`, ...). *Rejected:* separate maps with a relation to
  the views (every step re-proves the relation).
- **The ghost split.** The writer holds half of `γd.core`; the lock the other half. The
  registrations (`γd.reg`, keyed by the watcher's address: the token is the entry) and the
  views (`γd.views`, an entry in each registration's `regRes`) are internal to the lock.
- **Per-registration resources outside the fractional lock invariant.** `BroadcastProgressTo`
  sends to `w` under `RLock`, which gives only a fraction of the lock invariant, but the send
  needs the exclusive `watcherOpen`. So each registration's `regRes` is in a slot of a
  separate invariant `demuxSlots`: `Lock` takes all slots (`demux_lock_acquire`, leaving the
  whole writer token `wtok 1`, which no reader can hold), `Unlock` puts them back; `w`'s
  registrant borrows its own slot under `RLock` (`demux_slot_borrow`/`return`, leaving half of
  its `wtok` fraction and half of its entry). *Rejected:* the resources in the lock invariant
  (not fractional); per-registration invariants (`Lock` would open one per watcher).
- **Mapped views are current.** A mapped watcher's view is the current stream and `maxRev`
  (`RegsOk.mapped`), so `Broadcast` refreshes them all at once (`regRes_refresh`, the facts
  survive an extension above `maxRev` because `n ≤ maxRev + 1 ∨ n = s`); a closed watcher's view
  is frozen. *Rejected:* lazily refreshed views (a reader's progress at the current `maxRev`
  would need the view updated, and readers cannot write the views' auth).
- **The token's two outcomes** are the view's phase (`RegPhase.mapped`/`closed c`), with the
  producer view `watcherAt γ sent phase.toWatcher`; `Unregister` returns the closed one after
  `Stop`. The key filter is pinned by a saved predicate (`predIs`), as functions are not
  countable.
- **Freshness.** `Register` needs `w` not registered; from `watcherOpen γ []` and the lock's
  `watcherOpen`/`watcherClosed` for `w` this follows only if `w` has one ghost name, so
  `Register` takes `watcherUnique w γ` (`watcherOpen_excl`, added to `InvWatcher.lean`, rules
  out the same name). A second registration of the same `w` would break delivery (the code
  overwrites one map entry and may leave `w` in both maps). *Rejected:* keying registrations by
  a fresh id (the double registration is unsafe anyway).
- **`minRev`.** `DemuxInv.hist_complete` (every stream batch at or above `minRev` is in the
  history) is what resync uses. The planned "`minRev` ≤ every history revision" is false
  against the code (`Init(100)` then an event at 5: `validateRevisions` checks `maxRev` only),
  so it was dropped rather than made a premise of `Broadcast`; nothing needs it.
  `updCore` states `minRev` in closed form (bumped iff the *last* append evicted), which the
  code's extra bump before the second-to-last append does not change.
- **The resync closure's invariant** (`iterSpec`): `P i` = the watcher's `watcherOpen`, the
  `nextRev` cell at `resyncNext n vis i` and `resyncSuccess` true, with the delivery facts at
  that `n`; `Q` = the same at the batch a send failed on with `resyncSuccess` false. Since
  `n ≥ minRev`, the batches `AscendGreaterOrEqual(n)` visits are exactly the stream's from `n`.
- **The map loops that write the map** (`broadcast*Locked`, resync) use
  `wp_map_for_range_mut_keys` (`MapRangeMut.lean`), the one `sorry`: Go allows changing the
  current key during `range`, Perennial's `map.forRange` keeps the map read-locked for the whole
  loop (a Perennial gap, documented in the file; the fix is a Go-faithful `forRange`). The
  invariant takes the key list, as `wp_map_for_range`'s does.
  *Since 2026-10-09* the fix is in Perennial (`6519b44f5`): the lemma is Perennial's
  `wp_map_for_range_mut_keys` (`Perennial.Golang.Theory.Map`, same statement), proved, and
  `MapRangeMut.lean` is gone.
- **`context`'s `closedchan` fact** (2026-10-09). Perennial's `context.isInit` held
  `closedchan`'s channel ghost state, so `[AllG GF]` would have been needed by every
  `IsPkgInit` instance of an importer of `context` and by about 640 raft, cache, client and
  server spec and proof files. Instead (Perennial `3ae7dc6a4`) `isInit` keeps only the
  points-to, and the ghost facts are the persistent `context.isClosedchanInit`, carried by
  every `*cancelCtx` (`isCancelCtxOf`). So `wp_WithCancel` gets it from its parent's
  `isCancelCtxCtx`, and only `WithCancel(Background())` takes it as a premise. On the cache's
  side, `New` and `newCache` take it (a package-init fact of `context`, established by a
  program's `main`). `isCacheFields` does not carry it: it carries `isCancelCtxCtx` of the
  internal context, which contains it.
  *Rejected:* adding `[AllG GF]` everywhere, which changes every raft and server spec for a
  fact only the cache's `newCache` uses.
- **`resyncLaggingWatchers`'s outcome** (`ResyncStep`) is stated existentially over the lock's
  views at acquire and release: it is invisible outside the lock, so the statement is weak.
  *Rejected (for now):* a ghost trace of the lock's states, which would anchor it but changes
  every lock-taking proof.
- `LatestRev` gives no lower bound (purge resets `maxRev`).


---

## Key predicates and request validation: keys as strings, a partial `Cache` predicate

**2026-10-09 · accepted**

`cache/predicate.go` and the request-side helpers of `cache/cache.go`, Lean-first
(`InvCache.lean`, a `Spec`/`Proof` pair per Go function).

- **`bytes.Compare` is a trusted model in Perennial**, not an axiom here. Go implements it in
  assembly (`internal/bytealg`); Perennial's `TrustedCode/bytes.lean` models it as a string
  comparison and proves `bytes.wp_Compare`, so the trust is the model's (as for `sync.Mutex`)
  and the TCB report is unchanged. *Rejected:* `axiom bytes.wp_Compare` here (a new axiom for
  a standard-library function); rewriting the fork to compare `string(k)` (changes the
  verified code).
- **A `[]byte` key is its contents, a `GoString`**, and the predicates are `GoString → Bool`
  in `go.GoStringLt`, the store's order, so `keyPredForRange` is literally `kvRange`'s test
  (`kvRange_eq_filter`). The closures capture the slices, so `ExactKey`/.../`KeyPredForRange`
  take them `↦*□` (the persistent `keyPredSpec` cannot own them); `validateGet`/`Watch`
  persist the fresh `[]byte(key)` and use the `Op`'s range end read-only (`opAt`), and
  `getPrefix` returns its slice `↦*□` (it may be the shared `noPrefixEnd`).
- **`isCacheFields` is partial and parameterized by `CacheFields`** (the four field values),
  `γr`, `γd`, `cap`: the request-side specs need only those fields, and the `Cache` stage
  will define its predicate as `isCacheFields ∗ …` rather than change these specs.
  *Rejected:* the full `Cache` invariant now (it depends on the `Get`/`Watch` design).
- **`Op` getters are specified through a pointer** (`opp ↦{dq} op ∗ opAt op o`), as the
  cache calls them (`op` is a local variable), like the store's `IsProgressNotify`; `OpModel`
  holds what the cache reads, not the whole `Op` (`cmps`, `thenOps`, `val`, … are unused).
- **Unsupported options give "some non-nil error"**, not `ErrUnsupportedRequest` wrapped
  (`fmt.Errorf`'s spec is Perennial's `sorry` and says only that).


---

## The etcd model: `isEtcdKvs` and the client's `Get`/`Watch` as the trust boundary

**2026-10-09 · accepted**

`Cache.Get`'s point is that its answer is etcd's: the key-values it returns are etcd's state
at some revision. Nothing in the cache's code can establish that (the cache only copies what
the client hands it), so the statement needs a model of etcd and a statement of what the client
promises about it (`InvEtcd.lean`). The design (decided with the user; adjusted here where
noted):

- **Why a model at all.** Without one, `Get`'s specification can only say "the snapshot the
  store holds", which is circular: a cache that returns garbage satisfies it as long as it
  returns its own garbage faithfully. The Rocq development's `is_etcd_kvs` (an axiomatized
  predicate on etcd's state) is the precedent; this is its Lean counterpart.
  *Rejected:* no link to etcd (the specs stop at the store's state).
- **`etcdState rev pfx s` is an axiom, persistent by construction, with agreement.** It says
  that etcd's state at revision `rev`, restricted to the keys with prefix `pfx`, is `s`. etcd's
  revisions are immutable, so the fact is persistent (`isEtcdKvs` uses it under `□`, so no
  persistence axiom is needed), and there is one state per revision (`etcdState_agree`, the
  only property axiom). Nothing else about etcd is assumed: the facts are produced by the
  client's statements.
- **Contents, not pointers (a change from the plan).** The plan stated the axiom on the store's
  `KvMap` (entries `(key, *KeyValue)`) with agreement `m = m'`. But every response allocates
  fresh `KeyValue`s, so two `Get`s at the same revision (or a `Get` and the watch stream)
  return equal contents at different pointers, and agreement on pointers would be false of
  the real client: the axioms would be unsatisfiable by the code they describe. So
  `etcdState` is about `EtcdKv` values (key, value, create/mod revision, version, lease), and
  `isEtcdKvs rev pfx m` (a definition) says that `m`'s `*KeyValue`s hold, in order, the contents
  of such a state (`kvValAt`, read-only field points-tos, as the store's `kvAt`), keys strictly
  increasing with prefix `pfx` (a pure side condition, not an axiom). Agreement becomes
  `isEtcdKvs_agree`: same keys, same contents.
- **The client's `KV.Get` is a definition, not an axiom (a change from the plan).**
  `isEtcdKV kv pfx` is the triple of `kv.Get(ctx, key, opts...)` (as Perennial's `isLocker` is
  the triple of `Lock`/`Unlock`), at the strength of etcd's documented API: any error; on
  success, a response header revision at which etcd had a state, and for a prefix get
  (`OpFull.isPrefixGet`) the response's `Kvs` are exactly that state. Defining it rather than
  axiomatizing it moves the assumption to where a `KV` comes from: the cache's specs take
  `isEtcdKV c.kv prefix` as a premise (in `isCacheFields`), and the Cache stage (`New`, which
  takes `client.KV`) will have to assume it of the client, as the one axiom about
  `clientv3.Client`. The options are modelled through their closures' triples (`optSpec`), and
  `OpFull` covers every field `Op.toRangeRequest` sends, so the triple cannot be fooled by an
  option the model does not see.
- **The store takes a certificate parameter `E`.** The store's lock-protected predicates
  (`storeLockInv`, `storeReader`, `storeWriter`, `storeLockedPhys`) take
  `E : w64 → KvMap → IProp GF`; each history snapshot carries `□ E r m` (the ring's item
  predicate is `snapCert E`, so no separate list in the lock invariant), `Restore`/`Apply` ask
  for it of what they append (`applyEventsSnaps`, `applyRespSnaps`: every snapshot appended,
  also those a full ring evicts again within the same `Apply`), `getSnapshot`/`Get` return it.
  The cache instantiates `E := etcdCert prefix` (`isEtcdKvs r prefix m`). The store stays
  generic: it neither knows nor needs what `E` means, and `isStore`, `storeSeen`,
  `storeRevLb` do not take it. *Rejected:* `E` persistent by a typeclass premise (the `□`
  does the same with no instance plumbing); `E` in the store's predicates fixed to
  `isEtcdKvs` (would make the store depend on the etcd model); certifying only the snapshots
  that survive in the ring (the ring's invariant needs every item certified when it is
  appended).
- **`revCond`'s locker.** `isStore` now fixes `revCond`'s locker to `s.mu.RLocker()`
  (`sync.rlockerOf`), and Perennial (`sync_proof/rlocker.lean`) translates and proves
  `rlocker`'s `Lock`/`Unlock` (the guarded `RLock`/`RUnlock`). Perennial's `isLocker`'s `Lock`
  takes nothing, but `RLock` needs a reader token, so Perennial gained `isLockerWith i Pre P`
  (`Lock : Pre → P`, `Unlock : P → Pre`) and `Cond.wp_Wait_with`; the waiter's reader token is
  the one it `RLock`ed with. No gap remained.

---

## The stream model: `EtcdStep`, certificates through the demux

**2026-10-09 · accepted** (the design decided with the user, adjusted here where noted)

`Cache.Get`'s etcd model (`etcdState`, `isEtcdKvs`) says what a snapshot *is*; the watch side
needs what etcd *did* between two revisions, so that the store's snapshots appended from the
watch stream are certified (`snapCerts (etcdCert pfx)`) and `Cache.Watch`'s answer can be stated
against etcd. `InvEtcd.lean`, `InvDemux.lean`, `InvWatcher.lean`, `InvCache.lean`.

- **One new axiomatized predicate, `EtcdStep r0 r1 pfx evs`** ("no event under `pfx` strictly
  between `r0` and `r1`; the events at `r1` are `evs`; `r0 ≤ r1`, `r0 < r1` if `evs ≠ []`"),
  over etcd's events as etcd stores them (`EtcdEv`: type and `EtcdKv` contents, not the
  store's `EvModel` with its `*KeyValue` pointer: contents, not pointers, as for `etcdState`),
  with two property axioms: **transfer** (`etcdState a pfx s` for any `a` with `r0 ≤ a < r1`
  gives `etcdState r1 pfx (applyEvsState s evs)`) and **composition** (a step with no events,
  then a step, is a step). *Changes from the plan:* (1) a `Prop`, not an `IProp`: etcd's history
  is immutable and resource-free, so the fact is persistent and timeless without the plan's
  persistence axiom, and it can sit in the watcher's invariant (opened without later credits)
  — an `IProp` axiom would have needed a persistence and a timelessness axiom; (2) transfer from
  any `a ∈ [r0, r1)`, not only from `r0` (same meaning: nothing changed in between): the
  certificates the demux hands a watcher chain from *some* revision at most the previous batch's
  (below the watcher's start), and the store's map is etcd's state at its own revision, which
  can lie anywhere in that interval; the plan's exact transfer would have needed a fourth
  "splitting" axiom. *Rejected:* `EtcdStep` over `EvModel` (pointers; the bridge needs the
  contents); a splitting axiom; exact chains in the demux (the writer cannot always produce
  them: after a re-watch at an earlier cursor, see below).
- **The bridge** `isEtcdKvs_step` (proved): a map that is etcd's state at `Y`, a step `p → r`
  with `p ≤ Y < r`, and a batch the store applies without failure (`applyBatch`) whose events
  match the step's (`evsMatch`: type, key, revision, and each `*KeyValue` holds the contents),
  give etcd's state at `r` (the store's `btInsert`/`btDelete` act on the same positions as
  `applyEvsState`'s, `btInsert_map`/`btDelete_map` through the pair list `PairsOk`).
- **The client's watch** `isEtcdWatcher w pfx` is a definition (like `isEtcdKV`): `Watch` with
  a prefix watch's options from `rev > 0` returns an SPSC channel (Perennial's `Spsc` idiom)
  whose `i`-th response satisfies `watchRespOk` from the watch's position before it to the one
  after (a monotone list `γ.cur` of positions, the consumer holding its current one): an error
  (`resp.Err() ≠ nil`), the created notification, a progress notification `p ≥ cursor` with
  `EtcdStep cursor p pfx []`, or sorted events above the cursor, below `2^63 - 1` (etcd's
  revisions; the demux's `RespRevsBounded` premise), whose batches chain exactly
  (`watchChain`). The receive is the atomic update `etcdWatch_recv_au` (for `select`).
  *Rejected:* a bespoke channel invariant (the `Spsc` idiom already has a per-position resource,
  and the positions' monotone list gives the chaining between responses).
- **The demux is parameterized by a certificate** `C : DemuxCert GF` (`cert p b`, timeless):
  the lock holds the stream's chain `certChain C base stream` (each batch above the previous
  one's revision, certified from *some* `p` at most it: a loose chain), with `DemuxCore.base`
  the revision the stream starts after (`Init(m)` sets it to `m - 1`). `Broadcast` takes, for an
  accepted response, `respCert C c r` (its batches chained from the stream's last batch, or a
  progress notification at or above `base`). The cache's `C` is `etcdStepCert pfx` (the batch's
  events are etcd's, with a step from `p`). *Decided here:* indexed by the *previous batch*
  (not by `maxRev`): progress notifications are not in the stream; the writer composes them
  into its own knowledge (`TailOk`: nothing changed between the last batch and its cursor) and
  certifies the next batch from at most the last batch (`etcdStep_compose`), or from its cursor
  when the cursor is behind the last batch (a re-watch from the original `rev`): that is why the
  chain is loose. *Rejected:* exact chains (above); certificates indexed by `maxRev` (the
  chain would then need the progress steps in the stream, changing every demux statement).
- **Delivering the certificates to the consumers: the watcher publishes.** The demux's facts are
  under its lock; the consumers (`applyStorage`, `Cache.Watch`'s goroutine) never take it. So
  the watcher gained a publication parameter `Pb : WatcherPub GF` (timeless): its invariant
  holds `Pb.pub none L` for every log `L` the producer had (every prefix of `sent`) and
  `Pb.pub (some c) sent` once closed; `enqueueResponse` takes the publication of the log the send
  would make, `Stop`/`Compact` that of the closed log (`watcherClosePub`); the consumer learns it
  at each receive (`watcher_recv_au`). The demux's publication `demuxPub C pred sr` is the
  delivery facts (`Delivered`, for the start `s` — the one `Register` was given, `sr`, unless `0`)
  and the delivered segment's certificate chain from a `p₀ < s`. For that the lock keeps
  `RegsStart` (each mapped registration started from `0`, after `base`, or is lagging at its
  start: a watcher whose start is at or below `base` is compacted before it is sent anything,
  since `base < minRev`), with three new `DemuxInv` fields relating `base` to the stream,
  `minRev` and `maxRev`. `demux_watcher_delivered`/`Unregister` are unchanged.
  *Rejected:* the facts only under the read lock (`demux_watcher_delivered`: the consumers do
  not take it); a per-response attachment (the consumer needs the whole prefix's facts, and the
  log-indexed publication gives them with one invariant field).
- **`watcherUnique w`**: half of `w.keyPred`'s points-to, the other half read-only in
  `isWatcher` (`newWatcher` splits it); two of them for one `w` contradict (own ½ + own ½ +
  discarded is invalid, `watcherUnique_excl`). Each registration keeps its own, so `Register`
  knows `w` is new. *Rejected:* the old persistent "one ghost name per address" (not
  derivable: Perennial has no meta tokens and `isChan` has no name agreement); a ghost token
  (it would not be tied to `w`).
- **The SPSC channels of `Cache.Watch`**: `rc`'s `i`-th response comes with a log `L` of length
  `i + 1` (an element of the monotone list `γ.fwd`) that is a `cacheWatchLog`: a published log of
  the watcher, or one closed by a compaction followed by its cancel response, or the single
  cancel of a rejected request. `cacheWatch_delivery` turns a published log into the statement
  about etcd.

## The watch loop is verified against the fixed code

**2026-10-09 · superseded the same day** by "No code changes unless a bug" (below): the verified
code is now upstream main plus the readiness fix only; the other two fixes are reverted.

`Cache.watch`, `getWatch` and `getWatchLoop` are proved against etcd's cache with three fixes
(fork branch `cache-ready-after-retry`, merged into `goose-lean` at `6ab61a1c7`), not against
upstream's code, which has two findings (STATUS, "The watch loop and Cache.Watch"): (1) two
writers of the store (an iteration's `applyStorage` goroutine was not waited for, so it could
`Apply` concurrently with the next iteration's or the next `get`'s `Restore`; harmless only by
`validateRevisions` and etcd's linearizability), and (2) the cache could stay not ready after a
retry (`Init` purged the demux after the store watcher was registered, under a `Once` that never
ran again). The fixes: `Init(rev)` once, before the loop, with the `Once` only setting `ready`
(`64313a1f8`); the upstream watch in a child context canceled when `watchEvents` returns
(`21ac13e0d`); `watch` waits for `applyStorage` after `Unregister` by receiving from `applyErr`,
returns its error if `watchEvents` did not, and the goroutine no longer joins `c.waitGroup`
(`a7de41a72`; the wait makes it redundant, and an `Add` per retry whose `Done` is not awaited
would leave the wait group's `int32` counter unbounded, so the loop could not be proved with
`cacheWgInv`'s finite budget).

- **One writer, a token.** The store's writer (`storeWriter`) threads through `getWatchLoop`,
  `get`'s `Restore` and `watch`; each iteration hands it to its `applyStorage` goroutine and gets
  it back through `applyErr`, modelled as a **handoff** channel (`Handoff.lean`, a generic idiom:
  the producer sends at most one value then closes, handing over `P v ∗ Ws` with the value or
  `Wc` with a close that follows none; the consumer takes it at its first receive, which may be
  `watchEvents`'s `select` or the wait, and may receive the close again). With the error the
  goroutine hands over just the writer; with the close, the writer at a synced state whose
  latest map is etcd's state at some revision (`watchWc`), which the next iteration's
  `applyStorage` needs. *Rejected:* Perennial's SPSC idiom (its consumer token is consumed by the
  receive of the close, but `watch` receives the close a second time after `watchEvents` did; and
  its close resource is separate from a value's, so receiving the value would not give the
  writer); a multi-writer store spec (the writer's state and latest tree in `store.mu`'s
  invariant, `Apply`/`Restore` for any state, a cache-level invariant tying revisions to etcd's
  linearizability): what the unfixed code would have needed, and a weaker statement of the
  store than the single writer the fixed code has.
- **`applyStorage`'s spec is generalized** to a store watcher starting at `s ≤ R + 1` (it was
  `s = R + 1`) when `R` is at most the store's latest revision: every iteration registers its
  watcher at the loop's first revision, so after the first the demux replays batches at or below
  `R`, which `Apply` rejects (`applyResp_stale`); on `nil` it now returns the store's
  certificate (`isEtcdKvs R'` of the latest map, `R ≤ R'`). The old statement is the case
  `s = R + 1`.
- **`watchEvents`'s spec** takes the demux initialized by the caller (`CursorOk` at `rev - 1`),
  a `Once` with trivial resources (Perennial's `Once.wp_Do`; `OnceFrame` is no longer needed
  here), and returns what it took from `applyErr`.
- **etcd's linearizability** for `get`, a premise of `getWatchLoop`: `isEtcdKVLin cf` (for every
  revision the store has reached, `storeRevLb`, a prefix get returns at least it). `isEtcdKVFrom`
  also bounds the revision below `2 ^ 63 - 1`, as the watch contract does, so that `getWatch`'s
  `rev + 1` does not overflow. (Superseded 2026-10-09 by `etcdReached`, "`New` and the client":
  no premise; the bound is in `isEtcdKV`'s result.)

## No code changes unless a bug: the shared-writer store and the WaitGroup assumption

**2026-10-09 · accepted**

The user's rule: no change to etcd's code unless it fixes a bug. Of the fix branch's three
commits only `64313a1f8` (the cache could stay not ready after a retry) fixes one; `a7de41a72`
(`watch` waits for `applyStorage`) and `21ac13e0d` (cancel the upstream watch) do not, and are
reverted (`goose-revert`, `ab1deb078`). The proofs fit the code as shipped.

- **Why the two are not bugs.** The drain (an old iteration's `applyStorage` still applying its
  stopped watcher's buffered responses beside the next iteration or the next `Restore`) is
  harmless: the store serializes its writers on `mu`, `validateRevisions` rejects whatever does
  not follow the store's latest revision, and the next `Get`, being linearizable, returns at
  least every revision a drain can apply. The open upstream watch is a resource leak, not a
  correctness issue (a finding for the maintainers).
- **The store has shared writers.** No exclusive `storeWriter`: the lock invariant alone keeps
  `StoreInv`, the certified history and `Synced`; writers hold the persistent `isStoreWriter`
  (Perennial's new `isRWMutexGuard`: a writer needs none of `RWMutex`'s bounded reader slots, and
  the loop starts unboundedly many goroutines); the latest tree, not fractional, lives in an
  invariant of its own, lent to the write lock's holder. `Restore` and `Apply` are specified for
  the state they find: `Restore` with a dominance premise (`P` with which no revision the store
  can be at is above `rev`), `Apply` with the caller's certificate for any state at or above its
  lower bound on the newest snapshot (`storeApplyCert`: the response changes nothing, or applies
  with its snapshots and revisions certified). Postconditions are existential, as readers' are.
- **The revision bound.** `Restore`'s dominance needs an upper bound on every revision the store
  can reach, including a pending drain's: a cache-level `monoNat` (`γb`) the loop alone advances,
  before each `Broadcast` and each `Restore`; the store's revision certificate and the demux's
  certificate say "at most the bound" (`cacheRev`, `cacheCert`), the loop knows etcd has reached
  the bound, so its linearizable `Get` returns at least it. *Rejected:* the demux's `maxRev` (not
  monotone: `Init` purges it to `0`); `etcdReached` alone (a lower bound: it cannot dominate).
  `Watch`'s statement keeps `etcdStepCert` (its channel's publications are weakened).
- **A model axiom: deletes are of present keys** (`etcdStep_delete_present`). With one writer a
  failed `Apply` (a delete of a missing key, which the store's model allows) was followed by a
  `Restore` before anything else wrote; with shared writers another writer could build on the
  half-applied map and append a snapshot that is not etcd's state. With the axiom (true of etcd:
  it emits a delete event only for a key it removes) a batch etcd certifies applies to a map that
  is etcd's state before it, so `Apply` never fails on a response it accepts. *Rejected:* proving
  from the demux's log that after a failure only the failing batch can be accepted again, and
  that it fails again (the steps are opaque to the model: no "nothing between" is derivable);
  a "poisoned" store state (readers' certificates would weaken).
- **`WaitGroup.Add`'s overflow is a model assumption** (Perennial `614fa61d3`). The loop
  `Add(1)`s per iteration and each `Done` runs in a goroutine the demonic scheduler may delay for
  ever, so the `int32` counter is unbounded and Go's panic on its overflow unprovable. As
  `append`'s length overflow, it is assumed: `WaitGroup.Add` is a trusted model, Goose's
  translation verbatim but for the atomic add, a compare-and-swap loop that assumes the sum fits.
  The assumption must be atomic with the add (an `assume` after Go's atomic add would be too late:
  the wrapped counter would be visible to other goroutines, whose `Done` would panic), hence the
  compare-and-swap, and `Add`'s atomic update opens at `⊤ \ ↑N` (the proof reads the state in the
  wait group's invariant before deciding to commit). *Rejected:* time receipts (bounding the
  execution to `2^31` steps, an assumption about every result); a fork change (not a bug).
  **Superseded 2026-10-10** (`STATUS.md`, "The wait-group counter and thread tokens"): the
  assumption was reachable (two `Add(1 << 30)` calls panic in Go) and is reverted in Perennial.
  The counter is bounded by Perennial's *thread tokens* instead: one per goroutine that has been
  `Add`ed and not yet `Done`, deposited by the thread that calls `Add` (its own; it gets a fresh
  one at the `go` statement), so the counter is below the thread bound `T` of the adequacy
  theorem, and `New` assumes `T + 3 ≤ 2^31` (three goroutines keep their own token). This is
  the argument the assumption gestured at (`2^31` goroutines cannot be live at once), made in
  the logic and stated once, as an adequacy hypothesis.
- *Rejected: the exclusive writer* (the previous design): it needs the loop to wait for each
  iteration's goroutine, a code change that fixes no bug.

## `New` and the client: translating `Client`, timers as the trust boundary

**2026-10-09 · accepted**

The last unit of etcd's cache package: `New`/`newCache`, `Close`, the three loops and what they
use (`InvConfig.lean`, `InvNew.lean`). The plan was decided with the user; what follows records
it and what the proofs changed.

- **`clientv3.Client` is translated, its fields' packages names-only.** `newCache` reads
  `client.KV` and `client.Watcher`, so `Client` is listed in `client/v3.toml`; its other fields
  need five more names-only packages (grpc, grpc's `credentials`, the client's `credentials`
  and `internal/resolver`, zap), under the limit of eight. One Goose bug, fixed in Perennial
  (an axiomatized generic type's Lean type). `Client.cfg` and four other fields keep
  axiomatized types, whose `sorry` instances high-priority `TypeRepr` instances for `Client`
  keep out of the trust base. *Rejected:* the axiomatized view (`clientFields` with two field
  load axioms): not needed, and two more axioms.
- **`isEtcdClient client pfx` is a definition, the assumption `New`'s caller makes**: the two
  field points-tos (persistent: the client's fields are not written after construction), the
  `KV`'s `isEtcdKV`, the `Watcher`'s `isEtcdWatcher` and `isEtcdProgressNotifier` (new:
  `RequestProgress` returns some error; etcd's progress notification shows up on the watch
  stream, where it is already modelled), and (until the fix below) etcd's linearizability for
  the caches built over the client: `□ ∀ c cf …, isCacheFields c cf … -∗ ⌜cf.kv = kv ∧ cf.pfx = pfx⌝ -∗
  isEtcdKVLin cf`. Linearizability is about the store's revision counter (`storeRevLb`), whose
  ghost names exist only once `newCache` has made the store, so it cannot be stated for a
  particular store before `New` runs. *Rejected:* quantifying over every store's ghost names
  (`∀ γs, □ ∀ lo, storeRevLb γs lo -∗ isEtcdKVFrom kv pfx lo`): any ghost counter can be
  allocated at any value, so the assumption would force every successful prefix get to return
  a revision of at least `2^63 - 2`: false of etcd, a vacuous theorem. *Deferred:* the
  temporal fact itself ("etcd has reached revision `r`", produced by the client's responses
  and carried through the demux's certificates, the store's revisions and progress
  notifications to `storeRevLb`), which would make linearizability a property of the client
  alone; it changes the demux's progress statements, the store's revision certificate and the
  watch path's specs. The stated assumption is true of a correct cache over etcd (the store's
  revisions come from this client's responses) but rests on that, which the proofs show for the
  snapshots (`isEtcdKvs`) and not for revisions moved by progress notifications.
  **Fixed 2026-10-09: `etcdReached`.** "etcd has reached revision `r`" is now a fact of the
  model (`InvEtcd.lean`): `etcdReached r` is `etcdReachedAt r'` for some `r' ≥ r` (or `r ≤ 0`),
  over two axioms, `etcdReachedAt` (an `IProp`) and its timelessness. *Why a model fact rather
  than the store's counter:* linearizability is a property of etcd and its client, so it must be
  statable before any cache exists, and the store's ghost counter can be allocated at any value
  (the rejected quantification above); a fact the client's responses produce is about etcd
  alone. It is an `IProp`, not a `Prop`, because it is knowledge obtained at a time: holding it
  means a response showed it before the holder's next call, which is what linearizability is
  about (a `Prop` would make "reached at some time, maybe later" usable now). *Why downward
  closed:* a `Get` at least `lo` is at least every `lo' ≤ lo`; the demux's progress
  notifications are at or below `maxRev`; and `0` comes free for a fresh store or demux.
  *What carries it where:* `isEtcdKV`'s triple takes `etcdReached lo` and returns `etcdReached r`
  with `lo ≤ r` unless serializable (a serializable get may be served by a lagging member: the
  exception keeps the assumption true of etcd); the watch receive gives it for created and
  progress notifications and, through `etcdStepCertBody`, each batch; the store takes a second
  certificate `R` (in the lock and the writer, `□ R latestRev`; `Restore`/`Apply` ask for it of
  the revision they move to; the cache's `R` is `etcdReached`); the demux's `DemuxCert` gained
  `prog` (the lock holds `□ prog maxRev`, a progress `Broadcast` brings it, a batch's certificate
  implies it, a watcher's publication gives it of every progress notification sent). `get` then
  calls the client with the writer's `etcdReached latestRev`, and `isEtcdClient` no longer
  mentions caches. *Rejected:* a bare axiomatized `etcdReached` with persistence, downward
  closure and zero as axioms (five axioms for what one predicate and a definition give);
  certifying the store's revision from `E` (progress notifications move it without a snapshot);
  `P` as a separate demux parameter (folded into `DemuxCert`, so no demux statement changed
  shape).
- **Timers are axioms in Perennial**, like `wp_Now`/`wp_Since`: `time.wp_NewTimer`
  (`time.isTimer t ch γ`: `C ↦□ ch`, a bag of times), `Timer.wp_Stop`, `Timer.wp_Reset` (some
  `bool`; Stop/Reset require `isTimer`, since Go panics on a timer `NewTimer` did not make).
  They over-approximate Go's timers (a stopped timer delivers nothing; the model allows it),
  which is sound for safety. *Rejected:* a trusted model (`NewTimer`'s Go body calls the
  runtime's `newTimer`, whose trusted model returns unit, and `sendTime`), a larger trusted
  base for no gain.
- **`WithCancel(Background())` is a new Perennial `sorry`**, `wp_WithCancel_Background`,
  beside `wp_WithCancel` (same reason): `Background()`'s `Done()` is `nil`, which
  `isContext` excludes, so `wp_WithCancel` does not apply; `wp_Background` (proved) gives the
  value.
- **The wait group and `Close`.** `Close` waits (`Wait`), which needs Perennial's waiter
  token; Perennial's `Add` from zero needs no registered waiter, so a `Watch` (`Add(1)`) and a
  `Close` must not overlap. The "open" token `cacheOpen cf q` (a fractional ghost variable)
  enforces it: `Watch` takes a fraction, `Close` the whole, which it deposits in
  `cacheWgInv` while registered. Nothing comes back through the wait group (the loops'
  writers stay in the goroutines), so `Close`'s postcondition is the token. Go's own
  implementation would not panic here (a waiter registers only while the counter is positive
  and the last `Done` clears it), so this is the spec's conservatism, not a finding.
- **`NewDemux` takes the caller's wait group abstractly**: `wgSlotProtocol wg Pslot Prun Pret`
  (the triples of `Add(1)` and `Done()`), instantiated by `newCache` with the cache's slot and
  "open" token. *Rejected:* `NewDemux` stating `cacheWgInv` (the demux would depend on the
  `Cache`).
- **`New`'s postcondition hands out the handles** (`cacheHandles`) as replicated separating
  conjunctions (the `RWMutex`es' bounded tokens: `2^30 - 2` store readers, `2^30 - 3` watch
  slots, `2^30 - 2` notifier handles), and requires `CfgBounded` of an accepted configuration:
  finding 5's `PerWatcherBufferSize ≥ 0` and the overflow bounds `newRingBuffer` and the btree
  need.

---

## The consistent index and the apply thread: a protocol of indices, the applier as the trust boundary

**2026-10-09 · accepted** (Lean-first; not yet reviewed with the user)

Goal: rule out etcd's consistent-index bugs (manual-notes.txt, bullets 3-4: `applyAll`,
server.go:978, and the post-lock hook, server.go:2448). What must hold: every backend commit
persists a consistent index `ci` that matches the effects it persists. If an entry with
writes in the buffer is above the saved `ci`, it is applied twice after a crash. If an entry
at or below it has no writes in the buffer, it is lost (#13766, where `ci` was set before the
entry's writes, outside the batch lock).

**Decision: model the buffer by indices, not data.** The protocol (`InvApply.lean`) tracks
`(k, p, eff, pending)`: `ci`, processed-through, the last entry with writes in the buffer, and
whether an entry's writes are in flight. The invariant is `eff ≤ ci ≤ p` out of flight; a
commit (holding the batch lock's token) saves `ci`, so `eff ≤ saved ≤ p` (`commit_save_au`).
The protocol's steps are lemmas, and each is used at the one place in the code that justifies
it: `hook_set_au` in the post-lock hook (under the lock, `ci := i` for `i = p + 1`),
`writes_done` in the writes update passed to the applier, `skip_done` after a no-write
outcome, `ci_advance_au` in `applyEntryNormal`'s deferred update. *Rejected:* an abstract
state `F : index → S` of "the backend after the committed log through `i`". It needs the
applier's semantics in the trusted contract, and says nothing more about the index
bookkeeping, which is what these bugs are about.

**Decision: the applier and the backend are the trust boundary, as contracts in the
protocol's terms, with the hook's triple as a premise.** `apply.Apply` (and `applyConfChange`)
either take the batch lock (`P`, whose invariant `applierFor ua P f` asserts), run the hook
`f`, write (the caller's update `Q ={⊤}=∗ P ∗ Post`) and unlock, in one critical section, or
write nothing. That is what etcd's design relies on, and the contracts state it; whether the
applier keeps an entry's writes in one critical section is not verified here. The hook itself
is verified (`getTxPostLockInsideApplyHook`). (2026-10-12: the apply package proves
`apply.Apply` against this contract plus the KV, and `applierFor` is its definition; only
`applyConfChange` stays assumed: "The server's apply", unit 3.) *Rejected:* axiomatizing "the applier advances
`ci`", which would leave the hook unverified; an opaque `entryNoop` receipt for the no-write
outcome (dropped: an entry without data skips the applier, and that path is justified by the
code itself).

**The read view.** `ci` is reloaded from the backend only while it is 0. That happens after
`NewConsistentIndex`/`SetBackend`, or while the stored index is absent; meanwhile no commit
writes the meta keys, which still hold the backend's initial `γ.m0`. The `ReadTx` contract is
`metaReadTx rt E (readView γ)`: while `written` is false, a read returns `m0`. It holds for a
real backend (reads see writes only after write-back), and is not satisfiable vacuously.

**raft v3.7, not the fork.** etcd's `go.mod` has raft v3.7.0, whose raftpb is protobuf-go v2
(`Index *uint64`, getters). The fork in `Code/go_etcd_io/raft/` is gogoproto. So etcd's
project in `etc/goose.py` also translates v3.7's raft/raftpb (types, and the getters with
bodies), as a `Part` with a module root of its own, `EtcdDeps/` (`EtcdDeps/Code/`, configured
by `EtcdDeps/Code/**.toml`; the getters' specs and proofs in `EtcdDeps/{Spec,Proof}/`): the two
have the same Go path, so they cannot share `Code/<pkg>`, and both define
`Perennial.go_etcd_io.raft.v3.*`, so no module imports both. They are in the one library
(`lakefile.toml`'s globs), which no module imports whole; `etc/tcb-report.py` runs Lean on the
server's `Link` separately. *Rejected* (on the old layout, before the merge with `lean`): a
library of its own for the server's proofs (`EtcdGroveServer`); in the layout by Go package
path the module path itself clashes, so the root is what has to differ.

**Findings (not bugs in the CI protocol, but worth recording):**
- `SetConsistentIndex` stores the index, then the term, as two atomic steps.
  `applyEntryNormal`'s deferred update and `applyConfChange`'s failure path store outside the
  batch lock, so a concurrent commit can persist the new index with the previous entry's term.
  For a term's first (empty) entry, that is the previous term. The persisted term is only read
  for schema-version detection and `verify`, so the protocol says nothing about the term.
- `UnsafeConsistentIndex` reads `ci.be` without the mutex `SetBackend` writes it under. It
  runs on the apply thread (the hook), as does `SetBackend`, so there is no race. The spec asks
  for the apply thread's half of `be` (`ciOwner`).
- `unsafeUpdateConsistentIndex`'s `verify.Verify` ("update of consistent index not advancing")
  is proved never to fire: `Verify`'s spec requires its closure to return `true`.

---

## Predicate indices: one record, as small as the specs allow

**2026-10-08 · accepted**

An Iris predicate's state is passed as **one record**, not as separate arguments, and
the record holds **only what some spec stated on the predicate needs** -- pure Lean
values, nothing of the Go struct beyond that (no slice headers, no addresses). Changing
what a predicate tracks is then a field added to or dropped from the record, and specs
that write a new state as an update (`{ r with f := v }`) survive it unchanged; a
change of arity touches every spec and every proof that mentions the predicate.
(`ownTracker`'s `votes`/`prs`/`peers`, three arguments until 2026-10-02, became `Trk`
the same way.)

**First application: `ownInflightsRaw`** (`InvTracker.lean`), the internal predicate
of an `Inflights`, was `ownInflightsRaw l iv buf` -- the Goose value and the ring
buffer's contents, as Rocq's `own_inflights`. It is now `ownInflightsRaw l r` with
`r : InflightsRing := { win : Inflights, start : Int, buflen : Int }`, and the value
and the contents are existential inside it (`r = inflightsRingOf iv buf`). The fields
are what `grow`'s spec -- the only internal one -- needs: the length (its premise and
its effect), the window (`size`, and that nothing else changes), and `start` (which
`Add`, after a `grow`, needs unchanged). Not the contents: no spec states them
(`FreeLE` reads them, but its spec is a relation on the window), so `grow`'s
postcondition went from "some slice `sl` and contents `buf' = buf ++ zeroes`" to the
deterministic `ownInflightsRaw l { r with buflen := max 1 (min (2 * r.buflen) r.win.size) }`.
`InflightsOk` is stated on the record, which also discharges `grow`'s former
`size < 2^62` premise.

Proofs open the predicate by `iNamed`/`iunfold … at` (never `unfold` on the goal,
which unfolds the postcondition too) and `subst Hring`, then work on the Goose value
as before; they close it with `ownInflightsRaw_intro`/`ownInflights_reseal`, whose
pure premise is last so that `iapply … $$ Hiv Hbuf Hbuf_cap` fixes the value.

**`ownUnstable`** (`InvRaftlog.lean`) was `ownUnstable u uv uents`, the Goose value and
the entries; it is now `ownUnstable u us` with
`us : UnstableSt := { ents, offset, inprogress, snap }`. Its 13 specs read `offset`,
`offsetInProgress`, the snapshot pointer -- always beside a separate premise
`ownSnap uv.snapshot snap` -- and the logger, as `uv.logger = ok ulg ∗ isLogger ulg`.
The predicate now holds the snapshot as `ownSnap` of `us.snap` and the logger as
`isLoggerVal`, so those premises are gone, and so are the posts' "unchanged" facts
about the value. New states are updates of `us` (`truncateAndAppend`'s is
deterministic), or a new record (`restore`); `stableTo` and `acceptInProgress` keep a
new state (resp. `offsetInProgress`) bound by the post, with its relation to `us`.
The `unstable` proofs open the predicate with `open_unstable` (`ownUnstable_open`: the
value built from the record's fields, so `us` stays a variable; "Records in proofs"
below) and close it with `close_unstable`/`ownUnstable_intro`. The `raftLog` callers
lend the field with `lend_unstable` (`raftLog_lend_unstable`, passing `unstableOf lv
ls`) and take it back with `reopen_unstable`; the `AccessStrict` macro `split_unstable`
is gone, since every `unstable` method hands back a value the caller has not seen.

**Also applied (2026-10-08)**, one commit each:

- `ownStorage` (the field of `StorageModel`), `isStorageWith`'s `P`, `memstorageFields`, `memstorageInv`'s ghost variable and
  `ownMemoryStorage` take one `StorState := { prev, ents, ss }` (`InvStorage.lean`)
  instead of three arguments; the persist lemmas return
  `{ σ with ents := storApp … }`, `newRaft`'s `InitialState` clause `{ σ with ss := ss' }`.
- `ownProgressMap m prs pvs` is `ownProgressMap m pvs`: the pointer map is existential
  (`AckedIndex` only carried it; `Committed` recovers it with `progress_map_agree`).
- Fields no spec reads are dropped: `Progress.recentActive` (checkQuorum, which reads
  it, is out of scope) and `ReadOnly.safe` (the option is case-split on the Go value).
  Both come back if a spec ever needs them.

- `ownRaftLogCore lv snap prev sents uents pend` (five state arguments, the storage as
  `∃ sprev stored ss`) is gone, inlined into `ownRaftLog l ls`, which holds
  `∃ (lv : raftLog) (σ : StorState)` and states its facts on `ls`; `LogStoreOk`,
  `LogPersistOk`, `StoredSnapOk`, `storApp` take `σ`. The `raftLog` proofs no longer
  destructure `ls` (`ownRaftLog_unfold` is gone; `iNamed Hlog` opens it) and pass the
  `unstable` methods `unstableOf lv ls` (`proj_simps`) instead of a literal record.
  `newLogWithSize`, the one spec that named the core, returns the storage and a wand
  `ownStorage st σ -∗ ownRaftLog l <initial state>`: `LogState` has no storage field,
  and `newRaft` needs that storage for `InitialState` before the log is complete.
  The `raftLog` proofs lost all 56 of their `dsimp only` steps (38 files, −289 lines).

**Tried and reverted: `ownRawNode rn id s rs` as `ownRawNode rn id rs`** with the node's
`NState` as `RNState.raft` (2026-10-08, reverted the same day). It removed nothing: every
node fact in the `RawNode` specs became `rs.raft.*` (the comparisons `nodeHardstate s =
rs.hard` became `nodeHardstate rs.raft = rs.hard`), the update `{ rs with raft := s' }`
hid which layer changed, and the proofs destructured the record again. The rule is about
loose state *arguments*; two cohesive records for two layers (the raft node's `NState`
and the RawNode's own `RNState`) stay two indices. (Superseded on
2026-10-09: `ownRawNode γ rn id rs` now hides the node state altogether, and `RNState` is
what a client observes -- "RawNode: client-facing specs" below.)

**Left as is**, deliberately: `visitClosure` (a closure
contract, not an ownership predicate) and `ownConfig`'s `cfg` (a configuration
parameter, which the rule exempts). The ghost predicates in `Protocol/` own no Go
object and were not audited against the rule.

---

## Records in proofs: keep them variables; `word`, `simp`, `proj_simps`

**2026-10-08 · accepted**

The record refactors above added about fifty `dsimp only at …` steps to proofs, which an
agent cannot guess: a projection of a **literal** record (`{ prev := p, … }.prev`, or
`⟨ents, off, ip, snap⟩.offset` from instantiating a spec at a record built from fields)
or of a **record-building function** (`(inflightsRingOf iv buf).buflen`) is an atom that
`omega` and `rw` treat as unrelated to `p` or `buf.length` (checked:
`omega` fails on the first and the third, `rw` on the first).

**Decision**, three parts:

1. **Records stay variables.** Predicates and specs quantify over the record, and proofs
   do not destructure it (`intro ⟨a, b, c⟩` and then working on `a`), nor build a
   literal where a variable will do; then every fact is about `σ.prev`, one atom
   throughout.
2. **`proj_simps f`** (`ProjSimps.lean`) generates, for a function whose body is a
   constructor, `@[simp, word_unfold] theorem f.proj_<field> : (f xs).<field> = <value>`
   by `rfl`. Applied to the 31 such functions in `Defs`, `Protocol/Model`, `InvTracker`,
   `InvMisc`, `InvRawnode`, `InvReadylog`, `InvRaftlog` (`unstableOf`) and the `Ready` proof; eleven that branch
   (`becomeLeader`, `progressMaybeUpdate`, …) have none. A literal record's projections
   need no lemma: `simp` reduces them.
3. **`word` rather than `omega`** where a goal mentions record fields: its preprocessing
   runs `simp only [word_unfold, …] at *`, which does both. `simp only at h` before a
   `rw` on such a hypothesis.

`CLAUDE.md` ("Proof writing") states the three for agents. For a predicate that hides a
Goose value behind a record, the open lemma gives the value *built from the record's
fields* (`ownUnstable_open`: `u ↦ { uv with offset' := us.offset, … }`), so a load yields
`us.offset`, the atom the spec's premises use, and closing is `rfl`. With (2) alone, 19 of the
`dsimp only` steps went; the rest came from the `raftLog` layer, whose proofs destructured
`ls : LogState` and called the record-indexed `unstable` specs with literal records. With
(1) applied there and in the `unstable` and `Inflights` proofs, none is left that exists
because of a record projection.

**Cost**: `word_unfold` makes `word`'s simp set larger. One very large proof
(`RawNode.Ready.wp_proof`) crossed the default 200000 heartbeats at the same wall time
(46 s) and has `maxHeartbeats 400000`. `simp` normalizes hypotheses further than before,
so six `simp … at H; exact H` became `simpa … using H`.

**Not pursued -- `@[reducible]` abstraction functions or `abbrev`s**: structure
projections are already reducible, and `omega` still fails on a literal record's
projection, so it does not compare atoms up to reducible unfolding. **Rejected -- a new normalization tactic**: an agent
would have to know to call it; `word` and `simp` are already what it reaches for.

---

## RawNode: client-facing specs that hide the protocol

**2026-10-09 · accepted**

The refinement of the protocol (`raft.wp_Step`, `ownRaftGhost`, `NStateRel`) exists to
give `RawNode` simple specs for its clients -- the node specs, later. Until 2026-10-08
the `RawNode` specs exposed it: `ownRawNode cfg rn id s rs` beside `ownRaftGhost γ id ps`,
premises `NStateRel s ps`, `PstepCommitMono`, `AdvanceOk s rs.steps`, posts with `Step cfg
id ps recv ps'`, and `Ready`'s committed entries witnessed through `s.logst.applying`.

**Decision**: `ownRawNode γ rn id rs` holds the node state, the ghost state and
`NStateRel` inside, indexed by one record of what a client observes:
`RNState := { delivered, unpersisted, steps, term }` -- the committed log handed
out so far (`isCommitted γ rs.delivered` inside), the entries `Ready` handed out for the
application to `Append`, the queued local steps (opaque), and the term (until 2026-10-10
also the gap flag `advanceable`, below). `Ready`
returns `ce` with `isCommitted γ (rs.delivered ++ ce)`; messages carry the opaque
`isRaftMsg γ m`; `HasReady` says nothing about its answer (liveness only); `Ready`'s soft
state, hard state and `MustSync` facts are gone (no spec used them; there is no crash
model), and so are `RNState.soft`/`hard`. `ownRawNode_persist` lent the storage for the
application's `Append` and returned `{ rs with unpersisted := [] }` (until 2026-10-10: now
`Ready` returns the right to append and `ownRawNode_appended` takes the receipt, "Storage:
a pending append, for node.go" below).

To keep `delivered` across `Propose`/`Advance`, `raft.Step`'s postcondition gained
`LocalStepOk` (for `MsgProp`, `MsgStorageAppendResp`, `MsgStorageApplyResp`: term,
`inprogress`, `unpersisted`, `snap` framed, `applying` kept unless the apply ack moves it).
`PstepCommitMono` is proved (`Step.commit_mono`, `Protocol/Facts.lean`), and Rocq's
`ready_stable_ok` (the append ack is stable once the application appended) too.

**The gap -- closed 2026-10-10.** Until then `Advance` was proved only for a queue without
the **self-addressed responses** `msgsAfterAppend` queues (a candidate's own vote, a
pre-candidate's own pre-vote, a leader's own `MsgAppResp`): `raft.Step`'s spec needs
facts of each that nothing recorded (`Term ≠ 0`, no entries, a non-rejecting
`MsgAppResp`, and a term bound for a `MsgPreVoteResp`), so `Ready` returned a flag
`RNState.advanceable` that `Advance` required and no client could establish. Now:

- `ownRaftPhys` records what `send` puts in `msgsAfterAppend` (`AAMsgOk`): responses from
  the node; a self-addressed one has a nonzero term, `Entries = Context = nil`, does not
  reject (an `appResp`), and a term no later than the node's (one later for a
  `MsgPreVoteResp`, a pre-campaign's own). `SendOk`'s response clauses ask the caller for
  these when `To = id`; the callers that answer `m.From` now know `m.From ≠ id`
  (`handleAppendEntries`, `handleSnapshot`, `stepFollower`/`stepCandidate` for
  `MsgApp`/`MsgSnap`, the `MsgPreVote` branches: `Step`'s transport premises). The term
  bound needs the term never to move back: `raft.wp_store_Term` takes `s.term ≤ v`, and
  `reset`, `becomeFollower`, `becomeCandidate` (no wrap), `loadState` take it as a premise.
- **A leader's term is nonzero** (`appendEntry` stamps its self-acknowledgement with it):
  `appendEntry` and `becomeLeader` take `s.term ≠ 0`. A candidate's comes from the winning
  `MsgVoteResp` (`stepCandidate`'s premise `m.Term = s.term` now also `m.Term ≠ 0`); a
  leader's proposal gets it from the ghost state: `ownRaftGhost_term_nz` -- a candidate or
  leader holds the campaign record of its term (`campOwn`), whose `CampOk` puts the
  boundary's term `0` below it. *Rejected*: an `ownRaftPhys` invariant `role = leader →
  term ≠ 0` (the field stores of `Term` and `state` would each need a premise, threaded
  through every `becomeX`), and a conjunct of `RoleOk` (reproving every refinement rule).
- `Ready` puts each self-addressed response in the queue as `Pending.self pv t`
  (`selfPending`: whether it is a pre-vote response, its term), with `pendingRel` holding
  `SelfMsgOk` and its `isMessage` (from the drained outbox), and `StepsOk` the term bound
  (self responses first, then the storage acknowledgements, as `acceptReady` queues them).
- **The term across `Advance`**: `raft.Step`'s postcondition gained `RespStep` -- a stale
  `MsgVoteResp`/`MsgAppResp` keeps the role; a `MsgPreVoteResp` moves the term at most to
  its own or one up from a pre-candidate, and never makes a pre-candidate -- and its
  `MsgPreVoteResp` no-wrap premise is now only for a pre-candidate. With the queue's term
  bounds, `Advance`'s loop keeps `TermInv`: the term is the start's or one more, and while
  self responses remain a pre-candidate is at the start's term (a won pre-vote leaves a
  candidate, which ignores the later pre-vote responses, and the other responses are
  then stale). So `Advance` takes `rs.term + 1 < 2^64` and returns the term up by at most
  one. *Rejected*: assuming at most one self pre-vote response per queue (false: two
  pre-campaigns before a `Ready` queue two), a premise counting the queue's pre-vote
  responses (opaque to clients), and `TermStep` alone (it lets each pre-vote response add
  one).

`advanceable` is gone: `ownRawNode` carries `StepsOk s rs.steps` unconditionally,
`Ready` does not return a flag, `Advance` takes any queue `Ready` left. The
`Ready`/`Advance` loop is verifiable through the specs.

---

## The transaction model: sequential ops at one revision, per prefix; leases without liveness; the create-revision persistence law

**2026-10-09 · accepted** (the design decided with the user; adjusted here where noted)

`client/v3/concurrency` (sessions, then mutexes, elections, STM) is built on etcd's
transactions and leases, which the cache's model (`etcdState`, `EtcdStep`, `etcdReached`) did
not cover. `InvEtcdTxn.lean` (beside `InvEtcd.lean`), `client/v3/InvCmp.lean`, the `OpFull`
extension in `client/v3/InvOp.lean`, `client/v3/InvClient.lean`,
`client/v3/concurrency/InvSession.lean`.

- **A transaction is pure and sequential.** `runTxn r s t` evaluates the comparisons on `s`
  (`cmpHolds`, etcd's `applyCompare`) and runs the chosen branch's operations in order, each on
  the state the previous one left, all at revision `r` (`runOps`, `applyTxnOp`: a put of a new
  key creates it at `r` with version 1; of an existing key keeps the create revision, sets the
  mod revision to `r`, increments the version, sets value and lease; a delete removes the keys
  its range selects; a get reads the state at that point). etcd itself rejects a transaction
  with two writes of one key; the model runs it anyway, which is harmless: the contract allows
  any error. *Rejected:* every operation on the state before the transaction (false of etcd:
  a get after a put in one transaction sees the put, the user confirmed).
- **A missing key compares as zeros, but a value comparison fails** (`cmpHolds`). This
  corrects the plan ("a missing key reading as ... empty value"): etcd's `applyCompare` returns
  `false` for a value comparison on a range with no key ("no way to represent missing value"),
  and compares the zero key-value otherwise. A comparison on a range holds if it holds of every
  key in it.
- **A get's response is a relation, not a function** (`rangeKvsOk`): a reordering of the
  selected keys sorted as requested, then limited. etcd sorts with Go's unstable `sort.Sort`,
  so ties (two keys created in one transaction, sorted by create revision) come in any order;
  a function (a stable sort) would claim an order etcd does not promise. The count is the
  number of keys in the range before the revision filters (etcd's `rr.Count`).
- **The revision advances only for a write** (`txnWrote`: a put, or a delete of at least one
  key). A read-only transaction is answered at the current revision `r`, the state is `s` at
  `r` and stays so (`runOps_noWrite`); a writing one has `s` at `r - 1` and the new state at
  `r`. Both are stated by `txnStates`. Linearizability is as for `Get`: `Commit` takes
  `etcdReached lo` and answers at `r ≥ lo` with `etcdReached r`.
- **Per prefix, as `isEtcdKV`.** The contract speaks of `etcdState r pfx`; `Commit`'s premise is
  that every key the transaction compares or touches is under `pfx` (`TxnModel.Under`), so the
  restricted state determines the comparisons and the writes. *Rejected:* a whole-keyspace
  state (the cache's facts are per prefix; one model is simpler).
- **The builder is the trust boundary** (`isEtcdTxnKV kv pfx`, a definition: `kv.Txn(ctx)`
  returns a `Txn` with an abstract state `B : TxnBuild → IProp GF` and the triples of `If`,
  `Then`, `Else`, `Commit`). *Rejected:* translating and proving the client's `txn` struct:
  its methods clone every comparison with protobuf's `proto.Clone` and turn every `Op` into a
  `pb.RequestOp` (`toRequestOp`, the protobuf messages of all four operation kinds), and
  `Commit` is a gRPC call, which would be the boundary anyway; the abstract builder states the
  same at the interface. The builders the caller runs (`Compare`, `Value`, ..., `OpPut`,
  `OpDelete`, the options) are translated and proved; `proto.Clone` of a `*pb.Compare` is an
  axiom (`proto.Clone.wp_proof`: a deep copy, owned).
- **Two history laws, as axioms** (about `etcdState`, which is an axiom): `etcdState_revs`
  (every key-value at `r` has `0 < createRev ≤ modRev ≤ r` and a positive version) and
  `etcdState_create_persist` (a key present at `r` with create revision `c` is present with the
  same create revision at every `a ∈ [c, r]`; stated between two known states). *Rejected:*
  the revision bounds in `EtcdStateWf`: `isEtcdKvs` carries `EtcdStateWf` as a side condition
  the cache proves for every snapshot it builds from watch events, and the watch contract says
  nothing of the events' create revisions, so it would have had to grow too.
- **Leases without liveness** (`isEtcdLease`, a definition): `Grant` returns an error or an ID
  other than `NoLease` (with `etcdReached` of its header revision); `KeepAlive` an error, or a
  channel (possibly nil) of which nothing is promised (`isChanAny`: a receive yields any value
  or the close: the stream may end at any time); `Revoke` an error or a response whose revision
  etcd has reached. A put's lease is recorded in the key-value; what expiry or revocation does
  to keys is a step of etcd's history like any other (`EtcdStep`), stated nowhere else.
  *Rejected:* modelling TTLs and expiry (a liveness/timing property; the recipes' safety does
  not need it: a session that ends is observed through `Done`).
- **`isEtcdClient` gains the transactions and the `Lease`** (`isEtcdTxnKV`,
  `isEtcdLeaseClient`); the cache does not use them (its `newCache` drops them). `Session`
  takes only what it uses (`isEtcdSessionClient`: the `ctx` field, the `Lease`, the logger).
- **The session's context must be cancelable.** `NewSession` calls `WithCancel(ops.ctx)`;
  Perennial's `wp_WithCancel` needs a `*cancelCtx` parent (`isCancelCtxCtx`), so `NewSession`'s
  spec takes that of the resulting options' context (the client's, which `newClient` makes with
  `WithCancel`, unless `WithContext` replaces it). `Close` uses `WithTimeout`, which rests on
  Perennial's `wp_WithDeadlineCause` `sorry`: it enters the trust base (not worked around).
- **`WithSort`'s by-key-ascending case.** `WithSort(target, order)`'s closure assigns the
  captured `order` (`order = SortNone`) when `target == SortByKey && order == SortAscend`: a
  write of a variable shared by every call of the closure, so concurrent calls race, and an
  `optSpec` (persistent: any number of calls, from any thread) cannot be proved for it. The
  specs of `WithSort` and `withTop` take `¬ (target = SortByKey ∧ order = SortAscend)`
  (`WithFirstCreate`/`WithLastCreate` use create revisions). *Rejected:* a non-persistent
  option spec (every other option is persistent); a "Gooseable" rewrite copying `order` into a
  local (possible later, if a caller needs that case).
- **zapcore's `time`/`io` imports.** `isClientLogger` (the client's `atomic.Pointer[zap.Logger]`)
  needs `zap.Logger`'s typed points-to, whose fields `clock` (`zapcore.Clock`) and `errorOutput`
  (`zapcore.WriteSyncer`) had axiomatized types (`sorry` instances), as zapcore imported nothing;
  `zapcore.toml` now imports `time` and `io`, which makes them interfaces.
- **Linking.** `client/v3/concurrency`'s results are in the namespace `concurrency`
  (`Proof/go_etcd_io/etcd/client/v3/concurrency/Link.lean`, `etc/gen-link.py --concurrency`), a
  clientv3 function's with the prefix `v3.`: the cache's Link links some of the same clientv3
  functions under the cache's assumptions, which the concurrency package's do not imply, and
  concurrency's `WithLease` shares its name with clientv3's. For the same reason the clientv3
  specs now take clientv3's `Assumptions`, and the zap specs import the cache's `Base` rather
  than the server's `InvApplier` (both Links use the same zap axioms).

---

## RawNode: the acknowledgement across a truncation

**2026-10-10 · accepted**

`RawNode.Step` took a `MsgApp` only with no `Ready` outstanding (`rs.steps = []`): the
queued `MsgStorageAppendResp` of the last entry `e` asked `e.index < offsetInProgress`
(`PendingOk`), which is `StableOk` once the application appended, and a truncating
`MsgApp` lowers `offsetInProgress`. `node.go` steps network messages between `Ready` and
`Advance`, so the premise had to go.

*Not true*: "either the acknowledgement misses or `e.index` stays below
`offsetInProgress`". A first `MsgApp` truncates below `e` (`offsetInProgress` drops to the
truncation), a second, from a leader of a higher term whose log has `e` (Figure 8 of the
Raft paper), truncates there again and puts `e` back: the acknowledgement hits with
`e.index ≥ offsetInProgress`. Go's `stableTo` is still right, because what it moves
stable is in the storage: the storage holds the `Ready`'s log up to `e`, and two logs
with `e` agree up to it.

**Decision**: say that, with the storage's contents as ghost state.

- `LogState.stored` (ghost): what the storage holds once `unpersisted` is appended
  (`LogPersistOk`: `storApp σ pend = stored`). Only `Ready` changes it (to the log).
- `StableOk` asks `stored` to be the log up to `id` (and nothing unpersisted, no
  snapshot). `persist_stable` handles both an in-progress `id` and one past
  `offsetInProgress`.
- `NetFrame`/`LocalFrame` keep `prev` and `stored`; `PendingOk` asks of the
  acknowledgement only `plogLast prev stored = e`, which every step then keeps.
- `ownRawNode` keeps the records of `stored` (`storedRecs`: `PlogWf`, `logRecs`), taken
  from the ghost state when `Ready` sets `stored` to the log. At `Advance`, Log Matching
  between them and the log's records (`stored_agree`) gives `StableOk` on a hit
  (`stableOk_of_stored`).

*Rejected*: keeping `offsetInProgress` in `PendingOk` with a disjunction ("or the
acknowledgement misses"), or reporting the truncation point in `raft.Step`'s `MsgApp`
postcondition -- both false or too weak after two `MsgApp`s, as above: what makes the
hit right is what the storage holds, which no fact about the current log records.

---

## Mutex: `lockedAt`, exclusion from the two history laws

**2026-10-10 · accepted** (the design decided with the user; adjusted here where noted)

`concurrency.Mutex` is a lock on a prefix built from etcd keys: the key created first holds it.
What its specs say, and what "mutual exclusion" means over etcd's model (`InvMutex.lean`).

- **The ownership fact is a statement about one revision.** `lockedAt pfx key c R`: etcd's state
  at `R` under the prefix has `key` with create revision `c` and no key with a smaller one.
  `TryLock` gets it at its transaction's revision (the owner get runs on the state the put left);
  `Lock` at its last `Get`'s revision, from `waitDeletes`' last `Get` (`R0`: nothing created
  before `myRev`) and `etcdState_create_persist` (a key created before `myRev` and present at
  `R ≥ R0` was present at `R0`, `lock_final`). *Changed from the plan's first form* ("at `rev`"):
  a waiter only learns its ownership when its last `Get` answers, at a revision after its key's
  creation.
- **Exclusion is derived, not assumed** (`lockedAt_exclusion`): if `(k1, c1)` and `(k2, c2)`,
  `c1 < c2`, were both present at `a ≥ R2`, then `k1` (created at `c1 < c2 ≤ R2`) was present at `R2`
  (`etcdState_create_persist`; `c2 ≤ R2` by `etcdState_revs`), against the minimality at `R2`. Only
  the two history laws; no protocol invariant over etcd's history (the model has no notion of
  who writes). `c1 = c2` is not excluded: two keys created by one transaction; a mutex's creates
  one key, but that is a fact about writers the model does not have. At one revision the holder's
  create revision is unique (`mutex_holder_unique`, from `etcdState_agree`).
- **`Lock`'s spec states what its code checks.** Its last check is that the key exists, not
  that its create revision is unchanged; so `nil` gives `lockedAt ∨ keyRecreated` (STATUS: two
  mutexes of one session on one prefix share the key). *Rejected:* a premise making re-creation
  impossible (it is about other clients' writes, which the model cannot state); dropping the
  disjunct (false of the model).
- **The state is a record of the fields, not an enumeration** (*changed from the plan's*
  `unlocked | locked key rev | released`): `tryAcquire` writes `myKey` before its transaction, so an
  error leaves a mix no constructor names, and every method runs from any state. `MutexSt.init`,
  `MutexSt.released`, `MutexSt.noKey` name the plan's states.
- **The client contracts grow minimally, as definitions**: the range clause of `kvGetResult`
  (`getRespRange`: one relation, `rangeKvsOk` of `rangeSel`, for every range get at the latest
  revision; the prefix get keeps its exact `KvMap` clause), `Delete` as a one-operation
  transaction (reusing `runTxn`/`txnStates`), and a single-key watch contract stated directly (a
  delete event at `r` means the key is absent at `r`). *Rejected:* the single-key watch through
  `EtcdStep` (a step is per prefix and lists every event under it; a key's watch sees one key's —
  a per-key step would be a second history predicate); a whole-keyspace state.
- **`Sprintf`'s result**: a sound model in Perennial (`%s` exact, everything else arbitrary)
  rather than a premise: a premise contradicting the old model (which returned the format) would
  have made the specs vacuous. The mutex needs only that the key is under the prefix.
- **`lockerMutex` is not specified**: it panics on any error, every client call may fail, and a
  panic is stuck in Perennial. *Rejected:* a spec promising success (false), an axiom (likewise),
  a `sorry` (it is not unfinished work). *Superseded* (2026-10-10, "Panic and recover"): with
  panics as outcomes, `Lock`/`Unlock` are specified: `Mutex.Lock`/`Unlock`'s `nil` case, or the
  panic `panic(err)`.

---

## Election: the mutex's leader fact, no final check, what `Observe` can promise

**2026-10-10 · accepted** (the design decided with the user; adjusted here where noted)

`concurrency.Election` (`election.go`) is the mutex's protocol with a value: the key created
first under the prefix is the leader. `InvElection.lean`.

- **The leader fact is `lockedAt`** (`leaderAt := lockedAt`), so the election's exclusion is the
  mutex's (`election_exclusion` is `lockedAt_exclusion`).
- **`Campaign`'s spec states what its code checks: nothing after the wait.** `nil` gives
  `leaderAt ∨ campaignLost` (no key older than the campaign's, and the campaign's key not there
  with its create revision). *Changed from the plan* ("the final `Get` of the key"): `Campaign` has
  no final `Get`; it returns after `waitDeletes`. A finding (STATUS, "Election").
- **`waitDeletes` takes `maxCreateRev ≥ 0`.** `Campaign` calls it with `leaderRev - 1`, which is `0`
  for a key created at revision `1` (the model's create revisions are only positive; etcd's first
  write is at revision 2): `WithMaxCreateRev(0)` is no filter, and the spec's conclusion (no key
  with create revision `≤ 0`) holds trivially. *Rejected:* a history law that create revisions are
  at least 2 (a new axiom for an unreachable case).
- **A transaction outside the prefix gets a weak `Commit`** (`txnAnyResult`: an error, or a
  response with a header and `Succeeded`). After a failed `Proclaim` the leader key is `""` and the
  leader session stays, so `Campaign`'s cleanup `Resign` (and a second `Proclaim`) commit on the key
  `""`, which the per-prefix contract does not cover. *Rejected:* a precondition excluding that
  state (`Campaign`'s own error path reaches it).
- **The range watch** (`isEtcdRangeWatcher`, replacing the single-key `isEtcdKeyWatcher`; one
  contract for a key and a sub-prefix): per event the key is in the range, at a revision `≥ rev`,
  reached, a delete means absent, and **a put's key-value is the key's in etcd's state at the
  event's revision**; events sorted above the stream's position (a monotone list, as the cache's
  `watchRespOk`); the receiver **owns the header's `Revision` of a response with events**
  (`watchHdrOwn`: `observe` writes `hdr.Revision = kv.ModRevision`; the client builds each event
  response from its own gRPC message and reads its header only before sending it; a progress
  notification's, broadcast to every watch, stays read-only). *Rejected:* the cache's
  `EtcdStep`-chain contract for the prefix watch (`observe` does not ask for progress or created
  notifications, and the chain's laws, without a law tying a key's create revision to a put event,
  would not give the first put's minimality either); a completeness promise (a second history
  predicate).
- **`Observe`'s responses say what the code gives against that contract** (`observedAt`: leader,
  or re-created leader key, or created after an empty prefix), at non-decreasing revisions
  (`observeElem`'s ghost list, from `Observe`'s `lo`). With a gap-free watch the last two are the
  leader; the contract does not promise gap-freedom. *Rejected:* stating the leader fact for every
  response (false of the model).
- **`Observe` takes `lo ≥ 0`.** `observe` watches the prefix from its get's revision, which the
  range watch needs non-negative; the get answers at `≥ lo`, so `0 ≤ lo` (always available:
  `etcdReached_zero`) is carried through the loop. *Rejected:* dropping `0 ≤ rev` from the watch
  premise (`rev - 1` would wrap for the least `int64`); adding `0 < r` to `kvGetResult` (true of
  etcd, but a change to the cache's contract for one caller).
- **`proclaim_only_leader` is pure** (`proclaimStep_guard`): `Proclaim`'s spec returns the model
  step (`ProclaimStep`: the guard held on the state before, the state after is the put), and the
  theorem reads off it that the key had the campaign's create revision and keeps it with the new
  value.

---

## STM: a higher-order closure spec, aborts as panics, what each isolation level gives

**2026-10-10 · proposed** (the intent decided with the user; the panic boundary, the read
transaction contract and the snapshot claim decided here, for review)

`concurrency.NewSTM` (`stm.go`) runs a user's closure against an `STM` interface and commits its
buffered reads and writes with one guarded transaction, retrying on conflict.
`InvSTM.lean` (vocabulary), `InvSTMAtomic.lean` (the commit key by key), `Results.lean`.

- **The closure is specified higher-order** (`applySpec pfx apply Q`, persistent: `runSTM` calls
  it once per attempt): for any STM `p` of any level with the interface's triples
  (`stmMethods lvl pfx p`: `Get`, `Put`, `Rev`, `Del`, and the internal `commit`, `reset`), from
  any state (`stmState lvl pfx p st`, exclusive: the attempt's read and write sets `st`), `apply`
  returns an error or `nil` in some state, and `nil` means `Q st'` of the attempt's final reads and
  writes. `Q` is pure: what the closure promises about what it read and wrote (e.g. "`x` is written
  with the value read from `y` plus one"); `NewSTM`'s `nil` gives `Q` of the committed attempt with
  `stmOutcome`. The closure can only use the STM through the methods it has triples for, and keeps
  no exclusive resource across attempts. *Rejected:* `P`/`Q` resources threaded through the
  attempts (each attempt starts over; a failed attempt's effects are invisible, so an exclusive `P`
  would have to be given back by an attempt that may abort by a panic).
- **The model of an attempt** (`STMSt`): reads (`ReadM`: the response's header revision, the
  revision `rev` of the state read, the key-value read) and writes (`WriteM`: put with lease, or
  delete). Each read carries `readFact` (etcd's state at `rev` has that key-value). The commit's
  comparisons per level (`ConflictsOk`) are stated on the model (permutations of the map order:
  the key lists `wp_map_for_range` gives).
- **What a commit gives** (`STMCommitted`, pure; `stmOutcome` adds the states, `txnStates`): the
  transaction ran at `R` on `s` (etcd's state at `R - 1` if it wrote, at `R` otherwise) and left
  `s'` (etcd's at `R`) = `s` with the writes applied; **every read is `s`'s key-value of its key**
  (`ReadsAgree`, all levels but `ReadCommitted`), from the comparison `ModRevision(k) = m` on `s`
  and the new history law below; `SerializableSnapshot`: every written key's mod revision in `s` is
  at most `first()`. `stm_atomicity` (Results, pure) reads this key by key
  (`runOps_writeOps_kvAt`): the attempt's reads are the values at `R - 1` and etcd's state at `R`
  is that state with the writes applied, each key independently of the write set's order: the
  closure ran atomically at `R`.
- **A new history law** (`etcdState_modrev_det`, `InvEtcdTxn.lean`): two states holding a key with
  the same mod revision hold the same key-value (a revision writes a key at most once). The
  existing laws do not imply it (they speak of create revisions and bounds). Without it a
  successful comparison on mod revisions says nothing about values.
- **The snapshot is not claimed** (a finding, STATUS "STM"): the serializable levels' documented
  promise "reads within the same transaction attempt return data from the revision of the first
  read" fails after a failed commit, when the next attempt's first read is of a key not prefetched:
  that read sets the snapshot at the latest revision, while prefetched reads (from the failed
  commit's `Else`) are older. The specs say what holds: each read's own revision (`readFact`), and
  at commit the comparisons; serializability (`ReadsAgree`) does not need a snapshot.
- **Reads at an earlier revision: a second contract for `Txn`** (`isEtcdReadTxnKV`,
  `readTxnResult`): a transaction of gets alone, each at the current revision or at its `WithRev`
  revision, serializable or not, answers each get on etcd's state at its revision. The `Txn`
  contract `isEtcdTxnKV` models gets at the transaction's revision only (`txnOpOf`), and a pure
  `runTxn` has no other state to read. *Rejected:* a history oracle in `runTxn` (every existing
  transaction proof would change for one caller).
- **Linearizability of a transaction, corrected** (`TxnModel.linearizable`): etcd serves a
  transaction whose operations are all serializable gets, or which has none, from the member's own
  state (`IsTxnSerializable`); `txnCommitResult` claimed `lo ≤ r` for every transaction, which is
  false for those (no existing proof used one). Now `lo ≤ r` only if an operation is not a
  serializable get. The STM's commits are linearizable when they have an operation
  (`ops ≠ [] → lo ≤ R` in `STMCommitted`); a `RepeatableReads`/`ReadCommitted` attempt with no
  write commits an empty transaction, answered by the member at a possibly older revision.
- **The range response's header** (`rangeRespAt`): it exists (`first()` and the serializable `Get`
  read it); its revision is not stated (nothing needs it).
- **Aborts are panic outcomes** (since 2026-10-10; before, the trust boundary, below). `stm.fetch`
  and the commits `panic(stmError{err})` on any client error, which every client call allows;
  `runSTM`'s deferred function recovers the panic and sends `(nil, err)`. Their specs say so
  (`stmRet r Q`: a return `#x` with `Q x`, or `r = stmAbort err`, the panic of the `stmError` as an
  `interface{}`, with `err ≠ nil`; proved with `wp_panic`), and so do `Get`, `Rev`, the interface's
  triples (`stmMethods`) and the closure (`applySpec`), which propagate it (`wp_auto` unwinds).
  `runSTM`'s proof follows the panic out of the attempt loop (`wp_for_post`) to the `Catch` of its
  goroutine's `with_defer_recover:`, whose deferred literal reads it with `recover()`
  (`wp_recoverPanic`), asserts it to `stmError` (which succeeds) and sends `(nil, err)`; the
  goroutine returns normally (`wp_fork`'s non-panic body). `NewSTM`'s spec is unchanged. A closure
  that recovered an abort and returned would still satisfy `applySpec` (its return is a return).
  *History*: Perennial's `panic` was stuck and it had no `recover`, so the abort was a trust
  boundary of two axioms (`stmPanic.spec`: the panic satisfies any postcondition, for
  `err ≠ nil`; `stmRecover.spec`: `recover()` returns `nil` where a verified run reaches it),
  sound by the argument that a verified run reaches the code after an abort only without one;
  both are gone (Perennial branch `panic`, "Panic and recover").
- **`Get`'s results** (`GetPost`): `Get(keys...)` returns, for some key `k` of `keys`, its write's
  value, or, not written, its read's value; the reads grow by keys of `keys` only and **a read, once
  there, stays** (repeatable reads within an attempt). For the serializable STM this needs an
  invariant (`PreOk`: a key both read and prefetched is written), since `Get` moves prefetched reads
  into the read set.
- **A map's length is bounded in the model** (Perennial `9276bd1ed`, `wp_map_len_lt`): `len(m)`
  of a map with `2^63` keys or more does not return (`assume false`), as `append` assumes its length
  does not overflow. `readSet.cmps`, `writeSet.cmps`, `writeSet.puts` and `gets` call
  `make([]T, 0, len(m))`, which panics on a negative capacity. *Rejected:* a size bound in
  `stmState` (an insert could not keep it without the same assumption); a precondition on the
  callers (likewise).

---

## Storage: a pending append, for node.go

**2026-10-10 · accepted**

`node.go`'s `run` goroutine owns the `RawNode` and keeps reading the `Storage` (`term`,
`slice`, `lastIndex`, `firstIndex`, `snapshot`) while the application, on its own
goroutine, appends the last `Ready`'s entries (`storage.Append(rd.Entries)`) and only then
calls `Advance`. Until 2026-10-10 the contract could not say so: `ownStorage st σ` was one
exclusive predicate held by `ownRaftLog`, and the application appended by borrowing it
(`ownRawNode_persist`), excluding raft's reads meanwhile.

Raft never reads what the pending append changes: `raftLog.term(i)` asks the storage only
below `unstable.offset` (or with nothing unstable), `slice` only below it, `lastIndex()`
only with nothing unstable -- and then nothing is pending -- and the batch (`unpersisted`)
starts at or above the offset (it is the in-progress part of the unstable suffix; only a
truncating `append` moves the offset, down).

**Decision.**

- `StorState.pend`: the batch the application may be appending, `[]` when none.
  `isStorageWith P AT DT st` (two new parameters: the right to append and its receipt)
  promises `Term(i)` only below the batch, `Entries(lo, hi)` only for `hi` at most its
  first index (`PendFrom`), `LastIndex` only with nothing pending; `FirstIndex`,
  `Snapshot`, `Hbounded` as before. Two new persistent clauses: `Hhandout` (`P σ` with
  nothing pending and a `PendOk` batch `p` `==∗ P { σ with pend := p } ∗ AT σ p`) and
  `Habsorb` (`P σ1 -∗ DT σ p ==∗ ⌜σ1 = { σ with pend := p }⌝ ∗ P (storAbsorb σ1)`).
  `StorageModel` gained `appendTok`/`appendedTok`; `isStorage st` instantiates `AT`/`DT`
  with them. `PendOk` (non-empty, starting above the boundary and at most one past the
  stored entries) is what makes `MemoryStorage.Append`'s cut and `Panicf` unreachable.
- Raft's side: `ownRaftLog` ties the batch to `ls.unpersisted` and puts it at or above
  the offset (`PendLogOk`); the read proofs discharge `PendFrom` from it
  (`pendFrom_of_logOk`), `lastIndex` from `LogPersistOk`'s `uents = [] → pend = []`.
  `acceptUnstable` runs the hand-out (`isStorage_handout`) and returns the right
  (`appendRight st p := ⌜p = []⌝ ∨ ∃ σ, appendTok st σ p`), and `RawNode.Ready`
  returns it with the `Ready`. `ownRawNode_appended` (replacing `ownRawNode_persist`)
  absorbs the receipt (`appendReceipt`) into `ownRawNode { rs with unpersisted := [] }`
  (`ownRaftLog_absorb`). `acceptUnstable` takes `ls.snap = none` (`Ready` has it).
- **The storage's identity.** A receipt is for one storage: absorbing one storage's
  receipt into a node reading another would be unsound (two nodes may hand out the same
  entries). So the client must name the storage: `RNState.storage` (the `Config.Storage`
  given to `NewRawNode`), and `ownRawNode` ties it to the log's: `LogState.storage`
  (`ownRaftLog`'s `Hstor`: `lv.storage' = ls.storage`), kept by every step like
  `unpersisted` -- `NetFrame`, `LocalFrame`, `raftLog.maybeAppend`'s and
  `handleAppendEntries`' frames gained the conjunct (`keep_frame` & co. as an auto-param
  `rfl`), `newRaft` returns it. *Rejected*: a ghost name per node (`RaftNames` is
  cluster-wide; every choice still has to reach the log's storage pointer, which only
  `LogState` sees); a law `ownStorage st1 σ1 ∗ appendedTok st σ p ⊢ ⌜st1 = st⌝` (false for
  two `MemoryStorage`s).
- **The right comes with `Ready`**, not from a lemma on `ownRawNode` as first planned:
  the hand-out runs where `unpersisted` is set (`acceptUnstable`), and a later lemma
  would need `ownRawNode` to record whether the right was taken out already.
- **`MemoryStorage`** (`InvMemstorage.lean`): three ghost names (`MemStorNames`, now an
  index of `ownMemoryStorage ms γs σ` and of its tokens). The lock's invariant holds half
  of the authority of `done` (a `mono_list` of the states the storage has been in; the
  contents are its last) and a lower bound of `hist` (a `mono_list` of the states the
  owner sanctioned, its authority with the owner); the other half of `done` is the
  writer's -- the owner's when idle, the token's while appending -- and a ghost variable
  `ep` of the hand-out is halved between the owner and the token. The hand-out extends
  `hist` and needs no lock (the invariant has only a lower bound); `Append` (under the
  lock) extends `done`; the absorb agrees on `ep` and takes the writer's half back. Under
  the lock the owner, holding `hist` at `H ++ [appended]` and a lower bound of `done` at
  `H`, knows the contents are `H`'s last or the appended state (`memView_agree`), which
  agree below the batch (`memView_term`, `memView_entries`). *Rejected*: a ghost variable
  of the state shared with the invariant (the hand-out would need the lock), and one
  tracking only raft's view (the owner could not bound what `Append` writes).
- `MemoryStorage.Append` and `NewMemoryStorage` are specified and proved (Lean-first).
  `Append` takes the batch's bound (`e0.Index + |p| ≤ 2^61`: a client assumption, as
  `Hbounded` is) and the right; its in-place arm needs the entries' capacity, now owned
  in `memstorageFields`; the bound the private helpers need is the invariant's
  (`memstorageInv`'s `Hpb`), the contents running ahead of the owner's view.

**Not done -- a new `MemoryStorage` is not an `isStorage`.** The contract's `Snapshot`
clause promises a non-empty snapshot (`maybeSendSnapshot` panics on an empty one); a new
storage has none. The plan was to promise non-emptiness only once compacted
(`σ.prev.index ≠ 0`), because `maybeSendSnapshot` follows a failed storage query. But it
follows any error of `raftLog.term(pr.Next - 1)`: `ErrCompacted` (then `prev.index > 0`)
*or* `ErrUnavailable`, for a peer whose `Next` is past the log + 1, which nothing in
`ownRaftPhys`/`ownProgress` excludes (raft keeps `Next ≤ lastIndex + 1` for a leader's
peers, unproved here). So the clause stays; `ownMemoryStorage` dropped `σ.ss.index ≠ 0`
(so `NewMemoryStorage` can produce it) and the instance `is_Storage_MemoryStorage ms γs`
adds it to `P`. Closing it needs a `Next` bound in the tracker invariant.

## RawNode: pre-vote out of scope, and the terms of the outbox

**2026-10-10 · accepted**

For `node.go`'s argument that terms never wrap, a receiver must know a message's term is
at most its sender's. With pre-vote on that is false (a `MsgPreVote` is at the next term,
a granting `MsgPreVoteResp` echoes the candidate's), and pre-vote is an optimization:
out of scope.

**Decision.** `ownRawNode` holds `s.prevote = false` (`NewRawNode` takes `Config.PreVote`
unset; `NetFrame`/`LocalFrame` keep `prevote`). `ownRaftPhys` records of every queued
message `OutTermOk s.prevote s.term m` (`prevote = false → Term ≤ term`), which `send`
establishes: it stamps the node's term into every message but a forwarded proposal and a
vote message, and `SendOk`'s vote clause bounds the caller's term under the same
condition. A pre-vote message is then only ever sent with pre-vote on: `campaign`'s
pre-election takes `t = campaignPreElection → s.prevote = true` (as does `hup`; `Step`
calls it so exactly when `r.preVote`), and `raft.Step.spec` takes a `MsgPreVote` only at
a node with pre-vote on -- a transport premise (the setting is the cluster's), vacuous
for `RawNode.Step`, which takes no pre-vote message.

*Rejected*: keeping `raft.Step` unrestricted and tracking "no pre-vote response to
another node in the outbox" in `ownRawNode`, or as a ghost flag of `NState` -- either
needs a new fact about every `Step` branch's outbox growth, where the premise costs one
hypothesis threaded into the three `MsgPreVote` branches.

## node.go: small client specs, a term budget, the Ready/Advance exchange

**2026-10-10 · accepted**

`node.go` puts a goroutine (`run`) between the clients and the `RawNode`. The specs a
client sees stay small (`isNode` is persistent; `Propose` and `Step` return `True`); what
`run` needs of them is carried by the channels' payloads (Perennial's `Handshake` idiom:
`propP`, `netP`, `readyP`, `advanceP`; a proposal's result channel is a `Handoff`).

**The terms never wrap.** `RawNode.Tick`, `Advance` and a step need `term + 1 < 2^64`.
A cluster-wide budget (`budgetInv`): a monotone bound `M` on every node's term and every
message's (`termLB`, persistent), and `c` tick credits out, with `M + c < 2^64 - 1`. A
tick spends a credit and may raise `M` by one past a term (`budget_spend`); a step moves
a node's term to at most a message's, already under `M` (`netP` carries `termLB` of the
message's term); `Ready`'s messages are of terms at most the node's (pre-vote off,
`OutTermOk`). The application allocates the budget with as many credits as it will ever
tick. *Rejected*: a per-node bound (a message from a peer can raise the term past it).

**The Ready/Advance exchange.** One driver; `dlv` (halves: `run`'s and the driver's) is
the committed log handed out, `rof` `run`'s record `(delivered, committed entries,
entries)` of the last `Ready`. A `Ready` carries `run`'s `dlv` half and a `rof` half: the
driver, holding both `dlv` halves, learns that the committed entries follow what it
applied. `Advance` carries a `dlv` half back with the `rof` half and the append receipt:
`run` recognizes its record, so the receipt is for the entries it handed out. *Rejected*:
an exchange whose order is visible in the specs (a ghost sequence number per `Ready`).

**An abandoned `Ready` may still be sent.** `run` computes a `Ready` and arms `readyc`,
but may take another case and come back with `HasReady` false, then send the old one.
`RNState`'s lower bounds (`outlb`, `unst`, `clb`), raised when it abandons the `Ready`
(`ownRawNodeReady_abandon_keep`), and `HasReady`'s `false` pinned to an idle node
(`ownRawNodeIdle`: no message queued, no unstable entry) show that it then holds no
messages and no entries, and committed entries still the next ones
(`ownRawNodeIdle_ready`). The append right is handed out inside the atomic update of the
send (`handshake_send_au_upd`, `ownRawNodeReady_handout`), so only a taken `Ready` gives
it away.

## The register: TaDa proposals over raft's client log

**2026-10-10 · accepted**

The register (`examples/register`) is linearizable at raft's commit, so raft's proposals
had to carry a client's atomic update. The design is TaDa style: the client owns the
state, and raft runs the update when it commits.

**The client log.** `cLog γ L` (a ghost variable, halves: one in `raftCommitInv`, one
the client's) holds the data of the committed client entries, first occurrences only
(`firstOcc`): a proposal retried, or delivered twice, appears in `L` once. `isEntryR`
records each entry's data (`entData`: none for raft's own entries, otherwise the data with
`isPropData` and `deposited`), so the committed log determines `L`.

**Deposit, fire, collect.** `node.Propose` with a fresh token (`propFresh γ d`, an
element of a ghost map whose authority the client holds) deposits a real Iris atomic
update `AU <{∃∃ L, cLog γ L}> @ ⊤∖↑raftN, ∅ <{cLog γ (L ++ [d]), COMM Q L}>` (`propAu`)
under `d` in `raftCommitInv`'s registry (`propsOwn`) and returns the persistent
`deposited γ d` with a ticket (`isProp`, `propTok`). A retry needs only `deposited`. When
the ghost commit makes the entry's data's first occurrence committed, it fires the update
(`fire_upto`, at mask `⊤∖↑raftN`); the later credit the update needs is stored in the
pending slot (`propSlot`: `d ∉ L ∗ £1 ∗ propAu`). The client trades its ticket for `Q`
(`node_collect`, two laters, so `do` takes two credits before it blocks). *Rejected*: a
predicate per entry (`entryP`) and linearizing at apply (both needed per-replica
machinery that the client log makes unnecessary); running `Q` at collect inside a fancy
update (it would not be the commit's linearization point).

**The register on top** keeps one invariant, `inv regN (∃ L, cLog γ L ∗ ghostVar γr.val ½
(regFold L) ∗ …)` (the other half of the value is the client's `regVal`). `do` wraps the client's update over `regVal` in the update over
`cLog` that it hands to `Propose` (`reg_propAu`): when fired, it opens `regInv`, runs the
client's update and moves both to `L ++ [d]`. The rest (the applied table, the waiters)
is plain physical state under the lock or the `run` goroutine.

**Fresh data.** `Propose` wants a token nobody had. The register mints one per
operation, keyed by its encoding's `(replica, seq)` (`MintOk`, `reg_mint`): `regInv`
holds the authority of the fresh-token map, each replica's last sequence number, and the
persistent record of each minted operation. A `seq` that would wrap is excluded by
operation credits (`opCred`: `2^64 - 1` per replica, one per `Put`/`Get`).

**Dedup by data, a Go change.** `apply` skipped an operation whose `seq` was at most the
replica's last applied one; with concurrent operations of one replica, `seq 2` committed
before `seq 1` makes it skip `seq 1`. It now skips an encoding already applied
(`applied map[string]bool`), which is exactly the first-occurrence rule of `cLog`.

**The storage.** raft's `StorageModel` is a class, so the register's storages are
recognized through a registry (`RegStor`: a ghost map from a `Storage` to its
`MemoryStorage` and names, in `regStorInv`). `NewStorage` registers a new storage; its
freshness comes from the registry keeping half of each registered storage's
`MemoryStorage` field. `InitialState` returns the voters slice itself (`RestartNode` takes
a fixed `ConfState`), and `run` refuses (spins) to append past `2^61` entries
(`MemoryStorage.Append`'s premise, which nothing else guarantees). `MemoryStorage.Append`
now takes an empty batch without a token (a `Ready`'s `appendRight` for no entries): the
promoted method still reads the `MemoryStorage` field, so `isReplica` keeps the storage's
record.

## The register's driver: specs at any storage registry, a filtering transport

- **No registry in the top-level statement.** The register's specs are stated under
  `[RegStor GF]`, a class holding the registry's ghost name, so that raft's `StorageModel`
  instance is an instance. A top-level statement must not assume a ghost name. `Main.spec`'s
  section has no `RegStor`, and `Main.wp_proof` takes each callee spec as
  `∀ [RegStor GF], X.spec`. The proof allocates the registry and sets
  `letI : RegStor GF := ⟨γ⟩`. The linked results pass in through implicit lambdas.
  `gen-link.py` already left `[RegStor GF]` off a spec that does not mention it. It now gives
  `[StorageModel GF]` to a spec stated over any storage model (`deliver`, `tick`).
- **Filter in Go rather than strengthen `Ready`.** Making `Ready` promise `NetMsgOk`-like facts of
  its outgoing messages would mean proving them per `send` site in raft. The type, `To` and the
  context are new per-message invariants in `ownRaftPhys`, like `OutTermOk`. The transport
  checks them in a few lines instead, and drops what fails. That costs nothing at run time,
  since raft sends nothing that fails, and the proof stays local to the example. Rejected:
  assuming them, which the brief forbade, or setting `Context = nil` in the copy, which
  rewrites messages rather than checking them.
- **Loops over a concrete voter list.** `Main` ranges over `[]uint64{1, 2, 3}` twice, building
  maps keyed by id. The invariants carry a big-sep over `take k` (resources produced, with
  pure map lookups), one over `drop k` (resources to consume), and the freshness of the
  `drop k` keys. Nodup of the list makes the keys distinct (`take_drop_ne`). The raft and
  sequence-token allocations come as big-seps over `listToSet`/`constMap` maps, which
  `bigSepM_constMap` turns into big-seps over the list.

---

## The watchable store: the plan, the interval tree's contract

**2026-10-11 · adopted** (the plan; the contract's design, unit 1b, to be written against it).
- **Contract first, the tree's proof last.** The watch guarantee is the result; the red-black
  interval tree (`pkg/adt`, 950 lines: insert/delete fixups with the `max` augmentation) is
  infrastructure, the longest single proof of the plan. So the tree gets model specs (a
  contract) first, pending (`?` in the link list: hypotheses of every result that reaches them,
  the recipes' mechanism), the watcher group and the store are proved over the contract, and
  the tree's proof comes last, discharging the hypotheses. *Rejected:* proving the tree first
  as the B-tree was (no pending hypotheses, but the guarantee two units later); taking the tree
  as six trusted axioms (fastest, but a trusted data structure in the mvcc collection).
- **String-affine intervals only.** The tree is generic over the `Comparable` interface
  (dynamic dispatch of `Compare`), but its only client, the watcher group, uses
  `StringAffineComparable` intervals (`""` as the end is +∞: a `WithFromKey` watch arrives
  with an empty, non-nil end). The model: intervals as pairs of Go strings under the affine
  order, the overlap test mirroring `Interval.Compare` exactly (`ivlCmp`: left if
  `b < b' ∧ e ≤ b'`, right if `b ≥ e'`, else 0), entries sorted by (begin, end) — `Insert`
  descends by begin then end and goes right on equality, rotations and the successor-based
  delete preserve the in-order sequence — and distinct (the group `Find`s before it
  `Insert`s; a precondition of `Insert`, so `Delete`'s removed entry is determined). `Stab q`
  is the entries overlapping `q` in that order; `Intersects q` whether there is one; `Find`
  the entry with exactly that interval. *Rejected:* a contract generic over a key type with a
  comparison and a predicate per comparable (the B-tree's `isItem`): no client needs it.
- **The nodes' pairs are read-only, for good.** A node's `iv` (`IntervalValue`: the interval
  and the `any` value) is written at creation only (`updateMax`, the rotations and the fixups
  touch `max`, the links and the colour), so `Find` and `Stab` return persistent read-only
  pointers to the nodes' `iv` fields (`p ↦□ …`): no lending protocol (as `unsafeVisit`'s) is
  needed, and the group reads `iv.Val` whenever it likes. The values are interface values the
  tree keeps opaque; the ownership of the watcher sets they wrap is the group's.
- **`ownIvt` is an `opaque` placeholder until unit 4.** The tree's ownership predicate
  `ownIvt t L` (the tree at `t` holds the entries `L`) is a Lean `opaque` constant (a
  definition with a hidden trivial body, not an axiom), used only through the contract's
  triples; unit 4 replaces it by the representation invariant (the sentinel, the colours, the
  `max` augmentation, the in-order list) and proves the triples, without changing any
  result's statement. *Rejected:* writing the representation invariant in unit 1b (unit 4's
  hardest design decision before any client exercises the contract).
- **Two corrections found by the tree's proof** (2026-10-12, unit 4a). (a) *The nodes' pairs
  are not read-only*: `Delete`'s two-children case copies the successor's `iv` into the deleted
  node (`z.iv = y.iv`, CLRS), so a `↦□` of a node's pair is unsound with `Delete` — a client
  holding `&z.iv` for good would later read another entry there. `Find` and `Stab` now *lend*
  the pointers at the tree's fraction with a wand giving `ownIvt` back (`p ↦{q} … ∗ (p ↦{q} …
  -∗ ownIvt t L q)`; `Stab`: a big-sep of the pointers and one wand); the watcher group reads
  `iv.Val` right after the call and returns the pointers before its next tree operation. (b)
  *`Stab` is wrong for a degenerate query*: `visit`'s pruning (`[node.begin, node.max)` against
  the query) misses entries when the query has `begin ≥ end` with a non-empty `begin` (a
  two-node counterexample: `[1, 10)` under `[5, 4)`, query `[5, 5)`); `Stab`'s spec takes
  `⌜b = "" ∨ affLt b e⌝`, which the only query the group makes, the point `[key, key ++ "\x00")`,
  satisfies. `Intersects` needs no premise (checked). Neither is an etcd bug: the client never
  holds a pointer across a delete nor stabs a degenerate interval.
- **The count's bound** (4a → 4b): `ownIvt` keeps `L.length < 2^63` because `Stab` returns
  `nil` on `count == 0` (a wrapped count would hide entries); `Insert` cannot establish it from
  the heap, so its spec takes `L.length + 1 < 2^63`, which the watcher group proves from its
  map's size bound (every interval has a member: `RangesOk`). `RbOk` is kept although no spec
  uses it: it is what makes the fixups provable in 4b/4c.
- **The watcher budget** (2026-10-12, 4b): the group cannot bound its size (Perennial's maps
  are bounded only at `len`, by assumption), so the bound is a resource, as the revision
  budget: `New` returns `2^63 - 3` watcher tokens, the stream's `Watch` spends one per watcher
  (`WatchParams.T`), the lock invariant keeps `live + unspent + 3 ≤ 2^63`; a cancel refunds
  nothing (a client that creates `2^63 - 3` watchers runs out, the truth about the program).
  *Rejected:* an axiom "a tree holds fewer than `2^63` entries", like Perennial's map
  assumption (smallest change, one more model assumption).
- **Duplicates in the tree** (2026-10-12, 4b; asked by the request path's session:
  `v3rpc.checkIntervals` inserts the same range twice, a legal request): the tree's invariant
  is non-strict (equal intervals in insertion order among equals, as the code's descent goes
  right of an equal), `Insert` takes no distinctness premise (so it is their `InsertAny`), and
  `Find`/`Delete` promise *some* entry with the interval (the code's `find` returns the topmost
  duplicate; which one `Delete` removes is not determined) — the watcher group, with one
  interval per range, recovers `find?`/`eraseP` by uniqueness. Their `Union` spec must also take
  the fraction and the count bound. Done at the merge (2026-10-12): `Union` takes `L.length + L'.length < 2^63`,
  which `checkIntervals` gets from a premise on the request (`delCount`, the deletes at every depth,
  in `txnReqWire`): nested transactions may share structure in memory, so no slice length bounds it.
- **The visitor's position** (2026-10-12, 4d; the third correction found by the tree's proof).
  `Visit`'s closure protocol (`ivVisitorOk q ivv I`: the visitor takes `I acc` and the lent pair,
  gives `I (acc ++ [(p, z)])`) held for any `acc`, so a visitor could not know how many entries it
  had seen; `Union`'s visitor calls `Insert`, whose count-bound premise needs that number below
  the other tree's size. The protocol now names the entries the visitor will see, `S` (`Visit`
  passes `stab (b, e) L`), and each call carries `⌜acc.map Prod.snd ++ [z] <+: S⌝`; the
  internal `visit` takes `S` with the premise that `acc` and its subtree's stabbed entries are a
  prefix of it. *Rejected:* a count bound as a premise of `Union` on the *sum* only, with the
  closure's invariant carrying the bound (it cannot: the invariant is over `acc`, whose length
  the old protocol did not relate to `L'`); an `ownIvt t L q` with the bound `L.length <
  2^63 - (something)` (changes every spec). No client of `Visit` but `Stab` and `Union`.
- **The hole's frames have locations** (2026-10-12, 4c). 4b's `ownCtx t s C n p mh` quantified
  the frames' nodes existentially: enough for `Insert` (the fixup only moves up, by reading
  `parent`), not for `Delete`, which reads a node back after a helper has walked up through
  its frame (`z` after `y.parent.updateMax`, to write `z.iv = y.iv`; `x.parent` after
  `rotateLeft(x.parent)` in the fixup's case 1 and `rotateRight(w)` in case 3). The helpers'
  specs now index the path by its frames' locations (`ownPathAt … ls …`, `ownCtxAt`, kept by
  `updateMax`, `replaceParent` and the rotations; the rotations also give the rotated-down
  node's fields back explicitly), and `find` returns the node under its path rather than
  behind a wand; the existential forms are derived lemmas, so 4b's proofs stand. *Rejected:*
  re-finding `z` by a second descent (not what the code does) and a separate predicate for
  `Delete` only (two hole predicates to keep in step). **The sentinel as `x`**: CLRS's `x`
  may be the sentinel (the spliced node had no child), whose `parent` the splice writes and
  whose colour the fixup's exit writes; `sentAt s x p` (`∃ v, s ↦ v ∗ ⌜x = s → v.parent = p⌝`)
  carries the one field the fixup reads, and `ownSentinel`'s existential absorbs the rest.
  `successor`'s walk up the parents (a node without a right child) is never reached by
  `Delete` (two children) and is not specified.

### The watcher group and the stream (unit 2)

**2026-10-11 · adopted** (design; the unit to be proved against it).
- **A group is a set of watcher pointers; the structures are indexes.** A watcher's `key`,
  `end`, `startRev`, `id` and `fcs` are never written after `watch()` builds it, so its range
  is a persistent fact of the pointer (`watcherFixed w r fcs`, as a key index's `kiKey`): a
  single key (`end == nil`) or `[key, end)` under the affine order (`end` empty, non-nil, is
  +∞: a `WithFromKey` watch). `ownWatcherGroup wg W` (`W` the members with their ranges) holds
  the key map, the interval tree (through its contract, the tree's values the `watcherSet`
  maps as interface values) and the all-watchers set, consistent with `W`: no empty set in
  the key map or the tree (both delete them), every set's members those of that key or
  interval. `add` is union (premise: not a member), `delete` removal returning membership,
  `contains key` a decidable existence over `W`, `size` the cardinality; `watcherSetByKey`
  lends (by a wand) the set of the members whose range holds the key, since the code returns
  its own maps by alias when it can (and a nil map when there is none: the specs say so).
- **The members' mutable state is the caller's.** `minRev`, `victim`, `compacted`, `restore`
  and `ch` are written by the store under its lock, or by the victim mover after taking the
  batch out, never through a group; a watcher in no group (a victim) has its state with the
  batch. So the group owns membership only, and `choose`, `chooseAll` and `newWatcherBatch`
  take the members' states as a big-sep (`watcherOwn w st`) and give them back. *Rejected:*
  the group owning its members' state (every move between groups and to the victims would
  split and rejoin it).
- **Batches are a pure fold.** `newWatcherBatch wg evs` is, per member, the fold of the events
  in order (`ebAdd`, mirroring `eventBatch.add`: a new revision counts, past
  `watchBatchMaxRevs` the first revision left out is `moreRev`), keeping those whose key the
  member's range holds at or above its `minRev`; the map's iteration order does not matter
  since each member's batch depends on the events only. An `mvccpb.Event` is a persistent
  fact of its pointer (`evIs e ev`: the type, the key-value pointer read-only for good, the
  previous key-value or `nil`): events are immutable once `End` has fixed a delete's
  `ModRevision`, and batches share them (the copies `newWatcherBatch` makes share the
  key-value).
- **Compaction and `restore` out of scope, as premises.** `chooseAll` (and so `choose`) take
  that no member is below `compactRev` or above `curRev` and none is restoring: the store's
  invariant on the unsynced group (unit 3), which excludes its compaction response and its
  panic. The group's own panics (`add watcher twice`, `removing missing watcher`, the tree's
  `Delete` failing) are plain `panic(...)`s on inputs the invariants exclude: premises, as
  `treeIndex.Put`'s, not panic outcomes (no logger to specify; the key index's total specs
  were for `zap.Logger.Panic`). `choose`'s subset is nondeterministic (map iteration): some
  subset of the right size, the group returned being `wg` itself or a fresh one.
- **The stream over an abstract `watchable`.** `watcher.go` is proved now against the
  `watchable` interface's contract (persistent triples `watch` — a live-watcher token and a
  cancel closure whose spec consumes it —, `progress`/`progressAll` — a persistent "is a
  watcher of this store" fact only, since `RequestProgress` runs without the stream's lock
  while `Cancel` may run —, `rev`), which unit 3's store satisfies. The stream's state (its
  `watchers` and `cancels` maps, `closed`, `nextID`) is under its own `sync.Mutex`; `Watch`
  returns a registration token per id (consumed by `Cancel`; `Close` cancels all). The
  constants `clientv3.AutoWatchID`/`InvalidWatchID` are translated with their values (`Watch`
  and `progressAll` compare against them).

### The watchable store's concurrency (unit 3)

**2026-10-12 · adopted** (design; three parts: 3a the write path, 3b the sync machinery, 3c the
theorem).
- **The store's lock invariant** (`watchableStore.mu`, its own `RWMutex`, shadowing the
  embedded store's `mu`): the synced and unsynced groups (unit 2's predicates), every
  registered watcher's state (`ownStates`), the victim batches (`ownWatcherBatch` each, with
  their watchers' states), and what unit 2's premises need: the three populations disjoint, a
  victim flagged, an unsynced watcher at or below the committed revision and a synced one
  above it — through a persistent lower bound of `currentRev` (`idxCert` of a committed log:
  `revMu` owns the revision, and it only grows), not the revision itself; no compaction
  (`compactMainRev = -1`, `isStore`) and no `restore`. A cancelled watcher (`ch = nil`) is in
  no population; `cancelWatcher` is idempotent, which the stream's contract relies on.
- **The guarantee as a channel protocol** (the cache's `InvWatcher` is the template): per
  stream channel, an invariant owning the channel (`ownChan`), a ghost log of every response
  sent (append-only; the senders are many — `notify` under the lock, `syncWatchers`, the victim
  mover outside it, the progress calls under a read lock — all non-blocking `select`s, each
  appending atomically with its send), and the consumer's received prefix, the in-flight
  buffer being the difference. Per watcher, a "next revision" ghost kept with its state (so
  with the lock, or with the victim mover while its batch is out): the responses sent for the
  watcher, plus any batch still pending for it, carry exactly the range's changes from
  `startRev` up to that revision, in revision order, each response's `Revision` at or above
  its events (`notify` sends one revision's events and advances to `rev + 1`; `syncWatchers`
  sends `[minRev, curRev]`'s, or up to `moreRev` under the cap; a victim's batch is resent
  as is). Progress responses interleave with no events. The client's side is a receive lemma,
  not a Go function (`wp_watch_receive`, as the cache's): receiving extends the prefix and
  yields the response's fact; the theorem (3c) reads the prefix per watch id. Safety only:
  nothing says a victim's batch is eventually sent (Iris proves no liveness).
- **The filters** are pure predicates: `F f := ∃ p, □ ∀ e ev, {{ evIs e ev }} f(e) {{ b;
  ⌜b = p ev⌝ }}` (etcd's `filterNoPut`/`filterNoDelete` are), and a watcher's delivered
  events are the range's changes with no filter true. *Rejected:* unconstrained filters and a
  theorem for unfiltered watches only.
- **Start revisions are at least 0** (`watch` and the stream's `Watch`): the documented domain
  (`0` is "now"). The code's behaviour on negatives is a remark: with no compaction, `-1` is
  read as `0` (with a warning in `rangeEvents`), and `≤ -2` makes `chooseAll` cancel the
  watcher with a compaction response at revision `-1` (`minRev < compactMainRev`), which the
  gRPC layer does not prevent — to reproduce with a Go test if wanted as a finding.
  *Rejected:* modelling the compaction-response path for an input nobody sends.
- **Contract changes**: `storeTxnWrite.End` releases the changes' key-values (the wrapper
  `watchableStoreTxnWrite.End` fixes a delete's `ModRevision` on them, then shares them with
  the watchers for good, `evIs`; the inner `End` reads only the slice's length): the write
  transaction's predicate is split so that `End` takes it without `changesAre`. `NewStore`'s
  `ReadView`/`WriteView` become owned fields (`newWatchableStore` overwrites them).
  `time.NewTicker`/`Ticker.Reset`/`Stop` are axioms with a bag channel, as `time.After`.
  The `watchable` contract of the stream (unit 2) is instantiated with the store's
  `WatchParams`: `IW` the registration, `WC` cancelled, `C` the channel's invariant, `F` the
  filter predicate, `CR` the close right with the registered watchers.
- **Refinements for 3a** (2026-10-12, after the second merge with `lean`): (1) **the
  history carries the change.** `notify` sends a revision's events before the inner `End`
  commits it (program order), and on the merged base the commit (`idxWriter_commit`) needs
  `revMu`'s half of the committed log's authority (`idxLogAuth`), so no certificate of the
  revision exists when its events go on the channel; the history's lower bound the writer
  holds (`histShape ilog pend`, advanced at every `Put`/`Tombstone`) is persistent before the
  commit but records keys, revisions and tombstones only. So `Ev` gains the change itself
  (`change : Change`; `key`/`tomb` become projections): a history lower bound then determines
  the log with its values, the response's fact is such a lower bound, and certificates
  (lower bounds of the same list) are comparable with it without any lock — the watch
  theorem is lock-free. *Rejected:* a ghost commit before `notify` (needs `revMu`'s half); a
  separate watch-log ghost (a second list to thread through `writerRes`, both `End`s,
  `NewStore` and `idxCert`); a theorem stated under a read lock only. (2) **The tree
  contract gets a fraction** (`ownIvt t L q`): `progressIfSync` sends progress responses
  under the store's *read* lock, so the lock's resource must be fractional, hence the groups,
  hence the tree (reads at any fraction, `Insert`/`Delete` at one; unit 4 proves it that
  way, as the B-tree's reads are). A fractional per-watcher "live" ghost (not an exclusive
  token) says a registered watcher is not cancelled, which a sender needs against the
  channel's "closed → all cancelled" clause. (3) **The `watchable` contract gains an owned
  resource** `P.R` for `rev`/`progress`/`progressAll` (the store's: a reader slot,
  `storeReader`, since `store.Rev` opens a read transaction), passed through the stream's
  `Rev`/`RequestProgress`/`RequestProgressAll`; `watch` and the stream's `Watch` take
  `0 ≤ startRev`.
- **Refinements for 3b** (2026-10-12): the backend contract's range read (`keyRangeReadSpec`,
  bbolt's cursor order: the bytes order, which `u64Be` makes the revisions' order) is a
  strengthening of a premise (`isKeyBackend` is `NewStore`'s), so no proof changed; `store.Close`
  is a trust-boundary axiom with a close-once right (`storeCloser`), as `restore`; tickers are
  axioms faithful to Go (`Reset` and `NewTicker` need a positive duration), and `time.Since` is
  assumed positive — the honest statement of a real hazard (`issues/
  etcd-watch-sync-ticker-reset-zero.md`) rather than a total `Reset` that would be false;
  the watcher group's all-watchers map is explicit (`ownWatcherGroupAt`) where a loop ranges
  over it while deleting; the notified log is a prefix of the certified one (`σ.Lmu <+: C`),
  which is all the sync machinery needs.
- **3c, the theorem's form** (2026-10-12): the guarantee is a persistent fact the receive
  lemma yields per response (`watchRecvOk`), not a statement over the whole channel history:
  the client holds only its received prefix and the channel's invariant, and each receive
  extends the fact; the theorems relate it to any certificate of the committed log (the history
  lower bounds are comparable), so a client that also reads the store gets the delivered events
  as the committed log's. The deliveries' revision cuts (`delivsCut`) are in the invariant
  because a received prefix of the flattened events must end at a revision boundary to be
  stated as `watchEvents … lo d`. *Rejected:* a theorem over `sent` (the sender's view: the
  client never holds it); per-delivery bounds in `Deliv` itself (every 3a/3b proof building a
  delivery would change; the cut as a separate persistent clause touched three).
- **The post-lock hook** (2026-10-12, the third merge with `lean`; "mvcc: the batch lock runs
  the hook"): the watchable store's write path takes the hook's resources exactly as the inner
  calls do, nothing of its own: `watchableStore.Write` takes `hookIs γ.st P f ∗ Pre ∗ □ {P ∗
  Pre} f() {Q}` and returns `Q` (as `store.Write`); `watchableStoreTxnWrite.End` takes
  `hookIs γ.st P f ∗ P` (what the inner `metricsTxnWrite.End`'s `txnEndPre` needs). The hook
  lives in the inner store's transaction (`storeTxnWriteCore` carries `hookIs γ Pw fw`, `End`
  makes `P` agree with `Pw` by `hookIs_agree_lc`), so `isWatchTxnWrite` is unchanged, and the
  caller's update (`Q ={⊤}=∗ P ∗ Post`) stays the caller's, between `Write` and `End`.

## mvcc: the log of changes as the model, the key index as a function of its events

**2026-10-10 · accepted** (Lean-first; the plan discussed with the user: "start on the mvcc KV
core, phase one")

Goal: verify the KV core of etcd's `server/v3/storage/mvcc` (`revision.go`, `key_index.go`,
`index.go`, `kv.go`, `kv_view.go`, `kvstore_txn.go`, `metrics_txn.go`) and, eventually, state its
result in the client model's terms (`InvEtcd.lean`, `InvEtcdTxn.lean`), so that `etcdState`,
`EtcdStep` and the history laws become theorems of the server. Restore, compaction, hashing and
the watchable store are out of scope for this phase. `Proof/go_etcd_io/etcd/server/v3/storage/mvcc/`.

**Decision: the model is a log of changes; everything else is a function of it.** `Model.lean`:
`Log := List (List Change)`, revision `r`'s changes (`put key value lease` or `del key`) in
sub-revision order; `stateAt log r` applies them with the client model's `putKv` (a new key is
created at `r` with version 1, an existing one keeps its create revision and gets version + 1),
a delete filtering the key out. The key index is `indexOf (evsOf log)`: the sorted
`(key, KeyIndex)` list built event by event with `kiPut`/`kiTombstone` exactly as the code
does, `kiGet`/`kiFindGen`/`genWalk` mirroring `get`/`findGeneration`/`walk`; the backend's key
bucket is `bucketOf log` (the bytes of a change's revision, `revBytes`, mapped to the
protobuf encoding `kvEncode` of what it wrote; `kvEncode` is opaque: `proto.Marshal`/`Unmarshal`
are the trust boundary). The store's ghost state will be the committed log (a monotone list)
and the in-flight write transaction's pending changes; the index and the bucket are determined,
so the invariants are equations, and the model's main theorem (to prove next, `kiGet_indexOf`)
says what the index answers of a key at a revision: the state's key-value there. *Rejected:*
a relational invariant between the index's generations and the states (every proof would carry
the generation structure); storing the key-value in a put change (then `LogWf` must say it is
what `putKv` computes: the fold computes it instead).

**Decision: the code-level specs are the model's functions, nothing more.** `keyIndex.put` is
`kiPut` (precondition: a revision above `modified`, else the code panics), `get` is `kiGet`
(`kiGetVal`: the 4-tuple with `ErrRevisionNotFound`), `findGeneration` returns `genPtr gs
(kiFindGen ki rev)` (the address of a generation in the slice, or nil), `walk` returns
`genWalk` for a closure deciding a predicate (`walkFnSpec`; `get`'s closure reads its `atRev`
cell, made persistent), `tombstone` is `kiTombstone` or `ErrRevisionNotFound` if the last
generation is empty (`kiLastEmpty`). The semantic content (what `kiGet` of the index built from
a log means) is a pure theorem, separate from the code proofs. The pure lemmas the proofs need
(`genWalk_eq_some`, `kiFindGenAux_{skip,tomb,found,next}`, `set_last`, ...) are in `Model.lean`.

**Representation (`Defs.lean`).** `ownKi p gs ki dq`: the mutable fields `modified` and
`generations` (slice `gs`) of a `*keyIndex`, at fraction `dq` (readers hold a fraction under the
index's `RLock`); the key is a persistent `kiKey` (never written after `&keyIndex{key}`).
`ownGens gs gens dq` is `∃ gvs, gs ↦*{dq} gvs ∗ cap ∗ ownGensL dq gvs gens`, `ownGensL`
recursive on the two lists (as the btree's `ownNodes`): `ownGens_acc`/`ownGens_acc_z` borrow
the `i`-th generation (its element points-to, as `&gs[i]`, and `ownGen` of its model) and give
it back with a new value, the model list `set`; `ownGensL_app` appends. *Rejected:* an indexed
big-sep `[∗list] i ↦ gv ∈ gvs, ownGen gv (gens.getD i _)` (`set` on it needs the two-list
`bigSepL_lookup_acc_impl` dance).

**Loads through a borrowed struct points-to.** Perennial's `wp_load`/`wp_auto` load a field
through `l ↦{dq} v` (the generated `AccessStrict` instances) only for a literal fraction and a
load at the head of the expression; a load of `g.revs` through `g ↦{dq} gv` with `dq` a variable
(a reader), or nested under `let:`/`Convert` (the `len(g.revs) == 0` tests), finds no
points-to. So the proofs split the borrowed generation into its field points-tos
(`gen_split`, `rev_split`; `gen_combine`, `gen_combine'`, `rev_combine` to refold) and load from
those, as the btree proofs do with `nodeFields`; and `wp_pures; wp_load` where `wp_auto`
reports no progress on a full-fraction nested load (`keyIndex.put`).

**Translation.** `Code/go_etcd_io/etcd/server/v3/storage/mvcc.toml` lists the KV core's functions
with bodies, including the **promoted methods of embedded fields** (`treeIndex.Lock` from its
`RWMutex`, `storeTxnRead.Range` from `storeTxnCommon`, `metricsTxnWrite.FirstRev` from the
embedded interface, ...): goose emits their `MethodUnfold` wrappers only for names the filter
translates. `store`'s typed points-to was axiomatized until its fields' packages were imported
(`time`, `pkg/v3/schedule`, names only); prometheus (`metrics.go`'s counters and gauges) is
translated names-only (`Code/github_com/prometheus/client_golang/prometheus.toml`), and its
`Inc`/`Dec`/`Add` on the package's variables are package facts (`mvccInit`, `Base.lean`:
metrics have no effect here), as are the three error variables. Two translator changes were
needed, in `/shared/perennial-mvcc` (branch `lean`, on `7c93f27aa`; not yet pushed or pinned):
`for i := range n` (Go 1.22: `kvstore_txn.go`'s `rangeKeys`), translated as the three-clause
loop it stands for (`$range` evaluated once, a counter cell `$range_i`); and `float64(n)` of
an integer (`metrics_txn.go`'s `End`), an uninterpreted function in `FloatOps`
(`int64ToFloat64`, ...) with `Float64Semantics` rules. Until the Perennial pin moves,
`etc/goose.py --check` with the pinned translator fails on mvcc.

**Next.** The pure theorem `kiGet_indexOf`; `index.go` (`treeIndex` over the verified btree:
`ownBTree` with `isItem p (k, p') := ⌜p = p'⌝ ∗ kiKey p k` and the mutable `ownKi`s beside it,
under the index's `RWMutex` guard: `P q := ∃ elog, ghostVar γ.elog (q/2) elog ∗ ownTreeIndex
(indexOf elog) q`); the revision encoding (`revBytes`, big-endian as the consistent index's);
then the transactions: `revMu`'s fractional invariant (`currentRev`, the committed log's lower
bound, the bucket's persistent entries), the batch lock's resources (the writer's halves, the
pending changes), the backend contract (`ConcurrentReadTx`'s snapshot of the written-back
bucket, the batch transaction's `UnsafeSeqPut`/`UnsafeRange`/`Unlock` as write-back), the
lessor's `GetLease`/`Attach`/`Detach` contract; `NewStore` on a fresh backend (a ghost
allocation first, `restore` later).

### The transactions: the store's locks and the backend contract

**2026-10-11 · proposed** (the read transactions first; the design for review, after
`revision.go` was proved)

What `kvstore.go`/`kvstore_txn.go` do with their three locks, and what each holds here:

- **`s.mu` (RWMutex)** is read-locked by every transaction (`Read` and `Write` both take
  `RLock`; the writers exclude each other through the batch transaction's lock) and
  write-locked by `restore`, `Compact`'s barrier and `Close`, which are out of scope. Its
  resource is `True`: the fields `restore` rewrites (`kvindex`, `currentRev`, ...) are
  persistent (`↦□`) in `isStore`, as if the store were never restored or closed. A transaction
  needs a reader slot of it (`sync.ownRWMutex`), as of the index's lock.
- **`s.revMu` (RWMutex)** protects `currentRev` and `compactMainRev` and, with them, *which
  revisions are in the backend*: `storeTxnWrite.End` takes it exclusively around `currentRev++`
  **and** the batch transaction's `Unlock` (the write-back of the pending puts into the read
  buffer), and `Read` takes it shared around `ConcurrentReadTx()` (the snapshot of the read
  buffer) and the read of `currentRev`. So a reader's snapshot holds exactly the revisions
  `≤ currentRev` it read. Its resource (`revMuInv s γ`): `∃ log, currentRev ↦ W64 (log.length - 1)
  ∗ compactMainRev ↦ W64 (-1) ∗ idxCert γ log ∗ bucketView (bucketMap log)`, with `log` the
  committed log (the index's certificate `idxCert γ log` says the index's history extends it;
  the index may already hold the pending revision's events, which `reader_answer` shows do not
  change answers at revisions `≤ currentRev`). `compactMainRev` stays `-1` (no compaction in
  scope). `bucketView` is the backend's view of the `Key` bucket (below).
- **The index's `RWMutex`** as before (`InvIndex.lean`).

**The backend contract** (`InvStore.lean`, the shape of the consistent index's
`InvCindex.lean`: linearizable reads of an abstract view at a mask, as the trust boundary of
bbolt and the read buffer):

- `bucketView m : IProp` is a parameter (the store instantiates it with a ghost map authority
  whose fragments are persistent, as the bucket only grows: `bucketMap log` is monotone in
  `log`), `m : GMap GoString GoString`, the `Key` bucket's written-back contents.
- `keyReadSnap rt m`: a `ReadTx` over a **snapshot** `m` (persistent): `RLock`/`RUnlock`
  return; `UnsafeRange(schema.Key, k, nil, 0)` returns `([k], [v])` with `v = m[k]` if `k ∈ m`,
  else `([], [])` (read-only slices, `↦*□`).
- `isKeyBackend b E bucketView`: `ConcurrentReadTx()` is a linearizable read of the view at
  mask `E` (`readAU`, as `metaRangeSpec`) returning `keyReadSnap rt m` of the `m` read;
  `ReadTx()` the same (the shared-buffer mode is also a snapshot while `s.revMu` is held
  shared: the writer's write-back is under `revMu` exclusively; `rangeKeys` is used in both
  modes); `BatchTx()` returns the batch transaction (its contract with the writes, later).
- The entries' values are the opaque `kvEncode kv` (`Model.lean`); `proto.Unmarshal(v, p)` with
  `v = kvEncode kv` fills `*p` with `kv`'s fields and returns `nil` (a trust-boundary axiom,
  `Spec/google_golang_org/protobuf/proto/Unmarshal.lean`); `proto.Marshal` the converse (the
  writers, later).

**The read transaction.** `isTxnRead tr γ log rev` (what `store.Read` returns, through the
`metricsTxnWrite{&txnReadWrite{tr}}` wrappers whose `Range`/`End` forward): the
`storeTxnRead`'s fields (`s`, the `tx` of both `UnsafeReader` and `ReadTx` type: the same
snapshot reader, `firstRev = -1`, `rev`, `trace`), the snapshot `keyReadSnap tx m` with
`bucketMap log ⊆ m` (the snapshot may be later than the certified log: a writer's write-back
between the reader's `ConcurrentReadTx()` and ... no: both are under `revMu`, so `m = bucketMap
log` exactly; kept as `⊆` since only inclusion is used), `idxCert γ log` with
`rev = log.length - 1`, and the reader slots of `s.mu` and the index (`idxReader`) held until
`End`. `Range(ctx, key, end, ro)` for `ro.Rev ≤ rev` and not `CountOnly`/`FastKeysOnly`
returns `RangeResult{KVs, Count, Rev = rev}` where `KVs` are fresh `*KeyValue`s of the
model's answer (`rangeAnswers`, `rangeTaken` of `Hist.lean`, at `ro.Rev` or `rev` if
`ro.Rev ≤ 0`): each key-value `kv` of the state at that revision in key order, limited and
counted as `treeIndex.Revisions` says; the three `CountOnly`/`FastKeysOnly`/`ErrFutureRev`
branches are the index's answers alone (`ErrCompacted` is unreachable with `compactMainRev =
-1`). `ctx` is a `context.isContext` whose `Done()` may be ready: then `Range` returns a non-nil
error and no result (the spec allows both outcomes, as etcd does).

*Rejected:* the reader keeping `s.revMu` shared for the whole transaction (it does not: `Read`
releases it before returning); a snapshot as a copy of the bucket's `GMap` in the reader
(it is: `keyReadSnap` is exactly that, as a persistent spec, no ghost state).

*Scope.* `Read` with both modes, `Range`/`FirstRev`/`Rev`/`End` of the read transaction and
the wrappers, `readView.Range`/`Rev`/`FirstRev`; `Write`/`Put`/`DeleteRange`/`End` next, with
the batch transaction's contract and the lessor's.
### `key_index.go`'s panics as outcomes

**2026-10-11 · adopted.** The key index's `put`, `tombstone` and `get` call `lg.Panic` on
inputs the tree index never gives them (a revision not above `modified`, an empty key index).
Their specs excluded those inputs by precondition ("else the code panics" as a remark). With
Perennial's panic outcome (`PanicV p`, a value the postcondition receives) the remark is now
formal: the specs are over all inputs, the former precondition selects the normal case, and the
other case is `r = PanicV #msg` with zap's message and the key index unchanged (every check
precedes every write; `tombstone`'s cases in the code's order, including `put`'s panic through
it). The callers keep their preconditions and resolve the `if`. `zap.Logger.Panic`'s axiom:
with a non-nil logger, the panic with the message (zapcore's `panic(ce.Message)`, whatever the
core); `zap.Logger.Fatal`'s: never returns (`os.Exit(1)`: divergence, as Perennial's
`AngelicExit`, so any postcondition — `False`), reached by no verified function (the protobuf
axioms never fail), hence not linked: a linked but uncalled result would be an exported root and
put its axiom in the baseline. The non-nil logger is threaded through `isTreeIndex` (a persistent
fact), `newTreeIndex`'s premise and `NewStore` (which has it after its `lg == nil` check).
*Rejected:* `Panic` without the non-nil premise (`∃ p, r = PanicV p`: a nil logger panics with a
nil dereference, not the message), which would have made the key index's specs say "some
panic"; modelling `Fatal` as a panic (a `recover` could catch it, which an exit cannot be).

### The write transactions: the batch lock's resources, the backend's write path, the lessor

**2026-10-11 · adopted** (the write side specified at the checkpoint `628f69632`, the proofs
finished the same day)

What `store.Write`, `storeTxnWrite.put`/`delete`/`deleteRange`/`End` do, and what each holds:

- **The batch transaction** (`backend.BatchTx`, names-only: the trust boundary of the backend's
  write path) is the writers' lock: `Write` takes it (`LockInsideApply`) after `s.mu` shared, and
  `End` releases it (`Unlock`). Its contract (`batchTxSpec bt View W Locked`, `InvStore.lean`):
  `LockInsideApply()` gives `Locked []` and the lock's resource `W`; `UnsafeSeqPut(Key, k, v)`
  under it appends `(k, v)` to the token's list; `Unlock()` with no puts takes `W` back and
  leaves the bucket as it is, with puts it takes `W` and the bucket's full view `View 1 m` and
  returns the view with the puts inserted in order (the write-back into the read buffer).
  `isKeyBackend` now also gives `BatchTx()`. The token's predicate `Locked` is existential
  (`isBatchTx`): the backend's own.
- **The batch lock's resource** (`W := writerRes s γ`): the index writer's handle at the committed
  log with no pending change (`idxWriter γ.idx ilog []`), half the committed-log ghost variable
  `γ.clog` (the other half under `s.revMu`: `End` agrees them and updates both), half of
  `currentRev` (`store.Write` reads `beginRev` under the batch lock alone, without `s.revMu`;
  `End` joins the halves to increment it), the index's certificate of `ilog`, and the revision
  budget: `ownTokAuth γ.revs ntok` with `ilog.length + ntok + 3 ≤ 2 ^ 63`. A write transaction
  costs one `revToken γ` (`store.Write`'s precondition; `NewStore`, later, hands out
  `2 ^ 63 - 5`: the initial log has length 2), which `End` returns to the authority when it commits, so `currentRev` never
  overflows and the pending revision's index is below `2 ^ 63` (the index's own bound).
- **`s.revMu`** (`revMuInv`) now holds its half of `currentRev` and of `γ.clog`; `End` with a
  change takes it exclusively around `currentRev++` and the batch `Unlock` (the write-back),
  as the code does, and releases it with the committed log one revision longer and the bucket
  `bucketMap (ilog ++ [pend])` (`bucketMap_append`: the old entries then the pending puts).
  Without a change `End` only unlocks (no revision is made: `commitLog`).
- **The transaction** (`storeTxnWriteIs tw s γ ilog pend`): the `storeTxnWrite`'s fields
  (`beginRev = ilog.length - 1`, `changes` the `*mvccpb.KeyValue`s written, `changesAre`: the
  `i`-th holds `changeKv` of the `i`-th pending change), the batch transaction locked with the
  pending puts (`Locked (pendPuts ilog pend)`: each change's revision bytes to its encoding),
  the writer's resources with the pending changes in the index writer's handle, the revision
  token and the transaction's reader slots. `put` and `delete` append a change: the index's
  `Put`/`Tombstone` (the writer's `idxWriter_commit` discipline of `InvIndex.lean`), the batch
  `UnsafeSeqPut` of `revBytes`/`kvEncode` (`proto.Marshal` is a trust-boundary axiom, the
  converse of `Unmarshal`: `kvEncode kv` of the pointer's fields), the `changes` append
  (`changesAre_snoc`). `put` reads the index first (`treeIndex.Get` by the writer: the specs of
  `Get`/`Range` take an `IdxKnow`, the certificate or the writer's handle, `idxKnows`;
  `changeKv_put` says the index's answer at the pending revision gives the create revision and
  version the code computes). `deleteRange` ranges the index at `writeRev` (the pending
  revision if it has a change, else the committed log's last) and deletes each key
  (`delKeys`: present after the pending changes, `delKeys_present`; distinct, `delKeys_nodup`).
- **The lessor** (`lease.Lessor`, names-only: the trust boundary): `GetLease(item)` returns some
  id; `Attach(id, items)` of a *granted* lease (`leaseKnown γ id`, a persistent ghost fact of
  `γ.leases` that `Grant`, out of scope, allocates) returns `nil`, so `put`'s panic on a failed
  `Attach` is unreachable: `Put`'s precondition is `leaseID = NoLease ∨ leaseKnown γ leaseID`;
  `Detach` returns anything (the code logs an error: `zap.Logger.Error`, an axiom, as
  `zap.Error`). Leases have no liveness here (as in the client's transaction model).
- **The wrappers**: `metricsTxnWrite.End` over a `TxnKind` (`isTxn`: a read or a write
  transaction behind the wrapper; `txnEndPost`: nothing, or the certificate of `commitLog`),
  so `readView` and `writeView` share it; `writeView.Put`/`DeleteRange` open a transaction with
  a token and return with the certificate of the committed log (`ilog ++ [[.put k v l]]`, or
  `commitLog ilog (delKeys ...)`) and the revision.

**The writer's range read** (2026-10-11, later the same day · adopted): `storeTxnWrite.Range`
ranges at `writeRev` and reads the bucket through the *batch* transaction, which sees its own
pending puts. So (1) the bucket view is split: `revMuInv` holds `bucketView γ q.half`, the batch
lock's resource `writerRes` the other half at the committed log (the two halves agree,
`bucketView_halves`); `End` joins them for the write-back; (2) `batchTxSpec` gains an
`UnsafeRange(Key, k, nil, 0)` triple under `Locked l ∗ View q m` answering from `m` with `l`
inserted, and its `Unlock` with puts becomes `{{ Locked l ∗ View 1 m ∗ (View 1 m' -∗ W ∗ Q) }}
Unlock() {{ Q }}` with `m'` the written-back map: the backend writes back, then releases the
lock with `W` built from the new view (the old triple follows; needed because `W` now holds
the view at the new committed log); (3) `rangeKeys`'s spec is stated over what it uses: the
`storeTxnCommon` fields `s`, `tx`, `trace` at a fraction, an owned reader capability
`keyReader rt m R` (`R` threaded through: `True` with a read transaction's snapshot,
`Locked (pendPuts ilog pend) ∗ bucketView γ ½ (bucketMap ilog)` for the writer, reading
`bucketMap (ilog ++ [pend])`), the index knowledge `idxKnows γ.idx kn` (the certificate or the
writer's handle, as `Get`/`Range`/`Revisions`/`CountRevisions` now all take) and
`0 ≤ rev < log.length` (all the proof needs; the read side's `rev = log.length - 1` implies it).
`storeTxnWrite.Range`'s result is `rangeOutcome` at `ilog ++ [pend]` and `writeRev ilog pend`:
the transaction reads its own pending revision when it has a change, else the committed log's
last (an empty pending revision changes nothing).

**The constructor on a fresh backend** (2026-10-11, later · adopted): `NewStore` is translated;
`restore` (and what it calls) is not: on a fresh backend it is a trust-boundary axiom, the
identity on the store's verified state (`currentRev = 1`, `compactMainRev = -1`, the empty
bucket view, `s.revMu` fresh), returning `nil`; a backend with data is out of scope (the real
`restore` rebuilds the index from the bucket). The fresh-backend assumption is a *premise*: the
caller gives the empty bucket view `ghostMapAuth γb 1 ∅` (the backend's creator's fact), not
something the store allocates — conjuring the view inside the store would let the proof assume
any bucket contents. The backend contract is quantified over the store's location and names with
that bucket name (`∀ s γ, γ.bucket = γb → isKeyBackend b (bucketView γ) (writerRes s γ)`: the
batch lock's resource `writerRes s γ` is the store's choice, as a lock's resource is its
client's), and the lessor's ghost name `γl` is the lessor's own (`isLessor le γl` over a
`GName`; `leaseKnown γl id`). The batch lock starts empty: `LockOutsideApply()` gives `Locked []`
and no resource, and `NewStore` deposits `writerRes` at its first no-puts `Unlock`; from then on
`LockInsideApply` hands it out as before. `NewStore` allocates the rest of the ghost state (the
log `[[], []]`, two empty revisions so `currentRev = 1`; the revision budget: `2 ^ 63 - 5`
tokens) and returns `isStore`, the two views, every reader slot and the tokens. The configuration
and the hash storage are not modelled (`NewHashStorage`, `schedule.NewFIFOScheduler`,
`zap.NewNop`, `schema.UnsafeCreateMetaBucket` are axioms returning a value); the range deleter
the lessor is given (a closure over `store.Write`) is opaque to it, and the lessor's later calls
of it on lease expiry are outside the model.

**`KeyIndex` and `Insert` under the history** (2026-10-11, later · adopted): the last two
methods of `index.go` are used only by `restore` (on its private index, before any reader) and
the tests, and `restore` mutates the key indexes it gets from `KeyIndex` outside the lock, which
the live index's invariant (the key indexes owned by the lock) cannot express. They are
specified under that invariant anyway, honestly narrower than their Go signatures: the history
fixes the tree's keys and their indexes, so `KeyIndex` promises only what survives the lock's
release (the pointer carries its key, `kiKey`, persistent; it is not `nil` when the reader's log
gives the key an index, `kiOfKey … ≠ kiEmpty`, which later events keep; with the writer's
knowledge the converse too) and `Insert` by the writer, with an owned key index equal to what
its log gives the key, always replaces the key's entry (the premise `≠ kiEmpty` puts the key in
the tree) and returns the old one, owned; the writer's log is unchanged. *Rejected:* making
`isTreeIndex` parametric in the lock's resource so a private index could use them at the tree
level with its key indexes owned: every index spec and proof and `InvStore` would change, for a
client (`restore`) that is out of scope.

*Rejected:* the whole `storeTxnWrite` points-to inside `storeTxnWriteIs` for the whole proof of
`put`/`delete` (the code reads `tw.s` for the lessor after the change is made: the predicate is
rebuilt at each return through a wand over `tw`'s points-to); `End` holding `s.revMu` for the
whole write-back only (it also needs the batch lock's resource back, which `Unlock` returns
through `W`).

## Leasing: the protocol as a premise on the history

**2026-10-10 · proposed** (units 1 and 2 of `client/v3/leasing`; the premise's form, the holder's
writes and the cache's lock decided here, for review)

`client/v3/leasing` caches a key `k` at the client (the *holder*) whose session lease owns the
*lease key* `pfx ++ k`; every leasing client modifies `k` in a transaction guarded by
`CreateRevision(pfx ++ k) < g + 1` (`g = 0`, or the holder's own entry revision), and a writer
that is not the holder first puts `"REVOKE"` into the lease key and waits for the holder to delete
it. Whether etcd's history obeys this depends on every writer of the deployment, not on one
client's code. `InvLeasingModel.lean`.

- **A premise, not an axiom.** `LeasingProtocol pfx h` (persistent) is a hypothesis the leasing
  theorems take: it holds of a deployment where every writer of a data key is a leasing client
  of prefix `pfx`, and nobody else writes lease keys. *Rejected:* an axiom (it is false of a
  deployment with a plain-client writer); proving it from the leasing clients' code (a ghost
  protocol over every client's transactions: what units 4 and 5 may establish for leasing
  clients, but a non-leasing writer always breaks it).
- **Its exact form.** A history `h` (`LeasingHist`): etcd's whole-keyspace state at every revision
  `z ≥ 0` (`h.st z`, linked to the model by `□ ∀ r ≥ 0, etcdState r "" (h.st r)`, keys unique),
  and `h.writer z`, the session lease of the leasing client whose transaction made revision `z`.
  `LeasingStepOk` for every `0 < z < 2^63` and data key `k` (outside `pfx`): (1) if `k`'s record
  changes at `z`, `pfx ++ k` is absent at `z - 1`, or present with a lease `L ≠ 0` and
  `h.writer z = L` (the holder's write); (2) a lease key that keeps its create revision keeps its
  lease (the only write to an existing lease key is the `"REVOKE"` put, `WithIgnoreLease`). The
  model's `etcdState` gives states only at observed revisions; the premise names every revision,
  so that `leased_value_stable` can walk from one observed revision to another
  (`etcdState_create_persist` carries the lease key's presence, `LeasingStepOk` the record).
- **The holder's own writes** (*changed from the plan*, which said "`k` changes only while
  `pfx ++ k` is absent"): false, since the holder writes `k` while holding the lease (its guard is
  its own entry's revision) and updates its cache (`Update`, `delete`). The model does not record
  who wrote a revision, so the premise names the writer (`h.writer`), and the lemmas exclude the
  holder's transactions explicitly: `leased_value_stable` (the lease key present at `a` and `b`
  with one create revision, no transaction of the holder in `(a, b]` ⇒ `k`'s record at `b` is its
  record at `a`); `revoked_protects` (a non-holder changes `k` after the `"REVOKE"` only once the
  incarnation is gone). How the holder knows which revisions are its own is unit 4's (its cache
  serializes its writes behind the waiter channels). *Rejected:* an abstract "holder write"
  predicate (vacuous unless instantiated); identifying the holder through the guard value `g`
  (any client can read a lease key's create revision; a range delete's guard is a maximum).
- **The lease-expiry window is excluded by the statements, not the premise.** When the holder's
  session lease expires, etcd deletes its lease keys (a step changing no data key) and other
  writers may then write `k`, while the holder's cache still serves `k` until its session monitor
  resets the entries. The premise allows it; the lemmas speak of a lease key still present. A
  cached answer is `k`'s record at a revision at which the lease key existed: not linearizable,
  and not claimed to be.
- **The whole keyspace.** The leasing KV's keys (data and lease) are anywhere in the keyspace, so
  its contracts are used at prefix `""` (`EtcdStateWf ""`, `TxnModel.Under ""` hold of every key).
  *Rejected:* a pair of prefixes (the model has no law relating two prefixes' states).
- **Contract extension: `WithIgnoreLease`.** `TxnOp.putKeep` (a put keeping the key's lease;
  `txnOpOf` maps a put with `ignoreLease` and no lease to it); on a missing key etcd fails the
  transaction, and the model's choice there (no lease) is never claimed by a successful response.
  `Compare(CreateRevision(lkey).WithRange(lend), "<", n)` needed no change (`cmpHolds` is over the
  range's keys, the zero key-value for an empty range, as etcd's `applyCompare`). Nested
  transactions (`OpTxn`, `txnLeasing.serverTxn`) and owned range responses (the cache stores and
  mutates the acquisition's response, which the contract gives read-only) are left to the units
  that use them (4 and 5).

### The lease cache: one lock, exact transitions, frozen entries

`InvLeaseCache.lean`. The cache (`leaseCache`: the entries map, the revocation times, the latest
header, under an `RWMutex`) is shared by every goroutine of the leasing KV (gets, puts, the lease
monitors, the session monitor, `clearOldRevokes`), and its lock also guards the KV's `session` and
`sessionc` fields (kv.go).

- **The lock invariant is fractional** (`RWMutex` readers hold `rfrac`): the state is a record of
  pure values (`LeaseCacheSt`, `LeaseEntry`, `CachedKv`, `HdrM`), held in a ghost variable so the
  fractions agree; the physical resources are field points-tos with fraction `q` (`lcOwn`,
  `entryOwn`, `respOwn`, `cachedKvOwn`; field by field, since the proof mode does not find a
  struct field's points-to inside a struct's), read-only headers, and the entries' persistent
  facts. *Rejected:* a `Mutex`-style invariant (readers would serialize: not the code).
- **The client's part `X st q`** (fractional, a parameter): what kv.go keeps under the same lock
  and its own invariant over the state. **Exact transitions:** a writer's spec takes the client's
  step `X st 1 ={⊤}=∗ X (f st) 1 ∗ Q st` for its transition `f` (`LeaseCacheSt.add`, `evict`,
  `evictRange`, `modify … del`, `setWaitc`), and returns `Q` of the state it found; a reader's
  returns what the client learns of the state it read (`lcPeek X Qr`). `Lock`/`LockRange` change
  only waiter channels (`WaitcOnly`), a persistent step (`lcWaitcStep`). `Update` and `delete` run
  with the lock held by their caller and are specified on the owned state. *Rejected:* specs
  "for some state" with no ghost link (the client could not relate two calls); logically atomic
  triples (the step premise is what kv.go needs, more simply).
- **The entries' facts** (`entryFacts`, persistent, kept for every entry and frozen entry): etcd's
  whole keyspace at the entry's revision has the key's acquisition record and the lease key with
  the holder's lease and a create revision at most the revision. The cached value changes with the
  holder's writes (`Update`), so "the cached value is `k`'s record at `rev`" is not an invariant;
  the facts are about the acquisition (`acq`), and unit 4 relates the cached value to the history.
- **Frozen entries.** `Get` finds an entry (`notify`), waits, and reads `*li` again; an eviction in
  between removes it from the map, but Go keeps it alive. Evicted (and replaced) entries are frozen:
  their resources made read-only (`DFrac.discard`) and kept; a monotone list records every
  `*leaseKey` installed under each key (`leaseKeyInstalled`), and the invariant keeps each one the
  key's entry or frozen.
- **Readiness.** `lc.entries` is nil until the session monitor makes it; `Add` writes it, so it
  takes `leaseCacheReady` (a monotone counter at `1`), which unit 4's session reset will give.
- **The trust boundary** (axioms): `strings.Compare` (Perennial has no model; a trusted model in
  Perennial, as `strings.HasPrefix`'s, would replace it: written and proved, but not committed,
  see STATUS) and `(*time.Time).Add` (Perennial models the value receiver only). *Since
  2026-10-10* both are Perennial's (`strings.wp_Compare` from a trusted model,
  `time.Time.wp_ptr_Add` from `ptr_Add_unfold`), as are `strings.TrimPrefix` and `errors.As`
  (units 3 and 4): see "Panic and recover", "The standard library's models".

### Nested transactions, owned responses, `isLeasingKV` (units 3 and 4)

**2026-10-10 · proposed** (units 3 and 4 of `client/v3/leasing`: `txn.go` and `kv.go`)

- **Nested transactions in the model, minimally** (`InvEtcdTxn.lean`): `TxnOp.txn cmps thn els`
  and `TxnOpResult.txn ok rs`; `applyTxnOp`/`runOps` are mutually recursive (structural), a nested
  transaction evaluates its comparisons on the state the operations before it left and runs its
  chosen branch at the same revision, as etcd does; `TxnOpResult.wrote`/`wroteL`, `TxnOp.Under`/
  `UnderL` likewise; `runOps_noWrite` by mutual recursion. Also `TxnOp.putIgnVal key lease?`
  (`WithIgnoreValue`, value kept; `none`: lease kept too), so that `txnOpOf` models the puts etcd
  accepts with `WithIgnoreValue` and the leasing `Update` can be compared with etcd on them. The
  existing `txnOpRespAt`, `txnBuilderSpec`, `isEtcdTxnKV` are unchanged; every cache and
  concurrency proof builds unchanged. *Rejected:* recursive `OpFull` (the getters' model is flat;
  the nested lists are described apart, `OpT`).
- **Operation trees** (`InvEtcdTxnOwn.lean`, `OpT`): an `Op` value is a leaf (`OpFull`, not a
  transaction) or `OpTxn(cmps, thn, els)`; `opTAtC c v t` describes the value, with `c = true`
  also the spare capacity of every nested `thenOps` slice (owned): `gatherOps` appends `elseOps`
  into it (`append(thenOps, elseOps...)`), which its spec states as the code is (it can then be
  called once per tree; the leasing KV's own callers pass plain operations).
- **Owned responses** (`txnCommitResultO`, `isEtcdTxnKVO`): the client's `Commit` returns a fresh
  message the caller owns; the contract now hands over the transaction's `Succeeded` and the
  top-level responses' fields the leasing KV writes or caches (a range response's header,
  key-values, `More`, `Count`: `rangeRespOwn`; a put's, delete's, nested transaction's header) and
  the full header (`hdrFull`, moved here from the lease cache with `HdrM`, `CachedKv`,
  `cachedKvOwn`). A new builder contract beside the old one (`txnBuilderSpecO`: `Then`/`Else` on
  trees, `Commit` owned); `isEtcdDoKV` for `kv.Do` of a get (as `Get`). *Rejected:* changing
  `isEtcdTxnKV` (every concurrency proof destructs it).
- **`isLeasingKV`** (`InvLeasingKV.lean`, persistent): the immutable fields, the client contracts
  at prefix `[]`, what unit 5's monitors need (`isLeasingClient`: range watcher, leases, session
  client and options; `lkv.ctx` a `*cancelCtx`), the lease cache with the KV's lock part
  `leasingX`, the wait group. **`leasingX`** holds `session`/`sessionc`, the session's readiness
  (monotone: once set, never nil), `sessionc` as a broadcast channel announcing readiness, and a
  **log of the cache's states** (a monotone list whose last element is the current state), so
  that a spec can state a cache transition (`leasingStep γ st st'`: `put`'s `Update`) and what a
  reader saw (`leasingSeen`). *Changed from the plan:* "every entry's lease is the current
  session's" is not an invariant: `get` adds the entry of an acquisition after reading the
  session, and a session reset in between leaves an entry of the old session's lease (a finding).
- **The wait group** as the cache's (`leasingWgInv`): `get` adds a lease monitor with a fraction
  of the "open" token and its thread token deposited; the monitor keeps a reader slot of the
  cache's `RWMutex` for good (as `Cache.Watch` keeps a watch slot): `get` takes two reader slots
  and returns the second unless it started a monitor.
- **Unit 5's functions as hypotheses**: `waitSession`, `waitRescind`, `monitorLease` are specified
  now and proved with the monitors; `etc/gen-link.py` marks them `fn: ?` and links every result
  reaching them in `section links_pending`, with their specs as hypotheses (`etc/verified-code.py`
  counts those results as unfinished).
- **Contexts**: a write may `revoke`, whose `waitRescind` calls `WithCancel(ctx)`: Perennial's
  `wp_WithCancel` needs a `*cancelCtx` parent, so `put`, `delete`, `Commit`, `Do` take
  `isCancelCtxCtx ctx` (as `NewSession` does); `get` does not.
- **User transactions are flat**: `Txn().Then`/`Else` take plain operations (`txnOpOf`), the
  nested transaction is the leasing KV's own (`serverTxn`'s `OpTxn`).


### Leasing unit 5: the session monitor's halves, contract strengthenings

**2026-10-10 · proposed** (unit 5 of `client/v3/leasing`: the monitors, `NewKV`, `Close`)

- **Split fields**: `monitorSession` reads `lkv.session` without the cache's lock (it is the only
  writer of `session` and `sessionc`), so `leasingXBody` holds half of both fields (`q.half`) and
  `sessionMonitor` the other half, with the current `sessionc`'s close right (`.Pending`) or the
  fact that it closed it (`.Done`), which makes the nonblocking `select` on `sessionc` exact.
  *Rejected:* a ghost copy of the session (a load needs a points-to).
- **`waitRescind` states its `nil` honestly**: `nil` with `leaseKeyDeleted`, or `nil` with no
  promise; the second is reachable (a finding), so no stronger spec holds.
- **Contract changes, both true of etcd**: a delete watch event's `*KeyValue` has readable `Value`
  and `Lease` (`delKvAt`, values unspecified); `Lease.KeepAlive`'s success returns a channel (the
  lessor always makes one; the old contract allowed `(nil, nil)`, through which `NewSession`
  returned a nil session with a nil error and `monitorSession` could not be proved).
- **`NewKV` hands out** every reader slot of the cache's `RWMutex` and the whole "open" token
  (as the cache's `New`), and the close function's spec rather than `Close`'s (`leasingCloseFn`);
  `isLeasingCancel` (the `cancel` field's spec) is apart from `isLeasingKV`, which `Close` alone
  needs.

## Panic and recover: a panic outcome in the language, `Catch` for `defer`

**2026-10-10 · implemented** on Perennial branch `panic` (`b4f46e1dd`..`c46da895a`, with the
standard-library models below up to `7cea8cc26`), pinned by this merge (the plan decided with the
user; the deviations the implementation made are listed at the end)

The STM (`stm.go`) aborts an attempt by `panic(stmError{err})` from `fetch` and both `commit`
methods, and `runSTM` turns the panic back into the returned error with a deferred `recover()`.
GooseLang has no model of this: `panic` is a stuck expression (`wp_panic : ▷ False ⊢ WP (Panic
msg)`), the right treatment for raft's assertion-style panics, whose proofs show they never
fire, and the wrong one for a panic meant to fire and be recovered; `recover()` has no
semantics at all. The STM proof closed the gap with two callee-spec axioms (`stmPanic.spec`: a
weakest precondition of `panic(stmError{err})` for `err ≠ nil`; `stmRecover.spec`: `recover()`
returns `nil`), sound by the informal argument that a verified run reaches `recover()` normally
only when nothing panicked, but of a different kind than the etcd model's axioms: a statement
the model refutes (the WP of a stuck expression is `False`), not an assumption about etcd. The
same gap left the mutex's `sync.Locker` wrappers (`lockerMutex.Lock/Unlock`, which panic on any
error) unspecified. The fix is a Perennial feature, decided as follows.

- **Panic propagates in the language, not in the exception monad.** Goose compiles `return`,
  `break` and `continue` through labeled values (`("execute", v)`, `("return", v)`, ...;
  `Golang/Defn/Exception.lean`): `;;;` short-circuits on any label but `execute`, loops pass up
  the labels they don't own, and a function body's `exceptionDo` strips the label (`Snd`). A
  fourth label `("panic", v)` would unwind a body and its loops with no new rules, but not a
  call: a callee's result crosses the call as a plain value in `let: "$r0" := f x in …`, and the
  continuation is ordinary GooseLang, not a `;;;` chain. Propagating through the monad would mean
  checking every call's result and lifting every continuation, a change to the shape of every
  translated function and of every proof that steps past a call. *Rejected.*
- **A panic outcome is a value**: `val.PanicV (p : val)`. One generic head step
  `fill_item Ki (Val (PanicV p)) → Val (PanicV p)` for every evaluation frame `Ki` is the
  unwinding; it is a legal ectxi head step (the hole holds a value), so iris-lean's `wp_bind` and
  the language axioms are untouched. `go.panic` is `λ: v, Val (PanicV v)`.
- **One new expression `Catch e h k`**: `Catch (Val (PanicV p)) h k → h p`,
  `Catch (Val v) h k → k v`; its frame is the only one that does not unwind. `wrapDefer`
  (`Golang/Defn/Defer.lean`) becomes `Catch (exceptionDo (body $defer)) (λ p, store p in a
  `$panic` cell, run the deferred chain, then: cell cleared by a `recover` ⇒ return the
  function's named results (zero values if unnamed), else re-raise) (λ r, run the chain; r)`.
  Goose emits the result expression (it knows the signature) and translates `recover()` as
  read-and-clear of `$panic` when it is lexically in a function literal that is the direct operand
  of a `defer` statement (the STM's and `sync`'s idiom); any other `recover()` is reported as
  unsupported, not modeled as `nil`. The model is thus stricter than Go (whose rule is dynamic:
  `recover` works only when called directly by a deferred function), never more permissive.
- **One postcondition, applied to panics too**: `Φ : val → iProp` now also receives `PanicV p`.
  `wp_panic : Φ (PanicV p) ⊢ WP (go.panic p) {{Φ}}`; `wp_unwind : Φ (PanicV p) ⊢
  WP K[PanicV p] {{Φ}}` for `Catch`-free `K`; `wp_catch` splits on the outcome. Existing specs
  `{{P}} e {{RET v; Q}}` name a normal value, so they exclude panics and existing proofs keep
  working; a spec that lets a function panic adds the disjunct `∃ p, r = PanicV p ∧ Ψ p`, which
  callers discharge with `wp_unwind` up to their `Catch`. This is the "panic postcondition"
  without a second weakest precondition. *Rejected:* a WP with two postconditions (a new program
  logic for one feature).
- **An unrecovered panic stays forbidden.** `wp_fork` requires `WP e {{ v, ⌜¬ isPanic v⌝ }}`
  (today a goroutine's panic is stuck, hence forbidden) and the adequacy theorem's `φ` is the
  client's, with `φ (PanicV _) = False` for the main thread. A verified program never panics
  unrecovered, which is how Go's "a panicking goroutine kills the process" is modeled; raft's
  assertion-style panics still need their unreachability proofs.
- **Left out, acceptably**: a deferred function panicking during unwinding (Go replaces the
  panic), `panic(nil)`, `runtime.Goexit`.
- **Cost**: GooseLang (the `val` constructor, `Catch`, two step rules, `Countable`/decidable
  equality); the ectxi instance (one frame); Lifting (`wp_catch`, `wp_unwind`, `wp_fork`'s side
  condition); `wrapDefer`/`wp_with_defer` (50 proofs here use the rule and 68 translated sites
  regenerate; a no-panic corollary of the same shape keeps the proofs nearly unchanged); Goose
  (`recover`, the result expression); the adequacy statement only through `φ`.
- **The STM afterwards** (done): `stmPanic.spec` became `wp_panic`, `stmRecover.spec` the cell read
  inside `runSTM`'s `Catch` (`wp_recoverPanic`); `stm.fetch`/the commits have the panic outcome
  (`stmRet`: the panic of `stmError{err}`, `err ≠ nil`), which `runSTM`'s proof turns into the
  `(nil, err)` return; the `lockerMutex` wrappers got specs the same way (a return, or
  `panic(err)`). The concurrency collection is at 11 axioms, all the etcd model's. See "STM",
  "Aborts are panic outcomes".
- **What the implementation changed** (Perennial's commits and docs, `PERENNIAL_PROOF_REFERENCE.md`
  "Panics"):
  - *Unwinding overlaps the other steps.* A frame around a panic can also take a beta, pair or Go
    instruction step, so the trusted step relation is `HeadStep`: the unwinding, or `base_step`
    on a redex that does not unwind (`Unwinds`). Frames that hold an evaluated operand carry a
    proof that it is not a panic (`AppLCtx v2 h2`, ...), and every pure step that binds or pairs a
    value needs `v.isPanic = false`; the tactics discharge it (`notPanicProof?`: `#x`,
    constructors, definitions of them, hypotheses), so proofs see it only for a generic
    `v : val` (here: a `let` binding an axiomatized constant, `etcdserverpb.AlarmType_NOSPACE`,
    now translated; and the generic results of `stmRet` specs, cased on first).
  - *`go.panic` is `λ: "v", Raise "v"`*, `Raise` a primitive (`RaiseOp`) that steps to
    `PanicV v`; `wp_panic : Φ (PanicV #p) ⊢ WP (go.panic #p)`. The builtins' run-time panics
    (`Panic "msg"`: an index out of range, a failed type assertion) stay stuck
    (`wp_PanicOp : ▷ False ⊢ ...`): raft's assertion-style panics keep their unreachability
    proofs.
  - *`recover` only where a deferred literal calls it*, by a separate wrapper:
    `with_defer_recover: r; e` (`wrapDeferRecover`), whose body also gets the `$panic` cell and
    whose `r` returns the results when the chain cleared the cell (named results are allocated
    outside the wrapper, hoisted); `recover()` is `recoverPanic $panic`. The 68 plain `with_defer`
    sites and `wp_with_defer` keep their shape (`wrapDefer` now runs the body under a `Catch` whose
    handler runs the chain and raises the panic again); the no-panic corollary of the plan was not
    needed. A `recover()` anywhere else is reported unsupported.
  - *`Catch e h k`'s handlers are expressions* (Goose emits lambdas), not values.
  - *Two new class fields*: `GoGlobalContext.intoVal_not_panic` (no Go value is a panic, so a
    spec `RET #x` excludes panics) and `MapSemantics.is_map_pure_not_panic` (`SafeMapKey` is
    unchanged); `wp_for` takes three non-panic hypotheses (discharged by the tactic) and a panicking
    body proves its `forPostcondition` (`wp_for_post_panic`); `wp_fork*`'s body ends in
    `⌜v.isPanic = false⌝`; `goose_adequacy_nopanic`.
  - *Unsupported*: a panicking loop condition or `range` body, a deferred function panicking while
    unwinding, `panic(nil)`, `runtime.Goexit`.
  - *Cost here*: two proofs changed for the adoption (`runSTM`, `applyEntryNormal`'s constant);
    the STM's specs changed for the panic outcome.

### The standard library's models (with the panic branch)

**2026-10-10 · implemented** (Perennial branch `panic`, `d958136aa`, `c01745d27`, `7cea8cc26`)

`client/v3/leasing` carried four standard-library axioms; Perennial now has their specs and the
callers use them directly, as the cache uses `bytes.wp_Compare`.

- **`strings.Compare`**: a trusted model in `TrustedCode/strings.lean` (Go's `<` and `==` on
  strings, as `bytes.Compare`'s model; Go's is `bytealg.CompareString`, assembly);
  `strings.wp_Compare` returns `strings.compareResult`.
- **`strings.TrimPrefix`**: a trusted model, goose's translation of `HasPrefix` and
  `string([]byte(s)[len(prefix):])` (Goose has no string slicing); `strings.wp_TrimPrefix`
  returns `strings.trimPrefix`.
- **`(*time.Time).Add`**: `Time.Add` translated, for the method set of `*Time`
  (`ptr_Add_unfold`); `time.Time.wp_ptr_Add` from `Time.wp_Add`, which stays an axiom (the body
  uses `&^`, which the model's Go semantics does not define, and the untranslated `addSec`,
  `stripMono`).
- **`errors.As`**: `errors.wp_As`, an axiom (reflection, `internal/reflectlite`, not
  translated), with `wp_AsType`'s precondition (`isErrorTree S T' T`: the specs of the tree's
  `As`/`Unwrap` methods and the typing of its errors) for a target `*T`; a leaf error (no `As`,
  no `Unwrap`: `errors.isLeafError`) is a one-error tree (`isErrorTree_leaf`). Go's panic for a
  target type neither an interface nor implementing `error` is not stated (method sets are
  uninterpreted). The caller (`acquire`) needs the client's error to be such a leaf: the client
  contract says so (`clientErr` in `txnCommitResultO`'s error case: a leaf, an `EtcdError` if of
  that type; true of gRPC status errors, `rpctypes.EtcdError`s and context errors). *Rejected:*
  an `errors.As` spec without the tree (false for an error whose `As` method loops or panics).
- **`status.FromError`** (grpc) stays an etcd-grove axiom.

## Recipes: the client contracts reused, the queue's claim, two prefixes as one

**2026-10-11 · implemented** (last bullet; `client/v3/experimental/recipes`, 778 lines: barrier, double barrier,
queue, priority queue, RWMutex, the key helpers and `WaitEvents`; the plan, for review)

The recipes are client code on `Session`, transactions and watches, the shape of concurrency and
leasing, so the plan reuses their contracts and adds as little as possible.

- **The client bundle.** `isEtcdRecipesClient client pfx`: the mutex client (`isEtcdKV`,
  `isEtcdTxnKV`, `isEtcdDeleteKV`, `isEtcdRangeWatcher`) plus a `Put` contract (`isEtcdPutKV`,
  mirroring `isEtcdDeleteKV`: the double barrier's `Put(key/ready, "")` is the first plain put a
  verified client makes), asserted beside `isSession s γ client id` on the same client, as
  `isMutex` does. The recipes take `*clientv3.Client` and `*concurrency.Session`; `Session.Client`
  and `Session.Lease` are already specified.
- **One prefix per recipe**: the barrier its key (a key is a range under itself), the queue
  `keyPrefix`, the RWMutex `pfx/` (read and write keys under it), the double barrier `key/`
  (waiters and ready). **The priority queue at the empty prefix**: `newSequentialKV` puts
  `prefix/…` and compares `__prefix`, two disjoint prefixes, so its contracts are instantiated
  at `""` (as leasing's), and the notes say the code touches only the two. *Rejected:* a
  contract over a set of prefixes (new machinery for one recipe; generalize if a later package
  needs it).
- **The queue's linchpin is `deleteRevKey`**: a transaction `ModRevision(key) = rev; Delete(key)`
  succeeds at most once per `(key, rev)` (`etcdState_modrev_det`: the record at a mod revision is
  determined, and a deleted key's next record has a greater one), so an item is dequeued at most
  once by any number of dequeuers. FIFO (the dequeued item has the least mod revision, or the
  least key for the priority queue, among the items present at the claim) holds on both paths:
  the get's single item (`WithFirstRev`, limit 1, `More` retried), or the first put event after
  the get's revision when the get's items were all claimed by others.
- **Exclusion for the RWMutex is the mutex's**: `lockedAt` with a role; a writer holds only after
  every lower key (read or write) under `pfx/` is gone, a reader after every lower write key, so
  writer/writer and writer/reader pairs are never both present at a revision after both acquired
  (`lockedAt_exclusion`'s argument), under the same session-lease premise as `Mutex`.
- **The double barrier promises a lower bound only**: `Enter` returns `nil` only if `count`
  waiter keys were present at some revision at or before its return (the ready put's writer saw
  them), and `Leave` only with the caller's key deleted. Reuse of a barrier across rounds is not
  promised by the code (a late entrant can see a leaver's key gone) and is not claimed.
- **The standard library, one Perennial batch**: `strings.Split` (a pure model), `errors.Is` on
  leaf errors (as `errors.As`: `ErrKeyExists` is never wrapped), and the integer directives of
  `Sprintf` (`%d`, `%v` of an integer, `%0Nd`: the decimal, zero-padded), in the model rather
  than as a premise: zero-padding is why the priority queue's keys sort numerically, a fact
  about Go's `fmt`, which the trusted models are for; it also makes `newUniqueKV`'s key
  `prefix/<decimal>` rather than a prefix plus junk. `fmt.Sscanf` stays an etcd-grove axiom (one
  caller). *Rejected:* the format as a hypothesis of every priority-queue theorem (nobody could
  discharge it).
- **Suspects, settled by Go reproductions before the Lean**: `waitEvents` returns `nil` when the
  watch channel closes (client closed, compaction past the watched revision), and (1)
  `Queue.Dequeue`/`PriorityQueue.Dequeue` then dereference `ev.Kv` (a nil-pointer panic, where an
  error is due); (2) `Barrier.Wait` returns `nil`, reporting release while the barrier is held.
  A nil dereference is stuck in GooseLang (a runtime panic is not a `Raise`), so if (1) is
  confirmed the proofs as shipped take a premise on the watch channel (an event before the
  close), stated on `WaitEvents`, and the bug gets a fix branch and an issue draft, as leasing's.
  Misuse panics (`RemoteKV.Put` after `Delete`, `WaitEvents` with no event types, `Leave` without
  `Enter`) become preconditions.
- **Units**: 0 translation and scaffolding (`recipes.toml` in full, bodies for `WithFirstRev`,
  `WithFirstKey`, `WithLastKey`, `WithMaxModRev`, `WithMinModRev`, `gen-link.py --recipes`, the
  collection, the reproductions, the Perennial batch); 1 base, bundle, `key.go`, `client.go`,
  `watch.go`; 2 barrier and the two queues; 3 RWMutex and double barrier; 4 results, baseline,
  notes, issues. 2 and 3 in parallel after 1.

### Unit 1: where the plan moved (2026-10-11)

- **`context.TODO()`.** The recipes pass `context.TODO()` to every `KV` call; its context is
  never done, its `Done()` is `nil`, so it is not an `isContext` (whose `Done` returns a
  channel), and none of the existing client contracts covers such a call. The bundle takes the
  contracts at `TODO()` (`isEtcdKVTodo`, `isEtcdTxnKVTodo`, `isEtcdDeleteKVTodo`,
  `isEtcdPutKVTodo`: the same postconditions, no context premise), not `isEtcdMutexClient`'s;
  `context.TODO` gets a spec and proof here (Perennial has none). *Rejected:* changing the
  existing contracts' context premise (every caller rewritten).
- **`WithFirstKey`.** `withTop(SortByKey, SortAscend)`'s `WithSort` closure writes the `order`
  it captured: a persistent closure spec (`optSpec`) cannot hold of it (concurrent calls race),
  hence `WithSort.spec`'s exclusion. The closures are called one at a time by the client, so
  `optSpecRes f g R`/`optsAtRes` thread a resource (the variable) through the calls, and the
  `TODO()` `Get` contract takes them (`optsAt_res` for the others). `WithFirstKey` is proved by
  stepping into `withTop` and `WithSort`.
- **`waitEvents`** returns an `*Event` with `eventAt` (what callers dereference), not `ev ≠ nil`:
  nothing says a watch event pointer is non-nil, and a load needs only the points-to.
- **`deleteRevKey`** takes `rev > 0` (for `rev = 0` on a missing key the comparison holds and the
  transaction succeeds deleting nothing); its `false` says `revKeyGone`.
- **At most once** is "the same revision" (`revKeyDeleted_same_rev`). "Dequeued at most once"
  (unit 2) needs more: that a written revision is one transaction's (a token per written
  revision in `txnCommitResult`), which the contract does not give.
- **Unit 1b's specs** state what holds without a premise: the key under `kp ++ "/"`, created
  fresh (`keyCreatedAt`). `newSequentialKV`'s order is not unconditional: a key under
  `kp/` that is not a 16-digit decimal (`kp/5abc` parses as 5, so `kp/0000000000000006` sorts
  below it) or a 17-digit successor (`9999999999999999 + 1`) breaks it; unit 1b states it under
  a premise on the keys under the prefix (all made by `newSequentialKV`, fewer than `10^16`).
- **`newUniqueEphemeralKey`** is proved now (one call), so three `sorry`s, not four.
- **`gen-link.py --skip-unproved`** links what is proved from the full list.

### Units 1b, 2 and 3: two decisions (2026-10-11, decided)

- **A token per written revision in the commit contract.** "Dequeued at most once" (two
  dequeuers never return the same item) needs that two successful writing commits never share a
  revision: `revKeyDeleted_same_rev` gives "the same revision", and the contract gave each
  commit a revision without ownership of it. The transaction contract (`txnCommitResult`, and
  the `TODO()` variants) now yields an exclusive token for the revision a writing commit made
  (`etcdRevToken r`, in the trust boundary with `etcdState`): true of etcd, where every
  committed write is its own revision; as `etcdState_modrev_det` was, a law of the history the
  model already assumes. *Rejected:* a ghost protocol over the recipe's own transactions
  (another client's dequeue is not the recipe's code).
- **The priority queue's order under a premise on the keys.** `newSequentialKV` parses the last
  key's last path segment with `%d` and formats `%016d`, so its order holds only if every key
  under `kp/` was made by it (`kp/%016d`) and fewer than `10^16` were allocated: a premise on
  etcd's state under the prefix (`SeqKeysWf kp s`), stated on the theorems that need it (the
  priority queue's "least key"), not an issue to file (the keys under a priority queue's prefix
  are the recipe's by construction; the overflow is at `10^16` items). *Rejected:* an
  unconditional order (false, above); a documentation issue (the package documents nothing of
  its key format).
- **Unit 1b: `fmt.Sscanf` is an etcd-grove axiom** (trust boundary, `Spec/fmt/Sscanf.lean`,
  `Proof/fmt/Sscanf.lean`: `fmt.Sscanf.wp_proof`), for the one call shape
  `Sscanf(s, "%d", &n)` with an `int` `n`: with `err = nil`, `n` holds `fmt.scanInt s` where
  that is defined; with an error, `n` is unchanged; the count is unconstrained. `fmt.scanInt`
  (pure): drop leading ASCII spaces, one optional sign (`+`/`-`), the longest run of decimal
  digits, which must be non-empty and whose value must fit an `int64`; the rest is ignored
  (`"5abc"` is `5`). Stated as "where defined", not "`err = nil` implies `scanInt s = some n`":
  Go also skips a tab and the other Unicode spaces (`"\t5"` scans as `5`), which `scanInt`
  does not model, and an axiom must not claim Go fails there. Checked against Go 1.27.1 on ten
  inputs (parsed: `" 5"`, `"+5"`, `"-0007"`, `"5abc"`, `"0000000000000005"`,
  `"-9223372036854775808"`; errors, `n` unchanged: `""`, `"+-5"`, `"\n5"`,
  `"9223372036854775808"`). *Rejected:* a Perennial model of the scanner (one caller).
- **Unit 1b: `clientErrIs`, a contract strengthening** (`InvEtcdTxn.lean`).
  `errors.Is(err, ErrKeyExists)` (`newUniqueKV`, `newUniqueEphemeralKV`) needs, for the client's
  own error (`putNewKV`'s third case: a gRPC status error, which has an `Is` method, so
  `wp_Is_leaf` does not apply), the error tree `errors.wp_Is` takes. The transaction contract at
  `context.TODO()` now gives it: `isEtcdTxnKVTodo`'s builder has a second `Commit` triple
  (`txnCommitErrTodo`: `txnCommitResult` and, on an error, `clientErrIs err`), and
  `clientErrIs err` is, for every target, an error tree `errorIsTree S M target` with `S err`
  whose `Is` methods claim only targets of their own error's dynamic type (`M ii →
  target = ok tii → tii.ty = ii.ty`). True of etcd's client errors: `(*status.Error).Is`
  returns `true` only for a `*status.Error`; `rpctypes.EtcdError`, `errors.New` errors and the
  context errors have no `Is`. The other `TODO()` contracts and `txnBuilderSpec` are unchanged
  (a minimal edit, as unit 2's revision token is in `txnCommitResult`). `putNewKV`, `newKV`
  and `newEphemeralKV` carry it in their third case; `newKey`'s spec is unchanged (its proof
  drops it). The recipes' package facts record `ErrKeyExists` as an `errors.New` error
  (`errNewLeaf`: a pointer error, a leaf without `Is`, `Base.lean`), so `errors.Is` of it is
  `true` (`wp_Is_leaf`). Neither loop needs `Is`'s answer on a client error: `true` retries,
  `false` returns the error.
- **Unit 1b: `newSequentialKV` does not create its key.** The transaction compares only
  `ModRevision(__kp) < g + 1`: a key `kp/%016d(n + 1)` that already exists (a key under `kp`
  not made by `newSequentialKV`, or one made after the get by a writer that does not put
  `__kp`) is overwritten. Unit 1's "created fresh" (`keyCreatedAt`) was false; the spec says
  what was put (`seqKeyPutAt pfx kp key val g r`: the get's state `sg` at `g`, the key made
  from it, `SeqNext`; the state at `r` is `putKv` of `__kp` then the key on the state at
  `r - 1`, where `__kp` had mod revision `≤ g`), and takes `pfx <+: __kp` (the bookkeeping key
  is under the contracts' prefix: the priority queue's are at `""`). Freshness is a corollary
  under premises (`seqKeyPutAt_created`, below).
- **Unit 1b: `SeqKeysWf`, exactly** (`InvRecipesSeq.lean`). `seqKey kp m = kp ++ "/" ++
  padZeros 16 (decimalNat m)`; `SeqKeysBelow kp N s`: every key of `s` **with the prefix
  `kp`** (not only `kp/`: `WithLastKey()` reads the prefix range of `kp`, and a key `kpz` sorts
  above every `kp/…`) is `seqKey kp m` for some `m < N`; `SeqKeysWf kp = SeqKeysBelow kp
  10^16`. The order theorem (`seqNext_order`, and `seqKeyPutAt_order` on the spec's result)
  takes `kp ≠ []` and `SeqKeysBelow kp (10^16 - 1) sg` (the state at the get's revision) and
  gives `m < 10^16` with `key = seqKey kp m`, every key with prefix `kp` in `sg` a `seqKey kp
  m'` with `m' < m` and `go.GoStringLt` below `key`, and `m = 0` or `seqKey kp (m - 1)` in `sg`
  (so `m` is one past the greatest; the new key keeps `SeqKeysWf`). The bound `10^16 - 1`
  is the simplest that makes `m < 10^16`. Freshness (`seqKeyPutAt_created`) adds that every
  key with prefix `kp` at `r - 1` was in `sg` (no key under `kp` appeared between the get and
  the transaction: true if every writer under `kp` also puts `__kp`, which the comparison then
  excludes) and gives `keyCreatedAt`'s facts at `r`. The priority queue's prefixes are
  `q.key ++ %05d(pr)` (always five digits), so its priorities never share a range; two queues
  whose keys are prefixes of each other (`q` and `q0`) can, which the premise excludes.
- **Unit 2: the token's form** (decided above, settled here). `etcdRevToken (r : w64) : IProp GF`
  and `etcdRevToken_excl : etcdRevToken r ∗ etcdRevToken r ⊢ False`, axioms in
  `InvEtcdTxn.lean` beside the history laws (an opaque predicate of the server, as `etcdState`;
  not timeless, nothing needs it). The builder's `Commit` under the prefix returns
  `txnCommitResultTok` (`txnCommitResult`'s disjunction with `if txnWrote … then etcdRevToken r
  else True` in the success case) rather than a token inside `txnCommitResult`: leasing's
  `serverTxn` builds a `txnCommitResult` from its own commit (`txnCommitResultO`, no token) and the
  six concurrency proofs keep it persistent (`txnCommitResultTok_result` drops the token). The
  token only when the transaction wrote: etcd's `storeTxnWrite.End` advances the revision only if
  the transaction changed something, which is the model's `txnWrote` (a delete of nothing does not
  write). `putResult` carries it unconditionally (a put always writes). *Rejected:* a token in
  `deleteResult` (no caller), in leasing's owned variant (out of scope); a token inside
  `txnCommitResult` (non-persistent: every use rewritten, leasing's construction impossible).
- **Unit 2: the get's `More` flag** in the `TODO()` get contract (`getRespMore`, beside
  `kvGetResult` in `isEtcdKVTodo`'s postcondition; etcd's semantics: `More` iff a positive limit
  cut the selection, none for count-only). The queues' wait path needs it (`More` false: the get
  listed every item). *Rejected:* adding it to `getRespRange` (every cache, concurrency and leasing
  pattern on it rewritten). Unit 1b's and unit 3's proofs that call a `TODO()` `Get` bind three
  conjuncts (`⟨HR, #Hres, -⟩`), and their `Commit` calls take `Hres` (not `#Hres`) and
  `txnCommitResultTok_result` (or unfold `txnCommitResultTok`); `putNewKV`'s `nil` has the token
  as a fourth conjunct (`newUniqueKV`'s proof drops it).
- **Unit 2: FIFO where it holds.** The plan's FIFO at the claim (`r - 1`) needs a history law the
  model does not assume: that a key-value lives unchanged from its mod revision while present
  (`EtcdModRevPersist`). Stated first as a hypothesis of `queue_fifo_before_claim` (the get path),
  not an axiom: one result needs it, and the trust base stays the plan's; on 2026-10-11 the owner
  promoted it to the history axiom `etcdState_modrev_persist` (`InvEtcdTxn.lean`, beside
  `etcdState_modrev_det`: that law fixes the record per mod revision, this one keeps it there),
  and the result is unconditional. `queue_fifo` is at the get's revision. The wait path is weaker (the watch contract does not promise that no
  event is skipped). The priority queue's least key is at the get only: at the claim it is false
  in etcd (a higher-priority `Enqueue` between the get and the claim; `STATUS.md`, Unit 2).
  *Rejected at first:* a seventh history axiom for one result; *taken* once the owner judged the
  law part of what the model should say of etcd's history.
- **Unit 2: `pqueue_order`, for the merge with unit 1b.** With 1b's order premise and theorem
  (`SeqKeysWf kp s`: every key under `kp ++ "/"` is `kp ++ "/" ++ padZeros 16 (decimal n)`, made by
  `newSequentialKV`, fewer than `10^16`), the statement is: for the priority queue on `key`, if at
  the get's revision `r0` of a get-path dequeue of `it` every key under `key ++ "/"` is
  `key ++ "/" ++ padZeros 5 (decimal p) ++ "/" ++ padZeros 16 (decimal n)` for a `p : w16` and an
  `n < 10^16` (what `Enqueue` writes, under `SeqKeysWf (key ++ "/" ++ padZeros 5 (decimal p))` for
  each `p`), then `it`'s `(p, n)` is the least, lexicographically, among the items under
  `key ++ "/"` in `s0`: the highest priority (the smallest `p`; five digits hold every `uint16`, so
  key order is numeric order), then the earliest allocated. It composes `pqueue_min_key`'s get path
  (`go.GoStringLe it.key w.key`) with the order of fixed-width decimals.
- **Unit 3: `rwHeldAt`, exclusion under unmodified keys.** `rwHeldAt pfx role key c R`
  (`InvRWMutex.lean`): `key` under `(pfx ++ role.name) ++ "/"`, `0 < c ≤ R`, and at `R` no key with
  the role's blocking prefix (`pfx ++ "write"` for a reader, as `RLock`'s `waitOnLastRev(pfx +
  "write")`, no slash; `pfx` for a writer) has a mod revision below `c` (`RWBlockFree`). Nothing
  about the holder's own key at `R` (neither `RLock` nor `Lock` checks it after the wait; the
  results are about keys present in a state, as `Mutex`'s). Exclusion (`rwHeldAt_write_exclusion`,
  `rwHeldAt_read_write_exclusion`) is `lockedAt_excludes_earlier`'s argument with one more
  premise, `keyUnmodified pfx k c` on both keys (a key-value of `k` with create revision `c` has
  mod revision `c` in every state): `waitOnLastRev` filters by **mod** revision
  (`WithMaxModRev(myRev - 1)`), `Mutex` by create revision, and `etcdState_create_persist` keeps
  the earlier key present at the later holder's `R` with its create revision but says nothing of
  its mod revision. A plain `Put` of a lock key by another client moves its mod revision past a
  later holder's and makes it invisible (not a finding: the recipe only creates and deletes its
  keys; a premise on other clients, as the session-lease one). *Rejected:* a new history law
  (mod revisions of one incarnation only grow), which would remove the premise but add an axiom
  for a misuse case.
- **Unit 3: the double barrier's statement.** Both: `Enter`'s spec states what each path knows
  (`enterReady`: the direct path's `waitersSeen` at its second get's revision; the waiting path's
  `readyPut`, a write of `key/ready` at a revision at least the key's creation), with no premise
  (`double_barrier_enter_ready`); `double_barrier_enter_count` adds the protocol's premise
  `readyPutsCounted` (every write of `key/ready` at `z` is preceded by a state at some `R ≤ z` with
  `count` waiters, which the direct path's fact discharges if only `Enter`s of barriers on `key`
  for `count` write it) and concludes `waitersSeen` at a revision etcd has reached. "Waiters" are
  the keys with the prefix `key ++ "/waiters"` (the code's get, no slash). `count > 0` is a
  precondition of `NewDoubleBarrier`, carried by `isDoubleBarrier`. `Leave`'s `nil` is "the key
  absent at some `r ≥ lo`, or its record's `KV` already nil" (`leaveResult`: `RemoteKV.Delete` on a
  record it already deleted is a no-op, and the record cannot tell a failed delete from a
  successful one); `Enter` and `Lock` return records with a `KV`, so `double_barrier_leave` and
  `rwmutex_unlock_released` conclude absence. The recursion is Löb induction (`iloeb`).
- **Unit 3: the key field.** `rwMyKey`/`dbMyKey m pfx (o : Option (Loc × RemoteKVSt))`: `none` is
  a pointer the proof does not track (nil after `New*`, or the previous key when
  `newUniqueEphemeralKey` fails), `some (ek, st)` the owned `*EphemeralKV` with its record and its
  `KV`'s contracts. `ek.rev` (`Enter`) loads through the embedded struct's points-to.
- **Implemented (2026-10-11, units 0 to 3 merged).** Every function of the package is specified
  and proved (38 of 38), sorry-free. Deviations from the plan, each in its unit's bullet above or
  in `STATUS.md`: the client's calls are at `context.TODO()` (contracts `*Todo`, not
  `isContext`); `WithFirstKey()`'s options need a resource; `fmt.Sscanf` an etcd-grove axiom;
  `clientErrIs` and the revision token (`etcdRevToken`, `etcdRevToken_excl`: two new axioms of the
  trust base) and the get's `More` flag in the client contract, with `txnCommitErrTodo` returning
  both the token and the error premise after the merge; `newSequentialKV` puts but does not create
  its key (`seqKeyPutAt`), so `PriorityQueue.Enqueue`'s spec returns `seqKeyPutAt` (not
  `keyCreatedAt`, as unit 2 had it); FIFO at the get's revision, at the claim only under the
  hypothesis `EtcdModRevPersist` (since promoted to the axiom `etcdState_modrev_persist`), the
  wait path
  weaker (the watch may skip events); the priority queue's least key at the get only (not
  linearizable); the RWMutex's exclusion under `keyUnmodified`; the double barrier's count under
  `readyPutsCounted`. **`pqueue_order`** as drafted above, with `PQKeysWf key s0` (every key
  under `key/` is `pqKey key p n = key/%05d(p)/%016d(n)`, `p < 10^5`, `n < 10^16`; `p < 10^5`
  rather than `p : w16`, a weaker premise) and the item's key under `key/` from `dequeuedAt`;
  `pqueue_enqueue_order` restates `seqKeyPutAt_order` on `Enqueue`'s result, and
  `pqKeysWf_seqKeysWf` shows the dequeue's premise gives each priority's `SeqKeysWf` (the
  enqueue's order takes the bound `10^16 - 1`, one less). No piece was missing.

## One `AllG`: `HeapGS` provides the ghost-state instance

Since Perennial `cb6a5921e` (2026-10-11) `AllG GF` is a singleton carried by `GooseGlobalGS`
(`gooseAllG`), hence by `HeapGS`; `ThreadGS` and `ReceiptGS` no longer bundle their own.
- **Section variables**: a section with `[hG : HeapGS hlc GF]` has no `[AllG GF]` (654 files
  changed); only the generic ghost theory without `HeapGS` (`Proof/go_etcd_io/raft/v3/Protocol/`,
  `Results.lean`) assumes `[AllG GF]`. *Why:* two instances in scope make the client's ghost
  resources (`own`, `ghostVar`, `threadTok`) a different term from Perennial's, and the cache
  proofs that take `threadTok` from `wp_fork_tok` or `dghostVar` from the broadcast idiom fail
  to unify. *Rejected:* keeping `[AllG GF]` and living with the two instances, which worked
  only while no Perennial lemma exposed ghost resources to clients.
- **Fixing `GF`**: the `AllG` out-parameter used to fix `GF` for a bare ghost-state term;
  `HeapGS`'s `GF` is not an out-parameter, so such a term needs `(GF := GF)` (porting guide,
  "Section variables"). A theorem that does not mention `GF` but is declared under the
  section's `[hG : HeapGS hlc GF]` (the register's `regStorIface_inj`) gets `GF` as a binder it
  can never infer: write `(GF := GF)` at its uses, or declare it outside the section.


## The server's txn: the two models meet, the sole writer as tokens

**2026-10-11 · plan, unit 0 implemented** (`server/v3/etcdserver/txn`, 749 Go lines: the
server's `Range`, `Put`, `DeleteRange`, `Txn` over the mvcc core; later units append)

The txn package is where the mvcc model (the log of changes, `stateAt`) meets the client's
transaction model (`runTxn`, `InvEtcdTxn.lean`): mvcc's `applyChange` is the client's `putKv`
and a delete is its filter, so the server's `Txn` on a request denoting `t : TxnModel` is to
produce `runTxn (W64 log.length) (stateAfter log) t` (the comparisons' verdict, the branch's
results, the committed log); that theorem (`txn_runTxn`) is the package's result, with the
corresponding ones for `Put` (`putKv`), `DeleteRange` (the filter) and `Range`
(`rangeSel`/`rangeKvsOk`).
- **The sole writer, as the revision tokens.** `Txn` reads (`checkTxn`, the comparisons) in a
  read transaction, ends it, then opens the write transaction and re-reads; it is safe and
  `runTxn` only if nothing commits in between. mvcc's `NewStore` hands out `2^63 - 5` revision
  tokens and its writer's authority bounds the log by them, so a caller holding all the tokens
  left for `log` (`ownToks γ.revs (2^63 - 3 - log.length)`) with `idxCert γ.idx log` pins every
  later write transaction to `log`: `soleWriter γ log` (unit 0b's `SoleWriter.lean`). Every
  spec takes `isKV kv s γ ∗ storeReader s γ ∗ soleWriter γ log` and returns `soleWriter γ
  (commitLog log pend)`: the apply thread's situation (the lessor's range deleter writes outside
  it).
- **The requests as the client's values** (unit 0, `Requests.lean`): a range, put or delete
  request denotes an `OpFull` (the fields `Op.toRangeRequest` sends; the others `newOp`'s), a
  comparison a `CmpModel`, a `TxnRequest` a `TxnModel` (recursively through `RequestOp`'s
  oneof); so the statements are in the client model's terms and `runTxn` applies as it is.
  *Rejected:* a record of the protobuf fields (a second vocabulary). The range end denotes
  mvcc's reading (`rangeEndOf`: `nil` the key alone, empty non-nil from the key on, which is
  `mkGteRange("\x00")`); on decoded requests (protobuf-go decodes an empty `bytes` field as
  `nil`) that is the client's `inRange`. A put denotes the server's total `putTxnOp` (the
  ignore flags keep the value or lease whatever the request says), not the client's partial
  `txnOpOf`. An empty oneof denotes nothing (`Txn` panics on it, `issues/etcd-txn-empty-requestop.md`).
  The responses mirror `TxnOpResult` (`txnResponseIs`), recursively; a nested response's
  header revision is `0`.
- **The index answers the state** (unit 0b, pure): for a well-formed log, mvcc's
  `rangeAnswers` are the keys of the state in the range with their revisions; `delKeys` is the
  client's filter, `rangeTaken` its `rangeIn`.
- **The lessor's `Lookup`** (unit 0, `Defs.lean`): `isTxnLessor` adds to mvcc's `isLessor` a
  `Lookup` triple returning `nil` or a granted lease (`leaseKnown`), which `checkLease` hands to
  mvcc's `Put`. Additive.
- **Package facts of other packages** (unit 0, `Base.lean`): the txn code returns
  `lease.ErrLeaseNotFound` and `etcdserver/errors.ErrKeyNotFound`, whose packages' facts are
  mvcc's (`True`) and the server's (`ErrNoSpace` only); `txnInit` states them (each a fixed
  non-nil error, true once the txn package and so its imports are initialized) rather than
  changing those files.
- **Contexts.** mvcc's `rangeOutcome` has an unconditional "context done" error disjunct, which
  in `Txn`'s write path leads to `lg.Panic`; preferred: a never-done context gives no error (a
  refinement of mvcc's spec, coordinated with the mvcc session); fallback: the result holds
  "unless it panics". `traceutil.EnsureTrace` (unit 0's axiom) returns a context with the input's
  deadline and `Done` (`{ cd with Values := vs }`): `context.WithValue` derives one that
  delegates them to its parent; the values are left open (only `traceutil.Get` reads them).
- **Sorting** (unit 0's axioms, `Spec/sort/`): `sort.Sort` over a `sort.Interface` given as
  `Len`/`Less`/`Swap` triples on a model list (`sorterSpec`): a permutation sorted by a strict
  weak order, at most `2^62` elements (Perennial's `slices.SortFunc` statement); `sort.Reverse`
  flips `Less`. The five `kvSort*` sorters are proved against them. *Rejected:* proving Go's
  pdqsort over `sort.Interface` (large, not etcd's).
- **The rest of the trust boundary** (unit 0): traceutil (`Get`, `StepWithFunction` runs its
  closure, its outcome a panic included; `AddField`, `Start/StopSubTrace` return), `proto.Size`
  of a put request (its atomically written size cache in an invariant, so the request stays
  persistent), `zap.Logger.Panic` (a panic outcome, `PanicV`), `zap.Int32`, the two metrics
  functions. mvcc's read-only write transaction (`NewReadOnlyTxnWrite`, `txnReadWrite`) is
  verified, not assumed (`InvRoTxn.lean`: its reads delegate, `Changes` is `nil`, `Put` and
  `DeleteRange` panic).
- **Unit 1** (2026-10-11, `Put` and `DeleteRange`; `notes/STATUS.md`, "Unit 1"). Three changes to
  the plan. (1) *The pin travels with the token.* A spec taking only the revision token cannot
  give the sole writer's corollary: after `End` the token is spent and nothing bounds the log
  the transaction found. `Put`/`DeleteRange` take, beside the token, any `ownToks γ.revs m ∗
  idxCert γ.idx log₀` and return `Pinned log₀ m ilog` (read inside the open transaction,
  `isTxnWrite_pinned`), as unit 0c's `store.Read`; `m = 0`, `log₀ = []` is the plain spec, the
  sole writer's `m = soleBudget log - 1` gives `ilog = log` (`pinned_sole`), and
  `put_soleWriter`/`deleteRange_soleWriter` are derived triples. *Rejected:* specs at the sole
  writer only (no token-level statement for other callers). (2) *`IgnoreLease` needs a premise.*
  The put writes the previous key-value's lease and mvcc's `Put` attaches it (`leaseKnown`); mvcc
  has no invariant that a stored lease is known, so `Put` takes `leaseOk` of the previous lease
  at the pinned log and returns `leaseOk` of the lease written (a sole writer can maintain "every
  lease in its state is known" from these). *Rejected:* an mvcc invariant on the leases of the
  committed state (`idxCert`/the writer's resources would carry it; another session's package).
  (3) *A range read at `context.TODO()`* (mvcc, minimal): `getPrevKV` ranges on the write
  transaction at `context.TODO()`, which is not an `isContext` (`Done()` is `nil`); the range specs
  take `rangeCtx todo ctx cd` and promise no context error at `context.TODO()` (`todo = true → r ≠
  null`), and `metricsTxnWrite.Range` is over `isTxn` of either kind (the plan's preferred option,
  "a never-done context gives no error", done for `TODO` only; the caller's `isContext` keeps the
  error case: `DeleteRange` with `PrevKv` reports it). *Rejected:* refining `rangeOutcome` itself
  (`InvStore.lean`, every mvcc proof). The request and response predicates of unit 0 are
  unchanged: `PrevKv`'s pointer is the range result's, made read-only (`kvIs`) since the result is
  dropped.

- **Unit 2 (Range, 2026-10-11).** The server's range is specified as the code computes it, not as
  the client model's `rangeKvsOk` (`RangeModel.lean`: `srvPre` the key-values read, at most the
  limit mvcc read with, as read, filtered; `srvSorted` a permutation sorted by the target when
  `effSortOrder` is `1`/`2` (Go's `sort.Sort` is not stable: ties in any order), unchanged
  otherwise; `srvTrunc`/`srvMore`/`respKv` the assembly), and bridged to the client's
  (`srvRangeOk_rangeKvsOk`, `range_rangeSel`) where they agree: the server and the client model
  differ on two points, both etcd findings, and the bridge says so instead of the spec hiding
  them: a fast keys-only read zeroes the lease (`leaseZ`; `issues/etcd-range-keys-only-lease.md`),
  and a sort by a non-key target with order `NONE` and a positive limit is cut early (premise
  `¬ cutEarly o`; `issues/etcd-range-sort-none-limit.md`). Changes to the plan: (1) **the sort's
  premise is a small log** (`sortOk o log`: a request that sorts reads a log of at most `2^62`
  changes, `LogSmall`): `sort.Sort`'s axiom wants at most `2^62` elements, which nothing bounds
  in the model (locations are unbounded), and the comparators' `(a - b) < 0` is the signed order
  only for values less than `2^63` apart: revisions are below the log's length, but a version
  counts puts, which `LogOk` does not bound below `2^63` (a revision may put a key many times);
  both follow from `LogSmall` (`stateAt_small`: at most `2^62` keys, revisions and versions in
  `[0, 2^62]`). `Range`'s general spec quantifies it over the logs its read may see (between the
  caller's certificate and its tokens), which the sole writer reduces to its log
  (`range_soleWriter`). *Rejected:* a premise on the selection's length alone (the versions
  would still need one). (2) **The sort target is a premise** (`validSortTarget`: one of the
  protobuf's; else `lg.Panic`, which the gRPC layer's `checkRangeRequest` rules out); the panic
  branch is unreachable, `zap.Int32`/`Logger.Panic` are not callees of the proof. (3) The
  sorters' list is of (pointer, key-value) pairs (`kvsAt`, owned key-values; `Swap` permutes the
  pointers, `Less` reads two elements). (4) `executeRange`'s result names the state read
  (`stateAt log (rangeRev rev o.base.rev)`) and mvcc's three outcomes (`rangeResult`: a future
  revision, a context error on a full read, the response); the context error stays (mvcc's
  `rangeOutcome` has it unconditionally). (5) `mkGteRange` (`delete.go`) is specified and proved
  here (`executeRange` calls it; unit 1's `deleteRange` too): the empty literal `[]byte{}` is
  shown non-`nil` by a variant of Perennial's `wp_slice_literal` (`wp_slice_literal_nn`). (Merged
  with unit 1, which proved the same function: unit 1's stronger spec, result `rangeEnd` itself
  unless `[0]`, and its `Write.lean` lemma are kept; `executeRange` gets `srvEnd` through
  `srvEnd_mkGte`.) (6)
  mvcc gains `metricsTxnWrite.Rev`/`FirstRev` for a read transaction (`checkRange`'s
  `ReadView`), additive.

- **Unit 3 (`Txn`, 2026-10-12).** (1) **The server's run, not the client's**: `Txn` is specified
  over `srvRunTxn` (`TxnRun.lean`), the client's `runOps` with every nested transaction's branch
  chosen by its verdict at the read state (`compareToPath` evaluates every comparison first) and
  the mvcc changes named (the write transaction's pending list); `txn_runTxn` relates it to the
  client's `runTxn` under `OpsStable`. *Rejected:* stating `Txn` over `runTxn` (false for a nested
  comparison on a key written earlier in the transaction: the client model is wrong there,
  `issues/etcd-txn-nested-compare-snapshot.md`); changing the client model (leasing's proofs use
  it). (2) **A context never canceled** instead of a panic: in the write path a range or a
  `PrevKv` delete at a done context returns an error that `txn` turns into `lg.Panic`; mvcc's
  `rangeCtx true` now also takes an `isContext` whose Done proposition never holds (`neverDone`:
  a receive on its channel would give it), and `executeRange`/`deleteRange` take `nd` with no
  context error. *Rejected:* a panic disjunct in `Txn`'s post (the result would hold "unless it
  panics"); refining `rangeOutcome` itself (every mvcc proof). (3) **The run's premises as a pure
  predicate on the run** (`OpsOk`, at each operation's state): a range's at its state
  (`sortSmall` replaces unit 2's `sortOk` of the log, which a write transaction's pending log does
  not give), an ignore-flag put's key present where it runs (the finding
  `etcd-txn-delete-then-ignore-put.md`), weak in `Txn` (missing at the read state: `checkTxn`
  fails) and strong in `executeTxn` (`opsOk_strong` with `checkTxn`'s `PathsIgnOk`). Ranges at
  revision `0` only (the client's `txnOpOf`), so `checkRange` never fails in `Txn`'s scope.
  (4) **Leases as a state invariant** (`leasesKnown`): `Txn` takes every lease of the committed
  state known and returns it for the new one (a put names a checked lease or keeps the previous
  key's); unit 1's per-call premise generalizes to a run. (5) **One transaction predicate for both
  paths** (`txnWriteIs`: a `*metricsTxnWrite` write transaction or the read-only wrapper, the
  latter with nothing pending and only ranges), and `executeRange` over `txnViewIs` (either kind
  or the wrapper), so `executeTxn`, `txn` and `executeRange` have one proof each. (6) **Responses**
  moved to `InvTxn.lean` and stated as the server answers (a range's `leaseZ`; `skip`:
  header-only), the skeleton `newTxnResp` allocates owned only where `executeTxn` stores.
  (7) `compareIs` states the operand's wrapper is not a typed `nil`; `checkTxn` returns `0` on an
  error; `metricsTxnWrite.Rev` of either kind, `metricsTxnWrite.Changes` added (mvcc, additive).

- **Unit 4 (the history laws of the log, 2026-10-12).** `HistoryLaws.lean` proves the pure content
  of the client's history axioms of `stateAt` (and of `stateAtPfx`, its restriction to a prefix):
  they *validate* the axioms against the server's model, they do not discharge them (`etcdState`
  stays an abstract axiom; a later refactor could instantiate it by the log). Each law takes the
  weakest hypothesis it needs: `create_persist`, `modrev_persist`, `modrev_det` only the word bound
  `log.length < 2^63`; `revs` `LogOk` and **`NoDupKeysPerRev`**. That one is **what the client
  axioms assume of the server** beyond `LogOk`: a revision writes a key at most once (else a key's
  version, a word counting its puts, can wrap to a non-positive signed value). `modrev_det` does
  not need it, against the plan's expectation (only the later of two writes of a key in one
  revision survives it). The commit keeps both (`LogOk.snoc`, `NoDupKeysPerRev.snoc`), the latter
  exactly when the transaction passes etcd's `checkIntervals` (`keys_nodup_iff_check`), which unit
  3 takes as the premise of a writing transaction. *Rejected:* a bound on the log's total change
  count instead of `NoDupKeysPerRev` (it bounds versions too, but is no fact etcd states; the
  distinct keys are its rule).

## mvcc: the certificate carries the log, the token count is exact, a read is pinned by tokens

2026-10-11, for the server's txn package, unit 0c (`notes/STATUS.md`, "Unit 0c"). The txn
package's sole writer (`txn/SoleWriter.lean`: the certificate of `log` and every revision token
not spent) must pin the logs its write and read transactions see to `log`; unit 0b found four
gaps in mvcc's specs. Each change is minimal and keeps every spec at least as strong.

- **The certificate carries the log.** `IdxNames` gains `log`, a monotone list of the committed
  log's revisions (`List Change` items); `idxCert γ log` adds its lower bound, the index writer
  (`idxWriter`) half its authority (`idxLogAuth γ (1/2) ilog`), and `idxWriter_commit` appends
  the pending revision (it takes the other half and gives it back). So two certificates are of
  logs in prefix order (`idxCert_prefix`, `idxCert_agree_len`), and a committed log extends every
  certificate (`idxWriter_cert_prefix`, `idxLogAuth_cert_prefix`). *Rejected:* the history's
  commit marker carrying the revision's changes (`HistItem.commit cs`): `histOf` would be
  injective with no new ghost, but `HistItem.commit` is a constant in some 200 places of
  `Hist.lean` and the index proofs; the second list touches only the definitions, the
  allocation and the three writer proofs that unfold `idxWriter` (one more conjunct framed).
  (`Change`'s countability moved from `InvStore` to `InvIndex`.)
- **The token count is exact.** `storeTxnWrite.End` with no change (`pend = []`) makes no
  revision and leaves the authority's count, so it now returns the transaction's `revToken`
  (`… ∗ if pend = [] then revToken γ else True`, also in `txnEndPost`, hence
  `metricsTxnWrite.End`); `writeView.Put`/`DeleteRange` drop it. Without it each such `End`
  lost a token for good and the sole writer's count (`ntok = 2^63 - 3 - log.length`) could not
  be kept.
- **`NewStore` returns `idxCert γ.idx [[], []]`** (its proof had it).
- **A read is pinned by the caller's tokens and certificate.** The revision budget's authority
  `ownTokAuth γ.revs ntok` is split in halves (`ownTokAuth_halves`, `ownTokAuthDfrac_split`):
  one is the writer's, as before (`writerRes`, `storeTxnWriteIs`), the other is under `s.revMu`
  (`revMuInv`, with `log.length + ntok + 3 ≤ 2^63` for the committed log); `revMuInv` also holds
  the other half of the committed log's authority (`idxLogAuth`). `End` changes both under
  `s.revMu` held exclusively (`currentRev++`). `store.Read` takes `ownToks γ.revs m` and
  `idxCert γ.idx log₀` (new binders `m`, `log₀`) and returns them with
  `⌜log₀ <+: log ∧ log.length + m + 3 ≤ 2^63⌝` for the log read: the tokens bound it from above,
  the certificate from below. With `m = 0` and `log₀ = []` (`ownToks_0`, `idxCert_nil`, ghost
  updates; the `readView` proofs do this) it is the old spec. *Why the certificate too:* the
  tokens alone give `log.length ≤ log₀.length`; without a lower bound read under `s.revMu` the
  read log could be a strict prefix of the sole writer's (unit 0b's "read pin" proposal had only
  the tokens). *Rejected:* a separate "committed length" monotone counter in `StoreNames`
  (its lower bound would have to travel beside `idxCert`, and `End` and `NewStore` return it);
  keeping the whole authority in `revMuInv` and borrowing it at `End` (the writer's pin,
  `soleWriter_pins_write`, reads it inside `storeTxnWriteIs`).

Spec changes: `store.Read` (two binders, pre and post), `storeTxnWrite.End` and
`metricsTxnWrite.End` (`txnEndPost`) posts, `NewStore` post, `newTreeIndex` post (the other half
of `idxLogAuth γ`). The `Link.lean` binders are unchanged (`gen-link.py --mvcc` reproduces it).

*Later (txn unit 1, 2026-10-11):* `metricsTxnWrite.Range` is over `isTxn mw s γ kind` (a write
transaction's range is `storeTxnWrite.Range`'s, `TxnKind.readLog`/`readRev`), and the range specs
(`rangeKeys`, `storeTxnCommon.Range`, `storeTxnWrite.Range`, `metricsTxnWrite.Range`) take
`rangeCtx todo ctx cd` (an `isContext`, or `context.TODO()`'s value) with `todo = true → r ≠ null`
in the post (`TxnRange.lean`); the old statements are the instances `kind := .read …`, `todo :=
false`. `metricsTxnWrite.Range` links `storeTxnWrite.Range` too.

---

## Read-index: a request registry per leader term, acks bounded by the event history

**2026-10-12 · accepted** (branch `worktree-raft-rest`)

`ReadIndex` (`ReadOnlySafe`; `ReadOnlyLeaseBased` needs bounded clock drift and stays out
of scope) is verified against the pinned raft, whose `readOnly` is the fixed one
(etcd-io/raft#392's stale validation is gone: a heartbeat's context is the leader's
request *position* in the term, `confirmedReads + len(unconfirmedReads)`, not the
client's context, and `maybeAdvance` confirms the positions a quorum acknowledged).

**What a `ReadState` promises.** A client creates a read context `c` with a fresh token
(`propFresh`, the proposals' token space); creation snapshots the global committed log
`Lc` into a registry in `raftCommitInv` (`readReq γ c Lc`, persistent, agreeing). A
`ReadState{Index: i, RequestCtx: c}` that `Ready` hands out carries `readOk γ c i`:
`|Lc| ≤ i`. Since committed logs are prefixes of one another, any committed log of length
at least `i` extends `Lc`: reading the applied state at an index `a ≥ i` reads a version
between the request's creation and now -- a linearizable read, stated with lower bounds
(the register's `Get`), not as an atomic update (the version is known only after the
fact).

**Why it holds.** At a request's arrival at the leader `L` of term `T` (commit `i`,
an entry of `T` committed, or a single voter), the global log `C` is justified by a
quorum `q` that acknowledged it at some term `t` (`committedJust`, `cq`). Either `t ≤ T`,
and then `|C| ≤ i`: for `t < T` because `C`'s last entry is of a term below `T` and `L`'s
log has an entry of `T` at `i`; for `t = T` because `C` was extended only by `L`'s own
commit (the commit lower bound `cmtLb γ L T n` now stored with the justification, against
the leader's monotone `cmtAuth`); or `t > T`, and then the request is *doomed*: every
member of `q` has acknowledged at a term above `T`. The arrival records which, under the
request's position `p`, in a per-(leader, term) mono list (`rqRec`). A heartbeat of
context `q ≥ p` carries the list's prefix (`rqLb`); a follower `v` answering it at term
`T` holds its event history (`ownEvs`, every event at or below its term), so `v` is in no
doomed request's quorum: its response carries `hbAck γ L T v q`. A quorum of such acks
for position `p` meets the doomed quorum, so a confirmed request is never doomed: its
`|Lc| ≤ |C| ≤ i`.

**Where the facts live.** `isMessage` is unchanged. The abstract `Msg` gained `ctx`
(default `[]`; `absMsg` takes it, default `[]`; `msgAbs` records `Context ↦*□ ctx`), and
the facts about contexts and read messages are `isCtx γ m` (heartbeat: the registry
prefix; heartbeat response: the ack; `MsgReadIndex`: `readReq`; `MsgReadIndexResp`:
`readOk`). They, the per-term registry, the leader's acks and the `ReadState`s are in a
predicate beside `ownRaftGhost`, `ownReadGhost γ id ps rd` (`rd` is the physical read
state, now `NState.rd`, which `ownRaftMisc` is indexed by). `ownRaftGhost` gains only
`cmtAuth` for a leader's terms (and `raftCommitInv` the read registry and `cmtLb`).

**Read credits.** The model lets the transport redeliver a message, so arrivals -- and
positions -- are unbounded, and a position that wrapped at `2^64` would confirm the wrong
requests. A `MsgReadIndex` therefore carries one read credit (`rdCred`, an `Auth Nat`
fragment, like the tick credits), linear: the client pays it at `ReadIndex`, a forward
moves it, an arrival moves it into the leader's stash, and the stash bounds the position.
`Ready` hands out each queued `MsgReadIndex`'s credit with it; the transport passes it
to `Step`. *Rejected*: a no-wrap premise on `Step` (no client could discharge it); a
credit per node (a forwarded request's destination is not known when it is paid).

**As built (2026-10-13), replacing "Where the facts live" above.** The facts went *into*
`isMessage` after all (a heartbeat's registry prefix, a heartbeat response's `HbAckOk`, a
request's `readReq`, a response's `readOk`): the transport and `Step` already carry
`isMessage` of every message, and a second predicate beside it would have doubled every
message invariant. The read state is protocol state (`PState.rd`, with `toPState` reading a
non-leader's read-only object as the fresh one `reset` installs), so each read path is a
`Step` rule refined once (`Refinement.lean`), and the ghost state is one more conjunct of
`ownRaftGhost` (`rdOwn`: the per-term registries `reRdq`, the leader's records and acks,
the `ReadState`s' and pending requests' facts, the outbox's credits). A context's bytes are
`isPropData` (the proposed-slice registry, read through `propDataInv`) rather than a heap
points-to, so the facts stay persistent. `Step.beat` takes any context a leader may send
(`HbCtxOk`: none, or a position up to its queue's end, unwrapped) rather than exactly the
current one, because a release broadcasts after each request and the spec collapses those
heartbeats. `stepLeader`'s read premises (`RdOk`, a nonzero term) are conditional on the
three types that read them, so the other branches discharge them by type.
*Rejected*: making `RdOk` a field of `ownRaftPhys` (it is a fact about the ghost records,
which the physical predicate does not see); a logically atomic `Read` for the register (the
linearization point is in the past when the `ReadState` arrives: it would need prophecy).

---

## Reconfiguration stage D: conf-change entries as data, their bytes through the proposal

**2026-10-13 · accepted**

Conf-change entries are in the log as data (notes/STATUS.md, "Reconfiguration, stage D");
three choices in how:

- **The leader's decoding needs the bytes; they travel with the protocol message.** `stepLeader`
  `Unmarshal`s each proposed conf-change entry and panics on an error, so `raft.Step` needs each
  conf entry's bytes, which decode (`ccEntsOk`, a heap fact). A local proposal
  (`RawNode.ProposeConfChange`) has them from `confChangeToMsg`; a forwarded one reaches the
  leader through the network, where only `isMessage` (ghost, heap-free) survives. So the bytes are
  recorded where the client data already are: the proposed slices' registry (`isPropData`,
  `propDataInv`), and a conf entry's `entDataIs γ e none` carries `∃ bs, isPropData γ e.Data' bs ∗
  ⌜CCDecodes e.Type' bs⌝`; `node.run` turns it back into bytes (`propData_ccEnts`).
  *Rejected*: restricting forwarded proposals to normal entries (a follower's `ProposeConfChange`
  would be unspecifiable); a pure premise (bytes are heap); putting heap points-to into
  `isMessage` (the protocol layer is heap-free and imports no `Base`).
- **The client log stays a log of normal entries.** `entDataIs`'s `some d` keeps `Type = 0`, so a
  conf entry is `none` and `firstOcc`/`cLog`/`propsOwn` skip it with no change; the zero-slice
  `none` case now also requires `Type = 0` (else a `Type = 1` entry with no data would escape the
  decoding fact).
- **`stepLeader`'s exact answer, existentially.** The loop's result depends on what each entry
  decodes to (an empty `ConfChangeV2` is refused); `LeaderProposeResult` quantifies over the decoded
  changes (`∃ cs, CCTypesOk ents cs ∧ ...`) rather than adding a parameter, so that the fifteen
  non-proposal call sites of `stepLeader` are unchanged; `Step.propose` takes any batch related to
  the proposal by `PropRepl` (each entry kept or a conf entry replaced by the zero entry), which is
  all the ghost state needs (`entData_propRepl`).

`Config.DisableConfChangeValidation = false` is a scope premise (with validation off a leader may
append a second conf change before the first is applied), like `ReadOnlyOption = 0`.

---

## Reconfiguration stage D: `ApplyConfChange` of an unchanged configuration -- `Step.reMatch`, `switchToConfig` open at its tracker

**2026-10-13 · accepted**

- **A model rule that lowers `Match`.** Even a change that leaves the configuration as it is
  makes `switchToConfig` install new `Progress` objects, and `confchange`'s specs (`ownNewPr`)
  say only that each is a copy of an old one *or* fresh (`Match = 0`): a remove and re-add of a
  voter in one `Simple` really does reset its `Progress`. A leader's `matched` can therefore
  drop to `0`; `Step.reMatch` says exactly that (each new entry `0` or the old one; entries may
  come and go). It is sound because `matchedOk` asks only `isAcked`, which holds of `0`.
  *Rejected*: strengthening `confchange`'s specs to track which objects are copies (every
  `Changer` proof would change, and remove-then-add still resets); a premise excluding resets
  (not expressible on `ownResult`).
- **`switchToConfig` takes the struct open at its tracker.** The new `Progress` objects share
  the old ones' `Inflights`, whose rings the old tracker owns; the caller must move them before
  the old tracker disappears, so the spec takes the tracker field and the re-sealing wand
  (`ownRaftPhys_reconfig`'s), the old tally and bound, and the new configuration with its
  records (`ownConfigV`). The old sealed statement is derived (`spec_nonleader`).
  *Rejected*: a wand in the precondition from the old `Progress` objects to the new
  configuration (the copies' values must agree with the old ones', which the wand could not
  see without the old points-tos).
- **No `Advance`-ordering premise yet**: for an unchanged configuration the order is harmless
  (issue file), and `ownRawNode` does not record applied entries; documented on the specs.

---

## Reconfiguration stage L: learners in the `Progress` record, the voter set as the index

**2026-10-13 · accepted**

- **The flag is in the record** (`Progress.learner`), and `ownTracker` relates it to the index:
  a tracked id is a learner exactly when it is outside `cfg` (`LearnerFlags`), so the learner
  set needs no index of its own -- it is `domSet s.progress \ cfg`. The price is that every
  give-back of a borrowed `Progress` carries `⌜p'.learner = p.learner⌝` (the methods' records are
  record updates, so it is `rfl`, or a `@[simp]` lemma for the branching ones).
  *Rejected*: a per-id flag map in `Trk` (a second index to keep in step with `peers`); an
  `ownProgress` indexed by the expected flag (the same premise on every give-back, plus a
  signature change everywhere).
- **A non-follower is a voter, in `ownRaftPhys`** (`Hvoter`), not in the ghost state: only
  `raft.wp_store_state` changes the role, and all its callers already know `id ∈ cfg`. So
  `raft.Step`, `stepCandidate`, `stepLeader` and `applyConfChange` no longer take it.
  *Rejected*: a `RoleOk`-style conjunct in `ownRaftGhost` (82 sites build or open it).
- **`RawNode` keeps its voter scope for now**: a learner node needs the configuration in
  `RNState` (part 3), because `node.run` looks the node up in its progress map around
  `applyConfChange`, and `NetFrame` says nothing about the progress map's domain. The
  `RawNode`/`node` `ApplyConfChange` premise is `CCNoop` (a no-op whatever the learners) until
  then.

---

## Reconfiguration stage A1: one body for both struct predicates, old specs as corollaries

**2026-10-13 · accepted**

- **`ownRaftPhysC` beside `ownRaftPhys`, one private body.** The body of the raft-struct
  predicate is generic in the tracker predicate and in `Hvoter`'s voter set
  (`ownRaftPhysG T V`, private to `InvRaftPhys.lean`); `ownRaftPhys cfg` is it at
  `ownTracker cfg`/`cfg`, `ownRaftPhysC c` at `ownTrackerC c`/`c.voters`, each sealed. The 134
  files on `ownRaftPhys` are untouched; `ownRaftPhys_toC`/`ownRaftPhysC_toPhys` convert at
  `CfgM.simple cfg (domSet s.progress \ cfg)`. *Rejected*: redefining `ownRaftPhys cfg` as
  `ownRaftPhysC (CfgM.simple ...)` (every accessor in `InvRaftPhys.lean` would go through the
  conversion); making `ownRaftPhys` an `abbrev` of a sealed generic predicate (changes
  elaboration in every caller). The ~60 field lemmas are still stated on `ownRaftPhys`; A2 can
  restate them on `ownRaftPhysC` and derive the old ones through the equivalence (a field
  access leaves `s.progress` alone).
- **`ownTrackerC` uses `confchange`'s representation** (`ownCfgCC`, `CfgInv`) so that a
  `Changer` result can be installed without translation; the learner flags are
  `decide (k ∈ c.learners)` (`LearnerFlagsC`), which every `Changer` operation preserves on a
  reachable state (a voter is never flagged; to be proved in A2). `ownTracker` stays a separate
  definition with a two-way conversion, not a special case by definition: 19 files unfold it.
- **Generalized specs replace the old ones; the old statements are corollaries**
  (`<fn>.spec_simple` in the `Spec` file, derived from the new `spec` through the tracker
  conversion), so that `Link.lean` still links one triple per function and each caller changes
  one line (`wp_apply (X.spec_simple wp_X) ...`). `JointConfig.VoteResult` is general in its
  receiver and vote map (any `*JointConfig`, any fractions), which also let `QuorumActive` stop
  inlining it.
- **`StepC` is a copy of `Step` with five rules generalized**, not a parameterization of
  `Step` (which would change every constructor use in the ghost layer); `step_iff_stepC` ties
  them. `CfgM` moved to `Protocol/StepC.lean` so that the protocol layer can name it.

---

## Reconfiguration stage A2: `ownRaftPhysCV` with an abbreviation, `specS` corollaries, a recorded `stepDownOnRemoval`, a detached `RawNode`

**2026-10-14 · accepted**

- **The specs move, the old statements stay.** Each raft function whose callers can be at a
  joint configuration gets its `spec` restated on `ownRaftPhysC`; the old statement is an
  `abbrev <fn>.specS` with `<fn>.spec_simple : spec → specS` (through `ownRaftPhys_toC'` and
  `ownRaftPhysC_toS`), so `Link.lean` still links one triple per function and an old caller
  changes one line (`wp_apply (X.spec_simple wp_X)`; `raft.Step.Postulates` fields are `specS`).
  Config-independent proofs were converted by renaming (the field lemmas' `C` copies), not
  duplicated. *Rejected*: proving each function twice.
- **`Hvoter`'s set is a parameter (`ownRaftPhysCV c V`), `ownRaftPhysC` its abbreviation.** A
  removed or demoted leader is, between `switchToConfig`'s install and its `becomeFollower`, a
  leader outside its configuration; the struct must be sealed there for `becomeFollower` (and
  `reset`), so their specs and the field lemmas are generic in `V`. Specs write
  `ownRaftPhysCV c c.voters` rather than the abbreviation: `iframe` does not unify an `abbrev`
  head with its unfolding up to the record equalities states need.
- **`r.stepDownOnRemoval` is recorded (`NState.sdr`)**, so that `switchToConfig`'s spec can ask
  for it when the leader leaves the voters; with it off the Go leader stays leader outside the
  configuration, which `Hvoter` excludes. A removed candidate is likewise excluded (and is a
  finding: it can win and panic).
- **The configuration after a `RawNode.ApplyConfChange` that changes it is not `γ`'s**:
  `ownRawNodeC` keeps the memory and drops the ghost state, rather than asserting
  `γ.reCfg = votersOf c'` (the protocol is proved at a fixed voter set). The `Advance` ordering
  is documentation, not a premise: no predicate records which entries the configuration
  reflects.
- **`CCGood` instead of strengthening `confchange`'s specs**: reachability is a pure invariant of
  the model (`ccApplyM_good`), so the `Changer` proofs are untouched.

---

## Reconfiguration stage A3: `joint` as a parameter of the loop's model, snapshots of any voters, no `StepC` step-down rule

**2026-10-14 · accepted**

- **`propConf` and `LeaderProposeResult` take `joint`, default `false`**, rather than a second
  copy of the conf-change loop's model: the refusal is `pending ∨ ccWantsLeave cc ≠ joint`,
  which is the old `pending ∨ ccWantsLeave cc = true` at `joint = false`. The ghost layer
  (`raft__Step/MsgProp.lean`, `PropRepl`) keeps elaborating against the default; the C result
  passes `c.joint`. *Rejected*: a `LeaderProposeResultC` duplicate (the dispatcher's `MsgProp`
  branch would need its own copy of the reasoning).
- **`readOnly.maybeAdvance.spec` replaced, no `spec_simple`**: its only caller is `stepLeader`,
  now at any configuration.
- **A snapshot of any (non-joint) voters, at any configuration.** `restore` never reads the old
  configuration except to drop it (`MakeProgressTracker`), so generalizing the node's
  configuration costs only the retrack; generalizing the snapshot's voters away from the node's
  is free (`SnapScope cfg` was already a parameter). The snapshot's voters are a new spec
  parameter (`scfg`) of `stepFollower`/`stepCandidate` rather than existential in `Hsnap`, so
  that the result can name the configuration after a restore. A joint snapshot `ConfState`
  stays out (`confchange.Restore` of a joint state is not specified); stated, not hidden.
- **The removed leader's step-down is a disjunct of `applyCCOkC_step`, not a `StepC` rule**:
  `StepC` is tied to `Step` by `step_iff_stepC` at non-joint configurations, and `Step` has no
  such rule either (a leader there is always a voter). The protocol at joint configurations will
  have to add one (or forbid self-removal).
- **Items 3-5 left with a plan** (notes/STATUS.md, "Reconfiguration, stage A3"): the `raft.Step`
  branches are physical triples with pure `Step` witnesses, so `raft.Step` at `c` is their
  conversion to `StepC` (with C result and step lemmas), and the old branch lemmas follow at
  `CfgM.simple`; the `RawNode` client's view (`RNState`) needs the learner set (and, for
  self-removal, the role) before `CCApplies` can be discharged for growing changes.

---

## Reconfiguration stage B2: non-empty voters in `RaftNames`, one `CfgStatic` constraint

**2026-10-14 · accepted**

- **`RaftNames.reCfg_ne`, a proof field**, rather than a premise of `ownRaftGhost_step(C)`'s
  callers or a conjunct of `ownRaftGhost`. `StepC` at an empty configuration lets anyone win
  (Go's `MajQ` convention), so the refinement needs `reCfg ≠ ∅`; `raft.Step`'s spec has no way
  to supply it (learners step, `ownRaftPhys` has no non-emptiness by design, and changing the
  Go-facing spec was out of scope), and a conjunct of `ownRaftGhost` would touch every rule's
  re-sealing. The field costs one premise of `ownRaftGhost_alloc`. *Rejected*: mapping `Step`
  at an empty configuration into `StepC` (`Step.lose` there has no `StepC.lose`, and no `c`
  makes every `JQuorum c` an `IsQuorum ∅`).
- **The constraint is `CfgStatic γ c` (incoming = `γ.reCfg`, not joint)**, not
  `c = CfgM.simple γ.reCfg lrn`: the same at B2, but with no learner bookkeeping, and the shape
  B4 replaces. The three quorum-reading rules convert `JQuorum c` to `IsQuorum γ.reCfg` at their
  start; the ghost definitions keep `IsQuorum γ.reCfg` (moving them is the winners table's
  work).

---

## Reconfiguration stage B3: a separate state `RState` and relation `StepR`, `Adm` for the configurations

**2026-10-14 · accepted**

- **The new fields are on `RState` (`Protocol/StepR.lean`), not on `PState`.** `PState` is what
  the ghost state holds and what `toPState` (`Defs.lean`) computes from the physical `NState`
  in ~100 places; adding `applied`/`pci`/`snap` there would make every code-side witness
  (`raft.Step`'s branches, `RawNode.Advance`'s `appliedTo`, which steps `MsgStorageApplyResp`)
  prove the new fields equal, and the configuration index, the configuration and the full
  prefix are not in `NState` at all. `RState` is `PState` plus `applied`, `pci`, `snap`,
  `cidx` (Nat, ghost), `cfg : CCState` and `fp` (ghost full prefix). `StepC`,
  `step_iff_stepC`, `ownRaftGhost_stepC` and every code proof are untouched. *Rejected*:
  fields with defaults on `PState` (the `where`-built states `pbecomeFollower` etc. would
  silently reset them; `toPState` would have to supply them, and then every `Step` witness
  that moves them would change).
- **`StepR` duplicates `StepC`'s rules** (as `StepC` duplicated `Step`) rather than lifting a
  `StepC` step: a lift constructor would let `StepC.campaign`/`propose` bypass the guard and
  the exact proposal loop, and `StepC`'s constructors cannot be split into "touches the new
  fields" and "does not" without renaming the ones the code-level C specs use.
- **`step_iff_stepC`'s replacement is a projection, not an equivalence.** `StepR` is strictly
  stronger than `StepC` (the guard, `propConf` instead of any `PropRepl`, `AppCommitEq`), so no
  embedding `StepC → StepR` exists; what the ghost needs is `stepR_static`: at a static
  configuration (`StaticAdm V`), from a state whose non-follower is a voter (`RoleVoter`, the
  code's `Hvoter`), a `StepR` derivation is a `StepC (CfgM.simple V ∅)` derivation of the
  `PState`s, and `ownRaftGhost_stepR` follows from `ownRaftGhost_stepC` in one line. The
  dispatcher boundary is unchanged: the code still produces `Step` witnesses.
- **`Adm : List Entry → CCState → Prop` parameterizes `StepR`**: the configurations a node may
  take on after a prefix, by `applyConf` or `snapRestore`. One relation serves both the static
  model (`StaticAdm V`, under which the projection holds) and the dynamic one (`AdmFold dec c0`:
  A3, a snapshot's `ConfState` is its prefix's fold); `StepR.mono` moves between them. A
  snapshot's configuration being its prefix's fold is not something the receiving node checks,
  so it is not a premise of its own; `Adm` carries it. *Rejected*: `c0` as a parameter with A3
  as a premise of `snapRestore` (then the static model, which has no `c0`, needs one), or A3 as
  a hypothesis of `RInv_stepR` only (then it would quantify over the derivation's choices).
- **The decoder is in `StepR`'s `applyConf`** (`dec (full.take k) e = some op`): the application
  passing the decoded change, in order, once per entry, is A1's scope, so the rule states it.
  `CCDec` takes the prefix (the review's gap 3): `cfgFold` is now `cfgFoldFrom dec []`, which
  passes the prefix along; `CfgOverlap.lean`'s lemmas are generic in it and kept their proofs up
  to the `pre` argument. `decOfData data` is the entry-only decoder from the proposed bytes
  (`isPropData`'s map as a function).
- **The invariants' message knowledge is a hypothesis per rule** (`AppKnow` for `appAccept`):
  the sender's log `G` with I1 at the message's commit index and log matching with the
  receiver's full log are ghost facts (B4). The induction `RInv_stepR` states it for any state
  with the invariant, since a derivation does not name the receiving state; B4 can use the
  per-rule lemmas inside its own induction instead.
- **`AppCommitEq` is a premise of `StepR.sendApps`/`win`.** I1 is false under `StepC`'s `AppOk`
  (`m.commit ≤ s.commit`); Go sends the exact commit index. Recorded in notes/STATUS.md as a
  finding about the model, not about Go.
- **`propDrop` receives nothing**: the code's dropped proposal takes no protocol step (its
  `Step` witness is `refl`), but `stepLeader`'s loop has already moved `pendingConfIndex`.

---

## Reconfiguration stage B4: winners table as a ghost map, `CfgAt` as the one static hook, the ghost stays on `StepC`

**2026-10-14 · accepted**

- **The winners table is a global ghost map `term ↦ ((winner, configuration), quorum)` whose
  persistent elements are part of `isWin`**, with the authority (and each entry's record) in
  `raftCommitInv`. So election safety (`isLeader_unique`) is the elements' agreement and stays
  a persistent, invariant-free lemma: the code proofs that use it (`raft__Step.lean`,
  `MsgSnap*`, `Facts.lean`, `Results.lean`) are untouched, and in the dynamic proof it needs no
  quorum intersection at all. The intersection argument moved to win time (`win_fresh`), the
  only place that inserts. *Rejected*: the table as a pure map inside the invariant read through
  the invariant (every `isLeader_unique` user would open `raftCommitInv`, code included).
  `isWin`'s signature is unchanged (the configuration is existential inside it), so `klOk`,
  `voteJust` and their users did not change.
- **`CfgAt γ P c`, defined at B4 as `CfgStatic γ c`, is the single hook for the configuration**,
  and `CfgAt.overlap` the single static lemma; the definitions record `(P, c)` with each quorum
  so B5 changes `CfgAt`'s body and the three uses of `CfgAt.overlap`, not the predicates' shapes.
  *Rejected*: a static/dynamic mode field in `RaftNames` (B4 would prove everything under a
  `mode = static` premise threaded to the code), and recording configuration indices `j` now
  (they need the decoder and `c0` in the ghost, i.e. B5's `cfgFold` link).
- **The dynamic-only facts (commit facts' at-most-one and witnesses, the campaign's witnesses,
  `W`) are not added as placeholders.** They are false for `StepC` runs (no `pendingConfIndex`,
  any commit index on `MsgApp`), so their content cannot be proved before the ghost follows
  `StepR`, and `True` placeholders would not save B5 any rule's proof.
- **The ghost keeps refining `StepC`, not `StepR`.** Nothing produces a `StepR` derivation (the
  code produces `Step`), and the dispatcher cannot convert one: `StepR` is strictly stronger
  (the campaign guard, the exact proposal loop, `AppCommitEq`), and its extra state (`applied`,
  `pci`, `snap`, and the ghost `cidx`, `cfg`, `fp`) is not in `PState`/`NState`. Refining
  `StepR` directly needs B7's code-side witnesses and an `ownRaftGhost` that holds the `RState`
  fields with `RInv`; `ownRaftGhost_stepR` (B3) stays the projection.

## Reconfiguration stage B5: a mode in `RaftNames`, guarded dynamic facts, the ghost refines `StepR` beside `StepC`

**2026-10-14 · accepted**

- **The mode is a field, `RaftNames.reDyn : Option (∀ e, DynCfg)`, and `ownRaftGhost` carries a
  flag `md` (default `false`) with `⌜γ.reDyn.isSome = md⌝`.** B4 rejected a mode field to keep
  the code proofs free of a `mode = static` premise; with the flag defaulting to `false` they
  are, and the code gets the static mode from its own `ownRaftGhost` (`ownRaftGhost_static`,
  two dispatcher lines). `DynCfg` is the configuration function of committed prefixes with the
  one fact the ghost uses (`adj`: overlap for prefixes at most one conf entry apart,
  `fold_adjacent`); `DynCfg.ofFold dec c0` instantiates it, so `Ghost.lean` does not import
  `CfgOverlap`. *Rejected*: two ghost states (static and dynamic) -- every rule's proof twice.
- **Dynamic-only facts are guarded, `dynOn γ P := ⌜γ.reDyn = none⌝ ∨ P`**, inside the shared
  predicates (commit facts, campaign facts on votes, I1 on `MsgApp`). The static mode proves
  them by the left disjunct, so the `StepC` refinement (where they are false, B4) is unchanged;
  the dynamic mode uses the right. *Rejected*: separate dynamic predicates (every message and
  record shape duplicated).
- **The commit fact is recursive** (`cqAt`, well-founded on the configuration index): in the
  dynamic mode it carries `ConfI1` (at most one conf entry above `a`) and, for the conf
  positions `≤ a`, witnesses that are themselves commit facts (`witsB`); `commitIn` (a node's
  commit index) carries the witnesses of its prefix. Campaign facts (`campDyn`: `ConfI1`, the
  witnesses, `commitIn` below the term) travel with each vote instead of in the campaign
  record, since the voter, not the candidate, is where `lc_core`'s far case needs them.
- **`doomed` keeps a witness set `U`** (the doom quorum and every witness quorum above `T`), with
  a finite choice (`doom_choice`) to pick it when a read is confirmed; repair 4 needs the
  reader's acknowledgement in each.
- **The step environment `dynEnv`** is a premise of the configuration-reading rules: static,
  `CfgStatic γ c`; dynamic, the facts of `RInv` they read (full log, `cidx`, `ConfI1`, `CfgAt` of
  the applied prefix, the leader's I3, the candidate's campaign record at its commit index).
  `ownRaftGhostR` (`ownRaftGhost … true ∗ RInv ∗` the records of the full prefix `∗` a
  candidate's campaign record) provides it; the per-rule lemmas do not know about `RState`.
- **Snapshot prefixes as a premise.** `StepR.snapRestore`'s new full prefix is constrained only
  by `FullOk` and `Adm`; rather than strengthen `StepR` (B3's model), the refinement takes the
  records of the derivation's admissible prefixes (`AdmS dec c0 S`, `□ ∀ fp, ⌜S fp⌝ -∗ logRecs`).
  The code (B7) supplies them from the snapshot message's knowledge.
- **`stepDown` by weakening, not by excluding it.** `TermsOk`/`WinsOk`/`LcmOk` allowed a term's
  entry only below the node's term or at it as leader; now at it as a non-candidate, so a
  leader may become a follower at its term. What that loses (a non-leader's acknowledgements of
  its term need a justification, `acksOk`) is restored by `LeadAcksOk` in `ownLogGhost` (a
  leader acknowledges only entries of its log, a candidate none of its term), which lets
  `ownLogGhost_stepDown` justify them by the leader's own prefix. *Rejected*: assuming
  `StepDownOnRemoval = false` (Go's default) -- a premise on the configuration that the code
  would have to carry, for a rule the model already has.
- **The ghost refines `StepR` in the dynamic mode and `StepC` in the static mode**, both from the
  same per-rule lemmas; B4's decision (the code-facing ghost stays on `StepC`) stands until B7.

## Model-level theorems in `Results.lean` are scaffolding (2026-10-14)

The verified boundary is the Go public API: the specs of `RawNode`/`node`/`NewRawNode`/...
(`Link.lean`). A protocol-level theorem restated in `Proof/go_etcd_io/raft/v3/Results.lean`
(`raft_election_safety`; the reconfiguration stage B5/B6 results `raft_reconfig_*`, with the
collection `etc/tcb-collections/raft-dyn.txt`) is kept only while it drives development: a
check that the model is not vacuous, or a root of the trust report that keeps a model proof
checked (no `sorry`, no axiom) before any Go spec reaches it. Once the Go code that reaches
it is verified (for `raft_reconfig_*`, stages B7/B8: the public specs carrying the dynamic
ghost), the stage that does so deletes the restatement and its collection. New stages do not
add model-level theorems as deliverables. (The user's decision, 2026-10-14.)


---

## Reconfiguration stage B7: `raft.Step`'s branches deliver `StepCD`; the spec is generic in a ghost mode

**2026-10-14 · accepted**

- **`raft.Step` at a configuration first (B7a), by conversion.** The branch lemmas are physical
  triples with pure witnesses, so moving them to `ownRaftPhysCV c c.voters` and `StepC c` was a
  textual conversion (accessor names, `Step` to `StepC` constructors) followed by fixes: the C
  inversion lemmas give `c = c'` off a snapshot. Five forks converted the leaf families in
  parallel against a recipe validated on one file. *Rejected*: keeping the static branch lemmas
  and lifting at the dispatcher, because `ownRaftPhys` cannot express a joint configuration.
- **`StepCF` plus `RFrame`, not `StepR` witnesses written per site.** Most rules leave
  `StepR`'s extra fields alone. So a sub-relation `StepCF` of `StepC` (without `campaign`,
  `win`, `propose`, `snapRestore`; `sendApps` with `AppCommitEq`) lifts to `StepR` once
  (`StepCF.toR`), and a branch only proves `RFrame s s'` (`applied`, the pending snapshot, a
  leader's `pci`) for `rOf` to agree. The constructor names are shared, so the frame branches
  converted textually. Only six special branches needed a hand-written `StepR` witness.
  *Rejected*: a lift of arbitrary `StepC` derivations (no inductive shape to inspect), and
  writing `StepR` at every site (about 80 sites, each with its own frame equation).
- **`StepCD` bundles both witnesses.** A branch delivers the `StepC` witness (static mode) and,
  under `DynHyp`, a `StepR` witness for every ghost part over `c`. This keeps the static path
  intact and makes the dynamic path available with no second set of branch lemmas. Branches
  outside the dynamic scope (a `MsgSnap`, a pre-candidate's campaign) give only the first
  (`StepCD.of_excluded`).
- **`pci` is the code's at a leader and `0` elsewhere** (`pciR`). The model's
  `lose`/`abandon` keep `pci`, while the code's `becomeFollower` clears it. A pre-candidate
  keeps it, since Go's `becomePreCandidate` does not `reset`. Mapping non-leaders to `0` makes
  the two agree with no new code invariant, and `StepR` reads `pci` only at a leader.
- **One spec, generic in a mode (`GMode`), not a conjunction of two triples.** The ghost-fact
  lemmas the dispatcher reads are generic in `ownRaftGhost`'s flag, and only the update depends
  on the mode (`ghost_stepCD`). So one dispatcher proof serves both modes, `raft.Step.spec`
  stays one Hoare triple, and the static statement is derived (`spec_simple`). *Rejected*:
  moving `RawNode`, `node.go` and the register to the dynamic mode in the same step, which is
  part 2's work.
- **The dynamic mode's unchecked conditions are premises (`GMode.Pre`), named.** They are: no
  `MsgSnap` (B8), no pre-candidate, A1 at `MsgStorageApplyResp`, and the dropped-proposal
  index bound. The A1 premise is on the acknowledged entry's index. The branch gives the new
  `applied` (`Happ`), and `RInv`'s `applied ≤ cidx` covers the case where `applied` does not
  move (`GMode.Pre.dynHyp`).
- **`appliedTo`'s auto-leave excluded at a leader rather than specified.** Its `r.Step` makes
  `appliedTo` and `raft.Step` mutually recursive, and the link (one proof per function,
  callees' specs as hypotheses) has no form for that.
- **`AppCommitEq` went into `ReplSends`'s definition** rather than into a separate
  postcondition conjunct. Every producer already satisfies it (`maybeSendAppend` is the only
  one that builds an `MsgApp`). Consumers that need only `ReplOk` take `ReplSends.replOk`.

## Reconfiguration stage B8: the general statements as `spec`, a snapshot's lists as a record, A3 as the receiver's premise

**2026-10-14 · accepted**

- **The general statement is the `.spec` and the old one `specS`** for `confchange.Restore`,
  `ConfState.Equivalent` and `assertConfStatesEquivalent` (as A1/A2 did for the raft
  functions). The link (`Link.lean`) gives each callee's `.spec`, so a caller needing the
  general statement gets it with no new link entry; the callers keeping the old statement
  (`newRaft`) convert in one line (`spec_simple`). *Rejected*: keeping `specG` beside `spec`
  -- a caller of `specG` would need its own link entry.
- **A snapshot's `ConfState` lists as one record, `CSLists`**, with one read-only predicate
  `ownCSL` for its four slices, from the storage (`HSnapshot`) through `raftLog.snapshot`, the
  pending snapshot, `send` and the outbox (`msgAbs`) to the receiver (`"Hsnap"`).
  `absSnap`/`absSnapFrom` take the record, so every pattern on `msgAbs` and every mention of
  `absSnap m sv voters` kept its text (the binder's type changed). The abstract message
  (`Msg`) still keeps the incoming voters only.
- **`SnapScope sv cl`** is `CSWf` plus what the comparison with `switchToConfig`'s sets needs
  (no repeats, `AutoLeave` off when not joint) and the bounds; the node is in one of the three
  lists `found` searches (`CSLists.Has`). The `ConfState`'s configuration is `snapCfg sv cl`
  (`csCfgM`), which `Restore` answers exactly (`restoreM_wf`).
- **The `MsgSnap` branch delivers `StepCDS`, not `StepCD`.** `StepCD` keeps the ghost part but
  its configuration index, which a restore replaces wholesale (configuration index,
  configuration, full prefix); and it is universal in `Adm`, which a restore cannot be (its
  prefix and configuration must be admitted). `StepCDS` quantifies over the prefix `fp'` and
  configuration state `cs'` the dynamic model admits, and gives some ghost part over the
  configuration afterwards. `GMode.StepOut` moves to any ghost part, at `AdmFold`
  (`StepR.mono` from `AdmS`).
- **A3 is a premise of the receiving `raft.Step`, stated on the snapshot's recorded prefix**
  (`GMode.SnapOk`, dynamic: `□ ∀ fp, logRecs γ base0 fp -∗ ⌜FullOk (snapId sv) fp⌝ -∗
  ⌜SnapConfOk ...⌝`). The prefix itself comes from the message (`isMessage_snap_prefix`: the
  sender's leader prefix taken to the snapshot's index, with records), so B5's
  snapshot-prefix premise `S` is supplied by the code without changing `StepR` (B5's plan).
  The form quantifies over recorded prefixes rather than naming one: records agree, so it is
  one prefix, and the statement names no node's log -- it is a fact about the ghost records
  that, once true, stays true, which is what a sender could later hand along with the message.
  *Rejected for now*: `isMessage` carrying A3 (the message from the sender's storage). The
  abstract `Msg` keeps only the incoming voters, so `isMessage` cannot name the other three
  lists; the physical outbox relation (`msgAbs`, in `ownRaftPhys`) has no ghost names. Either
  needs a structural change (the lists in `Msg` and every `Msg.mkV` site, with the refinement's
  `sendApps` taking the A3 of the snapshots it sends; or the `RawNode` delivery predicate
  handing the fact out), recorded in notes/STATUS.md as left.
- **The static mode's snapshot** is `GMode.SnapOk`'s static clause, `listToSet scfg.voters =
  γ.reCfg ∧ scfg.outgoing = []`: the configuration a restore installs is still `CfgStatic`.
  `raft.Step.specS` keeps its premise list (its callers, the `RawNode` files, discharge
  `"Hsnap"` by the message type and did not change).


---

## Reconfiguration stage B7 part 2: one `ownRawNode`, generic in a mode

**2026-10-14 · accepted**

- **The mode is a field of `RNState`, not a parameter of `ownRawNode`.** Every spec already
  says `ownRawNode γ rn id { rs with … }`, which keeps the mode, so no statement of a spec
  that does not care about reconfiguration changed shape. The mode is the ghost state's
  (`ownRawNode_mode`: static iff `γ.reDyn = none`).
- **One body for both modes** (`ownRaftPhysCV cf`, `ownStepGhost` in `rs.mode.toG …`), not a
  `match` on the mode: every proof is written once, through `raft.Step.spec` in the node's
  mode. The static view (`ownRaftPhys γ.reCfg`, `ownRaftGhost`) is recovered where a proof is
  about the static mode only (`ownRawNode_static_open`/`_intro_static`).
- **Discharge the dynamic premises from the struct rather than state them to the client.** No
  pre-candidate: a new conjunct of `ownRaftPhys` (a pre-candidate has pre-vote on), kept by the
  one role store that makes one. The dropped proposal's index room: the log's own bound
  (stable part below `isStorage`'s `2^61`, unstable part a Go slice), as `appendEntry` already
  derives it. *Rejected*: an index budget like `node.go`'s term budget (nothing to budget: the
  bound always holds).
- **`stepDownOnRemoval` persistent in `raftOwn`.** The dynamic `ApplyConfChange` needs `sdr`
  on at the current state; carrying `s'.sdr = s.sdr` through `raft.Step`'s frames would touch
  every branch and callee result (tried: the cascade reaches `stepLeader`'s results). The field
  is never written after `newRaft`, so a persistent points-to gives it for free.
  `ownRawNode` keeps `sdrOk` (the field's value, on in the dynamic mode).
- **`GMove` in `GMode.StepOut`** (merged with B8b's `∃ g'`): the RawNode layer needs to know
  that the configuration index moves only at a `MsgStorageApplyResp` (and how), to keep
  `RNState.capplied` exact for the client's A1.
- **`ApplyConfChange` is one triple with a mode split** in its premises and its post, the
  static outcome unchanged under `⌜rs.mode = .static⌝`.
- **`node.go` stays static** (`isNode`'s `Hstatic`): its `confc` arm and channel protocols carry
  the static premise; making them dynamic needs the configuration index shared with the driver
  (left).

## Verifying a fork revision of raft: the single-voter read-index fix (stage F)

**2026-10-14 · accepted**

- **The raft pin is a fork revision, not upstream.** `issues/raft-readindex-singleton-stale.md`
  is a real stale read under reconfiguration; a spec premise can exclude it statically
  (`1 < size cfg`) but not once configurations change, where it would be a restriction on runs.
  So the verified code is etcd-io/raft `40f8be7` plus the fix (and its regression test): commit
  `0560cb7` on branch `raft-goose-lean` of `upamanyus/etcd`, a branch holding etcd-io/raft's
  history (the fork repository otherwise holds etcd). `etc/goose.py` pins it (comment there),
  CLAUDE.md says so, and the register's `go.mod` replaces `go.etcd.io/raft/v3` by the same
  revision under the path `github.com/upamanyus/etcd/v3` (Go refuses the plain path: the fork's
  `go.mod` declares a `/v3` module). Not reported upstream yet. *Rejected*: restricting runs
  (no single-voter configuration while a leader may get `MsgReadIndex`), or keeping the shortcut
  static-only -- both leave the code as shipped unverified on a path users reach.
- **The shortcut is two model rules, refined by the heartbeat argument with the quorum `{id}`.**
  `readSingle`/`readReleaseSingle` (a request, or every pending one, answered at the commit
  index) for a leader with an entry of its term committed, at `CfgSingle c id`. The leader's own
  acknowledgement confirms the arrival's record: no new ghost state, and the same proof in both
  modes. *Rejected*: the static-only route of `notes/raft-readindex-spec.md` §4.4 (voter
  membership of campaigners in `isCampK`, past-term commit bounds in `lcmOwn`), which would have
  changed the ghost definitions and still not covered the dynamic mode.

## ReadIndex and proposals as persistent atomic updates over the full log (stage R)

**2026-10-14 · accepted** (`notes/raft-readindex-spec.md`, the backend unit T1's handoff; the
user's defaults for its open questions)

- **The client's view is the full committed log** (`rLog γ L`, ghost variable `reRLog`, replacing
  the first-occurrence client log `cLog`), moved only by deposited **persistent** atomic
  updates: `propAu γ d Q` at every committed occurrence of `d` (result `□ Q L`, the log before),
  the standing `noopAu γ` at raft's own entries (given by the client at allocation, through a
  continuation `allocClient` of `ownRaftGhost_alloc(_gen)`), and a read's `readAu γ Qr`, which
  leaves the log as it is. The register, whose operations are linear and must run once, keeps the
  first-occurrence slots itself (`opSlot`, the client's update with a later credit), which raft's
  `propSlot` used to be.
- **Reads fire at the deposit and at every commit after it** (open question 1, the user's
  default): an update over the live log cannot be fired at a prefix already committed, so "from
  the safe index on" is impossible; the read index enters only in what may be collected
  (`readWit`, `read_collect`: every committed log at least `i ≥ |Lc|` long was fired at).
  `readReq γ c Lc` now records the **exact** global log at the deposit.
- **The updates bind raft's entry with `∀∀`, not `∃∃`** (correcting the note's pair `∃∃ (L, e)`;
  open question 7 moot): in an atomic update the `∃∃` value is the client's choice (it hands over
  the precondition), the `∀∀` the linearizer's. So `propAu γ d Q = □ AU <{ ∃∃ L, rLog γ L }> @
  ⊤ ∖ ↑raftN, ∅ <{ ∀∀ e, rLog γ (L ++ [e]) ∗ entDataIs γ e (some d), COMM □ Q L }>`, the client
  learning the entry's data from the binder. (The notation does take several `∃∃` binders.)
- **One later credit per ghost step, with the commit invariant in two halves.** The note's plan
  (one `£ 1` per ghost step, used by `commit_extend`) does not work as stated: `Step`/`StepC`/
  `StepR` are transitive closures, so one derivation may commit several times, each commit firing
  updates under the invariant's later, and one credit strips one later. The commit invariant is
  split: the log half (`raftLogInv`, at `raftN.@"log"`) and the registry half (`raftRegInv`, at
  `raftN.@"reg"`: the registries, `noopAu`, a quarter of `reRLog`; the log half has the other
  quarter, so both are at the global log). A ghost step opens the registry half once with its
  credit (`regs_open`) and threads its contents (`regsOwn`) through the derivation
  (`ownRaftGhost_stepC_in`, `ownRaftGhostR_stepR_in`), whose case lemmas run at
  `⊤ ∖ ↑raftRegN` and open the log half only; the updates' outer mask `⊤ ∖ ↑raftN` excludes both.
  *Rejected*: a commit-counting index on the step relation (a copy of `StepC`'s forty rules and
  of every branch's derivation); deferring the firing to whoever collects (the log of `rLog`
  lagging the committed one, against the user's firing discipline, and a credit at `⊤` at every
  collection).
- **The credit comes from `raft.Step.spec`'s precondition** (the note's fallback; the
  [unsure] of §4.2): `raft.Step`'s dispatch applies the branch lemmas to the whole call, so no
  pure step precedes a branch's ghost update without restating them; `stepPost` carries the
  credit to each branch's `finish_branch`. Its callers (the `RawNode` methods, `tickElection`/
  `tickHeartbeat`, `node.run`'s arms, `Advance`'s pending loop, `ApplyConfChange`) take it from
  their own pure steps; no public `RawNode`/`node` spec changed for it.
- **A separate token map for read contexts** (`reRdFresh`, `rdFresh`; open question 5); the
  read registry's authority (`reReads`) is raft's, in the registry half.
- **The deposit is in the spec** (open question 9): `RawNode.ReadIndex`/`node.ReadIndex` take
  `rdFresh γ c ∗ readAu γ Qr ∗ isCommitted γ L0` and return `∃ Lc, ⌜L0 <+: Lc⌝ ∗ readReq γ c Lc ∗
  isRead γ c Qr`. Consequence for the register: its read's waiter is made (under the lock) before
  the call, so it cannot hold the deposit's record; the applier answers with the read state's
  index and the value after a committed log at least that long (`readAns`), and the reader, with
  the call's post, turns it into `readP`.
- **`▷ ▷` at collection** (open question 6): `read_collect`, `prop_collect` give `▷ ▷ □ Q`; a
  client spends `£ 2` (the register does, in `do`).
- **No extra facts in `readAu`'s precondition** (open question 8); lease-based reads and
  crash-restart stay out (10, 11).
- Raft's read registry is `readsReg` (the register already had a `readsOwn`).

## Stage N: `node.go`'s configuration shared with the driver, by slots and lower bounds

**2026-10-15 · accepted**

- **What is shared, and how.** In the dynamic mode `run` must check a conf change against its
  `RawNode` (`DynCCPre`: the entry handed out, past the configuration index, at the
  configuration in use) from what the driver knows, and A1 at `Advance`. The committed log
  handed out is a `mono_list` (`dlm`): `run` holds the authority, the driver lower bounds, enough
  since the change's facts are about a prefix. The configuration of the last applied change is a
  ghost variable in halves (`cap`), which `confc` carries to `run` and `confstatec` back; its
  index is also a monotone nat (`cam`) whose lower bound the driver hands to `advancec` with A1.
  `Advance` may move the `RawNode`'s index past the shared one over no conf entry, so `runCfg`
  states `ca ≤ rs.capplied` and `NoConfIn` between, rather than equality.
- **The answer slot `ccq`.** A handshake's receiver gives its `Q` before it sees the payload
  (`handshake_receive_au`), so neither `confstatec` nor `advancec` can hand back a resource whose
  value depends on the request. The driver therefore keeps half of `ccq` at the answer it expects
  (`(k + 1, cs')`) and sends the other half with the request; `run`'s answer carries `cap`'s half
  with `ccq`'s at the same value, and agreement tells the driver which value came back.
  *Rejected*: `advancec` returning the `cap` half (the `Q` problem: `Advance`'s new index is only
  known after the receive); the driver sending `dlv` or `rof` halves as witnesses of the log
  (in the busy state the driver holds both `dlv` halves, so `run` cannot tie them to its own).
- **Statement shapes kept.** `nodeDriver`/`nodeDriverBusy` keep their parameters (the lower
  bound is inside); the driver's view is a separate token `nodeCfg γ ca cfg`, which
  `RestartNode` hands out and `Advance` frames; the static mode never moves it.

## Stage N: the conf-change bytes a cluster admits (`RaftNames.reCCOk`)

**2026-10-15 · accepted**

- **Why.** B3's decoder (`CCDec`) is a pure function of an entry (and its prefix); an entry's
  data is a `GoSlice`, whose bytes are in the heap, recorded only in the ghost map of proposed
  slices (`reSl`), which grows after allocation. So no decoder fixed at allocation can be what an
  application's `Unmarshal` computes (`decOfData`'s `data : GoSlice → List w8` cannot be
  chosen). A client applying conf entries by decoding them must instead know which bytes a
  conf-change entry can carry: `RaftNames.reCCOk ty bs`, fixed at allocation, recorded with each
  conf entry's data (`entDataIs`), asked of each change proposed (`CCAllowed`). A client that
  admits one change `op` (the register: removing replica 3) then uses the constant decoder
  `ccDecOf op` and proves that what it decoded is `op`.
- *Rejected*: a register-only invariant over the proposed conf changes (raft's ghost state does
  not record who proposed an entry, and any holder of `isNode` may propose any change); not
  decoding in Go (the apply loop passing a fixed change for every conf entry: not idiomatic, and
  wrong as Go code); a ghost decoder (B5's model and every `cfgFold` are pure).
- **Cost.** One field, one conjunct in `entDataIs`'s conf-entry case, one premise of the two
  `ProposeConfChange` specs; static clusters admit everything.

## Stage N: the register removes a voter (not adds a learner)

**2026-10-15 · accepted**

- **The change** is `RemoveNode 3` from {1, 2, 3}: a simple change of the voters (quorums
  shrink to {1, 2}; a removed leader steps down, `StepDownOnRemoval`), no joint consensus, no new
  node (so no node outside the initial voters and no `MsgSnap`, both out of scope). Removing it
  again is nothing, so the configuration is `c0` or `c1` whatever number of conf entries is
  committed. *Rejected*: adding a learner (simpler model lemmas exist, but the voters do not
  change and the learner node would not exist).
- **`Main` proposes once, and no operation waits after it** (raft may drop the proposal;
  `do`/`Read` do not retry a request dropped by a leader that steps down, as during a
  transfer). The transfers that end `Main` go to replica 2. `TestRemoveMember` (unverified)
  retries the proposal, waits for a leader of the remaining voters, and checks the operations.

## Stage S: a snapshot's `ConfState` recorded by the storage and the log; the certificate's carrier deferred

**2026-10-15 · accepted (partial)**

- **The storage records the lists, the log the certified snapshots it may send.**
  `StorState.scs`/`sal` (the storage returns exactly what `CreateSnapshot`/`ApplySnapshot`
  stored) and `LogState.ksn` (the storage's snapshot and every restored one). Raft keeps
  `raftLog.snapshot`'s result in `ksn` as an invariant of `ownRaftLog` (`Hsksn`, `pendKsn`) rather
  than as a fact of each call, so that the outbox (later) can name it. The pending snapshot's
  membership lives in `ownUnstable` too (`UnstableSt.ksn`): the `unstable` methods return an
  existential struct value, so a pointer-keyed fact held beside the log would be lost at each call.
- **The certificate `raftSnapCert` is stated on the ghost records**, as `GMode.SnapOk`'s dynamic
  clause is (any recorded prefix ending at the snapshot's id), plus `SnapScope`'s facts and the
  static clause, so one persistent fact serves both modes and the transport premise `SnapScope`.
- **Carrying it to the receiver: the abstract message was extended, then parked.** The first
  version (branch `stage-s-msg-extension`) put the lists in `Msg` and the certificate in
  `isMessage`, with `PState.snaps` and certificates in `ownRaftGhost`: the producer (`sendApps`)
  then gets the certificate from the sender's ghost state, the receiver from the message, and
  `raft.Step` loses two premises. The integration session asked to avoid changing `Msg`,
  `isMessage` and `ownRaftGhost` when a route local to the `RawNode`/node layer exists. One does
  (notes/STATUS.md, stage S, "Left" 1: an outbox invariant on the physical messages, certificates
  in `ownRawNode`, `Ready` handing one out with each `MsgSnap`, the transport carrying it to
  `RawNode.Step`), but it pays off only with `MsgSnap` at `RawNode.Step` (S2), so neither is on the
  branch: the records stay, the carrier waits for S2.

---

## The server's apply: the hook through mvcc, the chain as triples, compaction out of the model

**2026-10-12 · plan, unit 0 implemented** (`server/v3/etcdserver/apply`, ~1180 Go lines: the
applier chain between the apply thread, whose contract `apply.Apply` it is, and the txn
package; units A, 1, 2, 3 append). The plan: close the loop between the apply thread's proof
(the entry's writes in one critical section of the batch lock, the hook first, or none) and the
txn package's (what is written, by the client model), by proving `apply.Apply` over the txn
results and making the server's `applierFor` a definition.

- **Translation** (unit 0). The package with bodies (`metrics.go`'s gauge and `init` names
  only), no Gooseable change: goose promotes the methods of an embedded *interface* field
  (`applierV3Capped{applierV3}`, ...) as `MethodUnfold` wrappers through `MethodResolve
  applierV3.ty` on the field, as it did for mvcc's `txnReadWrite`. The protobuf-go v2 messages
  the package reads or builds are listed by name in `etcdserverpb.toml` (and `membershippb`); a
  listed struct whose field names a type of a package not imported (`AuthRoleGetResponse.Perm`,
  `authpb.Permission`) is emitted with a dangling reference (a goose gap: the import filter is
  not consulted for listed structs), so `authpb` is imported names-only. `lease.Lease` and
  `storage.BackendQuota` become translated structs (their packages import `sync`, `backend`):
  the backend reads `l.ID`, the capped applier embeds a `BackendQuota` value.
- **The apply package does not import the server's translation** (unit 0). The server's
  proofs will import the apply package's (unit 3: `applierFor` a definition), so the apply
  package's `Base` holds the instances of the packages it reaches (moved from the server's
  `BaseApply.lean`, which imports it), and the raftpb vocabulary (`InvRaftpb.lean`) imports it
  instead of `BaseApply`. The shared contracts it needs from the server move to the apply
  package (`waitOk`, now with `IsRegistered`: `apply/Wait.lean`); `pbutil.MustUnmarshalMessage`'s
  spec is stated over the message packages' assumptions, not the server's.
- **The request is decoded, not encoded** (unit 0; the plan said `irrEncode : IRRModel → List
  w8`, as mvcc's `kvEncode`). `irrDecode : List w8 → Option IRRModel` (opaque), and the decoder's
  axiom takes `irrDecode bs = some rq`. *Why:* protobuf encodings are not canonical and the
  model forgets the contents of the requests the package passes on unread (the auth requests:
  presence only), so "the entry's data is `irrEncode rq` for some `rq`" fails of real entries,
  where "it decodes to some `rq`" does not; a decoder is a function, so no injectivity is
  assumed. The KV requests are the txn package's models (`OpFull`, `TxnModel`), so the apply
  package's statements are in the client model's terms; `dispatchKind` is the first set field in
  `dispatch`'s order (no "exactly one" premise).
- **The components as contracts** (unit 0, `Contracts.lean`). Every names-only component the
  package calls through an interface (the auth store, the lessor, the quota, the raft status,
  the snapshot server, the consistent indexer, the wait) or a names-only struct pointer with
  state (the alarm store, the cluster) is a persistent predicate of triples, the trust boundary;
  every backend write among them has the hook's shape `csContract P f Pre Q Post` (`Pre`, the
  hook's triple `{P ∗ Pre} f() {Q}`, the write `Q ={⊤}=∗ P ∗ Post`; the writer returns `Post ∨
  Pre`). The lessor's `Revoke` deletes its keys through the store's writer: at the sole writer of
  `log` it returns the sole writer of `log` with deletions committed. Pure names-only helpers
  (semver, `types.ID.String`, `AlarmType.String`, zap, the txn package's loggers, the gauge's
  `WithLabelValues`, `context.WithValue`, the quota's constructor and `Cost`) are axioms. The
  gauge's `Inc`/`Dec` are the returned gauge's contract (mvcc's `gaugeSpec`), not axioms.
  *Rejected:* the alarm store's methods as axioms (its writes need the hook's `P f`, which an
  axiom would have to quantify over).
- **semver** (unit 0): `MustParse` returns a version or panics (`PanicV`), by an opaque
  `semverValid` of the string: the premise of a `ClusterVersionSet` entry, as Perennial's panics
  are modelled (`Logger.Panic`).
- **The context** (unit 0). The backend applier calls the txn package at `context.TODO()`, whose
  `Done()` is `nil` and which Perennial's `isContext` does not describe; `EnsureTrace(TODO())` is
  `WithValue(TODO(), ...)`, whose `Done` is its parent's. The plan's "`txnCtx` in the four entry
  points' premise, the proofs change little" did not hold as stated: the context flows from
  `Txn`/`Put`/... into `txn`, `executeTxn`, `put`, `executeRange`, `deleteRange` and
  `traceutil.Get`, each taking an `isContext`. Done instead: `doneNil ctx` (a context whose
  `Done()` returns `nil`) and `txnCtx ctx cd := doneNil ctx ∨ isContext ctx cd` (mvcc's
  `TxnRange.lean`), the premise of every txn function that takes a context (a rename in their
  specs, `Results.lean` too) and of the `EnsureTrace`/`Get` axioms (which return a `txnCtx`);
  `rangeCtx true` takes `doneNil` in place of `TODO()`'s value; the two range reads choose their
  `todo` from it (`txnCtx_rangeCtx`: never canceled if `doneNil`). At `TODO()`, `txnCtx_todo`;
  `Txn`'s `neverDone` with the descriptor `neverCd`. *Rejected:* an `isContext` for
  `WithValue(TODO())` in the axiom (Perennial's `isContext` needs a `Done` channel: unsound).
- **Compaction is out of the model** (plan): mvcc's `isStore` fixes `compactMainRev = -1`;
  `applierV3backend.Compaction` gets no spec and `dispatch`'s spec will take `dispatchKind rq ≠
  compaction` (unit 2).
- **The chain** (unit 0, `Chain.lean`, skeleton): `Chain` (`baseChain = auth (quota backend)`,
  `alarmChain` by the alarms), the outcome relation `chainStep B c rq log o` over the backend's
  relation `B` (corrupt, capped, auth reject before a write; quota may report `ErrNoSpace` after
  one), and `applierSpec c a`, the layers' structs and inner appliers; the layers' method
  triples are unit 1's.
- **Links: reuse** (unit 0, `gen-link.py`). The trust report runs Lean once per group of part
  roots; the apply package's roots reach `EtcdDeps` (raftpb, through `MustUnmarshalMessage`'s
  spec) and import mvcc's `Link.lean` (through the txn package's), so they meet the server's
  `Link.lean`, which defined `binary.bigEndian.wp_PutUint64`/`wp_Uint64` and `zap.wp_Error` as
  mvcc's does. Rule: a callee whose result a Link this one imports already defines under the
  same full name is imported, not redefined; the Links searched are the `@` callees' and a
  mode's declared ones (`REUSES`: the server's imports mvcc's). The apply package's results are
  in a namespace of their own (`apply`), as the txn package's.

- **The layers' triples** (unit 1, `Chain.lean`). `applierSpec E c a` is not recursive in its
  shape: it is the method triples of `a` as the chain `c` runs them (`applierTriples`), stated
  with `chainStep backendStep c` and `chainRes c`, which recurse on `c`; each layer's methods are
  `Spec/`+`Proof/` files over `applierSpec E c inner`, and the constructors prove the triples
  (promoted methods through the inner's). The environment `E : AEnv` (store, ghost names, the
  batch lock's `P f`) is a record. Every method takes and returns the apply thread's
  `kvOwn E log` (reader slots, sole writer, leases known: `newHeader`'s `store.Rev` needs the
  first two), so `dispatch` (unit 2) threads one resource. The KV methods and `LeaseRevoke` are
  stated for the request `rq` `dispatch` passes on (`dispatchKind rq`), so that unit 2's outcome
  is `chainStep`'s; their answers keep the txn package's response predicates at the exact model
  values. A writing method returns `Post ∨ Pre`, not "`Post` iff applied": a put whose ignore
  flag finds no key took the lock (`Post`) and wrote nothing; a read-only `Txn` is applied with
  `Pre`.
- **The auth layer's mutex** (unit 1): `aa.mu`'s resource is `authInfo`; `Apply` locks it and
  hands `authInfo` to the `applyFunc` through `chainRes`. *Rejected:* `authInfo` thread-owned
  with a trivial lock resource (`Apply` and unit 2's uber-applier would carry `chainRes`).
- **A lease checkpoint request with one checkpoint** (unit 1): the lessor persists each
  checkpoint in its own critical section, which the critical-section contract cannot express
  (`issues/etcd-apply-lease-checkpoint-sections.md`): a premise, not a weaker contract.
- **`auth.AuthStore` translated** (unit 1): `auth.toml` imports the packages its methods'
  signatures name; it was an axiomatized type whose generated instances are `sorry`.

- **The uber-applier: persistent and thread-owned halves** (unit 2, `InvUber.lean`). `uberIs E p
  opts` (fields written once, the options' contracts, the base chain) is persistent;
  `uberOwn E p c` (the `applyV3` field and its chain) is the apply thread's, since
  `restoreAlarms` rewrites it, also from inside the chain's `Apply` (an alarm request: `dispatch`
  → `Alarm` → `restoreAlarms`), which is why `dispatch`'s `A`/`B` carry `applyV3 ↦` and the
  chain's resources `chainRes c a` stay those of the applier `Apply` was called on. The chain
  after `restoreAlarms` is existential (`alarmChain ns cr`: the alarm store's `Get` is any
  slice). `applierFor ua E` takes the environment, not `P f`: the persistent and owned halves
  must name the same store, which `P f` do not pin.
- **`apply.Apply.spec` strengthened; the server keeps the old contract as an axiom until unit 3**
  (unit 2). The new precondition's `rqOk x.log rq` depends on the log the earlier entries wrote,
  so the server's loop can supply it only with the fold (`applyEntries_model`, unit 3); a
  threaded `applyKV` with no claim about the next state cannot. The old statement is kept as
  `apply.Apply_server.spec` with its axiom (renamed from `apply.Apply.wp_proof`; not derivable
  from the new one, which has more premises), the server's `applierFor` axiom unchanged.
  *Rejected:* deriving the old statement (impossible); putting `applyKV` in an invariant (the
  call is not atomic).
- **The cluster writes only with `shouldApplyV3`** (unit 2, `Contracts.lean` `cPre`/`cPost`): so
  that `apply.Apply` without `v3`, which gets no hook triple from the server, can call the
  cluster's methods and still return `Pre`. A strictly stronger restatement of the unit 1
  triple (membership's `RaftCluster` saves to the backend `if shouldApplyV3`).
- **`errors.Is`** (unit 2): the server's axiom (any error, any target) restated under the
  `errors` package's assumptions and shared with `dispatch`, since Perennial's `errors.wp_Is`
  (at `e4e126e46`) needs an error tree the components' errors do not have. On `lean` the
  `errors.Is` spec now takes the tree (Perennial `e6ec34885`): the merge states `applyErrIs` of
  the chain's and the contracts' errors (STATUS, unit 2, "Gap for the merge").
- **The applier's errors, as `errors.Is` sees them** (the merge of unit 2 into `lean`): `lean`'s
  `errors.Is` proof kept (under the `errors` package's assumptions, unit 2's generalization);
  `applyErrIs` moved from the server's `InvApplier.lean` to the apply package's `Base.lean`
  (with `errLeaf`, `errVarLeaf`, `applyErrIs_nil`/`_leaf`), so that `apply.resultErrOk` is the
  server's `resultOk` and the apply package does not import the server. Where each error comes
  from: the contracts assert it of the auth store's and the lessor's errors (a trust-boundary
  fact, as `clientErrIs` for the client); the error variables the chain returns or compares
  with (`ErrCorrupt`, `ErrNoSpace`, `ErrKeyNotFound`, `ErrLeaseNotFound`, `ErrFutureRev`,
  `ErrCompacted`) are `errors.New` errors by the apply package's facts (`applyErrVars` in
  `applyInit`, not in their packages' facts, which their proofs destructure by position); the
  triples of the methods that leave the log carry `applyErrIs err`; a KV method's answer names
  its error and `DispatchLemmas` derives `applyErrIs` from it (`putOutcomeIs_errIs`, ...,
  `keep_errIs`). The range read's context error, which no tree describes (mvcc's
  `fmt.Errorf("%w", ctx.Err())`), is excluded rather than described: `txn.Range`/`DeleteRange`
  take `nd` (a context never done, as `executeRange`/`deleteRange` already did) and the backend
  calls them at `context.TODO()` (`neverCd`). *Rejected:* a tree for the context error (would
  need `fmt.Errorf`'s `%w` wrapper's tree and the context errors' types, for a branch that does
  not run); `applyErrIs` in `kvPost` (every KV method's proof would change, for a fact its
  answer already implies).

- **The server bridge: `E` a parameter of `isServer`** (unit 3). The applier's environment `E`
  (store, ghost names, `P`, `f`) must be the same in the persistent `apply.applierFor v.ua E`
  (in `isServer`'s fields) and in the thread's `apply.applyKV E ua x`, and nothing in the heap
  pins it (the hook `v.hook` is a value, not a field), so `isServer s γ ci TM E` takes it, its
  fields pin `E.P = batchLockInv γ TM ∧ E.f = v.hook` by equations (a proof rewrites them where it
  hands the hook's triple to `apply.Apply` or `applyConfChange`). The thread's resource is
  `srvApplyKV s E x := ∃ ua, srvUberApplyAddr s ↦□ ua ∗ apply.applyKV E ua x`: the `ua` is the
  field's, which `isServer` hides behind its `∃ v`; the two `↦□` agree. `applyConfChange`'s
  contract (an axiom) named the old `applierFor ua P f` too: restated at `apply.applierFor ua E`
  (and `HasLC.hasLC`, where `apply.applierFor` lives). *Rejected:* `E` existential in
  `isServer` (the thread's `applyKV` could not name it); `E` built from parameters `(s, γ)` and
  the hook (the hook is not in the heap, so no agreement).
- **The fold as a relation** (unit 3). `apply.Apply`'s post is a relation (`applyStep`: the
  auth store's, the quota's, the alarm store's answers are any), so what a batch does is a
  relation too: `entryStep m v3 x x' out` (no data: `x' = x`, `skipped`; else the decoded
  request's `applyStep`), `batchStep c m` (a normal entry by `entryStep` with `v3` iff above the
  consistent index `c` the batch starts at; a conf change leaves the KV) and `entriesStep c ms`
  their composition. `v3` is a function of `c` and the entry's index: in `apply`'s loop the
  entry's test is against the current `ci`, which is the starting one or an earlier entry of
  the batch (below this one), so `index > ci` iff `index > c`. `applyEntries` hands `apply` the
  entries above the applied index, `unapplied ai ms` (a filter; `unapplied_eq_drop` is the code's
  offset).
- **`entriesOk` over every run** (unit 3). `rqOk x.log rq` depends on the log the earlier
  entries committed, which the relation does not determine, so the premise cannot be "the
  entry is fine at the state the batch reaches": `entriesOk c (m :: ms) x := (normal → entryOk x
  m) ∧ ∀ x1, batchStep c m x x1 → entriesOk c ms x1`, i.e. at every state any run reaches the
  entry in (the server does not choose the run). It is also asked of replayed entries (`v3 =
  false`), at the state they meet: `apply.Apply.spec`'s premise does not depend on `v3`, so a
  replayed entry's request must satisfy the txn package's premises (`rqOk`) although it is not
  run (`apply_no_v3_no_write`): stronger than the code needs; weakening it is a change to
  `apply.Apply.spec` (`rqOk` only if `v3`), left open. *Rejected:* `entryOk` in
  `entriesFrom` (pure in `ms`, it cannot see the state); a premise on all reachable states of the
  whole KV (stronger than needed, and not a property of the batch).

## mvcc: the batch lock runs the hook

**2026-10-12 · adopted** (the server's apply package, unit A; plan: the apply package's
"The hook through mvcc"; `notes/STATUS.md`, "Unit A: the hook through mvcc")

The real backend's `batchTx.LockInsideApply` runs the server's `txPostLockInsideApplyHook`
under the lock (`backend/batch_tx.go`). The server's protocol (`apply.Apply.spec`,
`InvApplier.lean`: `hook_set_au` is the hook's triple, `writes_done` the caller's update)
assumes the applier's writes happen in one critical section that runs the hook first; mvcc's
backend contract had `LockInsideApply : {True} … {Locked [] ∗ W}`, no hook, so the server
could not be proved of the real write path. The contract now carries it, in the shape of
`apply.Apply.spec`:

- **The backend** (`batchTxSpec bt View W Locked P f`, `isBatchTx … P f`, `isKeyBackend b View
  W P f`): the lock's invariant is `W ∗ P` (`W` the store's resource, from `NewStore`'s first
  `Unlock`; `P` the backend's from its creation); `LockInsideApply : ∀ Pre Q, {Pre ∗ □ {P ∗ Pre}
  f() {Q}} … {Locked [] ∗ W ∗ Q}` (the hook `f : val`, called `App (Val f) (Val #())`, runs on
  the caller's `Pre` under the lock); both `Unlock` triples take `P` back;
  `LockOutsideApply : {True} … {Locked [] ∗ P}` (no hook: the hook is nil when `NewStore` runs,
  the server sets it later, `server.go:412`; `P` is handed out so that `NewStore`'s `Unlock` can
  return it).
- **The store records `P f`**: `StoreNames` gains `hook` (a saved proposition of `P`,
  discarded) and `hookFn` (a `dghostVar` of `f`, discarded; `val` is countable); `hookIs γ P f`
  (persistent) is both. `isStore s γ` holds `∃ P f, hookIs γ P f ∗ isKeyBackend b … P f`, so its
  arity is unchanged and no spec that ignores the hook changed. `NewStore` takes the backend's
  contract at any `P f` and returns `hookIs γ P f`. Two views agree (`hookIs_agree`: `f = f'`,
  `▷ (P ≡ P')`); `hookIs_agree_lc` spends a later credit for `□ (P -∗ P') ∗ □ (P' -∗ P)` now
  (`store.Write` and `storeTxnWrite.End` take one from their first pure steps).
- **The write path**: `store.Write` takes `hookIs γ P f ∗ Pre ∗ □ {P ∗ Pre} f() {Q}` and returns
  `Q` beside `isTxnWrite`; `storeTxnWrite.End` takes `hookIs γ P f ∗ P`; `metricsTxnWrite.End`
  takes `txnEndPre γ kind` (`True` for a read, `∃ P f, hookIs γ P f ∗ P` for a write;
  `txnEndPre_write`). `csContract P f Pre Q Post := Pre ∗ □ {P ∗ Pre} f() {Q} ∗ (Q ={⊤}=∗ P ∗
  Post)` (the three conjuncts of `apply.Apply.spec`) is what a writing call takes:
  `writeView.Put`/`DeleteRange` and txn's `Put`/`DeleteRange`/`Txn` return `Post` iff they opened a
  write transaction, else `Pre` (`Put`'s lease check, `Txn`'s failed check or read-only request).
  The caller's update is applied right after `Write` (ghost: the writes are the caller's model,
  `writes_done`), before `End`.
- **The no-hook instance**: `P := True`, `f` a no-op, `Q = Post = Pre` (`csContract_noHook`).
  The results (mvcc's, txn's sole-writer corollaries) are stated at any `P f Pre Q Post`.

*Rejected:* `P f` as parameters of `isStore` (some 40 spec files would change for nothing);
the hook's effect folded into `W` (the hook needs the caller's `Pre`, which is per call: it has
to be in the lock's triple). *Considered:* `Unlock` taking `▷ P` (Perennial's `Mutex.Unlock`
convention), which would spare `End` its credit; kept `P`, the form `apply.Apply.spec` uses.

## The request path: raft as a contract, the wait registry, the checks as the premises' discharge

**2026-10-12 · plan, units 0 and 2 implemented** (the gRPC KV handlers `server/etcdserver/api/v3rpc/
key.go` → `EtcdServer.Range`/`Put`/`DeleteRange`/`Txn` (`v3_server.go`) → the proposal and its
wait → the apply loop; units 1 (the checks, the handlers), 2 (the wait, the ids, the proposal),
3 (the read side), 4 (the loops, optional) append). Goal: a client request's response is the
apply package's outcome of that request at the log it met, with mvcc's certificate, and the
gRPC checks discharge the txn package's request premises.

- **Raft as a contract, not the verified raft** (unit 0). The server's raft is etcd's
  dependency (raft v3.7.0, protobuf-go v2 raftpb, `EtcdDeps/`, names-only); the verified raft
  (`Code/go_etcd_io/raft/`) is the fork 118 commits earlier, and both translations define
  `Perennial.go_etcd_io.raft.v3.*`, so no module imports both. `raftNode.Propose` (promoted from
  `raft.Node` through `raftNodeConfig`) gets, as a contract of the server's `Node` field
  (`raftPropose`, `InvRequest.lean`), exactly the statement the verified `node.Propose` proves
  for the register (`propArg`/`propRes`/`propAu` over `cLog`), restated over the server's own
  ghost names (`ServerRaftNames`; a context `mvcc.txnCtx` in place of `Background`); its apply
  side (`batchCommitted`: a batch's client data are the committed client log's next entries,
  each deposited and claimed by its id) is what unit 4 states the loops with. Discharging it is
  retargeting the verified raft to v3.7 (`notes/STATUS.md`, "Retargeting raft to upstream").
  *Rejected:* retargeting first (it blocks the path on a large mechanical port; the path's own
  content, the checks, the wait protocol, the handoff, does not depend on it).
- **The wait registry: a handoff per registration, a registration condition** (unit 0). The
  wait's contract (`isWait w γi R`) is generic in the registration condition `R : id →
  expectation → IProp`: `Register(id)` takes the id's slot (`idSlot`, from the generator) and
  `□ R id Ψ`, returns a handoff channel (`cache/v3/Handoff.lean`: buffer 1, sent once, closed)
  carrying `Ψ x`, or `nil` with the proposer's consumer token (its own `Trigger(id, nil)` after a
  timeout); `Trigger(id, x)` from anyone else takes `∀ Ψ, R id Ψ -∗ Ψ x`. The server's condition
  (`reqWaitR`): `Ψ = resultΨ E rq` for the request `rq` the id was claimed for (`idClaim γi id
  d`, `irrDecode d = some rq`). The apply thread learns the registered request through the claim
  agreement: the entry's data and the registration's data were claimed for the same id.
  *Rejected:* a registry of saved predicates the apply thread looks up (it would still need the
  claim to identify the request); `Ψ` in the wait's own state (the wait package's proof would
  name the server's model).
- **Ids: credits per process, claims per cluster** (unit 0). `idGen` hands `2^48 - 1` credits
  (`Auth Nat`), each `Next` an `idFresh` id (unclaimed, with its wait slot). Claims are one
  cluster-wide map: that other members' entries never claim an id this member issued is the
  premise that member ids differ in their low 16 bits (`issues/etcd-request-id-member-prefix.md`),
  part of the raft contract's apply side.
- **The checks as pure functions of what they read** (unit 0, `v3rpc/Defs.lean`). A
  `RequestOp` as the checks see it is `ReqOp` (the txn package's `OpFull` for range, put,
  delete: a `TxnOp` forgets the put's value and lease, which `checkPutRequest` reads), and each
  check is a function to its first error (`CheckErr`, the `rpctypes` variable), so unit 1's specs
  are "returns `CheckErr.var` of the function's value, or `nil`". `checkIntervals` is the code's
  algorithm over the `adt` model (`ivCheck`), not the intended predicate: a `"\x00"` range end is
  the empty interval, and a nested transaction's puts are not checked against later siblings'
  deletes (`issues/etcd-txn-check-intervals-sibling.md`); what it gives the txn package
  (`intervalsOkCheckStmt`) is stated under both exclusions. The range end is read from the
  denotation (`rangeEndOf`): equal to the request's bytes off the wire.
- **`proto.Marshal` of a raft request, up to the model** (unit 0). A second axiom on
  `proto.Marshal` (`proto.MarshalIRR`, beside mvcc's `KeyValue` one: mvcc must not import the
  apply package's model): an error, or bytes that decode (`irrDecode`) to a request with the same
  id, header and kind, and to the request itself when no range end is `[0]` (`irrWireOf`): the
  model denotes both `"\x00"` and an empty non-nil slice by `[0]`, and the wire turns the latter
  into `nil`.
- **Trust boundary, unit 0**: 22 axioms (otel's tracer, spans and attributes; prometheus'
  histogram; `strconv`, `time`'s float and comparison helpers; traceutil's bookkeeping; the txn
  package's read-only loggers; the transport queries; the request timeout; the cluster id;
  `MarshalIRR`), each a function with no effect the model sees, or the encoding. The components
  reached through the server's fields (the raft node, the wait, the generator, the read loop, the
  auth store's request side, the feature gate) are contracts (`InvRequest.lean`), established by
  the server's construction (not translated) or by units 2 and 4. `trace.isSpan` gains
  `AddEvent`/`RecordError`; `context.WithValue` takes `traceutil.StartTimeKey` and returns a
  context of the parent's descriptor.
- **The server as the handlers see it: a contract over parameters** (unit 1, `v3rpc/InvKV.lean`).
  The handlers call `*EtcdServer`'s `Range`/`Put`/`DeleteRange`/`Txn` through the `RaftKV`
  interface, and the header calls `KV().Rev()`, `Cluster().ID()`, `MemberID`, `Term`, `Leader`:
  all nine are triples of one persistent predicate `raftKV s A` (in `kvServerIs`, the handlers'
  precondition), not callees in the link, so the handlers are proved before units 2 and 3 prove
  `EtcdServer`'s functions, which then prove `raftKV s A` for their instance of the parameters
  `A : KVAns`: what a call needs (`A.call ctx`: the context, the per-request credits), what a
  successful answer holds (`A.ok q resp h r`), what an error is (`A.err q err`), what `Rev()`
  needs (`A.revR`). The fixed part is what the handlers need: a request that passed its check,
  and either a non-nil response whose header's four id fields are owned (`hdrW`: `fill` writes
  them) and whose revision is read-only and not `0`, or owned (`hdrRevIn`), or a `nil` response
  and an error `togRPCError` can take (`srvErrIs`). *Rejected:* `EtcdServer`'s specs as the
  handlers' callees (unit 2's files, written in parallel; the header's five getters would have
  needed the server's fields, which the apply thread's `isServer` does not give other
  goroutines).
- **Header ownership is a requirement on the apply side** (unit 1). `header.fill` writes the
  response header's `ClusterId`, `MemberId`, `RaftTerm`, `LeaderId`: the response the apply
  thread built must reach the handler with those fields owned. The txn package's response
  predicates (`putResponseIs`, ...) keep only the revision, read-only, and drop the other
  header fields: unit 2 (the wait's handoff) must keep them (`hdrW`) from the response's
  construction (txn's `Put`, ..., the applier's `newHeader`) to the proposer, a change to the
  txn and apply packages' response predicates.
- **Two names-only interfaces translated** (unit 1): `etcdserver/api.Cluster` (its methods name
  `types`, `membership`, `semver`: `api.toml` imports them) and `etcdserverpb.KVServer` (with
  `context` imported, which translates the package's other service interfaces too): a method
  call on, or a conversion to, an interface whose underlying type is an axiom does not reduce.
  *Rejected:* an axiom about `Cluster.underlying`.
- **`errors.Is` at `context.DeadlineExceeded`, an axiom** (unit 1, `Spec/errors/
  IsDeadlineExceeded.lean`). Perennial's `errors.wp_Is` takes pointer targets (its tree walk
  compares pointers; its `reflectlite` model says only that pointers are comparable);
  `DeadlineExceeded` holds `deadlineExceededError{}`, an empty struct, for which Go's `==`
  never panics. The axiom is `errors.Is` at the value that variable holds, for an `err` in an
  error tree. `context.Canceled` (an `errors.New` error) needs only that it is a pointer error,
  which Perennial's `context` package fact does not keep: a v3rpc package fact
  (`ctxCanceledPtr`). `parseProposeCtxErr` (unit 2) needs the same two.
- **`checkIntervals` over the interval tree with duplicate intervals** (unit 1). A transaction
  deleting the same range twice inserts the same interval twice (`Insert` adds a second node,
  after the equal ones): the adt contract gains `intervalTree.InsertAny` (`Insert` without its
  newness premise; pending, as the rest of the contract, for the mvcc session's tree proof). The
  map's keys and the tree's intervals are stated as sets (the map ranges in any order; `Union`
  inserts in `Visit`'s order). The deletes' range ends are as off the wire (`reqOpsWire`: `nil`
  or not empty; unit 0's premise), since `checkIntervals` reads an empty non-`nil` range end as
  a point and mvcc as no upper bound.
- **What `checkIntervals` gives needs the key check too** (unit 1, `CheckNodup.lean`). Unit 0's
  `intervalsOkCheckStmt` lacked it and is false (`intervalsOkNoKeysStmt_false`): the affine order
  reads `""` as +∞, so a put and a delete of the empty key pass `checkIntervals`. The statement
  now takes `opsCheck n ops = none`; `kvServer.Txn` runs `checkTxnRequest` first, so nothing
  reachable is lost.

**2026-10-12 · unit 2 implemented** (the wait, the ids, the proposal path, the apply side):

- **The handoff channel, with the registration's record** (unit 2). `Register(id)` returns, with
  the handoff channel, a persistent record `waitRegd γw id t` (a ghost map of every id ever
  registered to the channel's consumer-token name `t`), and `Trigger(id, nil)` takes the
  proposer's consumer token with that record: the shard's entry for `id` then names the same
  token, so the `nil` carries the proposer's own token (a receive of it would meet the token the
  proposer kept: impossible). The channel is never closed without a send (`Wc = False`), so the
  proposer's receive yields a value satisfying `Ψ`. *Rejected:* unit 0's `Trigger` premise
  `∃ γh, x = nil ∗ handoffConsumer γh false` (nothing ties `γh` to the channel registered
  under `id`); a registration token kept in the wait's state per id (the slot is consumed by
  `Register`, and the record must survive the deletion).
- **The id claim mints raft's fresh token** (unit 2, `srvMintInv`). `Propose` with `fresh` wants
  a token nobody had for the data; the data decode to a request carrying the fresh id, so a
  mint invariant (raft's fresh-token authority, every token of data claimed under their id)
  lets the proposer mint it when it claims the id for the data (`srv_claim_mint`). The update
  deposited is the trivial one (`Q = True`, the client log's other half in `srvCLogInv`): the
  server does not linearize at raft's commit, its result comes through the wait.
  *Rejected:* `Q` carrying the result (the apply thread, not raft's commit, computes it).
- **`waitOk` stays in the apply package, as `IsRegistered` with a reader's resource**
  (unit 2). `pkg/wait`'s `IsRegistered` read-locks a shard's `RWMutex`, which needs a reader slot
  (Perennial bounds readers), so `waitOk w RD` is `{RD} IsRegistered(id) {RD}` and
  `apply.Apply` threads `RD`; the apply thread's `srvApplyKV` holds `waitOk w RD ∗ RD` (from
  `isWait_waitOk`), and the server's fields hold `waitInv` for `Trigger`. *Rejected:* `waitInv ⊢
  waitOk` with `waitOk`'s `{True} Trigger {True}` (not implied: `Trigger` needs `waitTrig`);
  `waitOk` as a parameter predicate of the apply package (more churn for the same content).
- **Typed facts for the trust boundary, not new contracts** (unit 2): the context's `Value` at
  `StartTimeKey` and `errors.Is` at the context errors are axioms (Perennial specifies neither);
  `time.Duration.Seconds` returns a word, `pbutil`'s conf-change id is `ccIdOf bs`,
  `WithValue`/`Tracer.Start` keep `isContext` (restatements). Three translations completed
  (raft's `Node` and `None`, rafthttp's `Transporter`, otel's `Tracer`: imports and a constant
  only) rather than axiomatizing loads of axiomatized types.

**2026-10-12 · unit 3a implemented** (the handoff gaps; `Put`/`DeleteRange` end to end):

- **The header's id fields: a separate, non-persistent conjunct** (unit 3a). The txn package
  allocates the response header (`&pb.ResponseHeader{}` in `put`/`deleteRange`); its four id
  fields go owned through `txn.respHdrOwn hf` beside the response's read-only predicate
  (`putResponseIs`, unchanged and persistent), then the apply package's `appliedHdr log hf` (the
  four fields, and the log at least `NewStore`'s two revisions with room for the write, so the
  response's revision is not `0`: `soleWriter` now keeps `2 ≤ log.length`), wrapped with the
  persistent outcome as `putAnswerIs`/`deleteAnswerIs` (the chain's triples, `dispatchAnswer`),
  through the wait's handoff (`resultΨ`, `appliedOk`: resources, nothing kept them under `□`), to
  `EtcdServer.Put`/`DeleteRange`'s success. *Rejected:* the fields inside `putOutcomeIs` (it is
  persistent and named by many layers; the handler's `A.ok` keeps it while `hdrW` takes the
  fields); `Txn` and `Range` (their headers are `newTxnResp`'s and `executeRange`'s: unit 3b).
- **The error facts in `applyErrIs`** (unit 3a). `applyErrIs err` gains `errKeyMsg err`: `nil`,
  or a safe key of `togRPCError`'s map (`SafeMapKey`) whose `Error()` returns (`errMsgOk`). Every
  producer discharges it: `nil`; the `errors.New` variables (`errVarLeaf` keeps the message
  triple, `errors.wp_New`'s; a pointer error is a safe key, `safeMapKey_ptrErr`); the contracts'
  errors (the auth store's, the lessor's: premises, now stronger). So `srvErrIs` is `applyErrIs`
  of a non-nil error (`srvErrIs_of_applyErrIs`). The proposal's errors needed it too, which the
  plan missed: the auth store's `AuthInfoFromCtx` and raft's `Propose` contracts return
  `applyErrIs` errors, `proto.MarshalIRR`'s error is one (protobuf-go's pointer errors), and
  `parseProposeCtxErr` returns only its variables: its `default` branch returns `cctx.Err()`,
  an error Perennial's `isContext` says only "typed" of, so **a new trust-boundary axiom**
  `context.ErrDone` (a done context's `Err()` is `Canceled` or `DeadlineExceeded`, Go's
  documented contract of `Context.Err`) and `errors.IsCtxErr` strengthened (`true` when the error
  is the target, Go's `Is` compares first) make the branch unreachable. *Rejected:* a conjunct
  beside `applyErrIs` on the server's path (every apply-side producer already had the facts; one
  predicate is simpler); a premise that every typed error is a safe key (false: an error of an
  uncomparable type).
- **`raftKV` per method; the server's parameters** (unit 3a, `ServerKV.lean`). `raftKV s A` is
  now `kvRangeOk ∗ kvPutOk ∗ kvDeleteOk ∗ kvTxnOk ∗ kvGetOk` (the handlers take their conjunct);
  `srvKVAns s E ρ A0` instantiates `A` for the write path (`srvCall`: the context, one id credit,
  a `leadTimeMu` reader slot, given back in `putAppliedOk`/`putErrOk`) and defers `Range`, `Txn`,
  `revR` to `A0` (3b's); `raftKV_of_server` proves the `Put`/`DeleteRange` conjuncts from the
  linked `EtcdServer.Put`/`DeleteRange` with the other three as premises. `KV().Rev()` stays in
  `kvGetOk` (3b): `header.fill` never calls it on these answers (their revision is not `0`).

**2026-10-12 · unit 3b implemented** (the read side and `Txn`; the server's contract discharged):

- **`txn.Txn`: two triples by caller** (unit 3b, `Spec/.../txn/Txn.lean`). The apply thread's
  (`specSole`: the sole writer, a never-done context) and the server's read-only transactions'
  (`specRead`: a reader's slots and tokens, a certificate, any context), `Txn.spec := specSole ∧
  specRead`, proved together; `executeTxn`/`txn.txn` take a never-done flag (`false` only for
  read-only runs) and a context-error outcome. *Rejected:* a premise that the request's context is
  never done (false of gRPC contexts); a separate spec file per caller (one Hoare triple per Go
  function: the conjunction is one spec).
- **The context error through Perennial's `fmt.Errorf`** (unit 3b). Perennial models
  `fmt.Errorf` as `errors.New(format)` (no `%w`): the read side's context error is an
  `*errors.errorString` leaf (`mvcc.errorfIs`, in mvcc's `rangeOutcome` and txn's `rangeResult`),
  and `applyErrIs` of it needs only that `*errorString` has no `Is`/`As`/`Unwrap` (a method-set
  fact, a package-fact premise in `srvErrVars`). *Rejected:* modelling the wrap in etcd-grove (it
  is Perennial's trusted model; the gap is recorded: Go's `togRPCError` maps the wrapped context
  error to `ErrGRPCCanceled`, the model's to `codes.Unknown`, and the handlers' specs say only
  "an error"); a trust-boundary axiom for the error.
- **Request premises in the handlers' contract** (unit 3b, `KVAns.pre`). The server's read-only
  `Txn` is within the txn package's model only for gets at revision `0` whose sort is not cut
  early (`txnInModel`): a pure premise per request, which `A.call ctx` (per context) could not
  carry. *Rejected:* `call` taking the request (a resource per request was not needed).
- **The store stays small, a premise of the readers** (`storeSmall`, unit 3b): the sort's bound
  (`LogSmall`) of every certified log; `txn.Range`'s sort premise is asked of certified logs only.
  The apply thread has the same premise per entry (`rangeOk`, `TxnPre`). *Rejected:* a premise on
  every log (vacuous for sorted reads).
- **`srvKVAns` concrete** (unit 3b): 3a's `A0` replaced by the read side's names (`γr`, `c`); every
  call resource comes back with every answer but a write's id credit; `revR` is the store's reader
  slots (`KV().Rev()` is `store.Rev`), which `fill` never needs on the server's answers.

## The server's raft wrapper: raft.Node as a contract, an SPSC stream to the apply side

**2026-10-12 · plan, carried out the same day** (`server/v3/etcdserver/raft.go`, ~450 Go lines; branch `server-raft`; `STATUS.md`, "etcd's server: the raft wrapper"). Two changes in the proof: the WAL's `Close` succeeds by the contract (else `onStop` panics in the loop's goroutine), and `start` case-splits `islead` rather than joining (the follower's select returns on `stopped`, which no join assertion reaches).
Toward an end-to-end statement (a client driver against a slice of etcd: the raft wrapper, the
apply thread, the applier chain, mvcc), the raft wrapper is the link between raft's `Ready` and
the apply thread, whose `applyEntries` assumes its batch "consecutive from `f0`, with no gap
after the applied index, as raft hands them over". Its proof is what discharges that premise.

- **Translation.** `etcdserver.toml` lists `raftNode`'s methods, `updateCommittedIndex`,
  `raftReadyHandler` and the promoted `raft.Node` methods (`raftNode.Ready`/`Advance`/`Tick`/
  `Stop`, through `raftNodeConfig`; goose emits their `MethodUnfold` wrappers only when listed);
  v3.7's raft gets `IsEmptySnap`, `IsEmptyHardState`, `isHardStateEqual` and `emptyState` (its
  initializer, which was an axiom), `SoftState`, `ReadState`; raftpb gets `Message`, `Snapshot`,
  `SnapshotMetadata`, `HardState` as structs with the getters the wrapper reads.
- **`raft.Node` is a contract shaped like node.go's verified specs** (`InvNode.lean`): `Ready()`
  is a handshake channel whose payload is the node's half of the delivered log `d`, its record,
  and the `Ready`'s data (the committed entries `ce`, with `C (d ++ ce)` for the contract's
  persistent "committed" predicate `C`; the entries to append with their append right; the
  messages, each `M m`; no snapshot and no read states, as node.go guarantees); `Advance()`
  takes the driver's busy token and the append receipt. The v3.7 raft is not the verified one
  (protobuf-go v2, `STATUS.md`, "Retargeting raft to upstream"), so the contract is stated in the
  server's terms (`EntryModel`, the v3.7 types), to be discharged by node.go's specs once raft is
  retargeted. *Rejected:* stating the contract over node.go's own predicates (no module imports
  both raft translations).
- **`applyc` is an SPSC channel** (Perennial's `isSpsc`), and the delivered log after each
  payload is a persistent mono-list `cum` (element `k`: the log forwarded after `k` payloads): the
  payload at position `i` carries `cum[i] = F`, `cum[i+1] = F ++ ce` and the batch's entries
  `ce`. The loop owns the producer half and the mono-list's authority (`cum`'s last is the
  node's delivered log); the apply side owns the consumer half and `cum[|received|]`, so it
  learns the batch extends exactly what it got. *Rejected:* a handshake with a record half (as
  node.go's `rof`): `applyc` has no return path and a handshake's receiver obligation `Q` is
  fixed before the value is known, so the loop could not recover its half.
- **The other components are contracts** (persistent predicates of triples): the WAL
  (`serverstorage.Storage.Save`), the `MemoryStorage`'s `Append` (append right to receipt), the
  transport (`Send` of messages each `M m`, `Stop`), the timeout detector, the ready handler's
  four closures, the gauges and counters, the ticker (its `C` a bag channel or nil, as
  `newRaftNode` makes it when `heartbeat == 0`), `proto.Clone` of a nil `*Snapshot` (a case added
  to its axiom). `notifyc`, `raftAdvancedC`, `msgSnapC`, `stopped` are bag channels of `True`
  payloads (or of `M m` for `msgSnapC`); `done` a broadcast channel. `latestTickTs` is under
  `tickMu` (Perennial's guarded `RWMutex`: `tick` writes through the persistent guard).
- **Out of the model, by the contract**: snapshots (`rd.Snapshot` nil: the `SaveSnap`/`Sync`/
  `ApplySnapshot`/`Release` branch is dead), read states (the linearizable-read path: nil, so the
  `readStateC` branch is dead; needed later for linearizable `Range`). Conf changes are not
  excluded: the loop's scan and the follower's second `notifyc` send are verified as written.
- **Ticks**: node.go's `Tick` spends a term-budget credit; the wrapper ticks without bound. The
  contract's `Tick` takes a resource `T` the caller supplies, and `start` takes `□ |==> T`: the
  gap a composition with node.go must close (a bound on a run's ticks).

## The backend: the buffers, bbolt as a key-value contract, the locks and the views

**2026-10-12 · the buffers adopted (unit 1); the rest proposed (units 2–3)** (`server/v3/storage/
backend`, ~1500 Go lines, translated with bodies but for the snapshot, the hash, defragmentation
and `verify.go`; branch `worktree-backend`; `STATUS.md`, "The backend"). bbolt is the trust
boundary: it is not merged here (its proof, branch `bbolt`, needs Perennial work not yet landed),
and its specs there are physical (pages, cursors as stacks, no contents), so the backend is
proved over a key-value contract of bbolt, stated here as axioms, which the bbolt proof is to
discharge.

### The buffers (`tx_buffer.go`, unit 1)

- **Entries as lists, the read buffer canonical.** A bucket buffer holds a list of entries
  `(key, value)` in the order they were added (`Model.lean`); keys compare as `bytes.Compare`
  (`go.GoStringLt`). The read buffer's buckets are *canonical*: strictly increasing keys
  (`entsSorted`), the form `canon l` (the stable sort by key of `l`, then the last entry of each
  key: `sort.Stable` then `dedupe`'s loop) gives. `merge` and `writeback` produce `canon` of the
  old entries followed by the new ones in every branch (`canon_of_sorted`,
  `canon_append_perm`: a non-stable `sort.Sort` of entries with distinct keys does not change the
  canonical form). *Rejected:* a finite map per bucket (`Range`'s binary search and the
  dedupe-or-not branches are about the list).
- **The write-back's assumption is a premise.** `writeback` sorts a non-sequential bucket with
  `sort.Sort` "assume no duplicate keys", and `merge` does not deduplicate when the read buffer's
  entry was empty: two puts of one key in one session are written back as two entries, and
  `Range` returns the older (`issues/etcd-backend-duplicate-put-stale-read.md`, reproduced). The
  write buffer's well-formedness (`WBuf.Wf`) is what `put` (distinct keys in a bucket written by
  `put`) and `putSeq` (keys increasing: its `verify.Verify` check, proved to pass) keep, as
  premises on the key put.
- **Slices read-only for good, every slot.** The buffers keep the key and value slices they are
  given and hand them to readers (`Range`, `CopyUsed`), so an entry's slices are `↦*□`
  (`entsIn`); every slot, stale or in use, has its slices so (`slotsRO`), since `merge` reads the
  first slot of an empty source buffer. A buffer's layout (`BBPhys`: its slice and slots) is
  explicit in `bbAt bb dq p es` so that readers holding fractions (the read buffer is under an
  `RWMutex`) agree on it; `ownBB` is the writable buffer, with a free slot and a length bound
  (`bufBound = 2^60` entries, so `3/2` growth does not overflow).
- **`sort.Stable` is an axiom** (`Spec/sort/Stable.lean`): Perennial translates it but proves only
  `sort.Sort`; its result is Lean's stable `List.mergeSort` (a stable sort by a strict weak order
  is determined). `verify.Assert` (`CopyUsed`'s) is an axiom for a true condition.

### bbolt as a key-value contract (proposed)

The backend's view of bbolt, `Proof/.../backend/InvBbolt.lean`: predicates are axioms (as the
btree's `ownBTree` was, "store: btree as the trust boundary"), the functions' specs are
`Spec/go_etcd_io/bbolt/<T>__<M>_kv.lean` (`bbolt.<T>.<M>.kvspec`, the suffix as the bbolt branch's
`_w` variants, so the files do not collide with its specs), each an `axiom` in
`Proof/go_etcd_io/bbolt/<T>__<M>_kv.lean`, stated from the Go documentation:

- **Data**: a database is its top-level buckets' contents, `Data := GMap GoString (GMap
  GoString GoString)` (no nested buckets: etcd has none); a bucket's cursor order is its
  sorted entry list. `ownDB db γ D`: the open database with committed data `D` (exclusive; the
  batch lock holds it). `bolt.Open` gives it for the data the file holds (`fileHolds path D`, a
  premise: what a fresh or restored file contains is the caller's assumption).
- **Read transactions**: `Begin(false)` snapshots `D`: `ownRTx tx q D` (fractional: readers of
  one batch interval share it; `Rollback` needs all of it), and `rtxStats tx` (exclusive: what
  `Bucket()`, `Cursor()` and `ForEach` mutate, the transaction's statistics: the backend calls
  them under `txMu`). The slices a read returns point into the memory map, valid only while the
  transaction is open (bbolt's documentation): `rtxBytes tx s b` (persistent) gives `s ↦*{dq} b`
  only together with a fraction of `ownRTx` (`rtxBytes_acc`). *Rejected:* `↦*□` results (false
  after `Rollback` unmaps a remapped file; and the bbolt branch's specs tie them to page
  fractions).
- **The write transaction**: `Begin(true)` (one writer: `wrTok γ`, given back by `Commit`) gives
  `ownWTx tx γ D S`: begun at `D`, contents `S` now. `Bucket`, `CreateBucketIfNotExists`,
  `DeleteBucket` (returning the variable `ErrBucketNotFound`'s value when absent), `Put` (key
  `1..MaxKeySize` bytes, value at most `MaxValueSize`: `nil`; bbolt copies the key and keeps the
  value, `↦*□`), `Delete`, a cursor over `S`'s bucket and `ForEach`; `Commit` makes `S` the
  committed data or returns an error (the backend then calls `lg.Fatal`, which never returns). A
  bucket handle's `FillPercent` field (the backend writes `0.9`) is owned by the transaction.
- **Getters**: `Tx.Size`, `Tx.DB`, `Tx.Stats`, `DB.Stats`, `DB.Info` (the backend's metrics)
  return some value.

### The locks and the views (proposed)

- **Two views.** The batch transaction's state `S` (bbolt's writer contents) is the lock
  holder's (`batchLocked γ st`, a record: `S`, the write buffer, whether the session wrote); the
  readers' view `V` (the bbolt read snapshot of the batch interval overlaid with the read buffer)
  is a ghost variable `γ.view`: half the client's (`bView γ q V`, `q/2` of it), a quarter under the
  batch lock, a quarter under `readTx.mu` (fractional, for `RLock`). Readers agree with the
  client's fraction; changing `V` needs all of it: the batch lock's `Unlock` after a session that
  wrote takes the client's whole half (`bView γ 1 V`) and gives back `bView γ 1 V'` with `V'` the
  session's `S` after the commit's hook if it committed. So no reader runs during an `Unlock`
  (mvcc's `s.revMu`, held exclusively by the store's `End` around `Unlock`, is this): `Unlock`'s
  two critical sections (the write-back, then the commit when a delete is pending) are not atomic
  for an unsynchronized reader, and the read-buffer cache of `ConcurrentReadTx` goes stale across
  them (`issues/etcd-backend-read-buffer-cache-stale-after-commit.md`, reproduced).
- **When the lock is free, `V ≈ S`** (equal on every key, an absent bucket as an empty one): the
  write buffer's leftover puts (the hook's, buffered after the write-back) precede every later
  put in the chronological order the write-back preserves, and every session with a delete
  commits at its `Unlock`. This is the batch lock's invariant, with the writer's physical state
  (`batchTx.tx`, `pending < batchLimit`, `pendingDeleteOperations = 0`, the write buffer, bbolt's
  `ownDB`).
- **The hooks are the client's**: the pre-commit hook (`Hooks.OnPreCommitUnsafe`, run by every
  commit, even a `ForceCommit` with nothing pending) is specified by a relation `H` on the data
  and the buckets it may change (the server's: `Meta`), proved by its owner over the batch
  transaction's own specs. The views are of the other buckets: the backend's own goroutine
  (`run`) commits, and so runs the hook, with no client to hand it a view, and the read-buffer
  cache goes stale on the hook's buckets at any commit (the second reproduction of the issue
  above). Reads of the hook's buckets promise what the hook's relation gives, no more. The post-lock hook (`txPostLockInsideApplyHook`) is a triple the client gives
  `SetTxPostLockInsideApplyHook`.
- **Readers.** `readTx.mu` (guarded `RWMutex`) holds the read buffer, the interval's bbolt
  transaction's share and the interval's `WaitGroup` adder (Perennial's join idiom: a
  `ConcurrentReadTx` adds one and gets the `Done` permission with a fraction of `ownRTx`;
  `unsafeCommit`'s goroutine `Wait`s for them, then `Rollback`s). `Add` needs the counter below
  `2^31 - 1`: readers spend a token (`rdTok γ`, `2^31 - 2` of them at creation, given back by
  `RUnlock`), as mvcc pins its readers. `txMu` (one for the backend's life, shared by every
  interval) holds each interval's buckets map and `rtxStats`, in a ghost map of the intervals.
  The cache (`txReadBufferCache`, its own mutex) holds a persistent copy and its version, valid
  for the current version outside `Unlock`.

### The backend's proofs: what changed from the plan (2026-10-13 · adopted)

Units 2 and 3 carried the plan out (`STATUS.md`, "The backend"); the proofs changed it here:

- **The view is a finite map.** `γ.view` holds `vData P (C, R)` (the readers' lookups off the
  hook's buckets as a `GMap`), not the pair: the `run` goroutine's commits move entries from the
  read buffer into bbolt without a client, and leave `vData` unchanged. A second ghost variable
  `γ.rvs` (halves: the batch lock, `readTx.mu`) holds the pair itself and whether an `Unlock`'s
  window is open, so the batch side knows its `C`, `R` are the readers'. The commit flips the
  window flag off while the hook runs (readers are locked out), so a hook sees an ordinary
  `batchLocked`.
- **`Unlock` takes the client's resource up front** (`∃ vd, bView γ 1 vd ∗ WR ∗ (bView γ 1
  (sData P S) -∗ Q)`): the commit's hook needs `WR` before the new view exists. The other case
  (`freeOk`: the session wrote nothing the readers see) needs only `WR`.
- **The write buffer's bound.** The hook's puts stay in the write buffer across commits (a commit
  does not write back), and `pending` restarts at 0, so a `pending`-based bound fails after
  repeated commits. The batch state carries ghost counters (`BCnt`: commits since the last
  write-back and others, data so the hook cannot change them); a client's `Commit`/
  `ForceCommit` costs a `wbTok`; the commit inside an `Unlock` is free; the `run` goroutine's
  commit is unpaid but happens at most once per write-back (`γ.used`, `γ.wbc`); the budget stays
  below `2^40`, `hookMax ≤ 2^16`, so the bound `pend + (k + 1) · hookMax` is far below `bufBound`.
  The hook's own puts must meet `UnsafePut`'s no-duplicate premise: etcd's consistent-index hook
  re-puts the same keys at every commit, so two commits with no write-back between violate it.
  In Go this is harmless (the second commit's reset drops the read buffer's emptied bucket, and
  the next write-back deduplicates it: `issues/etcd-backend-duplicate-put-stale-read.md`), but a
  proof of the server's hook against this contract has to avoid it or the premise must weaken.
- **The bbolt contract gained** Timeless instances for its predicates, `rtxStats_excl` and
  `txLive_nonnull` (a live transaction is not nil: `t.tx != nil` decides the code's branches).
- **The intervals.** Each interval's buckets map is exchanged, at fractions, against `txMu`'s
  token (`intvInv`); its `WaitGroup` protocol has an authority for the readers' budget (the
  `int32` counter's bound), a finished state and a per-interval token, so the rollback goroutine's
  `Wait` gets the whole transaction back.
- **The cache** has poison marks for the window (a reader cannot mark a state while the clients'
  half of the view is deposited; `bView` also holds half of `γ.cvw` for this).
- **Stopping.** `bOpen` carries a close right (`γ.cls`); `Close` deposits it with the clients'
  half of `γ.opn` in a stop invariant over two broadcast channels (`isStopChans`, at
  `HasLC.hasLC`: Perennial's broadcast channels need later credits, so `Close`'s and `run`'s specs
  are stated there and `isBackend` stays generic); `run`, woken by `stopc`, gathers the whole open
  token for `CommitAndStop`, which leaves the persistent `bStopped`.
- **The lock checks** (`verify.go`'s `ValidateCalled*`) are axioms that return: a deployment
  assumption (`ETCD_VERIFY` lock checks off), stated in their Spec files.
- **Not proved**: `New`/`NewDefaultBackend`/`newBackend` (bbolt's `Options` is an axiomatized type:
  Perennial's `os.FileMode` alias), so the invariants' allocation is assumed by whoever creates
  `isBackend`; `batchTx.Commit`/`CommitAndStop` (dead: `batchTxBuffered` overrides them);
  `UnsafeForEach` (three functions), the snapshot, the hash and defragmentation.

---

## Perennial `a54e1999f`, not its `lean`

**2026-10-12 · accepted (decided with the user)**

**Decision:** pin Perennial `a54e1999f` (its proof layout), not its current `lean`
(`d0324b842`). Since `3fbe65749` Perennial's model does not propagate a panic to the caller, so
etcd's STM, which recovers `stm.fetch`'s and `commit`'s panics in `runSTM`, is not provable
there. The calls Perennial's new `ArgsWf` excludes (errors, `Duration`s, `LeaseID` as `fmt`
arguments; a context's `Err()` formatted) are trust-boundary axioms and strengthened
assumptions, each listed in `STATUS.md` ("Perennial `a54e1999f`") to be replaced by proofs.

**Rejected:** axioms for the STM at `d0324b842` (the model's code is stuck where `fetch`
panics; an axiom that `runSTM` returns would contradict it and could derive `False`); the STM's
specs restated in Perennial's "stuck" style (a premise equivalent to `▷ False`: vacuous results
that look verified); waiting for Perennial to propagate panics before any bump (the layout
change broke etcd-grove's imports now). The port to `d0324b842` is kept on branch
`perennial-d0324-wip`.

---

## `fmt.Errorf`'s `%w` errors: the model's body, not the axiom

**2026-10-13 · accepted (the merge of `origin/lean`, Perennial `a54e1999f`)**

**Decision:** the two `fmt.Errorf("...: %w", err)` calls whose error reaches the gRPC layer
(`mvcc.storeTxnCommon.rangeKeys`' `ctx.Err()`, the txn package's `executeTxn` wrapping it) keep
`mvcc.wp_Errorf_errorfIs`, which steps into Perennial's model of `Errorf` (`errors.New(format)`,
an `*errors.errorString`), not etcd-grove's trust-boundary axiom `fmt.Errorf.wp_proof`. The
request path needs `applyErrIs` of the error, which asks for a leaf (no `Unwrap`) pointer error;
the axiom gives only that `Error()` returns, and extending it with the leaf would be false of
Go, whose `%w` error is a `*fmt.wrapError` whose `Unwrap` `errors.Is` follows. A pointer-type
clause (true of Go) does not give `applyErrIs`.

**Rejected:** the axiom with an `errLeaf` clause (false of Go for `%w`); the axiom with Go's
error tree (`Unwrap` returning the `%w` argument): `applyErrIs` of the tree would need the
context error's tree, and `context.DeadlineExceeded` is a non-pointer error, which `applyErrIs`'
`TreeTyped` (for every target, `DeadlineExceeded` included) cannot describe; that is a redesign
of `applyErrIs` (targets restricted to pointer errors), not a merge. So the request path's error
facts for a canceled read rest on Perennial's model, which Perennial documents as not modeling
`%w` (`Perennial/TrustedCode/fmt.lean`): the known gap, `notes/STATUS.md`, "Merge of
`origin/lean` (Perennial `a54e1999f`)".

---

## mvcc: compaction — the compaction revision under revMu, the index compacted per key, the bucket minus a kept set

**2026-10-13 · unit 5a implemented (the specs, the model, the contracts; the proofs of the
compaction functions are units 5b/5c)** (`notes/STATUS.md`, "The store's compaction")

The store's compaction (`kvstore.go`'s `Compact`, `updateCompactRev`, `compact`,
`compactBarrier`, `checkPrevCompactionCompleted`, `compactLockfree`; `kvstore_compaction.go`'s
job `scheduleCompaction`; `store.go`'s meta keys; `index.go`'s `Compact`/`Keep`; `key_index.go`'s
`compact`/`keep`/`doCompact`, not `since`) was out of every model (`compactMainRev` fixed at
`-1`). What unit 5a fixed, with the user's design as the starting point and the corrections the
code forced:

- **`compactMainRev` under both locks, half each.** The plan read `rangeKeys`' load of
  `s.compactMainRev` as racy (no lock). It is not: a transaction holds `s.mu` shared for its whole
  life (`Read`/`Write` to `End`), and `updateCompactRev` writes the field holding `s.mu` exclusively
  (in `Compact`; in `compactLockfree`, under `restore`'s) and `s.revMu` exclusively; the watchable
  store's `syncWatchers` reads it under `s.revMu` shared. So `muInv s γ q` (new: `s.mu`'s resource
  was `True`) and `revMuInv` each hold half the field's points-to and a quarter of the compaction
  revision's authority (`crevUB`, a monotone counter of `crevN c = c + 1`, in the index's names:
  `IdxNames.crev`, so the index's lock can hold lower bounds), with `-1 ≤ c ≤ currentRev` (`muInv`
  via a certified log). The other half of the authority is the **compaction right**
  (`compactRight γ c`): `Compact`, holding both locks, gathers it all and updates field and
  counter; its holder knows the revision exactly. A transaction keeps its part of `muInv`
  (`muHeld s γ c`: the reader's token and `muInvAt s γ rfrac c`) and lends it to `rangeKeys` and
  the index's reads (`muHeld_cmp`, `muHeld_crev`). Lower bounds (`crevLb`, persistent) are what
  the job and the index carry. *Rejected:* an Iris invariant around the field opened at the load and
  the store (a GooseLang store is two steps; the invariant would re-derive `s.mu`'s exclusion);
  the field under `s.revMu` alone (`rangeKeys` does not hold it); a fractional `ghostVar` for the
  exact value plus a separate monotone counter (one counter, fractional, gives both: parts agree,
  lower bounds persist).
- **The store's existing statements are of a store never compacted** (`crevFrozen γ`: the
  compaction right at `-1` given up into an invariant, `compactRight_freeze`). The txn, apply,
  request-path and server packages' statements say a read at a revision answers the state there;
  of a compacted store that is false (`ErrCompacted`), and their models have no such outcome. So
  `storeReader` (the readers `store.Read`/`Write` take) carries `crevFrozen`, `isTxnRead`'s
  `storeTxnReadIs` and `storeTxnWriteIs` hold it, `Read`/`Write` find the revision `-1` by it
  (`crevFrozen_agree`), the read transaction's `firstRev` stays `-1`, and `rangeOutcome` (the
  `Range` specs') keeps no compacted case: no statement of another package changed (only
  definitions: `storeReader`). `NewStore` returns the compaction right and readers of a store that
  may be compacted (`storeReaderC`); `newWatchableStore` freezes (the watchable store's compaction
  branch, `syncWatchers`' compaction response, stays unmodelled, as the plan said: as a frozen
  store, not a premise per watcher), `storeReaders_of` turns the readers. A compacting client (the
  server's apply thread, which calls `Compact`: next) holds the right instead, and needs the
  compaction-aware forms of `Read`/`Write`/`Range` (later: `rangeKeys` is already general).
  *Rejected:* `Compact` needing nothing of the caller (the plan's): then no other package's
  statement stays true without a premise on every reader; an `ErrCompacted` disjunct in
  `rangeOutcome` guarded by a lower bound (unsound: the revision can be higher than the bound);
  reader slots each carrying a fraction of the right (compaction would need every reader back:
  the watchable store's loops keep two forever).
- **`rangeKeys` is general** (`rangeOutcomeC r err log rev c`: a read below `c`, after the
  future-revision check, is `ErrCompacted` with `{KVs: nil, Count: -1, Rev: 0}`, else
  `rangeOutcome`); its spec takes the field's part and the authority's part (given back). The
  read and write `Range`s call it at `-1` and convert (`rangeOutcomeC_neg`).
- **The index: each key compacted at a level of its own** (`idxLockInv`: `IdxCRep cmax evs L`,
  `Compact.lean`: every key's index is its events' compacted at some `-1 ≤ c ≤ cmax`, absent if
  that empties it; `crevLb γ cmax` and a committed log's lower bound longer than `cmax`). The job
  compacts key by key under the lock (`treeIndex.Compact`), so a level per key. Readers present a
  part of the authority at `c ≤ atRev` (`crevUB`: new premise of `Get`/`Range`/`Revisions`/
  `CountRevisions`, given back; `KeyIndex`/`Insert`, `restore`'s, at `-1`); writers need nothing
  new (their revision is above `cmax` by the committed-log bound and `idxLogAuth`). The pure
  theorems (`Compact.lean`): `kiGet_kiCompact` (a compacted key index answers as the
  uncompacted one at or above the level), `kiGet_of_kiCompact_empty`, `kiCompact_kiCompact`/`_le`
  (compactions compose: the job's pass over a key a writer or an earlier pass changed),
  `kiCompact_neg`, `kiCompactO_step` (compaction commutes with the writer's next event,
  `IdxCRep.step`), `IdxCRep.kiAt`/`rangeAt`; checked against `key_index.go`: `doCompact` walks the
  generations while not the last and the tombstone's main is below `atRev` (strictly), then the
  walk keeps the last revision at or below `atRev`; `compact` cuts that generation there and drops
  the earlier ones, `modified` and each generation's `created`/`ver` unchanged (so `ver` is no
  longer the revisions' count: the version computed from the end, as `get` does, is unchanged);
  `keep` (the hash's) takes back a tombstone ending a generation that is not the last
  (`kiKeep`), which `compact` keeps in `available` (the asymmetry the code documents).
- **The bucket: deletions invisible to the logical view; reads may miss what compaction may
  delete.** The plan had the bucket view be `bucketMap log` minus a deleted set. The job deletes
  under the batch lock alone (no `s.revMu`), and half the view is `s.revMu`'s (a reader's snapshot
  is taken under it): the job cannot update the view. So the view stays `bucketMap log` (grows
  only); the backend contract's reads (`ConcurrentReadTx`/`ReadTx`'s snapshots, `snapThin`; the
  batch transaction's point read and its limited range) may miss keys the store's `Del` says
  compaction may delete (`delKey γ k`: a revision's bytes with main at most a lower bound `c` of
  the compaction revision and not kept by compaction at `c` of a certified log, `KeyDel`), and
  `UnsafeDelete(Key, k)` requires `Del k`. A frozen store deletes nothing (`crevUB_noDel`,
  `crevFrozen_noDel`, `snapThin_crev`, `snapThin_frozen`): `Read`, the write transaction's
  `Range` and `rangeEvents` get exact snapshots. The plan's "kept set covers what a read at or
  above the compaction revision names" is `named_not_del` — **false** when the compaction
  revision deletes a key and puts it again (`doCompact` keeps the tombstone and drops the put, the
  key's live revision: `issues/etcd-compaction-delete-then-put.md`, reproduced): its premise
  `NoDelPutAt` is the compacted store's readers', not the compaction's.
- **The backend contract** (`InvStore.lean`): `isKeyBackendD b View Del W Dep P f` (and
  `isKeyBackend`, its `Dep` hidden; `isStore` keeps the `D` form with `□ Dep`): `Del` the
  deletable keys (the store's choice, as `W`); `Dep` the **deposit witness** the no-puts `Unlock`
  returns: with it `LockOutsideApply` gives `W` (the job's lock; `NewStore`'s first lock, before
  the deposit, still gets none — honest, where returning `W` there would duplicate it); the batch
  transaction's `UnsafeDelete`, its limited `UnsafeRange(Key, lo, hi, limit)` (`limit > 0`: the
  first `limit` entries in `[klo, khi)` of the bucket with the puts, thinned), its
  `UnsafePut(Meta, k, v)` at the two compaction keys of a value the store writes there
  (`metaRevVal`); the snapshot's reads of those keys (`metaReadSpec`: nothing, or some value the
  store wrote), and `ReadTx()` with no view for them alone (`metaReadTx`:
  `checkPrevCompactionCompleted` holds neither lock); `LockForSafeRangeDelete`/`Unlock…`,
  `Size`/`SizeInUse` with no effect. The token `Locked` stays a list of puts (the plan's list of
  ops is not needed: deletions do not change the logical view, meta puts are not in it). The
  meta keys' own view (`metaCompact γ q sched fin`, not the consistent index's `MetaCI`) is the
  store's record in the batch lock's resource (`compactRes`, with the finished compactions'
  counter whose lower bounds are `compactedAt γ rev`); reads of the keys return any value the
  store wrote (racy with the job; the result only decides whether the hash is stored).
- **The channel `Compact` returns** (`compactChan ch Q`, Perennial's broadcast idiom: closed once,
  a receive gives `□ Q`). For the job: `Q = compactDone s γ rev` = `compactedAt γ rev`, or the
  store stopped (`storeStopped`: `stopc` closed, the job's loop received it, `scheduleCompaction`
  failed and the barrier at `context.TODO()` closes), or a context closed (the job's context
  cancelled: the barrier closes later, from another job, with no evidence of either). For
  `ErrCompacted`'s barrier: `Q = True`. *Rejected:* `compactedAt` alone (false of the two
  interrupted paths).
- **The scheduler** (`pkg/schedule`: `NewJob`, `job.Do`/`Name` translated; `fifo` names-only):
  the shape agreed with the session verifying the server (which will strengthen it in place
  with the FIFO order): `isScheduler f γ` (persistent; `NewFIFOScheduler` returns it), the run
  token `schedRunning γ` (exclusive, the scheduler's goroutine's: every `Do` receives it and
  returns it, no overlap), `jobIs γ j Pre Post` (persistent: `∀ ctx cd, {schedRunning γ ∗ Pre ∗
  isContext ctx cd} j.Do(ctx) {schedRunning γ ∗ Post}`, the context maybe cancelled), the axiom
  `{isScheduler f γ ∗ jobIs γ j Pre Post ∗ Pre} f.Schedule(j) {True}` (no run token:
  `compactBarrier` schedules from inside a job), and `γ.jobs`, a monotone list of the scheduled
  jobs' postconditions' names, for the order (unused yet). `NewJob` makes `jobIs` from the
  closure's triple (`jobFnSpec`).
- **Trust boundary, no effect**: the hasher (`newKVHasher`, `kvHasher.WriteKeyValue`/`Hash`,
  `hashStorage.Store`: crc32 has no Perennial model; `kvHasher` is an axiomatized type, so the
  job's proof will rest on its generated instances' `sorry`: a trap for 5b, `notes/STATUS.md`),
  zap's `Uint32` (new), the compaction metrics (`histSpec`'s `Observe`, in `mvccInit`), the two
  meta key names' bytes (in `mvccInit`: `schema` is names-only for them and its own facts are the
  consistent index's).
- **The configuration**: `isStore` holds the configuration with `0 < CompactionBatchLimit` (the
  job's loop ends when a batch is short of the limit; the backend reads a non-positive limit as
  none); `NewStore` takes `0 ≤ cfg.CompactionBatchLimit` (a zero limit is defaulted: `mvccInit`
  fixes `defaultCompactionBatchLimit = 1000`), the premise that the code's unvalidated flag needs
  (`issues/etcd-compaction-negative-batch-limit.md`, reproduced).

### The compaction over the real backend (merge, 2026-10-13)

**2026-10-13 · adopted** (the merge of `lean`, the backend's units 1–5, into `mvcc` after unit 5a;
`STATUS.md`, "Merge: lean into mvcc, the backend meets the compaction")

**Decision: one contract, theirs, with the compaction's clauses inside it, the compaction-only
calls guarded by `Cmp`.** `isKeyBackendG b View RT WT PutOk Del W Wi Dep Cmp P f`
(`InvStore.lean`) keeps the backend side's names and layering (the tokens `RT`/`WT`, the put
condition, the late-bound lock resource `Wi`/`lateW`, `keyReadLocked`/`rdCap`, `batchTxInitSpec`
with `LockedO`) and adds unit 5a's: the deletable keys `Del` (the snapshots' `snapThin`, now in
`keyReadSnap`'s `RLock` postcondition since the snapshot is chosen there; the batch
transaction's point read may find a deletable key gone), the deposit witness `Dep` (returned by
`batchTxInitSpec`'s `Unlock`, `NewStore`'s session; the job's `LockOutsideApply` takes it and
gives `Locked [] ∗ W`), `Size`/`SizeInUse`; and, under `⌜Cmp⌝`, `UnsafeDelete(Key)`, the limited
`UnsafeRange` under the lock, `UnsafePut(Meta)` at the compaction keys, `ReadTx` for the meta
keys alone (`metaReadTx`), `LockForSafeRangeDelete`/`UnlockForSafeRangeDelete`. The store's
instance takes `Cmp := storeCmp γ` (`γ.kb = none`); `NewStore`'s premise is `storeBackend`
(the instance's contract, with some `Dep`).

**What the real backend proves** (`BackendBridge.lean`, `isKeyBackendG_of_backend` with `Cmp`
false and `Dep = True`): exact snapshots (`snapThin_refl`), the point read's key found, the job's
`LockOutsideApply` (`bt_lockOutJ`: the lock holds the late-bound `W` from the backend's creation,
so no deposit witness is needed), the init `Unlock`, `Size`/`SizeInUse` (`bk_size`,
`bk_sizeInUse`), `ForceCommit` (theirs). **What it cannot**, so `Cmp` is false of it and the
compaction's specs (`Compact`, `updateCompactRev`, `compactLockfree`,
`checkPrevCompactionCompleted`, the job's `compactJobPre`) take `storeCmp γ`:

- *Deletion from `Key`*: `batchTxBuffered.UnsafeDelete` requires a bucket that is not
  safe-range (`P.SB bi.name = false`), and the batch lock's invariant (`safeSt`) keeps every
  committed key of a safe-range bucket in the writer's contents (what transfers the put
  condition "above the writer's keys" to "above the committed keys"). Not an axiom of bbolt's
  contract: the backend's own model.
- *The readers' view*: a deletion committed at the job's `Unlock` changes what readers see
  (`vData`), which the backend's `Unlock` allows only with the clients' whole view
  (`bView γ 1`); half of it is under `s.revMu`, which the job does not take (nor does Go). mvcc
  (and Go) rely on readers never looking up the keys compaction deletes; the backend's view
  would have to be one up to deletable keys: a backend redesign.
- *The `Meta` keys*: `Meta` is one of the hook's buckets, whose contents promise readers
  nothing, so a read cannot give `metaRevVal` (without which `BytesToRev` panics); a put needs
  the key absent from the write buffer, which may hold the hook's leftovers; and a meta put
  costs a pending operation that the bridge's `bkLocked` counts only for `Key` puts.
- *Budgets and slots*: every batch of the job spends a write-back token (`wbTok`) on its
  `Unlock` and its `ForceCommit`, unboundedly many; `safeRangeDeleteMu`'s reader slots are not
  handed out by `isBackend` (the constructor is unproved).

**Adjustments to unit 5a's statements**: the compaction specs above take `storeCmp γ`;
`keyReadSnap` no longer carries `metaReadSpec` (unused; the meta reads come through
`metaReadTx`); the no-puts `Unlock` no longer returns `□ Dep` (the init session's does); the
limited range's slices stay read-only for good (the assumed backend's: a capability like
`rdCap` would make the job's delete-through-the-key juggle tokens; revisit with the backend's
support); `rangeEvents`/`restore` quantify over `Dep`/`Cmp`; `New`/`newWatchableStore`/`NewStore`
take theirs' instance premise (`storeBackend`) and keep `0 ≤ CompactionBatchLimit`;
`batchTx_reader` is theirs with unit 5a's "nothing deletable" premise.

*Rejected:* changing the backend to support deletions from `Key` here (its statements stay as
`lean` has them: a redesign of its view, not a merge); stating the compaction clauses as a
premise of the bridge's results (an assumption false of the backend's own model: its
`UnsafeDelete` leaves a delete pending, which `bkLocked` excludes); `Del := False` for the real
instance alone (the meta and range clauses would still need a guard, and the job's spec would
be unprovable instead of inapplicable); dropping `Dep` (the assumed backend's lock resource is
the store's `writerRes`, not late-bound: the lock cannot hold it before `NewStore` makes it);
dropping `snapThin` (the assumed contract would be false of Go's backend once compaction runs).

### The index side's proofs (unit 5b, 2026-10-13 · adopted)

**2026-10-13 · adopted** (`STATUS.md`, "The store's compaction", unit 5b)

- **`walk`'s closure is effectful.** `generation.walk`'s spec takes `walkFnSpecR f p R Q`
  (`Defs.lean`): on a revision where `p` holds the closure returns true keeping `R`; where it
  fails it returns false turning `R` into `Q r`; `walk` gives back `walkPost revs p R Q` (`R` if
  every revision passed, else `Q` of the one it stopped at, `genWalk`'s). The pure closure of
  `keyIndex.get` is the case `R = True` (`walkFnSpecR_of_pure`); `doCompact`'s takes the
  `available` map with `R` = the map at `A`, `Q r` = the map with `r` inserted. *Rejected:* an
  invariant indexed by the visited revisions (no caller needs more than "unchanged until the
  stop"; the walk stops at the first failure, so the effect happens once).
- **Contract correction: `treeIndex.Compact` takes the compactor's token.** 5a's spec needed
  only persistent facts (`isTreeIndex`, `crevLb`, `idxCert`), so it allowed two concurrent
  passes: then one pass can `compact` a key index the other deleted (an empty one: `lg.Panic`),
  or delete by key a key put again in between, and the clone's pointers are not owned by anyone
  when visited (unprovable, and false of Go: `issues/etcd-index-compact-overlapping.md`). It
  also allowed a pass at a revision below an earlier pass's, whose `available` is then not
  `keepSetIs` (the key indexes are already compacted above it). The new ghost name `IdxNames.cmp`
  (`ghostVar (Int × List Loc)`) holds the last compaction's revision and the pointers a pass has
  yet to visit, half in the lock's resource (`idxCmpOwn γ q L cmax`: every pending pointer is in
  the tree, every key's level at most the revision, nothing pending unless `0 ≤ cmax`), half the
  compactor's (`idxCompactor γ c`, exclusive). `Compact` takes `idxCompactor γ c` with
  `c ≤ rev` and returns `idxCompactor γ rev`; `newTreeIndex` returns `idxCompactor γ (-1)`
  (`NewStore` drops it for now: unit 5c keeps it where the jobs find it, they run one at a time
  on the FIFO scheduler, `schedRunning`). The writers keep the invariant unchanged in substance:
  `Put`/`Tombstone` keep every pointer (`idxCmpOwn_mono`), `Insert` replaces one only with no
  compaction (`cmax < 0`, its `crevUB … (-1)`; `idxCmpOwn_neg`). `InvStore.lean` changes only its
  `Countable IdxNames` instance (the new field). *Rejected:* keeping the deleted key indexes'
  resources in the lock (a stale pass would still delete a key put again, by key); the
  scheduler's run token in the index's spec (the index cannot name the store's scheduler);
  pointer stability without ghost state (the lock invariant is a state predicate: nothing in it
  forbids a lock holder to drop an entry whose compaction empties it).
- **`doCompact` at any fraction.** Its 5a spec took the key index at fraction 1, but `keep`
  (under `RLock`, at any fraction) calls it: the spec now takes `dq` (it only reads the key
  index). `compact` passes 1.
- **Revisions as map keys.** `go.IntoValInj Revision` is derived from the determinism of the
  struct's field loads (`Revision.TypeAssumptions.get_Main`/`get_Sub`), and `SafeMapKey Revision.ty
  r` from the struct comparison's semantics (`Defs.lean`): no new assumption.
- **What `Compact`'s map is.** The pass's invariant: the map holds exactly the revisions
  `kiAvail` keeps, of the log, for the keys visited so far (each key's index at its visit is its
  events' compacted at a level at most `rev`: `IdxCRep.avail_some`, `reader_avail`); a key with a
  kept revision was in the clone (`keepAt_keys`: at clone time, a key absent from the tree is one
  whose compaction emptied it, which keeps nothing at `rev`). `Keep`'s: `keepFold` over the
  lock's entries is every key's `kiKeep` (`keepFold_spec`; a revision `keep` takes back is no
  other key's, `IdxCRep.avail_inj`), and `kiKeep` is the log's (`reader_keep`).

### The store's side: the compaction right carries the scheduler queue (unit 5c)

**2026-10-13 · adopted** (`STATUS.md`, "The store's compaction", unit 5c)

**Decision: the compaction job is a tracked job of the store's FIFO scheduler, and the exclusive
compaction right holds the queue.** `treeIndex.Compact` takes the index compactor's token
(`idxCompactor γ.idx c`, unit 5b) and consecutive compaction jobs must get it in order. The
compaction right is now `compactRight γ c = crevUB γ.idx ½ c ∗ compactQueue γ c`, where
`compactQueue γ c = ∃ Ps p Q R, schedQueue γ.sch (Ps ++ [p]) ∗ savedProp p Q ∗ R ∗ (Q ∗ R -∗
compactTok γ c)` and `compactTok γ c = ∃ c' ≤ c, idxCompactor γ.idx c'` (the request path's
`run` threads the apply thread's resources the same way). `compact` schedules the job tracked:
`Prev := Q` (the previous job's `Post`, or the scheduler's initial `True`), its `Pre` holds `R`
and the wand, `Post := compactTok γ rev`; `NewStore` builds the queue at `-1` from
`NewFIFOScheduler`'s `[n, p₀]` (`Q = True`, `R` the token from `newTreeIndex`, which it no longer
drops). The token is "at or below" the job's revision because a job whose context was cancelled
(the scheduler's `Stop`) never runs its pass and hands the token on unchanged. `Compact` takes
the right and returns it at `rev` on success (unchanged on `ErrCompacted`/`ErrFutureRev`); the
apply thread, etcd's only caller, holds it, which serializes compactions. Go's `compact` call
(kvstore.go:283) runs after `s.mu` is released, so an exclusive right owned by the caller is the
only thing that can carry the queue to it. `crevFrozen` freezes the right's half of the revision
authority only (the queue is dropped: a frozen store schedules no compaction). The barrier jobs
(`compactBarrier`'s reschedule, `updateCompactRev`'s on `ErrCompacted`) are untracked
(`Prev = Post = True`, `schedLive`), their `Pre` the channel's close right and `□ Q`;
`compactBarrier`'s closure calls itself (Löb induction).

*Rejected:* the untracked form with the token exchanged through `schedRunning` (an invariant
holding the token, opened by whoever runs): a job scheduled later could run first as far as the
contract says (the untracked form promises no order) and find the token above its revision,
where `treeIndex.Compact` needs `c ≤ rev`; the queue under `s.mu` or `s.revMu` (in `muInv` or
`revMuInv`): `compact`'s call site holds neither lock, and the lock's resource is fractional
(the readers' parts) while the queue is exclusive.

**Contract corrections (unit 5c):**
- `compactRes`'s finished-compactions counter is at least the record's finished revision, no
  longer equal to it (`∃ n, monoNatAuthOwn γ.fin 1 n ∗ ⌜crevN (finRev fin) ≤ n⌝`): a finishing job
  writes `finishedCompactRev = rev` and raises the counter to `rev` if below, and the batch lock's
  resource does not know the jobs run in revision order. `compactedAt γ rev` now reads "a
  compaction at `rev` or later finished" (the same in Go's runs, where jobs are ordered).
- `store.compact` takes and returns `compactQueue γ rev`; `scheduleCompaction` takes
  `compactTok γ rev` and returns `idxCompactor γ.idx rev` in both outcomes (its pass runs first).
- `store.Compact` takes `-1 ≤ c`: the counter `crevN c = (c + 1).toNat` cannot tell a right below
  `-1` from one at `-1`, under which Go returns `ErrCompacted` for `rev ∈ (c, -1]` while the spec
  promised `rev ≤ c`. Every right a caller holds is at `-1` or above (`NewStore`'s, then each
  success's `rev > c`). (`compactLockfree`'s `muInvAt` already carries it.)
- New trust boundary: `time.Time.Unix` (`Spec/time/Time__Unix.lean`, an axiom like `time.Since`:
  Perennial's `time` does not translate it; the job's deferred `dbCompactionLast.Set`), and the
  job reaches the hasher's second generated instance (`kvHasher_into_val_typed`, `sorry --
  axiomatized type`: it allocates the hasher), as 5a anticipated.
- `crevFrozen` is the invariant of the right's revision half (`crevUB γ.idx ½ (-1)`), not of the
  whole right (the queue holds saved propositions, not timeless).

### Compaction-aware readers (unit 6a): the delete-then-put premise on `Compact`, the frozen reader a corollary

**2026-10-13 · adopted** (`STATUS.md`, "The store's compaction", unit 6a)

**Decision 1: the one who compacts asserts `NoDelPutAt` at its revision.** `store.Compact`
(`compactLockfree`, `updateCompactRev`) takes `idxCert γ.idx log`, `sint.Z rev < log.length` and
`⌜NoDelPutAt log (sint.Z rev)⌝`: compaction at a revision that deletes a key and puts it again
deletes the key's live value (`issues/etcd-compaction-delete-then-put.md`), after which a read
`Fatal`s. Transactions that delete then put exist (any `store.Write` user may issue them); the
gRPC checks (`checkIntervals`) exclude them on the request path only; the apply thread, which
compacts at a revision of the raft log, cannot prove it of an arbitrary applied entry; what can
is a statement about who wrote revision `rev` (e.g. every applied transaction passed the request
path's checks), which belongs to the compactor's caller. So the premise is the compactor's, for
its own revision. The fact is
`crevSafe γ c` (a certified log with revision `c` and `NoDelPutAt` there: no ghost state,
`NoDelPutAt` is of revision `c` alone, so every certified log covering `c` has it,
`crevSafe_cert`). It is recorded where each reader finds it: in `s.mu`'s resource for the current
revision (`muInvAt`'s certified log, which already held `c < log₀.length`; a transaction reads it
from `muHeld`), in the job's premises (`compactJobPre`), and on every key the job deletes
(`delKey`: the backend contract's `Del` now carries the deleting compaction's `NoDelPutAt`). The
readers use the last: a read at or above its transaction's revision `crev` may meet a key deleted
by any earlier compaction `c' ≤ crev` (the job of an earlier `Compact`, possibly still running),
and needs `NoDelPutAt` at `c'`, not at `crev` (`rangeAnswers_not_del`: `named_not_del` through the
prefix order of the certified logs, `KeyDel_prefix`, `NoDelPutAt_prefix`).
*Rejected:* a history invariant on `End` (no transaction deletes then puts a key): its writers
exist and the store cannot refuse them; it would be a premise of every `store.Write` user, the
txn package's and the server's statements included, for a property only compaction needs.
*Rejected:* the fact for the current revision only (in `muInvAt`): a reader at `crev` meets keys
deleted by earlier compactions, whose revisions are lower bounds (`delKey`'s `crevLb`), not the
current one; a ghost map from revisions to the fact (the deletable keys can carry it directly).

**Decision 2: the transactions observe `crev` and carry a tag `Z`; the frozen ones are their
defaults.** The store's specs take `storeReaderC` and quantify over the transaction's compaction
revision `crev` (fixed while it holds `s.mu`; `store.Read` reads it into `firstRev`) and a
persistent tag `Z` given back at `End` (`storeReaderC ∗ □ Z`): `Z = crevFrozen γ` for the frozen
readers (so `End` gives `storeReader` back), `True` for a compacting client. The transaction
predicates (`storeTxnReadIs`, `isTxnRead`, `isRoTxnWrite`, `storeTxnWriteIs`/`Core`,
`isTxnWrite`/`Core`, `isTxn`/`isTxnEnd`) take `(crev : Int := -1) (Z : IProp GF := crevFrozen γ)`:
at their defaults they are the frozen transactions, so the statements of the packages above mvcc
(`mvcc.isTxn mw s γ kind`, …) are unchanged in text and in meaning, and the specs that only pass
the transaction through (`Put`, `DeleteRange`, `Changes`, `Rev`, `put`, `delete`, `deleteRange`,
`NewReadOnlyTxnWrite`) are general with their frozen statements as instances (unification picks
the defaults). The specs whose shape changes (a `Range`'s outcome `rangeOutcomeC`, `FirstRev`'s
value, `storeReaderC` for `storeReader`, `Read`/`Write`'s lower bound `crevLb γ.idx c`) have
their old statement as `<fn>.specFrozen` and the corollary `<fn>.spec_frozen`, all in one
Proof-side module, `Proof/…/storage/mvcc/FrozenSpecs.lean` (a `Spec` file holds its triple and
nothing else; the clients import the module, as they import mvcc's `Inv` modules); the clients
above mvcc apply it in one line (`have h := mvcc.<fn>.spec_frozen h`). The snapshot a transaction reads may miss
keys compaction deleted (`txReader`'s `snapThin`, `keyReaderD`, `batchTx_readerD`); `rangeKeys`
shows the keys a read at or above `crev` names are present (above).
*Rejected:* separate general predicates (`isTxnReadC`, `isTxnC`, …) with the frozen ones as
abbreviations: every lemma twice, and the iris tactics match hypotheses up to syntax, not
unfolding; a `TxnKind` constructor for the general transactions (the txn package's `cases kind`
would change); the frozen fact in the store-level resources (a compacting client's `End` cannot
produce `crevFrozen`, so the frozen `End`'s `storeReader` must come from the transaction:
the tag); `rangeOutcome` with an `ErrCompacted` disjunct guarded by a lower bound (unit 5a's
rejection: the revision may be higher than the bound).

## The read loop's notifier: deposited lower bounds

**2026-10-13 · accepted (the request path's unit 4a, `server/v3/etcdserver/read`; `STATUS.md`,
"Unit 4a: the read loop")**

**Decision:** `LinearizableReadNotify(ctx)`'s caller knows a lower bound `c` of the committed index
(`committedAtLeast γr c`), obtained before it reads `r.notifier`; the loop issues `ReadIndex` after
it swapped that notifier out, and the read state's index is at least the committed index then. Two
lower bounds of a monotone index do not compare, so the client **deposits** `c` where the loop
collects it: each notifier has a ghost mono nat, its **need** (the largest bound a client of it
required). Under the read lock the client raises the current notifier's need to `c` (`read_deposit`),
the read invariant keeping a committed lower bound at least the need (the join of the clients'
bounds: whichever is larger). Under the write lock the loop swaps the notifier out and takes the need
and its committed bound `n` out of the invariant (`read_swap`), so `ReadIndex` at `n` answers every
deposited bound. The need is then **frozen**: its authority goes into an invariant of its own
(`needFrozen`, persistent; Perennial's mono nat has no persistent authority), since no client can
take the notifier any more; the close of the notifier's channel (Perennial's broadcast idiom, a
persistent `notified`: the error, `nc.err ↦□`, and if `nil` the frozen need with an applied index
at least it) lets every waiter compare its lower bound of the need with the frozen authority.

The current notifier is named by a ghost variable whose halves the lock's resource (`readMuP`, with
`r.notifier` at the lock's fraction) and the read invariant hold, so a reader learns which notifier
(and need) is current by agreement at any fraction. That ghost variable's name is part of
`ReadNames` (`notifier`), because Perennial's `RWMutex` bounds its readers: each caller of
`LinearizableReadNotify` holds a reader slot (`readReader r γr`, `sync.ownRWMutex`), a predicate the
server's read call resources (`srvRdCall`) must be able to name. `NewRead` takes the full ghost
variable (any value) at that name.

**Rejected:** comparing the client's bound with the read index directly (two lower bounds); a
persistent authority of the need (Perennial's `MonoNat` has none; the invariant is the frozen
authority); the read lock's resource with no ghost name (`r.notifier`'s fraction alone): the client
must learn the current need's name from what it holds under the lock, and a name pinned to a location
needs a ghost name anyway; the slot as an existential in `isRead` (a slot of a different lock
predicate than the read invariant's cannot be ruled out); `context.DeadlineExceeded` kept out of
`applyErrIs` (the loop returns a done context's `Err()`: `applyErrIs`' typing clause now holds for the
targets `errors.wp_Is` takes, pointer targets, `ptrTarget`, which a struct error meets).

## The applied index: a certified log per index

(2026-10-13, the request path's unit 4b.) Unit 4a's read loop proves that a linearizable read
waits until the applied index reaches an index `ci₀ ≥ c`, `c` a lower bound of the committed
index the reader knew of (`readIndexOk γr c`). That says nothing about *which* state the read
sees until the ghost applied index (`γr.applied`) is tied to what the apply thread applied.

**The deposit is at `setAppliedIndex`.** The apply thread is the only writer of
`s.appliedIndex`; `apply` calls `setAppliedIndex(e.Index)` right after each entry (after
`applyEntryNormal` or `applyConfChange`). Its spec takes the apply thread's half of the mono-nat
authority (`srvAppliedOwn γr v`, `v < v'`) and mvcc's certificate of the KV log `L` it left
(`idxCert E.γ.idx L`, from `srvApplyKV`), and, at the atomic store, raises both halves to `v'`
and inserts `v' ↦ L` into a ghost map `γr.logs` as a persistent element (`appliedLogAt γr v' L`).
So the index a reader can learn about (`appliedAtLeast`) and the log are published by one atomic
step; no separate "applied" event is needed. A conf change leaves the KV, so its index gets the
log before it. Indices are fresh because the invariant keeps every key at most the current index
and the apply thread's next index is larger (`apply`'s entries are consecutive from `ai + 1`).

**The invariant holds only the current index's log.** `srvAppliedInv` holds the atomic at `v`,
the other half of the authority, the map's authority (keys `≤ v`), and `appliedLogAt γr v L` with
`idxCert L` for the current `v` only. A reader with `readIndexOk γr c` (an index `ci₀ ≥ c` was
reached) opens it and takes the *current* `v ≥ ci₀` and its log (`readIndexOk_log`): `c ≤ v`, so
`v` itself serves as the read's `ci₀`. Keeping every index's certificate would be the same facts
(all persistent) with more bookkeeping, and nothing needs an older one: the read only needs some
index at least `c` whose log it extends.

**The prefix statement comes from `txn.Range`'s `log₀`.** `txn.Range`/`txn.Txn` take a
certificate of a lower-bound log `log₀` and return a log `log` with `log₀ <+: log`. The server's
`Range`/`Txn` passed the reader's own `log₀` (of `NewStore`'s two revisions); in the linearizable
branch they now pass the longer of it and the applied log `L₀` (`idxCert_prefix`: two certified
logs are prefix-ordered; `readIndexOk_logR`), so the answer's `log` extends `L₀`:
`readLogOk γr c log` (the read index and `∃ ci₀ L₀, c ≤ ci₀ ∗ appliedLogAt γr ci₀ L₀ ∗ L₀ <+:
log`), in `rangeReadOk`/`txnReadOk` and the handlers' answers. With `applied_log_at` (the deposit,
and `appliedLogAt_agree`), `range_linearizable` reads: a linearizable read at `c` returns the state
of a log extending the one applied through some index `ci₀ ≥ c`, which is exactly the apply
thread's log after the entry at `ci₀`.

**The proposer does not need the names.** The proposer's view (`srvReqFieldsAt`) reads both
indices only for the request limit's gap, so it holds the two invariants at *some* read names
(`srvIndexInvs s E := ∃ γr, srvAppliedInv s E γr ∗ srvCommittedInv s γr`) instead of threading
`γr` through `isServerReq` and every request-path spec; the reader's view (`srvReadFieldsAt s E γr`)
and the apply thread's (`isServer … γr`, `srvAtomics s E γr`) hold them at the read loop's names.

### The backend meets mvcc (unit 4, 2026-10-13 · proposed)

mvcc's results rest on `isKeyBackend b View W P f` (`InvStore.lean`), an assumed contract of
the backend's `Key` bucket; the backend is now proved against its own contract (`isBackend`).
Unit 4 derives the first from the second, so that the Put/Get path's KV core rests on bbolt's
contract only. The mismatches, and what changes:

- **The views.** mvcc's `View q m` is the `Key` bucket; the backend's `bView γ q vd` is every
  bucket off the hook's `P.HB`. The instance takes `P.HB := (· ≠ "key")`: the backend's view is
  the `Key` bucket, every other bucket is unconstrained (the lessor, auth, membership and the
  consistent index write them; their reads promise nothing here, as the hook's buckets now), and
  `View q m := ∃ vd, bView γ q vd ∗ ⌜keyBucket vd = m⌝`. The backend's `Unlock` case without the
  clients' view generalizes from `freeOk` to "the session changed nothing the readers see"
  (`vData` unchanged, the write buffer empty off `HB`; a delete in another bucket then commits
  without a view, as the `run` goroutine's commit does).
- **The lock's resource** splits as mvcc's: `WR := W ∗ P`, the store's `W` (it holds half the
  view: given back through the `Unlock`'s wand) and the hook's `P` (given up front: the commit's
  pre-commit hook and the post-lock hook need it). `LockInsideApply` runs the post-lock hook on
  `P ∗ Pre` (mvcc's `{P ∗ Pre} f() {Q}`) and returns `W ∗ Q`.
- **The post-lock hook set once.** `plHook` becomes a `dghostVar`: `SetTxPostLockInsideApplyHook`
  takes the clients' owned half; the client may then make it read-only (`plHookRO γ f`,
  persistent), which `isKeyBackend`'s fixed `f` needs (etcd sets it once, `server.go:412`).
- **The slices.** mvcc's results are `↦*□` (`keyVals`, `rangeVals`), false of bbolt (its slices
  die with the read transaction). mvcc's contract takes the backend's `rdB rtx`-style slices with
  a read capability under the reader's resource (`keyReader`'s `R`, `keyReadSnap`'s snapshot
  token): `rangeKeys`, `rangeEvents` and the transactions read the bytes before their `End`.
  `UnsafeSeqPut`'s key and value become `↦*□` (the backend and bbolt keep them; mvcc's slices are
  fresh: it persists them).
- **The bucket.** `schema.Key` is `backend.Bucket(bucket{id: 1, name: "key", safeRangeBucket:
  true})`: `schema.toml` translates `bucket`'s methods and the bucket variables; schema's package
  facts give `isBucket` of `Key` (and `Meta`).
- **The bridge** (`Proof/go_etcd_io/etcd/server/v3/storage/mvcc/BackendBridge.lean`):
  `isBackend γ P (W ∗ Pk) b ∗ plHookRO γ f ⊢ isKeyBackend (iface b) (View γ) W Pk f`, with
  `Locked l` the backend's session whose `Key` bucket is the lock-time contents with `l` applied.

*Rejected:* per-bucket views in the backend (the right generalization for several writers of
visible buckets, but every reader proof changes; the `HB` instance gives mvcc its bucket alone and
leaves the others to a later unit).

### The bridge (unit 4, part 2, 2026-10-13 · adopted)

`BackendBridge.lean` proves mvcc's contract of the real backend. What the plan above did not
foresee, and how it is resolved:

- **The contract takes the backend's tokens as parameters** (`isKeyBackendG b View RT WT PutOk W
  P f`) rather than fixed to the backend's: mvcc stays generic in its backend, and the store
  uses the instance without tokens (`isKeyBackend := isKeyBackendG … True True noPutCond …`), so
  no spec above mvcc changed. `RT` (a reader's slot of the backend and a share of it open) is
  taken by `ConcurrentReadTx`/`ReadTx`, given back by `RUnlock` and lent to the calls that need the
  backend open; `WT` (a write-back's budget) is spent by every session; `PutOk` is what the
  backend's `UnsafeSeqPut` needs of a put (bounds, keys increasing). *Rejected:* wiring `RT`
  through `storeReader` now: it does not compose until `WT` and the view do (STATUS, "Unit 4").
- **The shared read transaction's snapshot is the one its `RLock` finds**: `ReadTx()` returns the
  shared `readTx`, whose interval (bbolt's read transaction) changes at every commit until its
  `RLock`. So the snapshot splits: `keyReadSnap View RT rt m L` is `RLock` alone, taking the
  caller's view `View q m` (kept) and *choosing* the slices' predicate `Rd` and the token
  (`keyReadLocked RT rt m Rd Tok`: `RUnlock`, the reads, `rdCap`); `rtHeld_view` ties the held
  state to the view. *Rejected:* a ghost location for the reader's state (more ghost state for
  what the view already says; mvcc holds `s.revMu`'s view at every `RLock`).
- **`NewStore`'s session has its own token** (`batchTxInitSpec`: `LockedO n`, `n` buckets
  created, at most two): a create keeps the puts but costs a pending operation, and the backend
  bounds a session's operations (`pend < 2^58`), so a token `Locked l` preserved by creations
  could promise no bound. The creations are of schema's `Key`/`Meta` (`globalAddr ↦□ b`: the
  backend needs `isBucket`); `UnsafeCreateMetaBucket`'s callback is on `Meta`'s value.
- **The range read rests on a premise** (`rangeSafe`: the readers' states keep the `Key` bucket's
  read-buffer keys above bbolt's), with the pure core proved (`rtRange_safe`). *Rejected:* adding
  the safe-range discipline to the backend now (every session lemma, the write-back and the
  commit would change); and dropping the range read from the bridge (the premise says exactly
  what is missing).
- **The hook's buckets are all but `Key`** (`bridgeParams`): the view is the `Key` bucket, every
  other bucket's contents promise nothing to readers, so a session without `Key` puts changed
  nothing readers see (`viewSame_noPuts`) and needs no view at its `Unlock`.

### The store over the real backend (unit 5, 2026-10-13 · adopted)

- **The instance is data in the store's names** (`StoreNames.kb : Option KBReal`), not saved
  propositions: the view, the reader and write tokens, the put condition and the lock resource
  are functions of it, so the store's lock invariants keep their fractional laws and no agreement
  costs a later credit; `none` is mvcc's assumed contract, so one generic proof serves both.
  mvcc imports the backend's `InvBackend` for the real instance's predicates. *Rejected:* saved
  propositions for the view and tokens (the bucket view's halves would agree only up to a later,
  breaking `revMuInv`'s fractionality); two families of specs (duplicated proofs).
- **The lock resource is late-bound by registration, not by changing the backend**: the real
  backend is created with `W := lateW gx` (a one-shot registration of `(s, γ)`, a `dghostVar` of
  countable data), which `NewStore`'s first `Unlock` sets; `isBackend` is generic in `W`, so no
  backend proof changed.
- **Above mvcc the instance is pinned to the assumed one** (`txn.isKV`'s `γ.kb = none`), rather
  than threading the real backend's write tokens and `2^56` bound through txn, apply, server and
  v3rpc: the server's apply loop has no counted write budget to give (`soleWriter`'s budget is a
  function of the log; empty write transactions spend a write-back too), which is a statement
  change at the top, not a threading.
- **Size of a range: a premise** (`keySized`), the order: the backend's invariant. *Rejected:* a
  size bound in the backend's discipline (its put premise would need the bucket's size, which
  mvcc cannot bound: a revision may have `2^63` changes).
- **An oversized value is fatal, not a premise**: bbolt's `Put` kv-spec covers it (Go returns
  `ErrValueTooLarge`), and the backend's `lg.Fatal` never returns; mvcc cannot bound its encoded
  `KeyValue` (`kvEncode` is opaque).
- **`ConcurrentReadTx` promises no range** (`rng = false`): its cached read buffer can repeat a
  committed key (the cache issue's third reproduction).


### The layers above mvcc over the real backend (unit 6, 2026-10-13 · adopted)

- **Generic, not switched**: `txn.isKV` drops `γ.kb = none`; every statement above mvcc holds
  for both instances, the instance's costs entering as resources that are free over the
  assumed backend (`storeWT`, `txn.storeWTs`) and bounds that hold of both (`2^56 ≤ putMax γ`).
  *Rejected:* pinning `γ.kb = some d` (the assumed instance's results would be lost for no
  gain).
- **The write budget is a counted resource, one token per entry**: `apply.Apply` (and the
  server's `applyEntryNormal`) spend one `storeWT`; `apply`/`applyEntries` take
  `txn.storeWTs E.γ n` for the `n` entries they apply. A token per *entry* over-approximates
  (conf changes and replays waste theirs) but is stated on what the apply loop sees, and an
  entry opens at most one store write transaction. *Rejected:* a write count in the pure
  `ApplyKV` (every `applyStep`/`entriesOk` statement changes), the budget as a function of the
  log (an empty write transaction writes back too: the backend's `pending` counts since the
  last commit, not per session), and a token returned on the paths that open no write
  transaction (each triple would grow a disjunct for a gain only of precision).
- **The change bound at the request**: a delete's range below `2^56` (`delOk log o`: it
  tombstones exactly those keys), a transaction's changes below `2^56` (`TxnPre`); for both
  instances. *Rejected:* a bound on the store's size (stronger than needed) and a check in
  the code (there is none in Go).
- **`keySized` stays a premise, at the composition**: `server_kv_backend` composes
  `mvcc_NewStore_backend` with the sole writer and the write supply, the creator's resources
  (including `keySized` and `N + 2` write-back tokens) as its premises, since neither the
  backend's constructor nor the server's is proved.

## The server's goroutines: the FIFO scheduler as a chain of saved postconditions, the construction premise

(2026-10-13, the request path's unit 4c.) `run` receives each batch of committed entries from the
raft wrapper and schedules its `applyAll` as a job on a FIFO scheduler (`pkg/schedule`); the jobs
run one after another in a worker goroutine, each with the apply thread's resources the previous
job left. `start` sets the fields the goroutines share and starts `run`; `Start` attaches the
other goroutines through `GoAttach`.

**The scheduler is a trust-boundary contract with a queue of saved postconditions.** The
scheduler's code is names-only (mvcc's compaction uses it too), so its contract is one axiom,
`Scheduler.Schedule`. What `run` needs is FIFO: the job for a batch runs after the jobs scheduled
before it, and gets what they left. The contract keeps a ghost queue (`schedQueue γ Ps`, a mono
list of saved-proposition names): a tracked `Schedule` names the previous job's `Post` (`Prev`,
the queue's last saved proposition) and appends its own `Post`; the job runs with `Prev` and must
return `Post`. So the scheduler never needs to know what the resources are, and `run` threads the
apply thread's state (`applyRes C A`, the one definition of that bundle) as `Prev := applyRes C
A`, `Post := applyRes C (A ++ ce)` without holding it between iterations (the loop invariant holds
the queue). An untracked `Schedule` (`Prev = Post = True`, while the scheduler is live) covers
mvcc's compaction, whose jobs carry everything in `Pre`. The alternative, a scheduler proved in
Lean over its list and condition variable, is work in the scheduler's own package; the contract is
what its proof would show. The worker's thread token comes with the run token (`schedRunning`),
so a job may call `GoAttach` (the alarm goroutine).

**`start`'s premise is one named predicate, `isServerBuilt`.** Every result about the running
server (`range_linearizable`, `txn_applied`, the v3rpc end-to-end results) took `isServerReq`/
`isServerRead` as premises; `start` now produces them, so they are conditional on what `NewServer`
hands to `start` alone. The premise is stated as the views minus the fields `start` sets
(`srvFieldsBuilt`, `srvReqBuilt`, `srvReadBuilt`, `srvRunBuilt`, `srvApplyAllBuilt`, `applyBuilt`),
plus the ghost state and contracts `NewServer` must set up, each a named conjunct, so a `NewServer`
proof (or a later unit adding a resource, as the backend's write budget did) slots in at one place.
The read names `γr` are the premise's, not `start`'s: the raft node's contract (`isRaftNode`,
`NewServer`'s) is stated over them (`Er.γr`, the read registrations). The names-only methods
`start` and `run` call on the server's collaborators are contracts in the premise where they need
ghost state (`clusterVersionOk`: `nil` then non-`nil` for good; `rnSnapOnce`: the snapshot `run`
starts from, once) and axioms where they need none (the monitors, `Cleanup`).

**`stopping` gets its own idiom, not Perennial's broadcast.** It is `make(chan struct{}, 1)`,
closed once by `run`'s shutdown, never sent on; Perennial's broadcast idiom allocates only
unbuffered channels. `StopChan.lean` restates the idiom for `Buffered []` (the invariant's two
states: open, with the closer's flag at half; closed, with `□ Q` and the flag discarded), with the
receives and the close. `GoAttach` needs more than a receiver's view: under `wgMu`'s read lock it
must know the channel is open (so its `wg.Add(1)` cannot race `run`'s `wg.Wait()`), which a
fraction of the closer's flag in the lock's resource gives (`wgMuP`), the writer collecting all of
it to close.

### The consistent index over the real backend (unit 7, 2026-10-13 · adopted)

The consistent index's pre-commit hook (`UnsafeSave` → `schema.UnsafeUpdateConsistentIndex`)
was proved against an abstract batch transaction (`metaWriter`); `CindexBackend.lean` derives
that contract from the real backend's, and proves the hook in `hookFnSpec`'s shape.

- **Duplicates allowed where the code tolerates them** (`WBuf.WfR`, `wbDupOk`): a bucket written
  by `put` may repeat a key if the read buffer has no such bucket (`writeback`'s `!ok` branch
  calls `dedupe`), or, in the pre-commit hook's window, if its read-buffer bucket is empty (the
  commit's `reset`, right after the hook, drops it). The window is a flag of the batch lock's
  ghost counters (`BCnt.hw`, so `hookStep` keeps it): the commit opens it (`BSess.setHw`) before
  the hook and the reset closes it; `freeOk` and `Unlock` require it closed (a hook does not
  unlock). `writeback`'s premise is `WfR` with "the read buffer lacks the bucket", `UnsafePut`'s
  `kb ∉ keys ∨ wbDupOk st id`. The hooks get `hookPre` (window open, room for `hookMax`
  operations, every write-buffer bucket empty or with an empty read-buffer bucket), which the
  commit proves from the bounds (`bgOk` gained: after a commit, until the next write-back, the
  read buffer is empty). *Rejected:* a premise only on the hook's buckets (a client's duplicate
  into a bucket the read buffer has *is* the issue's stale read); deduplicating in the model (the
  code does not); allowing duplicates whenever the read-buffer bucket is empty (a write-back may
  follow a client session: the `ok` branch's `merge` keeps both).
- **The hook's own keys are a ghost variable** (`BParams.HK`, `hkData`, `hkOwn`): their values
  in the writer's contents, half the batch lock's (`batchGhostAt`), half the client's. A put of
  one needs the client's half (`hkPut`), a delete or a bucket delete must not touch one, a
  sequential put must not be one. The server's batch-lock resource holds the client's half as
  its meta keys (`metaTM γB P mm`), so the hook knows what the writer's `Meta` holds, whatever
  sessions ran since the last commit. *Rejected:* a pure premise of the hook on the state (not
  stable across other sessions); per-bucket ownership (the readers' view would change).
- **Room for the hook**: `Unlock` takes `pend + hookMax < 2^58` (its commit runs the hook), and
  `unsafeCommit`/`commit` carry it; free states have it (`room_of_freeOk`). mvcc's sessions
  carry their puts' bound (`sessPuts`: at most `2^56`; `bkLockedO`: at most two creations).
- **The meta contract, generalized** (`InvCindex.lean`): a read's value slice is readable under
  a resource (`metaValsA Acc`; `Acc := TM` for the batch transaction, whose slices are bbolt's
  while the lock is held; `True` for the assumed `ReadTx`, whose statements are unchanged);
  `readCIAUA` lends it to the decoding (`readCIAU` is its `True` instance); `metaWriter tx TM PTi
  PTt`'s puts each spend a token (the hook may put `hookMax` entries) and store non-zero values.
  The specs of `UnsafeReadConsistentIndex`, `unsafeUpdateConsistentIndex`,
  `UnsafeUpdateConsistentIndex(Force)` and `UnsafeSave` changed accordingly; `ReadConsistentIndex`,
  `ConsistentIndex`, `UnsafeConsistentIndex` did not.
- **The reads of `ReadTx` stay a premise** (`isMetaBackend`): they run only while the index is 0
  (after `NewConsistentIndex`/`SetBackend`, at startup), and the readers' view promises nothing
  of the hook's buckets; deriving them needs a readers'-side ghost of the committed hook keys.
- **The hook as a `hookFnSpec`** (`ci_hook_backend`, `ci_hookFnSpec`; linked in the server's
  `Results.lean`): for any function that runs `ci.UnsafeSave` on its argument. etcd's hook is
  `BackendHooks.OnPreCommitUnsafe` (`server/storage/hooks.go`, names only: its `confState` part
  and the struct are not translated), and the backend's constructor, which would take its
  `hooksSpec`, is not proved; so `server_kv_backend` (generic in the hooks' resource `Pk`) holds
  at `Pk := batchLockInv γA (metaTM γB P)` with the hook's contract still the creator's premise.

### The server's backend hook (unit 8, 2026-10-13 · adopted)

- **The hooks' contract is derived by Löb induction, not assumed**: `isBackend` holds the hooks'
  contract (`hooksSpec`) and the hook's puts need `isBackend` (the batch transaction's specs take
  it). `isBackendNH` is `isBackend` without the hooks' contract; `isBackend_of_hooks` derives
  `isBackend` from it and a hooks' contract given `▷ isBackend` (the hook's call takes a step
  before it needs the backend), so `BackendHooks.OnPreCommitUnsafe`'s spec takes `▷ isBackend`
  and `▷ saveSpec`. *Rejected:* `hooksSpec` taking the backend predicate as a parameter (a cycle
  of definitions); keeping the hooks' contract a premise inside `isBackend` (what unit 7 left).
- **The indexer's save as a contract of its own** (`saveSpec`, `hookSaveStep`: a hook step with
  one put of room and the `confState` key free to put): `OnPreCommitUnsafe` is proved for any
  indexer meeting it; the consistent index's `UnsafeSave` does (`ci_saveSpec`, from
  `ci_hook_backend_run`, which keeps `hookRun`). The `confState` put needs `hookMax ≥ 3` and the
  key not one of the hook's own (`hooksParams`): the consistent index's two keys are the own keys,
  `confState` is written only by the hook.
- **`MustUnsafeSaveConfStateToBackend` is the trust boundary** (axiom): it is `json.Marshal` of
  `any` and one `tx.UnsafePut(Meta, "confState", bytes)`; its spec is that put's triple lifted,
  any bytes. The `ConfState` it reads takes no resource: `ConfState` (protobuf-go v2) is an
  axiomatized type whose typed points-to is a generated `sorry` instance, and `SetConfState`
  stores a fresh clone no one writes. *Rejected:* `cs ↦{dq} c` (reaches `sorryAx`).

### The lessor's KV-facing methods and the live leases (unit 8, 2026-10-13 · adopted)

- **A lease is live relative to the lease owner's half, not for good.** mvcc's `put` calls
  `Attach` and panics on its error, which the real `Attach` returns once `Revoke` has deleted the
  lease; the persistent `mvcc.leaseKnown γl id` (granted once, known forever) promised `Attach`'s
  success after a revocation. Now the lessor's ghost map `γl` (the store's `γ.leases`) holds the
  live set `L` (the lease map's domain), half in `le.mu`'s invariant, half the lease owner's
  (`lease.leaseOwn γl L`): the apply thread, the one goroutine that grants and revokes. A live
  lease is the pure `id ∈ L` for that half; `Attach` takes the half (any holder of it agrees with
  the lessor's under the lock), `Grant`/`Revoke` change `L`. *Rejected:* a persistent fact
  indexed by a revocation epoch (every statement carrying the epoch: the same threading, more
  ghost state); fractional, duplicable facts consumed by `Revoke` (a dropped fraction makes the
  lease unrevokable); a revocation forbidden for known leases (no `LeaseRevoke` proof).
- **Threaded where the code needs it, and only there**: mvcc's `put` path (`leaseOwn`), the txn
  package's lease checks (`lessorUser`: the half and a reader slot for `Lookup`'s read lock) and
  its put and transaction paths, the apply package's `kvOwn` (`leasesLive`: some `L` with the
  state's leases in it and the owner's resource; a definition, so the apply, server and v3rpc
  specs are unchanged). `checkTxn` takes the owner's resource only for a request that is not
  read-only (`⌜lu = false⌝ ∨ lessorUser`), so the server's read-only `Txn` (the request path's
  `specRead`) is unchanged.
- **Reader slots**: `GetLease` and `Lookup` take `le.mu`'s read lock, which Perennial's
  `RWMutex` spec meters (`ownRWMutex`). The store keeps one slot (`lessorRdOf`, in its writer's
  resource: `GetLease` is called by `put` and `delete`, so no delete spec changes); the owner one
  (in `lessorUser`, for `Lookup`). Slots name the lessor through the ghost map's pinned element
  (`lessorPin`), so the owner's resource names `γl` only. *Rejected:* a slot in the delete specs
  (it reaches the request path's `DeleteRange`).
- **`Revoke` and `Grant` stay assumed, now honest about the live set**: `Grant` only adds (the
  granted lease in the new set); `Revoke` removes the lease and keeps the state's leases live,
  the coupling of the lease's item set (`l.Keys()`, maintained by mvcc's `Attach`/`Detach`) with
  the store's keys that its deletions rely on, stated as its contract. The apply level's
  `Lookup {{ True }}` (with `leaseIs`) is left as it was: the proved `Lookup` needs a reader slot.

### The lessor's apply-side methods (unit 9, 2026-10-13 · adopted)

- **More of the lessor under `le.mu`, its statements unchanged** (`lessorExtra lp M q`, a new last
  conjunct of `lessorMu`): `demotec`, the expiry notifier (`notifierAt`: its map holds exactly the
  queue's items, each under its own id, each item's `index` its position: what `heap.Fix(&q,
  old.index)` needs to stay in range), the checkpoint heap (a queue of items), `cp`, and every
  granted lease's `leaseMeta` (`ID`, `ttl`, `revokec` read-only; `remainingTTL`; the lessor's half
  of `expiry`). **`expiry` in two halves**: `refresh`/`forever` write it holding `le.mu` and
  `l.expiryMu`, `Grant` reads it under `le.mu` alone (`&LeaseWithTime{time: l.expiry}`),
  `Remaining` under `l.expiryMu` alone; `l.expiryMu` guards the other half (`leaseExpiry`).
  *Rejected:* `expiry` whole under `expiryMu` (`Grant`'s read would be unprovable).
- **The read-only configuration and the backend as separate persistent facts**, not in
  `lessorInv` (whose statement unit 8's specs, mvcc's and the txn package's use through
  `lessorRdOf`/`lessorUser`): `lessorCfg lp` (`minLeaseTTL`, `checkpointPersist`, `cluster` with
  its `Version()` contract, `checkpointInterval`, `lg`, `leaseRevokeRate`) and `lessorBackend lp P
  f`: `le.b` read-only and a **contract on the backend for the `Lease` bucket**
  (`leaseBackend b P f`: `BatchTx()` returns a transaction whose `LockInsideApply()`, under the
  batch lock's `mvcc.csContract P f Pre Q Post`, gives a token `Lk Post` that `UnsafePut` into
  `schema.Lease`'s bucket keeps and `Unlock()` turns into `Post`), as mvcc's `isKeyBackend` was
  for the store before `BackendBridge.lean`: not yet proved of the real backend. `le.b` read-only
  leaves `Recover` (which replaces it) out. *Rejected:* `lessorInv` parametrized by the backend
  contract (every unit-8 statement and, through `lessorRdOf`, mvcc's and the txn package's would
  change); the backend pinned in the lessor's ghost map (no simpler, and `Recover` breaks it
  too).
- **`container/heap` as the trust boundary, the notifier proved over it**: `heap.Push` and
  `heap.Fix` (names only: a standard-library package Perennial does not translate) are axioms
  over a generic `heap.heapIface h R E` (`Len` the length, `Less`/`Swap` called only in range,
  `Swap` the list swap, `Push` appends): the contents end a permutation (the heap order is not
  tracked). `&q` (a `*LeaseQueue`) meets it (`queue_heapIface`, from the proved `Len`, `Less`,
  `Swap`, `Push`), and `RegisterOrUpdate` is proved over it (the map/queue invariant through the
  permutation; an item the caller owns is not in the queue, `queue_item_fresh`). *Rejected:*
  `RegisterOrUpdate` itself an axiom.
- **What stays at the trust boundary** (axioms, each the function's documented behavior over the
  resources it touches): `schema.MustUnsafePutLease` (`proto.Marshal`; a put into `Lease`),
  `version.LessThan` (names-only `api/v3/version`), `scheduleCheckpointIfNeeded`
  (`int64(le.checkpointInterval.Seconds())`: Perennial's semantics has no float-to-integer
  conversion), `Promote` (float arithmetic, `time.Duration(rateDelay)`, `sort.Sort` by
  `Remaining()`, which read-locks each lease's `expiryMu`: a reader slot the invariant does not
  keep) and `Demote` (translated, not proved: `close(le.demotec)` needs the channel's close right,
  which a fractional lock invariant at any later-credit level cannot hold as is). The metrics are
  package facts (`leaseInit`: counters and a histogram whose `Inc`/`Observe` return).
- **The apply package's contract, derived where proved**: `apply.isApplyLessor`'s `Grant` returns
  a `leaseTTLIs` lease (its `ID` and `TTL()`: `Keys()` read-locks the lease's `mu`, a reader slot a
  grant does not hand out, and the apply package does not call it on a granted lease; was
  `leaseIs`); `apply.isApplyLessor_of_lessorInv` derives the contract of the real lessor from
  `lessorInv`, `lessorCfg`, `lessorBackend` and the contract's `Revoke` and `Lookup` clauses (the
  premises). The server's `lessorOk` is derived whole (`lessorOk_of_lessorInv`). Neither is yet
  used by the server's construction premise (`srvFieldsAt`/`isServerBuilt` still state
  `lessorOk`/`isApplyLessor`): the lessor's constructor is not proved.
- **`Revoke` is not proved** (translated): (1) it reads `le.rd` after unlocking `le.mu` (a data
  race with `SetRangeDeleter`/`Recover`: `issues/etcd-lessor-revoke-rd-unlocked.md`), so it needs a
  share of `rd` outside the lock, which unit 8's `SetRangeDeleter` spec (any caller) does not
  leave; (2) `le.rd()` is the store's write closure: its contract (`NewStore`'s closure over
  `store.Write`, under the sole-writer discipline) would have to be recorded by `SetRangeDeleter`;
  (3) `l.Keys()` read-locks the lease's `mu` (a reader slot per lease for the owner); (4) its
  `UnsafeDeleteLease` runs under the store transaction's batch lock, through `le.b` (the backend
  being the store's); (5) its postcondition (the state's leases still live after deleting `l`'s
  keys) needs the coupling of each lease's item set with the store's keys, kept by mvcc's
  `put`/`delete` through `Attach`/`Detach`; and `close(l.revokec)` a close right. Each is a
  design change across mvcc's and the txn package's statements; left as the contract's premise.
- **Noted for the expiry loop** (not proved): `revokeExpiredLeases` mutates the notifier
  (`Unregister`, `RegisterOrUpdate`) under `le.mu.RLock()`; safe in Go only because the loop's
  goroutine is the one reader that touches the notifier. A proof needs the notifier out of the
  fractional lock invariant (e.g. an invariant exchanging it for the write lock's or the loop's
  token).

### The auth store's request side (unit P2, 2026-10-14 · adopted)

- **The real store's methods, over contracts for what it calls through interfaces**, as unit 9's
  lessor: `authInv st R` holds the store's fields (the atomic `revision` in an invariant of its own,
  `lg`/`be`/`tokenProvider` read-only, `enabledMu` and `rangePermCacheMu` with their guards) and
  three contracts: the backend's read transaction (`authBackendOk be R`: `RLock` turns the caller's
  `R` into a held token, `UnsafeGetUser` keeps it, `RUnlock` gives `R` back; schema's
  `authBackend` would meet it over the backend's `readTx` with `R` its reader slot, but its
  `UnsafeGetUser` unmarshals an axiomatized `authpb.User`), the token provider (`info` returns an
  auth info with read-only fields, or nil), and each cached interval tree (`ivtQuery`: `Intersects`
  and `Contains` of a bytes-affine interval return, keeping its slices; `adt.ownIvt`, the tree's
  proof, is over string-affine intervals). *Rejected:* the backend contract with an IProp-valued
  token chosen by the store's invariant (one more parameter of every statement for nothing the
  proofs use); the trees' contract as `adt.ownIvt` (wrong comparables).
- **Results return nothing about the permission**: the contracts `isAuthStore`/`isReqAuth` only
  promise an error the gRPC layer can take, so the proofs show no panic and the frame, which is
  what lets `hasRootRole` be an axiom returning any boolean (its only work is on the axiomatized
  `authpb.User`).
- **The contracts cannot be derived as stated** (they take no resource), for two model reasons:
  `RWMutex` readers are bounded in Perennial (a reader slot per concurrent reader: `IsAuthEnabled`
  read-locks `enabledMu`, `isRangeOpPermitted` `rangePermCacheMu`, `isOpPermitted` the backend's
  read transaction), and `NewBytesAffinePoint`'s `make([]byte, len(key)+1)` needs `len(key) <
  2^63 - 1`, which every slice in memory meets but the model's `make` does not assume (unlike
  `append`'s length, `README.md`, "Model assumptions"). The derived forms take a reader resource
  `RD` (held and given back: the shape of the request path's `waitOk w RD`) and the key's bound;
  `isAuthStorePerms_of_authInv` and `isReqAuthR_of_authInv` derive them of the real store. *Not
  done here:* changing `isAuthStore`/`isReqAuth` to these forms, which threads a reader resource
  through the apply thread's and the request goroutines' resources (as `srvRdCall`) and the key
  bound through the request checks (a key is a request's bytes: the bound is a fact of the gRPC
  layer's decoding). *Rejected:* the reader slots in the store's invariant (a slot is held across
  the call: unboundedly many concurrent requests would exhaust any finite supply).
- **`metadata.FromIncomingContext`'s axiom states non-empty value lists**, narrower than grpc's
  code (which copies any context's metadata): `AuthInfoFromCtx` indexes `ts[0]`, a panic on a
  context built with an empty list (`issues/etcd-auth-token-md-empty.md`); grpc's transports build
  each key from at least one header field. *Rejected:* a premise on the context in `isReqAuth`
  (the request path's contexts come from grpc's handler axioms, which would have to state it).
- **`AuthInfoFromTLS` is the trust boundary whole**: `credentials.TLSInfo`, `tls.ConnectionState`
  and `x509.Certificate` are axiomatized types (no field of them steps), and its one-result type
  assertion panics for a peer with other credentials (`issues/etcd-auth-tls-info-assert.md`;
  unreachable in etcd's servers): the axiom states only its result.
- **The auth package's instance moved to `auth/Base.lean`** (from the apply package's `Base`, which
  imports it): its facts are its own error variables (`authErrVar`, the shape of `errVarLeaf`,
  which it cannot import: the apply package imports it) and `rpctypes`' token keys (another
  package's variables, stated here as the txn package states its foreign errors).
- **A proof note**: Perennial's `wp_apply` fails (silently, or with "unknown free variable") on a
  hypothesis whose precondition is an `IProp` bound by the proof (the contract's token `Tk` from
  `icases %Tk`); the proofs use `wp_bind` and `iapply` there.

---

## The request path, closed: delivery, the premises kept, and why

**2026-10-13 · adopted (the request path's unit 4d)** (`notes/STATUS.md`, "Unit 4d: the
wrap-up", "The request path: results and premises")

**Delivery: the wait registry's ghost state tells live from gone.** `IsRegistered` was "some
boolean", so the apply thread's skip of a side-effect-free entry (and `SkipRangeExecution` of a
transaction) said nothing about the waiter. Each shard now records every registration it ever had
(`γr`: id ↦ the consumer token's name and a flag), with the flag exclusive while the id is in the
live map and discarded once a `Trigger` takes it out; a reader who knows the registration
(`waitRegd`) and does not find the id gets the discarded flag (`waitGone`). The shards' names are
recorded in the wait's ghost map (`k ↦□ (γs, γr)`): without that pin a reader's slot and a
writer's shard view, each an existential, could not be shown to name the same maps. The clause is
optional in the caller's knowledge (`ot : Option GName`), so the apply loops, which do not learn
the registration (the raft contract's claims are made before `Register`), keep the old triple
(`none`), and `request_delivered` states the delivery at a known registration (`some t`).
*Rejected:* a persistent "absent" fact without the registration in the precondition (false of a
later registration of the id); a value-changing persistent element (`id ↪□ (t, live)`: persistent
elements do not change; the flag is a separate one-shot ghost variable); carrying the registration
through the raft contract now (it would change the claims, `idClaim`'s value, for a result the
loops do not need yet: the retargeting of raft to v3.7 is where the contract changes).

**`storeSmall` stays a physical premise.** The write budget (`2^64 ≤ N` tokens, one per applied
entry) bounds entries, not changes: one entry's `Txn` carries up to `--max-txn-ops` changes per
nesting level, so no bound below `2^62` changes follows. An etcd store with `2^62` changes does
not exist (revisions are `int64`, each change costs bbolt bytes); the discharge would be a change
counter in mvcc's store invariant bounded by the revision. Not done: it touches mvcc's invariant
(the mvcc session's) for a bound no execution reaches.

**The `%w` limitation stays documented, not redesigned.** Perennial `a54e1999f`'s `fmt.Errorf` is
`errors.New(format)`: no `*fmt.wrapError`, no `Unwrap`. A faithful axiom (`Errorf` with `%w`
returns an error whose `Unwrap` is the argument) would contradict the model's body, whose result's
method set has no `Unwrap`; so the canceled read's error stays an `*errorString` leaf in the model
(`codes.Unknown` in the model, `codes.Canceled` in Go; no stated result names the code). The fix
is Perennial's (its model building `wrapError`), a follow-up there.

**`raftRequestAlarm` stays a contract.** The id credit is available (`□ |==> idCred`) and
`isServerReq` could ride in `applyRes`, but `raftRequest` holds a reader slot of `leadTimeMu` for
`parseProposeCtxErr`, and Perennial's `RWMutex` lends a bounded number of slots, each kept for the
reader's lifetime; the apply thread spawns an unbounded number of alarm goroutines (one per
NOSPACE entry until the alarm applies), none of which returns its slot. A persistent read
permission in Perennial's `RWMutex`, or a bound on the alarm goroutines, would let it be proved.

**The construction premise is planned, not proved.** `isServerBuilt`'s clauses map to `NewServer`
and `bootstrap` (STATUS's table): most from existing results (`server_kv_backend`, the
consistent index, `NewUberApplier`, `NewGenerator`, `NewNotifier`) and ghost allocation, four
needing contracts of names-only constructors (lessor, alarm store, auth store, transport,
compactor, stats, cluster version), three premises no `NewServer` proof can discharge (the raft
contract, the id budget, `storeSmall`).

## The client's model as a class the server instantiates; the wire as the handler's theorem transported

(The vertical slice's unit V1, 2026-10-13; `notes/STATUS.md`, "The vertical slice: client to
server".)

**A class, not axioms.** The clients' fourteen axioms about etcd (`etcdState` and its laws,
`etcdReachedAt`, `etcdRevToken`, `EtcdStep` and its laws) are the fields of `class EtcdModel GF`,
a section variable of every client file that reaches them; the server's `etcdModelOfServer E` is a
`def`, applied where the slice is stated, not an `instance` (a client result is about any model;
the slice picks the server's). A field is the real fact: `etcdState` is a certified log's state at
the revision restricted to the prefix, `EtcdStep` a certified log's events under the prefix
between two revisions, `etcdRevToken` a ghost token the apply thread mints when the log grows,
`etcdReachedAt` a certified log having the revision. Nothing is `True` or `False`.

**`EtcdStep` became an `IProp`.** The server's step is a fact about its certified log, a ghost
lower bound; a pure proposition cannot refer to it. The cost: `TailOk`/`WriterOk`/`CursorOk` in the
cache's watch loop became persistent, timeless `IProp`s, and the pure lemmas over them
entailments. The alternative, a `Prop` field quantifying over "the" server log, has no log to
name.

**`LogSmall` in the state, not `NoDupKeysPerRev`.** `etcdState_revs`' positive version holds of a
log that writes each key at most once per revision, which etcd's server does not guarantee (two
known `checkIntervals` gaps); it holds too of a log of at most `2 ^ 62` changes (the version
counts puts), which the read path already assumes (`storeSmall`). So `etcdState` carries
`LogSmall`, and the server's results producing it take `storeSmall` (from `isServerRead`).

**The state at a revision of a certified log, not of a certificate of that length.** `etcdState
rev` is `underPfx pfx (stateAt log rev)` for some certified `log` with `rev < |log|`; the brief's
"a certificate of a log of length `rev + 1`" needs a certificate of a prefix, which mvcc does not
provide (its history and event lower bounds would need prefix lemmas), and says the same.

**The token where the log grows.** `apply.Apply` is the apply package's, which knows nothing of
clients; the server's `applyEntryNormal` holds the authority (`revAuth`, in `srvApplyKV`) and mints
after `Apply` returns, from `applyStep_grow` (a step appends at most one revision). The token rides
the entry's result through the wait (`resultIs`), delivered once, to the handler's answer. A
revision no request awaits (a lease revocation's) mints a token no one receives: exclusivity needs
only that keys never repeat.

**The wire is the handler's theorem, transported.** The generated gRPC stub is names-only; its four
methods are axioms stated as the server's end-to-end theorems with the server-side resources
removed and the response the client's fresh copy (the same field formulas), at committed index
`0` (a fresh handler knows none), the revision field without the store's reader slot
(`hdrRevC`), and errors only as non-nil (gRPC transports a status, not a value). The connection is
one opaque predicate (`grpcConnTo`) inside `connectedTo` with the server facts the theorems
assume. The axioms' premises (the per-call pool, the transport's integrity, protobuf round-trips)
are stated in prose: they are what a proof of gRPC and protobuf would discharge. What the
transported statements do not give the clients' contracts (linearizability's `lo ≤ r`, mainly)
is listed in STATUS rather than weakened in the contracts.

**Superseded at the merge of unit C1 (2026-10-14).** The wire above (`grpcConnTo`, `connectedTo`,
the stub's four axioms, `isKVClient`) is gone: unit C1 translated the generated stub and proved
`kVClient.Put`/`Range` down to grpc's `ClientConn.Invoke`, whose contract (one axiom) and the
connection predicate `isKVConn conn K` are the lower boundary now ("The client meets the server
(unit C1)" below; STATUS, "Merge of `origin/lean` (units 8, 9, C1)"). The class, the server's
instance and the token's path stay; `DeleteRange`/`Txn` stubs are V2's to prove in C1's style.

## The client meets the server (unit C1)

**2026-10-14 · adopted (unit C1)** (`notes/STATUS.md`, "Unit C1: the client meets the server")

*Superseded in part* (2026-10-14) by "A generic gRPC specification" (below): the `Put`/`Range`
axiom, the connection `isKVConn`, the run premises `putRunOk`/`rangeRunOk` and the runtime's
resources `K.R` ("What a call gives", "The runtime's resources are the server's premises" below)
are replaced by the generic contract; the boundary's position, the wire, the retries, the call
options and the context errors stand as written.

**The trust boundary is grpc's `ClientConn.Invoke`, interceptors included.** The client's KV path
is verified from `kv.Put`/`kv.Get` down to the generated stub (`kv.Do`, `ContextError`, the retry
client, `kVClient.Put`/`Range`, `NewKV`, `RetryKVClient`, `NewKVClient`, `withRepeatablePolicy`);
what is assumed is one call, `(*grpc.ClientConn).Invoke` of the KV service's `Put` and `Range`
(`Spec/google_golang_org/grpc/ClientConn__Invoke.lean`, an axiom): the network, grpc's client and
server, the protobuf codec, the client's retry interceptor (installed at dial, `client.go`), and the
server's runtime (its gRPC server's per-call goroutines, its unary interceptors, the quota wrapper
`quotaKVServer`). *Rejected:* the boundary below the interceptor (a contract of grpc's `invoke`,
the interceptor proved): the interceptor's loop reads the auth token (`shouldRefreshToken`,
`refreshToken`, through the client's auth client), logs through zap, backs off with timers, filters
call options by type assertion; proving it is a unit of its own, and what it would discharge is
stated below.

**What a call gives: a run of the handler on a copy, or an error.** The connection
(`isKVConn conn K`, an axiomatized persistent predicate: a fact about a grpc object and the process
at its other end, like bbolt's predicates) names the server's handlers (`K.put`, `K.range`:
function values) and what the server's runtime gives each run (`K.R ctx'`). `Invoke`'s triple takes
the caller's request (`inp ↦ req`, owned: protobuf's marshaling writes its size cache) and a zero
reply (`out`, owned), and a persistent premise `putRunOk K o Q` (`rangeRunOk`): the handler's
triple, with `K.R ctx'` and a fresh decoded copy of the request (`txn.putRequestIs r o`, the
server's own predicate: the copy's fields read-only, its size cache in an invariant, at the
server's model of the request, `putReqOp`/`rangeReqOp`), whose success gives a response message
(`putRespMsg resp m`, `rangeRespMsg`: every field the wire carries, read-only) with the caller's
persistent knowledge `□ Q m`. It returns `nil` and `out` holding the same message with `□ Q m`, or a
client error (`clientErr`) and nothing. The run premise is persistent because the handler may run
several times; `Q` is persistent so that nothing of the runtime's resources leaks to the client.
*Rejected:* the axiom stated over the server's predicates (`isServerReq`, `kvServerAt`, the
answers `putAppliedOk`, ...): it would put the server's whole model in the trust base; with the run
premise the client's results discharge it from `put_end_to_end`/`range_end_to_end` (proved), and
the axiom says only "the server runs its handler on a copy". A deep-copy relation between the
server's response and the reply: the message predicates are read-only field contents (no
ownership, no server-side resource), so the same predicate holds of both, which a copy relation
would only restate.

**The wire.** The server's model of the client's request is that of a copy: its range end is the
contents of `RangeEnd` (`rangeReqOp`; protobuf does not carry an empty bytes field, which the
server decodes as `nil`, and `txn.rangeEndOf nil [] = []`), its key the contents of `Key`
(`nil` and empty agree); a slice's identity is not on the wire. The reply's message predicates say
contents only, for the same reason.

**Retries.** The interceptor's attempts are inside the boundary. A `Range` (`withRepeatablePolicy`)
is retried on `Unavailable`; a `Put` (`nonRepeatable`) on "no connection/address available"
(`isSafeRetryMutableRPC`: the request was not sent) and also, whatever the policy, after a gRPC
`Canceled` or `DeadlineExceeded` while the caller's context is live (`issues/
etcd-client-retry-put-ctx-error.md`: a branch for a per-attempt context etcd no longer has;
reproduced: a mock server receives the `Put` twice). The contract says what this allows: a
successful reply is the last run's (the interceptor returns at the first `nil`, and grpc's codec
resets the reply before unmarshaling), earlier runs may have happened and may have applied the
put; an error says nothing about any run.

**The runtime's resources are the server's premises, stated per run.** etcd's handlers need, per
call, a context (`isContext` of the stream's context), one id credit, reader slots of
`leadTimeMu`, the store, the logger's lock and the read loop's lock (`srvCall`, `srvRdCall`); a
server-side caller obtains them from the server's runtime, which nothing here models. So `K.R ctx'`
is given to every run by the axiom: for etcd's server (`client/v3/Results.lean`, `etcdKVConn`)
`srvCall s ρ ctx' ∗` the reader slots of `srvRdCall`. This is the same idealization the server's own
results make (`isServerBuilt`'s id budget `□ |==> idCred ρ.ids 1`, `notes/STATUS.md`: the
generator's `2 ^ 48 - 1` ids are assumed not to wrap), and the reader slots come back from each
run (the handler's triple returns them), so the bound Perennial's `RWMutex` puts on concurrent
readers is not reached by the runtime's own accounting. The committed index a linearizable read
knows of is not the runtime's: `committedAtLeast γr c` is the client's (persistent; `0` is free),
so `K.R` does not mention `c` and `kvServerAt` is used at any `c` (it reads only `revR`,
`kvServerAt_srvKVAns`).

**Call options and context errors are typing premises.** `Invoke`'s frame needs that no call
option writes the caller's memory (grpc's `Header`, `Trailer`, `Peer` options do): `callOptOk`
admits grpc's scalar option types (the stub's `StaticMethodCallOption`, `client.go`'s
`defaultCallOpts`) and a `retryOption` whose closure writes only the interceptor's `retryPolicy`
(`withRepeatablePolicy`'s, proved). The client's call-option slice is full (`len = cap`, as
`client.go` builds it): `retryKVClient.Range` appends `withRepeatablePolicy()` to it, which with
spare capacity would write the slice's shared backing array from concurrent calls (grpc's own
`combine` copies for this reason). `ContextError` hands its result, possibly the context's error,
to `errors.As` on `kv.Put`'s second `ContextError`; `ctxErrClient` (a premise of `kv.Put`/`kv.Get`)
says the context's `Err()` returns client errors and keeps returning one once it has: Go's
documented contract and the method sets of `Canceled`/`DeadlineExceeded`, which the model lacks
(as `clientErr` itself, which `rpctypes.Error`'s axiom now carries: an `EtcdError` is a leaf error).

**A future proof of the interceptor would discharge** the retry part of the axiom: from a contract
of grpc's plain `invoke` (one attempt: a run on a copy or an error, the same shape), the loop gives
"the last attempt's run, earlier attempts' runs unknown"; the options' filtering (`filterCallOptions`,
a type assertion on `retryOption`) would discharge `callOptOk`'s retry case; the token refresh
needs the auth client's contract. What stays assumed is grpc's transport and the server's runtime
(`isKVConn`: the dial, the registration, the runtime's resources).

**What C1 does not state.** Only a single-endpoint connection to one server (a client with several
endpoints balances attempts over members: unit C2's cluster-level contract), only a `Get` without
a sort option (`Op.IsSortOptionValid`'s sort case reads `etcdserverpb`'s enumeration maps, package
facts not stated), only `Put` and `Get` (`kv.Do`'s delete and transaction cases are not specified:
the precondition `doRunOk` rules them out).

## A generic gRPC specification

**2026-10-14 · adopted** (`notes/STATUS.md`, "Unit C1", "The generic gRPC specification")

*Superseded in part* (2026-10-14, unit P3b) by "The server end of the gRPC boundary" (below): the
server side (`grpc.serve`, `grpcListener`, the handler's level) is now grpc's runtime running the
generated handler with `dec` and the interceptor chain.

*Superseded in part* (2026-10-14, unit P3a) by "The retry interceptor proved: the gRPC boundary
below it" (below): the client axiom is now grpc's `Invoke` as the interceptor chain over one
attempt; `isGrpcConn` is replaced by `grpcConn` and the client's `isEtcdConn`. The server side,
the messages, the registration and the specs stand.

**The user's request:** one gRPC axiom for every operation, in the shape of Grove's urpc (Rocq,
`urpc_proof.v`/`urpc_spec.v`): a method's spec registered persistently, a client call of any
registered method, the server proving its handlers against the specs. The vocabulary is
`Proof/google_golang_org/grpc/InvGrpc.lean`; the client axiom
`Spec/google_golang_org/grpc/ClientConn__Invoke.lean`.

**Predicate transformers, as urpc's underlying layer.** A method's spec is
`Spec : Req.M → (Rep.M → IProp) → IProp` (`GrpcSpec Req Rep`) over the request's and reply's
*models*: `Spec m Φ` is what a caller asking `m` gives for an answer `m'` with `Φ m'` (urpc's
`is_urpc_spec_pred`, a saved spec; the `RpcSpec` record with a witness type and `Pre`/`Post` is a
special case, `Spec m Φ := ∃ x, Pre x m ∗ ∀ r, Post x m r -∗ Φ r`, and was dropped). The client
gives `□ ▷ Spec m Φ` (the □ pays for redelivery: the retry interceptor's attempts; the ▷ as in
urpc's `wp_Client__Call_pred`) and, on success, gets `∃ m', Rep.recv out m' ∗ Φ m'`. No saved
predicate is needed: the spec is a parameter of the registration (`isGrpcRpc addr name Spec :=
∃ h S, grpcServes addr name h S ∗ grpcHandlerOk h S Spec`), not ghost state, so two specs of one
method are two facts about the one handler served there, both sound.

**Messages** (`ProtoMsg`): a Go type `T` (passed as `*T`), the model `M` of its wire content,
`send l m` (the sender's message: what marshaling needs, owned, returned by the call), `recv l m`
(a decoded copy: read-only, persistent), `blank l` (a zero `*T` the receiver owns). Each instance
asserts that the codec's copy of a `send` at `m` is a `recv` at `m`; that is not checkable without
a codec model, so **the instances are trusted wire models** (`pbPutRequest`, `pbRangeRequest`,
`pbDeleteRangeRequest`, `pbPutResponse`, `pbRangeResponse`, `pbDeleteRangeResponse` in
`client/v3/InvKVConn.lean`; a wrong instance, e.g. `recv := False`, would make every handler meet
every spec). They are C1's predicates repackaged: a request's model the server's (`putReqOp`,
`rangeReqOp`, `deleteReqOp`: `OpFull`), its decoded copy the server's own `txn.*RequestIs`, a
response's model every field the wire carries, `send = recv` (C1's read-only `putRespMsg`, ...;
the runtime writes the response's size cache, which nothing owns after the handler: inside the
boundary, as in C1).

**The server side and its resources.** A handler `h` (a unary method of the registered service
implementation, called `h ctx req`, returning `(resp, err)`) meets `Spec` with the per-run
resource `S` (`grpcHandlerOk h S Spec`, persistent): from `S`, `isContext` of the context the
runtime made, the decoded request at `m` and `Spec m Φ`, it returns `S` and, on success, a
response `Rep.send resp m'` with `Φ m'`. The one server-side axiom, `grpc.serve addr ms S n`
(in `InvGrpc.lean`): a server holding the listener at `addr` (`grpcListener addr`, exclusive,
urpc's `host c↦ ∅`: one registration per address) that registers the methods `ms` (distinct full
names), each handler meeting its spec with `S`, and hands the runtime `n` copies of `S`, is served:
`grpcServes addr m.name m.handler S` (persistent, opaque) for each; `grpc_serve_rpcs` derives
`isGrpcRpc`. The pool is the honest account of the runtime's resources: a run holds one copy and
gives it back, so the runtime is assumed to run at most `n` handlers at a time. For etcd the copy
is `etcdRunSlot` (the reader slots of `s.leadTimeMu`, the store, the logger and the read loop:
bounded `RWMutex` slots, passed explicitly, never duplicated; Go's own `RWMutex` admits at most
`2 ^ 30` readers, so a bound of that order is a real limit of the server, not only of the proof);
the id credit a run consumes is minted from the server's `□ |==> idCred ρ.ids 1` (`srvStarted`'s,
the server's existing idealization), and the context comes from the runtime. *Rejected:* C1's
`K.R` given freely to every run (an unbounded supply of reader slots); the slots' count in the
spec visible to the client (the client sees only `Spec`).

**The handler's level: the service method.** The handler registered is `kvServer.Put` (`Range`,
`DeleteRange`) at the server's `*kvServer`, as in C1. Between grpc's runtime and it are etcd's
generated `_KV_Put_Handler` (`rpc_grpc.pb.go`: `dec` into a new `*PutRequest`, then the
interceptor or `srv.(KVServer).Put`), the server's unary interceptor chain (`v3rpc/
interceptor.go`: logging, metrics, the leader/learner checks) and the quota wrapper
`quotaKVServer` (which may answer `ErrNoSpace` without running the handler); all three stay
inside the boundary, assumed transparent on success (a success is the handler's). *Rejected for
now:* the boundary at `MethodDesc.Handler` (`_KV_Put_Handler` proved, grpc's `dec` closure a
generic codec contract): it would verify only the generated dispatch, and still need contracts for
the interceptor chain and the quota wrapper (etcd code, not translated); a later unit can move the
boundary there without changing the client's side.

**The client side: one axiom.** `grpc.ClientConn.Invoke.spec` is stated for any method, request
and reply types and spec: `isGrpcConn conn addr` (persistent, opaque: the `*ClientConn` reaches
`addr`; established by the unverified `clientv3.New`, a premise like C1's `isKVConn`),
`isGrpcRpc addr method Spec`, `□ ▷ Spec m Φ`, `Req.send inp m`, `Rep.blank out`, the call options
(`callOptsOk`); it returns `Req.send inp m` and `nil` with `∃ m', Rep.recv out m' ∗ Φ m'` (the last
run's) or a client error and nothing. C1's honest retry semantics stand (other runs may have
happened; `issues/etcd-client-retry-put-ctx-error.md`). The client's stack (the stub, the retry
client, `kv.Do`, `kv.Put`, `kv.Get`) is proved for any spec of the method and any `Φ`; the
results instantiate etcd's specs (`client/v3/Results.lean`: `etcdPutSpec`, `etcdRangeSpec`,
`etcdDeleteSpec`), and the client's end-to-end results take the registration and the connection as
premises, the server's facts having moved to `etcd_kv_served`.

**What the trust base is now:** `Invoke`'s axiom, `grpc.serve`, the opaque `grpcListener`,
`grpcServes`, `isGrpcConn` (and the two persistence facts), the message instances, `StaticMethod`.
Gone: the `Put`/`Range` clauses of `Invoke`, `isKVConn`. A new method (`Txn`, `Compact`, another
service) needs its message instances, its spec and its handler proof (`etcd_deleteHandlerOk` shows
it for `DeleteRange`), no new axiom.

**The revision's token under the generic spec** (merge with the slice's unit V1, 2026-10-14):
V1's per-revision token (`revMinted`, exclusive) was dropped under C1's wire, whose `putRunOk`
asked for persistent knowledge (the transport may run the handler more than once). Under the
generic spec it is carried: a run's `Spec m Φ` is consumed by that run, the client supplies
`□ ▷ Spec m Q` (one per attempt) and receives one reply's `Q m'`, which need not be persistent.
So `etcdPutSpec`/`etcdDeleteSpec` give `putReplied`/`deleteReplied` (the persistent
`putReplyOk`/`deleteReplyOk` and the token), and `client_put_end_to_end` returns the token of the
revision its reply reports.

## The retry interceptor proved: the gRPC boundary below it

**2026-10-14 · adopted** (`notes/STATUS.md`, "Unit P3a")

**The boundary is grpc's `invoke`, one attempt; the interceptor chain is stated as grpc composes
it.** grpc's `ClientConn.Invoke` (`call.go`) runs `cc.dopts.unaryInt(ctx, method, args, reply, cc,
invoke, combine(cc.dopts.callOptions, opts)...)`, where `unaryInt` is built at dial by
`chainUnaryClientInterceptors` from `WithUnaryInterceptor`'s interceptor followed by
`WithChainUnaryInterceptor`'s (the first called with an invoker, `getChainUnaryInvoker`, that runs
the rest and finally `invoke`). The one client axiom (`Spec/google_golang_org/grpc/
ClientConn__Invoke.lean`) says exactly that, for any method and any chain: `grpcConn conn addr ics
dopts` (opaque, persistent: the chain `ics` and default options `dopts` the connection was dialed
with) and, for any postcondition, `WP Invoke` follows from `chainWP conn ics inv ...` for every
invoker `inv` meeting `grpcInvokerOk` (`InvGrpc.lean`). `chainWP` is recursive on the chain: with
no interceptor, the invoker's call; otherwise the first interceptor's call with an invoker `inv'`
of grpc's making, about which the interceptor knows only that its calls are the rest of the chain
(`□ ∀ args, chainWP rest inv args -∗ WP (inv' args)`); `grpcInvokerOk_of_wp` transports the
attempt contract to such an `inv'`. *Rejected:* stating the axiom for etcd's single interceptor
only (the brief asks for grpc's composition; a client with chained interceptors would need a new
axiom); an axiom per `getChainUnaryInvoker` closure (the recursion would be grpc code to verify
with no gain: it is one line).

**One attempt** (`grpcInvokerOk conn addr inv`, a definition, the contract grpc's `invoke` is
assumed to meet): for a method registered with `Spec`, a request `Req.send inp m` (returned), a
reply buffer `Rep.own out` (a new `ProtoMsg` field: owned at any content; a zero reply,
`Rep.blank`, is one, `blank_own`), the caller's `□ ▷ Spec m Φ` (persistent: grpc's own transparent
retries, and a service config's retry policy, may deliver the request again within one `invoke`),
and call options grpc applies (`grpcOptOk ps`: holding only scalars, or `grpc.Peer(p)` options for
buffers `p ∈ ps`, owned and returned, `grpcPeerBuf p`: the zero peer or one grpc wrote,
`grpcWrotePeer`, opaque): `nil` with `Rep.recv out m' ∗ Φ m'`, or a client error grpc's `status`
accepts with `out` back. The peer buffer is owned because grpc's `PeerCallOption.after` writes it;
`peer.Peer.String` (an axiom) reads it. *Rejected:* `Spec m Φ` (not persistent) per attempt: true
of `invoke` only without grpc's internal retries, which a dial option enables.

**The interceptor's contract** (`etcdInterceptorOk ic`, `client/v3/InvKVConn.lean`): unit C1's
`Invoke` contract with the invoker and the connection as arguments: for any connection (`grpcConn`,
for `cc.Target()`) and any invoker meeting `grpcInvokerOk`, the call with the client's options
(`callOptsOk`), the request, a zero reply and `□ ▷ Spec m Φ` returns `nil` with the last attempt's
reply and `Φ`, or a client error. `Client.unaryClientInterceptor` returns such a closure
(proved); the client's connection is `isEtcdConn conn addr := ∃ ic, grpcConn conn addr [ic] [] ∗
etcdInterceptorOk ic`, a definition: what `clientv3.New` dials (`dialSetupOpts`), given no
`Config.DialOptions` adding interceptors or default call options (an assumption about the
unverified constructor; `issues/etcd-client-dialoptions-unary-interceptor.md`: a
`WithUnaryInterceptor` there replaces the retry interceptor). `etcdConn_Invoke`
(`client/v3/EtcdInvoke.lean`) derives unit C1's statement from the axiom and the contract; the
stubs use it, so the client's results are unchanged in form, their premise `isGrpcConn` (opaque)
now `isEtcdConn` (defined), and errors also `statusErrOk`.

**Inside the interceptor's proof.** The loop is proved with the invariant: the attempt counter,
`lastErr` (`nil` only before the first attempt, otherwise a client error grpc accepts), the
request, the reply buffer and the peer buffer. Each attempt reuses `□ ▷ Spec m Φ`; a context
error with the caller's context live (`ctx.Err() == nil`, `isContext`'s `Err` triple) continues,
whatever the policy (`issues/etcd-client-retry-put-ctx-error.md`): the contract allows it. The
options: the interceptor's own (`reuseOrNewWithCallOptions(defaultOptions, optFuncs)`, a package
fact for `defaultOptions`, the dial's options' closures `optApplyOk`) and a call's (its
`retryOption`s, `retryApplyOk`: they write only `retryPolicy`) are read-only once built
(`retryOptsAt`), their backoff function one that returns (`optionsOk`, for the axiom
`waitRetryBackoff`). The client (`retryClientOk`): its logger, `Token` and `authTokenBundle`
(read-only since `New`, a bundle whenever a token: what `getToken` needs not to panic).

**The trust base it adds.** grpc: `Peer`, `peer.Peer.String`, `ClientConn.Target`, `status.Code`;
Go's `errors.Is` of a status error against an `EtcdError` value or a pointer (`errors.IsStatusErr`:
Perennial's `wp_Is` needs a pointer target and the error tree; an `EtcdError` is a comparable
struct); zap's `Uint`; etcd functions kept names-only: `waitRetryBackoff` (a timer and a `select`,
the backoff function's float jitter), `withVersion` (grpc's `metadata`: a value context, same
`Done`/`Err`), `getToken` (the auth client: an `Authenticate` RPC through the same connection, its
interceptor included), `Endpoints` (a read under `epMu`'s read lock: Perennial's `RWMutex` readers
hold bounded, exclusive slots, which a persistent closure cannot carry). *Rejected:* proving
`Endpoints` with a reader slot in the interceptor's contract (it would thread a slot through every
caller of `Invoke` for a log line's condition).

**Errors grpc's `status` accepts** (`statusErrOk err`, `cache/v3/Base.lean`; unit P3a also fixed
`rpctypes.Error`): `status.FromError`/`Code` call the error's `Error()` and (through a type
assertion) `GRPCStatus()`, and `errors.As` on it; `errors.Is` calls its `Is`. So the premise is:
`nil`, or a leaf error (no `Unwrap`/`As`) whose `Error()` returns and whose `GRPCStatus()` and
`Is(error)`, if its method set has them, return (`grpcErrMethodsOk`, conditional on
`methodSet`, which the model leaves uninterpreted: an error known to lack them, an `EtcdError`, by
the package fact `rpctypesEtcdErrorTy`, satisfies it vacuously). It travels with `clientErr`
through every error the client returns or receives (grpc's, the context's via `ctxErrClient`, a
watch's close error, a leasing transaction's).

## The server end of the gRPC boundary

**2026-10-14 · adopted** (`notes/STATUS.md`, "Unit P3b")

Supersedes the server side of "A generic gRPC specification" ("The server side and its
resources", "The handler's level: the service method"): the boundary is now grpc's server
runtime, below etcd's generated handlers, the quota wrapper and the unary interceptors.

**grpc runs the `MethodDesc.Handler`.** grpc's `processUnaryRPC` calls, for a registered unary
method, `md.Handler(srv, ctx, dec, s.opts.unaryInt)`: the generated handler of the registered
`ServiceDesc`, the service value given to `RegisterService`, a `dec` closure over the request's
bytes, and the interceptor `chainUnaryServerInterceptors` built (`nil` for none, the interceptor
itself for one, a closure over `getChainUnaryHandler` for more). The axiom `grpc.serve` says
exactly that, for any service: a run of `m.handler` on `m.srv`, the run's context, a `dec`
meeting `grpcDecOk` (it decodes the request at the call's model into a zero `*T` it is given: the
codec's unmarshaling, part of the trusted wire model as the message instances are) and an
interceptor meeting `grpcSrvChain ics` (the chain as grpc composes it, `srvChainWP`, mirroring the
client's `chainWP`), with one of the `n` run slots. *Rejected:* the chain as an assumed contract
of etcd's interceptors (they are etcd code, now proved); an axiom per number of interceptors (the
composition is one recursive definition).

**The server object.** `grpcServerAt addr ics regs` (opaque, exclusive; it was `grpcListener
addr`) is the server built with the chain `ics`, its registered unary methods `regs` (full name,
`MethodDesc.Handler`, service value); `grpc.serve` takes any methods among `regs`, with distinct
names. It is a premise of the server's result, established by unverified code (`v3rpc.Server`,
`grpc.NewServer`, `RegisterKVServer`, `Serve`), as the client's `grpcConn` is of `clientv3.New`.
The ghost step keeps the result's form (`etcd_kv_served` gives `isGrpcRpc`); without `ics` and
`regs` in the predicate the axiom would let a proof pick an interceptor-free chain or another
service value than the one registered. *Rejected for now:* proving `RegisterKVServer` against a
`RegisterService` axiom (it needs that axiom and two method-set facts, `srv.(interface{
testEmbeddedByValue() })`): it would only prove the `KV_ServiceDesc` fact `etcdKVRegs` states.

**Transparent interceptors.** An interceptor's contract (`srvInterceptorOk ic R Q`) is
"transparent": called with its per-run resource `R`, it calls the handler once on the same
context and request and returns its result, or returns `(nil, err)` for a non-nil `err` without
calling it; `R` comes back either way; the caller gives both continuations (`∧`). `Q` is what it
reads of the request: etcd's learner check (`isRPCSupportedForLearner`) reads a `*RangeRequest`'s
`Serializable` (`learnerReqOk`), which the generated handler has from the decoded request. A chain
of such interceptors runs the handler or fails (`srvChainWP_of_ok`), with the resources of all.
The log interceptor's `R` is a reader slot of `s.lgMu` (`s.Logger()` after the handler); the
server's run slot (`etcdGrpcSlot`) holds the handlers' slot, one more `leadTimeMu` reader slot
(the quota's NOSPACE alarm, `raftRequest`), and the interceptors' resources. grpc-prometheus's
interceptor (not etcd code) is assumed transparent (a premise). `logUnaryRequestStats` is a
names-only axiom: it reads the request and the response (`proto.Size`, the stringers), which the
message predicates do not cover field by field; after the handler both are read-only, which the
wire models already trust (the runtime's marshaling of the response).

**The quota wrapper.** `NewQuotaKVServer(s)` embeds `NewKVServer(s)`'s service in a
`*quotaKVServer`; its `Put` checks `qa.q.Available(r)` (the apply package's `apply.isQuota`, from
`storage.NewBackendQuota`'s axiom) and on failure raises the NOSPACE alarm (`s.Alarm`, an axiom
with `raftRequest`'s request-path premises: `Alarm` is `raftRequest` of an alarm request, which
`raftRequest`'s verified spec does not build) and answers `ErrGRPCNoSpace`; its `Range` and
`DeleteRange` are the embedded service's (Goose emits the promoted wrappers only for methods in
the translate list). The service value registered is the `*quotaKVServer`; that it implements
`KVServer` (the generated handlers' `srv.(KVServer)`) is a method-set fact, assumed as a class
(`QuotaKVServerIsKVServer`; `methodSet` is uninterpreted).

**What the trust base gains:** `grpcServerAt`; the names-only `EtcdServer.Alarm`,
`IsMemberExist`, `IsLearner` (with `membership.localKept`, an assumption that the local member is
not removed while the server serves: `issues/etcd-unary-interceptor-learner-removed.md`),
`api.IsCapabilityEnabled`, grpc's `MD.Get`, Go's `utf8.ValidString`, prometheus's
`CounterVec.WithLabelValues`, `logUnaryRequestStats`. Gone: `grpcListener`, and the generated
handlers, the quota wrapper and the interceptors from inside the boundary.

## Traces on the request path (unit P1b, 2026-10-14)

`pkg/v3/traceutil`'s `*Trace` methods read and write the trace's fields (`t.steps = append(..)`),
so a trace is a resource, not a fact. `Proof/go_etcd_io/etcd/pkg/v3/traceutil/Defs.lean`:

- **`ownTrace t e`** (exclusive): the `Trace` struct, its fields slice and its steps slice (with
  their capacities), each step's fields slice; `e` is the `isEmpty` field (written only at
  creation: `TODO()`'s traces are empty, `newTrace`'s are not; `EnsureTrace` keeps a context's
  trace only if not empty). Every method takes and gives it back (`Step`, `AddField`,
  `StartSubTrace`, ..., `StepWithFunction` lends it to its function); `LogIfLong` and
  `LogAllStepsIfLong` consume it (their logging aliases the steps' field slices, and nothing
  uses a trace after logging it).
- **`ownFields sl`**: a fields slice owned with its capacity, the values formattable by
  Perennial's `fmt` (`fieldsWf`: nil or a predeclared basic type), since `Step`/`InsertStep`/...
  keep the slice in the trace and `LogWithStepThreshold` formats it with `%v`.
- **`ctxTraceIs ctx o`** (persistent): what `ctx.Value(TraceKey{})` returns, `o = some t` (the
  trace `t`) or `none` (no trace: nil, another type, a nil `*Trace`). The context only names its
  trace; its ownership is held separately. Sources: `context.WithValue(parent, TraceKey{}, t)`
  (its spec, extended), any other `WithValue` and `Tracer.Start` preserve the parent's
  (`□ ∀ o, ctxTraceIs ctx o -∗ ctxTraceIs ctx' o`), `context.TODO()`/`Background()` carry none
  (`ctxTraceIs_todo`/`_background`, proved from `emptyCtx.Value`'s body).

**Who owns a trace** (the design default of the brief, kept): the goroutine serving the request.
`EtcdServer.Range`/`Txn` (premise `ctxTraceIs ctx ot ∗ ownTraceOpt ot te`; the gRPC handler's
context has none, `v3rpc.srvCall` now says so) make it with `EnsureTrace`, step it, lend it to
`doSerialize` (which steps it and hands it to `get`), whose `txn.Range`/`txn.Txn` find the same
trace in the context (`EnsureTrace` keeps a non-empty one: `⌜∀ t0, ot = some t0 → te = false →
trace = t0⌝`) and give it back; the deferred closure adds fields and logs it. **Inside mvcc** the
trace passed to `store.Read`/`Write` is owned by the transaction predicate while the transaction
is live (`isTxnRead`/`isTxnWrite`/... take a `trace` parameter and hold `∃ te, ownTrace trace te`;
`*_trace_acc` lemmas borrow it, e.g. for `getPrevKV`'s `StepWithFunction`, `executeTxn`'s
sub-traces, `put`'s `AddField`); `End` returns it. **The apply thread's traces** (`txn.Put` etc.
at `context.TODO()` make a fresh one) are handed to the request goroutine with the result: KV
methods' posts carry `apply.traceRes trace` (nil or owned), `dispatch` stores it in the result
(`apply.resTrace ar`), the wait's `resultΨ` carries it, and `raftRequest` steps and logs it
(`GetStartTime`/`SetStartTime`/`InsertStep`/`LogIfLong`). The read loop's per-iteration trace
(at `Background()`) stays in its goroutine. No trace is used by two goroutines at once: the
apply→request handoff is a transfer (the apply thread never touches `ar.Trace` after
`Trigger`).

`LogWithStepThreshold` stays at the trust boundary (`fmt` of `any`/`Duration`, `rand`, zap).
`InsertStep` (an overlapping `append`) was too until unit P4, which proved it over a lemma of this
repository, `wp_slice_append_shift` (`traceutil/SliceShift.lean`: `append(s[:a+1], s[a:]...)`
from Perennial's `wp_slice_copy_within` and `wp_slice_copy`; no Perennial change).

**The run's context** (with unit P1b's owned traces): a handler run is given, besides
`isContext`, `grpcRunCtx ci`: the context's `Value(k)` for a key of a named type of etcd's
packages (`go.etcd.io/etcd/...`) returns `nil`. grpc's server context carries grpc's own values
(metadata, peer, the stream) and those of what runs in front of the handler (stats handlers such
as otelgrpc's, etcd's `v3rpc` interceptors, none of which stores under an etcd key type), so this is
part of the trusted server runtime; it gives `traceutil.ctxTraceIs ci none` (`TraceKey`), what
`v3rpc.srvCall` needs. *Rejected:* `ctxTraceIs` itself in `grpcHandlerOk` (it would make grpc's
generic vocabulary, and every client spec mentioning `isGrpcRpc`, depend on `traceutil`'s
assumptions).

## A write's witness for later reads (unit C2a, 2026-10-14 · adopted)

**Decision:** every result the apply thread hands a proposer carries `appliedWit γr log` for the
log after the entry: `∃ i, committedAtLeast γr i ∗ appliedLogAt γr i log ∗ appliedMono γr`. A
client that got a successful `Put` passes `i` to its next linearizable `Get`
(`etcdRangeSpec`'s `committedAtLeast γr c`, with `c := i`), whose `readLogOk γr i l` gives a log
applied through some `ci₀ ≥ i` that `l` extends; `appliedMono` (the applied logs grow with the
index) closes `log <+: l` (`client_get_after_put`). The read side is unchanged.

**Three pieces, each where the code does it.**

- *Committed before applied.* The raft loop calls `updateCommittedIndex(&ap, rh)` before
  `applyc <- ap`; the server's closure raises `s.committedIndex` to the batch's last index. The
  ready handler's contract gives `committedAtLeast γr v` (`isReadyHandler rh R γr`), the `applyc`
  payload carries `committedLast γr ce`, and the apply side spreads it to each entry
  (`batchCommittedIdx`, from `srvIdxOk`'s consecutive indices). This is no new claim about raft: it
  is the server's own committed index, the one `ReadIndex`'s contract (`isReadRaft`) relates read
  indices to.
- *Deposited before handed over.* The proposer may return (and its client read) before
  `apply` calls `setAppliedIndex(i)`, so the log of index `i` is deposited in `γr.logs` before
  `Trigger` (`applied_predeposit`, in `applyEntryNormal`; for a conf change, in `apply`).
  `srvAppliedInv` admits the key `v + 1` while a ghost variable `γr.pend` (halves: the invariant,
  the apply thread's `srvAppliedOwn`/`srvAppliedPre`) says it is in, and `setAppliedIndex(v + 1)`
  publishes it. *Rejected:* depositing at `Trigger` only (conf changes and empty entries have no
  trigger, and `setAppliedIndex` would need two modes); an exclusive map element of `v + 1` held
  by the apply thread (it needs `v + 1 < 2 ^ 64` from the start, a construction premise).
- *Applied logs in prefix order.* `appliedMonoMap M` in the invariant: a deposit extends the
  current log (the apply thread holds `appliedLogAt γr v x.log` and a step only appends,
  `entryStep_prefix`). The client gets it as a capability (`appliedMono`, a persistent
  `□ ∀ …, ={⊤}=∗ ⌜L1 <+: L2⌝` from the invariant), because the comparison happens after both the
  `Put` and the `Get` returned, outside any server resource. *Rejected:* comparing by certificates
  alone (`idxCert_prefix` gives comparability, not the order); a caller-supplied log lower bound
  for `Range` (true at one member, as mvcc's committed log is monotone, but it bypasses the read
  index and does not lift to a cluster, plan item 3 of C2).

**The names.** The wait's registration condition fixes the proposer's expectation (`resultΨ`), so
the witness's read names must be the proposer's: `ReqNames.rd`. The apply thread's view
`isServer … ρ γr` says `ρ.rd = γr` (and the construction premise `isServerBuilt`), so the apply
thread deposits at the names the waiter expects; the read side (`isServerRead s E γr`) is
unchanged, and `etcd_kv_served` registers the `Put` at `ρ.rd` (a user instantiates its `γr` with
`ρ.rd` to get both at one name). *Rejected:* a read-names parameter on `isServerReq` (29 files of
request-path specs for a name only the wait's condition uses).

## The auth premises over a reader resource (unit A2, 2026-10-14 · adopted)

**Decision:** the server's auth contracts take the caller's reader resource: `isReqAuth st RD`
(`AuthInfoFromCtx`) and `apply.isAuthStore st P f RD` (the permission checks, `IsAdminPermitted`,
`IsAuthEnabled`), each call taking `RD` and giving it back, and the permission checks the key's
length below `2 ^ 63 - 1`. These are P2's derived forms, so the real store meets them:
`isReqAuth_of_authInv` and `apply.isAuthStore_of_authInv` at `RD := auth.authRd st R` (a slot of
`enabledMu`, of `rangePermCacheMu`, and the backend's read resource `R`). One resource for both
contracts: `AuthInfoFromCtx` uses only `authRd`'s `enabledMu` slot, and every holder of one needs
the other's checks too.

**The resource is the environment's** (`apply.AEnv.RD`, the plan of integration I1): every
statement over the apply chain or the server's views already names `E`, so the contracts are
`isAuthStore … E.RD`/`isReqAuth … E.RD` and no statement gains a parameter. Its holders, each a
thread that calls the store:

- the apply thread, in `kvOwn E log` (every applier method's precondition: the auth layer's KV
  methods and `UserGet`/`RoleGet`, the backend's `AuthStatus`);
- the auth layer's mutex (`authIs`: `authInfoOwn p ∗ E.RD`), for `Apply`'s admin check:
  `Apply` runs before the `applyFunc` hands the thread's resources to the methods, and its own
  precondition is the caller's opaque `A` (so a second resource, given to `newAuthApplierV3` at
  construction). *Rejected:* `E.RD` in `chainRes` (one copy, but `chainRes` is `E`-free and in
  every method's statement); `E.RD` in `Apply`'s triple (the `applyFunc` would then lack it while
  `Apply` holds it);
- a read call's `srvRdCall` (the read path's `AuthInfoFromCtx`, `chk`, `CheckTxnAuth`), lent to
  `EtcdServer.Put`/`DeleteRange` by v3rpc's handlers, which hold one;
- the write path beside `srvLeadTimeReader s` (`processInternalRaftRequestOnce`'s
  `AuthInfoFromCtx`, up through `raftRequest`, `Put`, `DeleteRange`, `Alarm`, the quota wrapper);
- the client's gRPC run slots (`etcdRunSlot`, and one more in `etcdGrpcSlot` for the quota
  wrapper's alarm): the bounded pool of runs is what makes the bounded `RWMutex` slots enough.

*Rejected* (again, P2): the slots in the store's invariant (unboundedly many concurrent requests).

**The key bound is a conjunct of the request models** (`rangeRequestIs`, `putRequestIs`,
`deleteRangeRequestIs`, `compareIs`: `⌜sint.Z ksl.len < 2 ^ 63 - 1⌝` of the `Key` slice, the last
conjunct, so a destructuring pattern ending in `-` is unchanged). The decoding states it (grpc's
`recv` is the predicate; `pbutil.MustUnmarshalMessage`'s request too): true of every slice in
memory, the gap is only the model's `make`. The nested transaction's checks inherit it through
`requestOpIs`. A lease's keys get it from the lessor's `Lookup` contract (`leaseIs`' `Keys()`).
The one proof that builds a request, `txn.Count`, takes it as a premise. *Rejected:* a model-level
`keyFits o` beside the predicates (a recursive predicate over the transaction's ops and
comparisons, restated at every layer that carries a request); a separate slice-level predicate
(the same recursion).

**The construction premise keeps the contracts** (smaller than stating `auth.authInv st R` in
`isServerBuilt`: the premise's other clauses are contracts of the same kind): a `NewServer` proof
would discharge them from `NewAuthStore`'s invariant with the two derivations, the admin part
`isAuthStoreAdmin` assumed.

**With the revision's token** (the merge with the vertical slice's unit V1, 2026-10-14,
`merge-origin7`). V1 carries the token of the revision a write minted (`revMinted E log log'`,
exclusive) along the same path. The two travel together in every result: `resultIsW` (and
`resultIs`, which keeps the token and drops only the witness), `appliedOk E γr`, `EtcdServer.Put`'s
success, `v3rpc.putApplied E γw` (`putAppliedOk = srvLeadTimeReader ∗ putApplied`), the client's
`putReplied E γr` (`putReplyOk E γr` and `revMinted`), which `etcdPutSpec E γr` hands the reply's
`Φ`. `putReplied_ok` drops the token and keeps the witness, so `client_get_after_put` stays over the
persistent `putReplyOk`. `DeleteRange`/`Txn` carry the token only (their witness is dropped at
`EtcdServer.DeleteRange`/`Txn`, as in C2a).

## The client contracts derived: certified floors, the restrictions (unit V2b, 2026-10-14)

**Decision:** the recipes' client contracts (`isRecipesKV`, `isEtcdRecipesClient`) are derived for
a real `*kv` at the server's instance `v3rpc.etcdModelOfServer E`, whose `etcdReachedAt` stays
V1's (`srvReachedAt E r`: a certified log longer than `r`). Linearizability (`lo ≤ r` of the
contracts) comes from **certified floors**: the caller turns `etcdReached lo` into a certificate
`idxCert F` with `lo < |F|` (`client.floor_of_reached`) and hands it to the request (the specs'
`∃ F, idxCert F ∗ …`); every reply carries `F <+: log`.

**Why not the witness** (the brief's plan: `etcdReachedAt r := ∃ L, appliedWit γr L ∗ ⌜r ≤ |L| −
1⌝`, with committed ≥ applied and `lin_of_reached`). Two clauses fail. (1) A get's reply must give
`etcdReached r` for its own revision `r`, mvcc's log at the read; that log may be ahead of every
log the apply thread has deposited (the read runs against the backend while the apply thread is
mid-entry), so no witness of it exists. (2) A write's `lo ≤ r` needs the caller's `lo` at the apply
thread, which only sees the entry; the witness relates a write to later reads, not to earlier
knowledge. The floors answer both: (1) the read's log is certified (`idxCert`), (2) the floor
rides in the id claim (`idClaim γi id d γf ∗ floorAt γf F`) to the apply thread, which hands it to
the txn lemmas (`pinned_floor`: the log the entry meets extends every certified log, `cert_join`).

**Relation to C2a.** C2a rejected "a caller-supplied log lower bound for `Range`" because it
bypasses the read index and does not lift to a cluster (plan item 3 of C2). The floors are that,
for every request, and the same caveat holds: they are one member's certificates. C2a's witness is
kept (now also on `DeleteRange` and `Txn` replies): the cluster-level step must replace the floors
by the cluster log (plan items 1–3), at which point the witness and the read index carry
linearizability.

**The restrictions** (accepted from slice-v2, in the contracts' statements, `InvEtcdTxn.lean`):
`getExact`, `exactGets`, `txnBuilderSpecX`, `kvGetResultR`, deletes `rangeEnd ≠ [0] ∧ t = 3`, puts
`t = 2`; each where the server does not answer as the clients' model says (the issues
`etcd-range-keys-only-lease.md`, `etcd-range-sort-none-limit.md`), or where the server's proof
models less than the code (`irrWireOf` up to range ends `[0]`; a writing transaction's gets may be
answered header-only, `SkipRangeExecution`). STATUS lists them with the premises.

**`context.TODO()` as a quiet context** (`ctxQuiet`, `ctxOk`): the recipes call the client at
`TODO()`, which is not a `context.isContext` of the model (no cancellation). The trust-boundary
contracts that took `isContext` (`grpcInvokerOk`, `withVersion`, `waitRetryBackoff`, `getToken`,
`refreshToken`) take `ctxOk` (either), a statement change, no new axiom.

**Rejected:** strengthening `getExact` with `¬(key = [0] ∧ rangeEnd = [0])` to cover `pfx = []`
(the recipes' `newSequentialKV` with `kp = []` breaks); the get contract is derived for `pfx ≠ []`
only, which the queue needs (`NewQueue`'s `kp ≠ []`); the priority queue (contracts at `""`) is not
covered.

## Put and Get as persistent atomic updates linearized by raft (unit T1, 2026-10-14 · adopted)

**Status.** Implemented (2026-10-14): the model, the KV ghost state and its invariants, the raft
contract restated, the read loop's registry, mvcc's log certificates, the apply thread's KV
ghost state, the server's `Put`/`Range`, the gRPC layer's deposits, the client's `kv.Put`/`kv.Get`
with persistent updates. Full build green, no new axiom, no new `sorry` (`notes/STATUS.md`, "Unit
T1"). The two gaps found while designing are resolved below ("The two gaps, resolved").
**Superseded in part (2026-10-15, unit T2)**: the per-key points-to (`k ↦kv vo`, `kvPutAu`,
`kvGetAu`), the plain workload's limits (puts without ignore flags, deletes without `PrevKv`, no
transaction) and the non-plain credit `srvNonPlain` below are replaced by one exclusive state
`etcdKV γ σ` and a transition for every KV operation: "Every KV operation as a persistent atomic
update on the whole state". The raft contract, the read loop's registry, mvcc's certificates and
the two gaps' resolutions stand.

**Goal.** TaDa-style specs, linearized by raft:

- `kv.Get(ctx, k)` takes `□ AU <{∃∃ vo, k ↦kv vo}> <{k ↦kv vo, COMM □ Q vo}>` and returns `□ Q vo`
  for the value it returns.
- `kv.Put(ctx, k, v)` takes a *persistent* update `□ AU <{∃∃ vo, k ↦kv vo}> <{k ↦kv putEffect op
  vo, COMM □ Q vo}>` and returns `□ Q vo` on success.

The update is persistent because the client's retry interceptor may apply a `Put` more than once
(`issues/etcd-client-retry-put-ctx-error.md`, each attempt a new request id, so a new raft entry),
and raft may commit one proposal's data more than once. A write is linearized at the commit of an
entry carrying it, a read at a committed index at or after its read index. A client-side prophecy
that turns these into ordinary atomic specs is later work.

### Decided

- **The full committed raft log** (user, 2026-10-14). The contract exposes the state at the start
  index `ai₀` (the snapshot's, `x₀`) and every committed entry after it, at consecutive raft
  indices (no snapshot after `run` starts: `rnSnapOnce`, as now). Positions are raft indices. The
  register's first-occurrence client-data log `srvCLog` leaves the server's contract. It was the
  register's, and justified there only by the register's Go dedup of applied encodings ("The
  register: TaDa proposals over raft's client log"). etcd's apply thread applies every occurrence.
- **Non-client entries are no-ops** in the KV model (empty leader entries, conf changes, entries at
  or below the consistent index `c₀`), as the apply thread treats them.
- **Every occurrence** (pitfall (b)). The persistent `Put` update fires at every committed
  occurrence of its data. No uniqueness premise.
- **`authOn` in the model** (true of Go: `isOpPermitted` returns `nil` when `!as.isAuthEnabled()`).
- **Plain workload by an invariant, not a premise on the log** (user's decision 1; enforcement
  below).
- **Read batching with a list of registered `Q`s** (user's decision 2; below).
- **One `ReadIndex` spec, whatever the number of voters** (user). The server's contract has no
  cluster-size premise. The verified spec's `1 < GMap.size γ.raft.reCfg` must go, and the singleton
  branch must become another case of the same spec (below).

### The KV ghost state and its invariant

- **Points-to** `k ↦kv vo` (`vo : Option GoString`, `none` for an absent key): an element of a ghost
  map `γkv`. The authority holds only the keys handed out. A key not in it is allocated at its
  current value (`kv_alloc`, inside the invariant).
- **The KV invariant** `kvInv γ γkv` (namespace `kvN`, disjoint from `srvRaftN`): `∃ L, srvRLog γ
  L ∗ ghostMapAuth γkv M ∗ ⌜plainLog L ∧ ∀ k vo, M !! k = some vo → vo = kvVal (kvRaftOf c₀ ch₀ x₀.log
  L) k⌝`. `srvRLog γ L` is the server's half of the committed raft log after `ai₀`. Raft holds the
  other half and moves both at each commit.
- **The model** (`KVModel.lean`, done): `kvRaftOf c₀ ch log₀ A`, the fold of `kvEntry` over raft
  entries. A normal entry with data that decodes goes through `dispatchLog` (`chainLog` through the
  chain `ch`, the start's: `restoreAlarms`' chain at `x₀`, fixed since no alarm request is plain);
  everything else is the identity. `kvVal log k` is the value of `k` after `log`. The model's value
  stays an mvcc log, so revisions, `idxCert`, `revMinted` and the vertical slice's `EtcdModel`
  instance (over certified logs) are unaffected. `k ↦kv` is a coarser view of the same log. The
  new specs do not use `EtcdModel`, and it is not changed.
- **Plain** (`plainReq`, `plainEntry`, `plainLog`, done):
  - *plain*: a put with lease `0` and no ignore flags; a range; a delete without `PrevKv`; a
    request that does not touch the store. A put or delete must not also carry a field that makes
    `Apply` skip it (`noSideEffect`) or check admin permission (`needAdminPermission`).
  - *not plain*: txn, compaction, lease grant and revocation, alarm requests, `AuthEnable`.
- **Determinism, as far as the current model allows** (done):
  - `batchStep_plain`: on a plain entry, every step the apply relation allows leaves the chain
    alone and changes the log as `kvEntry` does, unless it is an auth rejection (the log
    unchanged);
  - `applyStep_plain`, `dispatchStep_plain`, `chainStep_plain`, `backendStep_plain`: the same per
    layer.

  The auth disjunct is what `authOn` removes.
- **The intermediate value lemma** (`kvRaftOf_ivt`, done): a log between `kvRaftOf A₀` and `kvRaftOf B`, with
  `A₀ <+: B`, is `kvRaftOf A` for some `A` between them, since each entry appends at most one revision
  (`kvEntry_grow`).

### `authOn` in the model (next step; mechanical but wide)

The auth layer's mode goes in the chain: `Chain.auth (on : Bool) (c : Chain)`, with `baseChain on`
and `alarmChain on ns cr`. `chainStep`'s auth case rejects only if `on`. `dispatchStep`,
`applyStep`, `entryStep`, `batchStep` and `entriesStep` keep their signatures (the mode is in
`x.chain`).

`isAuthStore st on P f RD` gains:

- if `on = false`, the permission checks and `IsAdminPermitted` return `nil`;
- `AuthEnable` requires `on = true`.

The real store meets it at `on = true` for free (`isAuthStore_of_authInv`). At `on = false` it meets
it given an `enabled = false` ghost fact in unit A2's `enabledP`, which only `AuthEnable` breaks.
`newAuthApplierV3`'s spec yields `.auth E.authOn c` (an `AEnv` field). This touches the 26 files
that name `.auth`, `baseChain` or `alarmChain` (about 100 lines) and `isAuthStore`'s users.
`chainLog`'s auth case then becomes exact for `on = false`, and `batchStep_plain` loses its auth
disjunct.

The apply thread must then know that no `AuthEnable` entry reaches it when `on = false`. That
knowledge comes from the plain invariant through the batch (`srvRLogLb` of the batch and `kvInv`'s
`plainLog`), replacing that part of `entriesOk`.

### Enforcing the plain workload (decision 1)

Every committed normal entry with data was proposed with a deposited update (raft fires only
deposited updates; the contract's apply side, `batchCommitted`, already says each is deposited).
The only way to make a proposal update (`srvPropAu γ d Q'`, raft-level) is `kv_prop_au`. It opens
`kvInv` and, on commit, must re-establish `plainLog (L ++ [e])`, so it takes `⌜∀ rq, irrDecode d =
some rq → plainReq rq⌝`. So:

- **The proposal path** (`processInternalRaftRequestOnce`, `raftRequest`, `raftRequestOnce`) takes
  `⌜plainReq r⌝` of the request it proposes, or a **non-plain credit** `srvNonPlain γkv`: an
  exclusive token allocated at construction and kept inside `kvInv`, so nobody holds it in this
  configuration. With it, a proposal could commit a non-plain entry, so `kvInv` gives the token
  back only in exchange for giving up the KV model, and no one does.
- **The non-plain handlers' specs** require `srvNonPlain γkv`:
  - `EtcdServer.Txn` (writing branch);
  - `LeaseGrant`/`LeaseRevoke`/`Compact`/`Alarm` and the auth admin requests (not on the request
    path's verified list);
  - the names-only contracts that propose: `compactorOk` (the auto-compactor; `nil` unless
    `AutoCompactionRetention ≠ 0`), the lessor's expiry loop (`revokeExpiredLeases`: no lease is
    ever granted, since a grant is non-plain), the hash monitors (`monitorKVHash`,
    `monitorCompactHash`: CORRUPT alarms).

  So `txn_end_to_end`'s writing case needs a credit no one has. It is no longer a usable result in
  this configuration, by design. The read-only `Txn` stays.
- **The server's internal plain proposals** (`publishV3`'s `ClusterMemberAttrSet`, the cluster
  version's `ClusterVersionSet`, `DowngradeInfoSet`) are plain (no store change) and deposit an
  update built by `kv_prop_au` with `Q' := True`.
- **The NOSPACE alarm** (the apply thread's goroutine, `raftRequestAlarm`, an axiom) is the hard
  case; see "Two gaps found", gap 2.

### The raft contract, restated (implemented, `InvRequest.lean`)

It is stated over `ServerRaftNames` (`rlog`, `rlb`, `fresh`, `props`, `ai0`): the committed raft log
after `ai0` as a ghost variable in halves (`srvRLog γ L`: the KV invariant's; raft's in its commit
invariant `srvRaftLogInv`, with the lower bounds' authority) and its persistent lower bounds
`srvRLogLb γ L`.

- **Proposals** (`Propose` takes `srvPropArg`: a fresh token and the update, or a retry's
  `srvDeposited`; gives `srvPropRes`):
  ```
  srvPropAu γ d Q := □ AU <{∃∃ L, srvRLog γ L}> @ ⊤ ∖ ↑srvRaftN, ∅
      <{∀∀ e, ⌜e.typ = W32 0 ∧ e.data = d ∧ srvIdxOk γ.ai0 (L ++ [e])⌝ ∗ srvRLog γ (L ++ [e]),
        COMM □ Q L}>
  ```
  fired at every committed occurrence of `d`; raft records it:
  ```
  srvPropWits γ := □ ∀ d Q L m e, srvIsProp γ d Q -∗ srvRLogLb γ L -∗
      ⌜L[m]? = some e ∧ e.typ = W32 0 ∧ e.data = d⌝ -∗ £ 2 ={⊤}=∗ □ Q (L.take m)
  ```
  (two credits: raft's collection is under its invariant's later and the saved predicate's).
- **Raft's own entries**: `srvNoopAu γ := □ ∀ e, ⌜e.data = [] ∨ e.typ ≠ W32 0⌝ -∗ AU <{∃∃ L,
  srvRLog γ L}> @ ⊤ ∖ ↑srvRaftN, ∅ <{⌜srvIdxOk γ.ai0 (L ++ [e])⌝ ∗ srvRLog γ (L ++ [e]), COMM
  True}>`, which the KV invariant gives (`kv_noop_au`) for raft to take at the node's start.
- **The apply side**: `srvC ρ E ai₀ c₀ x₀ L` (raft's `E.C` of every `Ready`'s committed entries)
  carries `srvRLogLb ρ.raft L`.
- **Reads** (`raftNode.ReadIndex`, `isRaftNodeIfc`, `isReadRaft`): `ReadIndex(ctx, beBytes id)` with
  `committedAtLeast γr n` takes `srvReadAu γ Qr := □ AU <{∃∃ L, srvRLog γ L}> @ ⊤ ∖ ↑srvRaftN, ∅
  <{srvRLog γ L, COMM □ Qr L}>` and registers `□ RQ id n Qr`. A read state answering `id`
  (`readStateOk`) gives `n ≤ rs.Index` and `srvReadWit γ Qr rs.Index`, with
  ```
  srvReadWit γ Qr i := □ ∀ L, srvRLogLb γ L -∗ ⌜uint.Z i ≤ uint.Z γ.ai0 + L.length⌝ -∗
      £ 2 ={⊤}=∗ □ Qr L
  ```
  Raft deposits the update at the `ReadIndex` call and fires it then and at every later commit,
  on the committed log of the moment (`notes/raft-readindex-spec.md`: `read_deposit`); the read
  index bounds the committed log at the deposit, so every committed log through an index `≥ i`
  was fired at (pitfall (a): the log through a raft index includes raft's own entries, which
  `kvRaftOf` skips). One spec, with no voter-count premise (pitfall (c)).

### The read loop: one update per `ReadIndex`, a list of registered `Q`s (decision 2)

Per notifier, the read invariant keeps a **list of registered predicates** `Qs : List (List
EntryModel → IProp)`, each with its client's KV-level persistent update (saved predicates, the
updates beside them in the invariant).

- A client calling `LinearizableReadNotify` appends its `Q` and learns, persistently, that it is
  registered at position `n` of the current notifier's list (`readRegAt γn n Q`, a saved predicate
  at `n`), along with its bound `c` in the need as today.
- The loop's swap freezes the list with the need (`needFrozen`: the list's authority in an
  invariant of its own).
- The loop builds **one** raft-level persistent update for its `ReadIndex`, `srvReadAu γ (λ L,
  [∗list] Q ∈ Qs, □ Q L)`, by `kv_read_compose`: open `kvInv` and hand raft `srvRLog γ L`; on the
  commit, holding the KV authority, fire every frozen client update in turn. Updates whose state is
  supplied by the prover do not compose sequentially on the prover's side, which is why the KV-level
  updates are fired on the eliminator's side, with `kvInv` open.
- `notified` carries `srvReadWit γ (λ L, [∗list] Q ∈ Qs, □ Q L) i`. A served client opens it at a
  committed `L` and takes element `n` (saved-predicate agreement, one later credit).

The `read` package stays generic: it is parameterized by the deposit (a persistent family of the
registered predicates' companions) and a composition premise, which the server instantiates with
`kv_read_compose`.

### The two gaps, resolved (2026-10-14)

1. **The read's log, pinned to a raft index** (the user's decision: mvcc's certificates, ghost
   only, no Go change, no observer at `store.Read`'s linearization point). mvcc's store certifies
   every log it commits by its *caller's* ghost map `γ.cok` (length ↦ log, persistent elements):
   `certOk γ log := ⌜log.length ≤ 2⌝ ∨ (W64 log.length) ↪[γ.cok]□ log ∨ (W64 0) ↪[γ.cok]□ []` (the
   last the free certificate a caller that does not use them mints, `certFree`). `revMuInv` keeps
   `certOk` of the committed log; a write transaction's `End` takes `certOkNext γ ilog pend`
   (`txnEndPre`), `store.Read` returns `certOk γ log` of the log it read; `NewStore` hands the
   caller `ghostMapAuth γ.cok 1 ∅`. The txn package passes the premise up (`txn.Put`: `□ ∀ ilog,
   ⌜Pinned log₀ m ilog⌝ -∗ certOk γ (ilog ++ [[putChangeOf …]])`; `DeleteRange`: `certOkNext` of
   its changes; `Txn`: `certOkNext` of a writing run), and the apply package as `certPre E c rq log
   := □ ∀ oc, ⌜chainStep backendStep c rq log oc⌝ -∗ certOk E.γ (oc.logAfter log)` (each layer's
   `certPre_mono`), `certPreV v3` at `dispatch`/`uberApplier.Apply`/`apply.Apply`, and the lessor's
   `Revoke` contract the same of its deletions. The server's elements say a log is the KV model of
   a committed raft log: `kvCertInv γ γk := inv kvcN (∃ C hi Lb, ghostMapAuth γk.cok 1 C ∗
   ghostVar γk.hi ½ hi ∗ srvRLogLb γ Lb ∗ ⌜certMapOk γk C hi Lb ∧ 2 ≤ γk.log0.length⌝)` with
   `certMapOk`: every element `n ↦ l` has `|l| ≤ hi`, `n = W64 |l|`, `|l| < 2^63` and `l =
   kvModel γk A` for some `A <+: Lb`. The apply thread holds the other half of `hi` at its log's
   length (`kvApplied γ γk A x`: `srvRLogLb γ A`, the half, `kvCert γk x.log`, `x.log = kvModel γk
   A`, `x.chain = γk.ch0`) and, before applying the next committed entry `m`, mints the
   certificate of `kvEntry … x.log m = kvModel (A ++ [m])` at a length above every certified one
   (`kv_cert_step`, `kv_applied_step`); by determinism (`chainStep_plain`, auth off) every outcome
   of the request's chain has that log (`kv_certPre`). A reader (`kv_cert_read`, `kv_read_log`):
   a certified `l` extending the log `L₀` applied through `i` (`kvLogAt`, from the applied index's
   invariant, `kvLogsOk`) is `kvModel A` of a committed `A` through an index `≥ i` (if `A` is
   shorter than `L₀`'s raft log, both models are prefixes of each other, so equal).
2. **The NOSPACE alarm** (the user's decision): the quota's contract says `Available` returns
   `true` ("the backend never reaches its quota: the disk never fills", a construction premise of
   `isQuota`); `chainStep`'s quota case is the inner outcome, so `ErrNoSpace` and the server's
   NOSPACE `Alarm` proposal are unreachable in the model.

The design discussion, as it was before the decisions:

1. **The read's log is not pinned to a raft index.** A linearizable `Range` reads mvcc's *current*
   log `l` (`txn.Range`: a certified `l` between the caller's certificate `log₀` and its revision
   tokens). The read side knows only `readLogOk`: `l` extends the log applied through some `ci₀ ≥
   i`. To get `□ Q (kvVal l k)` from `srvReadWit`, `l` must be `kvRaftOf A` for a committed `A` with
   `|A| ≥ i - ai₀`. `kvRaftOf_ivt` gives that from an **upper bound** `l <+: kvRaftOf B` for some committed
   `B`. No existing fact gives one. The apply thread commits an entry's changes to mvcc before
   depositing its log (`applied_predeposit`), so a reader may see a log that no deposit names yet.
   The sole writer's revision tokens bound every committed log, but they are the apply thread's, so
   a reader has none (`txn.Range` takes `m = 0` tokens).

   Options:
   - (a) mvcc's read transaction exposes its linearization point: `store.Read` (and through it
     `txn.Range`) takes an observer, run while it holds `revMu` with the committed log
     (`revMuInv`'s `ghostVar γ.clog`). The apply thread deposits its next log *before* the mvcc
     commit (it is `kvRaftOf` of the batch, known in advance by determinism), with an invariant that
     the store's committed log is the deposited log at the applied index or the next. This is a
     change to mvcc's read and write-transaction specs (`store.Read`, `storeTxnWrite.End`) and to
     the apply thread's deposit.
   - (b) The same through the revision tokens: the apply thread parks all but one of its tokens
     in the applied index's invariant between entries, and readers borrow them for
     `txn.Range`'s bound. This changes `kvOwn`'s sole writer through the whole apply package.

   (a) is the smaller and more faithful change.
2. **The NOSPACE alarm.** The quota layer's outcome is a relation (`applied l true`: the quota
   reports `ErrNoSpace` after a write, depending on the backend's size). On it the apply thread
   starts the alarm goroutine, which proposes an `ACTIVATE` alarm, a non-plain request: it would
   need the non-plain credit. The apply thread cannot rule the outcome out from the model.

   Options:
   - (a) The quota's mode in the model, like `authOn`: `quotaFull : Bool`. With `false`, the
     backend quota's names-only contract says `Available` is true, so the outcome is never
     `applied l true`. This is a premise on the environment (the disk), not on the log, like
     `storeSmall`.
   - (b) A model of the alarm store, so alarm entries become deterministic (larger).

### What the raft library's proof must prove

Against the verified raft's names (`Protocol/GhostState.lean`, `InvNode.lean`):

- `cLog`/`propAu`/`fire_upto` move to the full committed log (`isCommitted γ L` already is one).
  Proposal updates become persistent and fire at every committed occurrence. Raft's own entries
  go through the standing update.
- `readReq`/`readOk` gain the read update. `node.ReadIndex`/`RawNode.ReadIndex` take `□ readAu`,
  kept in the leader's read registry with the request. Each commit step fires every registered
  read update whose safe index the new committed log reaches (and registration fires it if the log
  is exactly `i` long), recording `srvReadWit`.
- The safe-index lemma becomes "the committed log at the call is at most `i` long", strengthened
  from `readReq γ c Lc`'s log the request knew.
- **One spec for every configuration** (static membership). The verified
  `node.ReadIndex`/`RawNode.ReadIndex` premise `1 < GMap.size γ.raft.reCfg` is dropped. The
  singleton branch (`raft.go:1343`: `IsSingleton()` answers at once with `r.raftLog.committed`,
  skipping the heartbeat round and `committedEntryInCurrentTerm`) is another case of the same
  spec, provable in the static mode only (a static single voter's committed log is the
  cluster's). Under reconfiguration the singleton branch can answer with a stale index (the raft
  team's `issues/raft-readindex-singleton-stale.md`); nothing more is claimed.
- **The read update deposited at the call** (`notes/raft-readindex-spec.md`): `readReq γ c Lc`
  with the exact committed log at the deposit, fired then and at every later commit; the
  witness's collection costs two later credits (`£ 2` in `srvReadWit`, as `srvPropWits`).
- **The delivered log is committed**: `srvC`'s `srvRLogLb` of every `Ready`'s committed entries
  from the start.
- **Raft's own entries** through `srvNoopAu`, taken at the node's start.

---

## The watch stream's server end: indexed queues, the delivery accounted by position (unit W-S, 2026-10-14)

**Decided.** The server end of a gRPC bidirectional stream is `srvStreamIs st γ Req Rep Up Dn ci
cd` (`v3rpc/InvWatchStream.lean`), the shape of `notes/grpc-stream-spec.md` with two ghost FIFO
queues (`monoList`s: the up queue's and the down queue's), the receiver holding the up queue's
receiver token and the sender the down queue's authority half. Each message carries a per-position
content: `Up i m` (what the client promises of its `i`th request) and `Dn j m` (what the handler
promises of its `j`th response). A method's stream specification relates `Dn` to the rest of the
world: for `Watch`, `watchStreamSpec γs γ cid mid Dn := □ ∀ j m, Dn j m ∗-∗ watchDn γs γ cid mid j
m`, persistent, a premise of the handler (the serving layer fixes `Dn` when the stream is
created, so the client's `NewStream` can return it with the same `Spec`).

**Why positions.** A response's content depends on the history of both queues and on the mvcc
stream's deliveries: a control response answers the request at some up position (`ctrlOk` names
the position, `upAtW`); an mvcc response is the next delivery of its watcher, and what "next" means
is a statement about the down queue's prefix before it (`mvccOk`: the watcher's responses with
events among the first `j` sent, then this one, are its responses with events received:
`sentEvsOf (downLbW L) w ++ [r] = rs.filter (evs ≠ [])`). The down queue's lower bound at the send
(`downLbW γs L` with `L.length = j`) makes the statement checkable by the client, who holds a lower
bound of the same list; a predicate transformer per message could not say it.

**Why the ghost source.** `WatchRespM.src` (an `Option mvcc.RespM`) records the mvcc response a
wire response was made of: the client cannot recompute it (the wire has the watch id, not the
watcher), and two watchers can share an id (an explicit id reused after a cancel:
`issues/etcd-watch-id-reuse-stale-events.md`). The order is per watcher, not per id; the send
loop's buffering is per id, so the pure model (`WatchSendModel.lean`: `SendInv` over the sent
indices, the buffered indices per id and the announced ids; `send_claim`) bridges the two with
one fact from mvcc: a watcher's responses with events all carry its id (`respOk`).

**Alternatives rejected.** (1) `Dn` chosen by the handler (the note's first draft: `Spec γ Dn` in
the handler's postcondition): the handler cannot choose what the client already holds; making it a
premise costs nothing (persistent). (2) Returning the run slot: `Watch` returns while `recvLoop`
may still be blocked in `Recv` (etcd's own comment: waiting would deadlock on a stream whose
context is done but whose receive is not), so the receive loop's resources are not given back;
the slot is per stream for the server's life, as the note's open point on the pool says. (3)
Modeling fragmentation, `prev_kv` and filters now: no client of the slice sends them; the
restriction `watchReqOk` (a premise on `Up`) leaves them to a later unit.

---

## Every KV operation as a persistent atomic update on the whole state (unit T2, 2026-10-15 · adopted)

**Status.** Implemented (2026-10-15, `notes/STATUS.md`, "Unit T2"): puts (any flag but a lease),
ranges, deletes (with or without `PrevKv`) and plain transactions are deterministic in the KV
model and step one exclusive abstract state; the server's and the client's `Put`, `Range`/`Get`,
`DeleteRange` and `Txn` take persistent atomic updates over it. It supersedes unit T1's per-key
points-to (`k ↦kv vo`, `kvPutAu`, `kvGetAu`) and merge M1's non-plain credit (`srvNonPlain`,
`srvNonPlainAll`), both removed. No new axiom, no new `sorry`.

### The user's decisions (2026-10-15)

- Every etcd KV operation (leases included, later) has a transition on the abstract etcd state;
  an operation not handled yet has no spec (no unobtainable token).
- **The abstract state is the whole store**: one exclusive predicate `etcdKV γ σ`, `σ` the store
  at its latest revision. Each operation's spec takes `□ AU <{∃∃ σ, etcdKV γ σ}> <{etcdKV γ (step
  op σ), COMM □ Q σ}>` (a read's step the identity, a rejected request's too) and returns `□ Q` of
  the state it linearized at. A per-key points-to is a client-side view (a ghost map in the
  client's own invariant beside `etcdKV`).
- Writes' updates stay persistent (retries, raft's duplicates); reads use raft's persistent read
  update (T1), pinned to a committed raft prefix through mvcc's certificates (T1).

### The state and the step (`KVModelDefs.lean`)

- `KVState := {kvs : List EtcdKv, rev : Nat}` (every key's value, create and mod revisions,
  version and lease; the current revision), `kvStateOf l := ⟨stateAfter l, l.length - 1⟩` (a read
  at `l` answers revision `l.length - 1`). `KVState.commit σ cs`: no change for no change
  (`commitLog`'s), else the changes at revision `σ.rev + 1`.
- `KVOp := put o | range o | deleteRange o | txn t`, `kvOpStep`: a put whose ignore flag's key is
  missing changes nothing (`ErrKeyNotFound`), else commits `putChangeOf`; a range nothing; a delete
  commits its range's deletions (`delChanges`); a transaction whose path does not find a key an
  ignore flag needs changes nothing (`checkTxn`'s error), else commits the server's run
  (`srvRunTxn`, nested branches by their verdicts at the state).
- `reqKVOp rq` (by `dispatch`'s kind), `kvReqStep`; the backend's deterministic log (`backendLog`,
  now with the put's rejection and the transaction) follows the state: `kvStateOf_backendLog`
  (`kvStateOf (backendLog rq l) = kvReqStep rq (kvStateOf l)` for `l ≠ []`); `dispatchLog_base`,
  `kvEntry_base`: at the start's chain with `v3`, an entry's effect is its request's backend log.
- **Plain** (`plainReq`): a put with lease `0` (any other flags), any delete, a plain transaction
  (`txn.txnPlain`: gets at revision `0`, puts naming lease `0` and keeping none: no
  `IgnoreLease`, whose `putKeep`/`putIgnVal _ none` drop the request's `Lease` field that
  `checkPut` still looks up), a range, or a request that does not write. Excluded (no spec):
  leases (grant, revoke, a put or transaction naming one), compaction, alarms (the quota
  assumption already excludes NOSPACE), `AuthEnable` and the admin requests.

### Making the apply relation exact (what determinism needed)

The apply package's outcome relation left four choices open; each is now closed by a
strengthened spec of the code, not by a premise:

- **A put's ignore flag**: `txn.Put.spec`'s commit now says the previous key-value an ignore flag
  needs was found, and the caller certifies only such a put's log (`□ ∀ ilog, ⌜Pinned ∧ (needsPrev
  → found)⌝ -∗ certOk …`); `backendStep`'s applied put carries it.
- **A delete with `PrevKv`**: its range read cannot fail at the apply thread's never-done context
  (`txn.DeleteRange.spec`'s `nd`); `backendStep`'s delete is the applied commit only.
- **A transaction's check**: `checkTxn.spec`'s error says, for a plain transaction, that a put of
  the path did not find a key it needed (`txnPlain t → ¬ PathsIgnOk …`: a range at revision `0`
  passes `checkRange`, a put naming lease `0` passes `checkLease`); `txn.Txn.specSole`'s success
  says `PathsIgnOk`, its error the same as `checkTxn`, and the caller certifies only a write whose
  path finds its keys; `backendStep`'s transaction carries both.
- **The auth layer on a transaction with auth disabled**: `CheckTxnAuth`/`checkTxnPermission`/
  `checkTxnReqsPermission` now return `nil` when the store is disabled (`on = false`: they are made
  of the permission checks, which do); `authMayReject` no longer lets a disabled auth layer reject
  a transaction.
- The capped layer (a `NOSPACE` alarm) may reject a transaction or not; the start's chain has no
  capped layer, so the determinism lemmas take `c.kvExact` (auth disabled, no capped layer:
  `Chain.kvExact`, `alarmChain false false false`'s) instead of T1's `authOn = false`.

### The KV ghost state (`InvRequest.lean`, `KVLemmas.lean`)

- `KVNames` has `st` (the state's ghost variable) in place of T1's `map` and `np`; `etcdKV γk σ :=
  ghostVar γk.st ½ σ`; the KV invariant holds the other half at `kvStateOf (kvModel γk L)` of the
  committed log `L`, with T1's plain/index facts and `γk.log0 ≠ []` (`kvInv_alloc` allocates both
  halves from an empty committed log).
- `kvAu γk f Q := □ AU <{∃∃ σ, etcdKV γk σ}> @ (⊤∖↑srvRaftN)∖↑kvN, ∅ <{etcdKV γk (f σ), COMM □ Q
  σ}>`, `kvOpAu γk op Q := kvAu γk (kvOpStep op) Q`, `kvReadAu γk Q := kvAu γk id Q`.
- `reqPropOk γk rq Qr`: a plain request with no write (`Qr` trivial), or a plain request of the
  operation `op` (`reqKVOp rq = some op`), no range end `[0]` (`irrNoZeroEnd`: the wire keeps it),
  with its client's `kvOpAu γk op Q`, `Qr L = □ Q (kvStateOf (kvModel γk L))`. `kv_prop_au` fires
  the client's update at the commit (`kvModel_snoc_state`: the entry steps the state by its
  request). The permits: `putPermit` (lease `0`), `deletePermit` (range end not `[0]`),
  `txnPermit` (`txnPlain`, `txnNoZeroEnd`), each with its `*_reqPropOk`.
- `kvDep γk Q`: a read update `kvReadAu γk Q0` with `Q L = □ Q0 (kvStateOf (kvModel γk L))`, or
  none; `kv_fire_reads`/`kv_read_compose` fire every registered read at the current state.

### The specs

- Server: `EtcdServer.Put … Q` (pre `putPermit`), `DeleteRange … Q` (pre `deletePermit`), `Txn … t
  Q` (a writing `t`: pre `txnPermit`), success adding `∃ σ, □ Q σ`; `Range … Q` with `kvDep`.
- gRPC layer: `KVDep := none | op o Q | read Q`; a put, a delete and a writing transaction take
  the deposited operation's update (`kvDepPre`), their answers add `∃ σ, □ opDepQ d σ`.
- Client: `etcdPutSpec` (`∃ Q, ⌜lease 0⌝ ∗ kvOpAu (.put o) Q ∗ ∀ m, putReplied … m ∗ (∃ σ, □ Q σ) -∗
  Φ m`), `etcdDeleteSpec` (likewise, range end not `[0]`), `etcdTxnSpec` (read-only and `Q`
  trivial, or writing, `txnPlain`, `txnNoZeroEnd`, `kvOpAu (.txn t) Q`), `etcdRangeSpec` (`kvReadAu
  Q` or nothing; `rangeReplyOk` carries `□ Q (kvStateOf log)` of the log read). End to end:
  `client_put_end_to_end`, `client_get_end_to_end`, `client_range_end_to_end` (any options that keep
  a range), `client_delete_end_to_end`, `client_txn_end_to_end`; `client_get_value`,
  `rangeReply_state` (the reply is the state's selection, count and revision).

### How `σ` meets the vertical slice's `EtcdModel`

The class is unchanged. `σ` is always the state of a certified log (`kvStateOf l`, `l` the KV
model of a committed raft log, which mvcc certified): a read's `□ Q σ` comes with `idxCert l`
(`rangeReplyOk`), so `rangeReply_etcdState` gives `etcdState (W64 σ.rev) pfx (underPfx pfx σ.kvs)`
in `v3rpc.etcdModelOfServer E` (`etcdState_of_cert_last`): the instance's `etcdState` at `σ.rev`
is `σ` restricted to the prefix. A write's `σ` is the state before the entry, at the log the
apply thread met (`x.log`, certified: the reply's `putReplied` etc.); the specs do not yet tie
`σ` to the reply's `x.log` (the proposal's witness is collected at the occurrence the reply is
of, but `resultIs` does not name the raft prefix): a refinement for the next unit.

### The V2b client contracts

A client that does not track the abstract state holds every operation's update with no result,
`kvAnyAu γ := □ ∀ op, kvOpAu γ.kv op True`, from `etcdKV` in an invariant of its own
(`kvAnyAu_of_inv`). The derived contracts (`kv_put_result`, `kv_delete_result`, `kv_txn_commit`,
`isEtcd*KVTodo_of_kv`, the recipes', `queue_vertical`) take it in place of `srvNonPlainAll`, plus,
for the operations with a lease, which no server spec covers until unit T3, their client-level
triples as premises (`kvLeasedPutTodo`, `kvLeasedCommitTodo`; bundled as `kvWritesOk`). Deletes and
lease-free puts and transactions are meaningful again; leased ones wait for T3.

### Unit T3: leases (the plan; not implemented)

- **State**: `σ.leases : List (w64 × Nat)` (id, granted TTL), the lessor's table; a key-value's
  `lease` field already in `σ.kvs`.
- **Transitions**: `LeaseGrant(id, ttl)` (the id fixed before the proposal, `reqIDGen` if `0`;
  `ErrLeaseExists` the identity; TTL raised to the minimum) adds the lease; `LeaseRevoke(id)`
  (`ErrLeaseNotFound` the identity) deletes every key attached to `id` (`σ.kvs` with `lease = id`,
  one revision, sorted as the lessor's revoke deletes them) and removes `id`; a put or a
  transaction naming a lease not in `σ.leases` is rejected (`ErrLeaseNotFound`), else attaches;
  `IgnoreLease` keeps the previous key-value's lease. `LeaseCheckpoint` and keep-alives change no
  `σ` (the remaining TTL is not in `σ`: expiry is not a function of the log).
- **Determinism**: the lessor's lookups at the apply thread must be `σ.leases` (`lessorUser γ.leases
  L` related to the model's table: the apply thread's `leasesKnown` becomes an equality with the
  committed log's lease table), and the lessor's `Revoke` contract (unit 9) must delete exactly the
  attached keys (its item set kept equal to `{k | σ.kvs[k].lease = id}` by `Attach`/`Detach`, the
  put and delete paths).
- **Expiry**: the lessor's expiry loop (`revokeExpiredLeases`, names-only) proposes revocations no
  client asked for. Leases may expire at any time, so a client holding `etcdKV` agrees to any
  revocation: the server's construction takes `□ ∀ id, kvOpAu (.leaseRevoke id) True` (what
  `kvAnyAu` gives), which the expiry loop deposits with its proposals.
- **Specs**: server `LeaseGrant`/`LeaseRevoke` (and `LeaseRenew`, `LeaseTimeToLive`, outside raft,
  no `σ` step), the client's `Grant`/`Revoke`/`KeepAlive`; `kvLeasedPutTodo` and
  `kvLeasedCommitTodo` then become theorems and leave `kvWritesOk`.

## Porcupine: vendored, complete only, a model as closure specs, a driver over TaDa

**2026-10-14 · proposed**

- **Vendored, not forked** (`third_party/porcupine`, a local Goose project like the register):
  upstream v1.3.1 (etcd's `tests/go.mod`), with the one rewrite Goose needs (a labeled `break`
  out of a `select` becomes a `done` flag, `UPSTREAM.md`; upstream's tests pass on it). Its Go
  module path is upstream's, so the translation's names are those etcd's tests import.
  *Rejected:* a GitHub fork (an outward-facing step for a one-hunk change; the vendored copy can
  move to one later, as etcd's `goose-lean` branch).
- **Completeness only**: the specs say a linearizable history is never `Illegal` (and is `Ok`
  without a timeout), not that `Ok` means linearizable. That is what "testing a linearizable
  library never fails" needs, and it makes the search's argument a backtracking invariant
  (`Theory.Inv`: the stack's configurations, a cursor past calls already tried, a cache of
  configurations each on the stack or without completion) with no termination argument
  (partial correctness).
- **The model is specified by its closures** (`ModelSpec`: a deterministic `SeqModel` over
  `(input, output)` interface values, a `rep` of states, a persistent `ioOk` of an
  operation's input and output): what porcupine calls is exactly `Init`, `Step`/`StepContext`,
  `Equal`, `Hash`. `Equal` need only be sound (true ⇒ same state), `Hash` nothing: the cache is
  sound for any hash. *Rejected:* a pure model with the closures as a trusted translation.
- **`StepContext` may refuse on a done context** (2026-10-19): etcd's robustness model returns
  `(false, nil)` once `ctx.Err() != nil` (`nonDeterministicState.apply`), even for a step the
  model allows, so `stepCtxSpec` takes the context (`isContext c cs`) and allows the answer
  `false` with `□ cs.PDone` beside the model's. Never a wrong `true`: the checker would push and
  cache a state that represents nothing. `checkSingle`'s loop carries `⌜Inv⌝ ∨ □ cs.PDone`
  beside `searchInv` (whose pure part keeps only the model-free `FramesPos`): its spec already
  allows `false` with the context done, so no caller's spec changes.
- **`rep` is not necessarily persistent** (2026-10-19, decided with the user): etcd's robustness
  model sorts its states in place in `Equal` (`issues/etcd-robustness-model-equal-mutates.md`),
  so each closure spec takes the `rep`s it reads and gives them back, of the same abstract
  states, and `checkSingle`, which keeps a state value in its stack, its cache and its current
  state, shares each in a non-atomic invariant of a pool it allocates (`Shared.lean`; one
  namespace, since it never opens two at once: `StepContext` opens the current state's, `Equal`
  one cached entry's against the candidate, which is owned). *Rejected:* a persistent `rep`
  (read-only: excludes etcd's model); a freshness premise on `Step`'s result (the separation of
  the old and new `rep`s says it).
- **`[NaInvG GF]` is assumed** (2026-10-19): the non-atomic invariants' camera is iris-lean's
  `NaInvG GF`, and Perennial's ghost state is the one universal camera `allG`
  (`Perennial/Ghost/All.lean`), which does not provide it. So every porcupine and lintest result
  takes `[NaInvG GF]` (`etc/gen-link.py` emits `variable [NaInvG GF]` in the `--porcupine`,
  `--lintest` and `--lintest-counter` modes, as it emits `EtcdModel` in `EM_MODES`): nothing in
  this repository provides it at a `HeapGS`, so these results are conditional on it. The right
  fix is in Perennial: `allG` should provide it (a code for the camera in `allG`'s syntax, or
  `na_inv` rebuilt over `allG`), when the assumption goes. A closed theorem picks a concrete
  bundle with a slot for `NaInvF` (`counterGF`, `lintest/counter/Adequacy.lean`), so it assumes
  no instance.
- **Cancellation as a token**: `checkSingle` returns `true`, or the history is not linearizable,
  or its context's Done proposition holds; `checkParallel` picks that proposition to be "this
  thread called `cancel`", minted from a token it holds until then, so a `false` result before it
  cancels refutes linearizability.
- **The driver is generic** (`examples/lintest`): the library, the inputs and the clock are
  closures with specs (`applySpec` logically atomic, `genSpec` with an input predicate `inOk`
  that `apply` assumes, `clockSpec` logically atomic and monotone); the linearization order is a
  ghost log of the linearization points with the clock value at each. `CounterClock` is proved;
  `MonotonicClock` (etcd's `time.Since`) is not specifiable in Perennial's time model
  (`STATUS.md`, "Porcupine").
- **No alias `Results.lean`** for porcupine and the driver (decided with the user): their
  `Link.lean` results (`porcupine.wp_CheckOperations*`, `lintest.wp_Run`) are the exported
  results, and the Links are the TCB report's roots; a file restating them would only repeat
  them. `lintest/counter/Results.lean` stays: it holds a new statement, `Check` on
  `CounterClock()`'s clock, closed (`wp_CheckCounterClock`).

---

## Changes to Perennial are general-purpose and separate (2026-10-15)

**The user's decision.** Perennial (the Go framework, its standard-library models and Goose) is a
shared, general-purpose dependency. It is not changed to unblock a particular proof here: no model
assumption, axiom or spec is added to Perennial because a proof in this repository is stuck, and no
change is shaped by one proof's needs. When a proof hits a limitation of Perennial (a missing or
too-weak spec, a translator gap, a tactic problem), the limitation is recorded (`notes/STATUS.md`,
and here for the reasoning), worked around locally in this repository (a lemma, a clearly marked
trust-boundary axiom here, or a local override, like `stepLeader.lean`'s `iframe ∗`), and the
general fix is proposed as an independent Perennial change, designed and reviewed on its own. Pin
bumps that bring such general changes are fine.

Why: a change made for one proof's convenience can be unsound for everyone. The cautionary case:
Perennial `9092f8eaa` made `WaitGroup.Add`'s counter overflow a model assumption, to unblock the
cache's proof; the assumption was false, and `105fb79f5` reverted it in favour of thread tokens
(`notes/STATUS.md`, "The wait-group counter and thread tokens"). The rule is in `CLAUDE.md`,
"Changes to Perennial".

---

## The mvcc watch specs for the watch client: `IWF`, per-stream id names, a bounded `nextID` (unit W-M, 2026-10-15 · adopted)

- **What a registration says is the store's choice, `WatchParams.IWF`.** The stream (`watcher.go`)
  is proved over an abstract `watchable` (`isWatchable wa P`), so `watchStream.Watch` cannot name
  the store's `watcherMeta`/`watcherFixed`. As for `IW`, `WatchParams` gains a persistent
  `IWF w r fcs lo` ("`w` has the fixed range `r`, filters `fcs`, first revision `lo`"), returned
  by the contract's `watch` (with the range `watchRangeOf k e endk startRev id`, the store's
  `end == nil` test) and passed through by `watchStream.Watch`; the store instantiates it by
  `watcherIs γ` (names, fixed fields, and `lo` = `startRev`, or for `0` the length of a committed
  log `C` with `idxCert`, what `watchableStore.watch` reads under `revMu`). *Rejected:* stating it
  directly in `watchStream.Watch`'s spec over the store (the stream's spec is generic in `P`, and
  W-S's `recvLoop` uses it at `storeWatchParams` through `wParams`, which unfolds to the same).
- **A watcher's start revision is a fact of its channel entry.** `watchRecvOk` needs
  `startRev ≠ 0 → lo = startRev` for any watcher a response is of; the receiver only has the
  channel invariant, so the fact (`startLo r γw.lo`) is a pure conjunct of `chanWatcher`,
  established at the registration (`watch_register`) and carried by every rebuild of the entry
  (six lemmas). *Rejected:* in `watcherMeta` (its unfoldings use the ghost-map element alone),
  in `respOk` (rebuilt at every send).
- **The stream's ghost names are a structure, `WsStreamNames`** (`tok`, the open token; `ids`, a
  ghost map from an auto-assigned id to its watcher, persistent elements `idAssigned γ id w`), in
  place of the `GName` of the open token: one name per stream, next to the others, rather than a
  second parameter of `isWatchStream` and of every stream spec.
- **`nextID` is bounded, so assigned ids are fresh.** `Watch` with `AutoWatchID` takes `nextID`
  and increments it (and skips live ids); a ghost map insertion needs the id not yet assigned,
  i.e. `nextID` never wraps. The invariant keeps every assigned id in `[0, nextID)` (`idsInv`)
  and, while open, `nextID + aboveCnt nextID WM ≤ |L|` (`aboveCnt`: the live ids at or above
  `nextID`; `L` the watchers ever registered on the channel, the close right's list) with
  `|L| + 3 ≤ 2 ^ 63`: a skip trades a live id at or above `nextID` for one increment, an
  assignment adds a watcher to `L`. The bound on `|L|` comes from the store's watcher budget: the
  contract's `watch` returns `(w :: L).length + 3 ≤ 2 ^ 63` (the registered watchers are
  distinct watchers with names, at most the budget's). *Rejected:* a per-stream token budget in
  `NewWatchStream` (W-S's handler would have to thread it); an unbounded statement (false: after
  `2 ^ 64` increments an id repeats).
- **W-S's control responses carry the watcher, not the id's uniqueness.** `ctrlOk γs γ m` gains
  `ctrlWatcher γ req m`: a registered create response names the watcher (`watcherIs`, the range
  `createRangeOk`). The id's uniqueness (`idAssigned`) cannot be stated there: `watchStreamSpec`
  is a premise of the handler, fixed before `NewWatchStream` allocates the stream's names.

## The stream wire: both ends on grpc's raw streams, the generated wrappers proved, the registration as the handler's premise (unit W-W, 2026-10-15)

The unary specification's author deferred streams; W-W built them in a new file,
`google_golang_org/grpc/InvGrpcStream.lean`, in the same style. The trust boundary is grpc's own
interfaces (`ServerStream` the runtime passes a `StreamDesc.Handler`, `ClientStream`
`ClientConn.NewStream` returns), not the generated code: the generated handler
(`_Watch_Watch_Handler`) and stub (`watchClient.Watch`) are proved over them, through the
generic wrappers (`GenericServerStream`, `GenericClientStream`), whose methods are axioms stated
as their Go bodies because Goose does not translate methods of generic types. W-S's interface
(`srvStreamIs`, on the wrapper) is derived (`srvStreamIs_of_raw`). The stream specification is
fixed per registered method and given to the handler as a premise (`grpcStreamMethodOk`, W-S's
§2a.4), so it must be satisfiable per stream (`streamSpecOk`). A failed send leaves the sender's
token at either list (soundness of the queues' ghost state). The server's stream interceptors are
modelled as a chain of transparent interceptors (they may change the stream's context), their
contracts premises; the client's stream interceptor is inside `NewStream` (etcd's, at no retry),
as P3a had the unary one before proving it. Details: `notes/grpc-stream-spec.md` §6.

## The stream interceptor's require-leader premise (unit W-W, the stream interceptor, 2026-10-15 · adopted)

`newStreamInterceptor` is proved against the generic contract (`srvStreamInterceptorOk ic
True`) for every path but one: when the client's metadata has `hasleader: true`, it wraps the
stream in a `serverStreamWithCtx` with `newCancellableContext(ss.Context())`, registers it in the
leader monitor's map and cancels it on return. That branch is excluded by a premise,
`v3rpc.runsNoRequireLeader`: at every run context, `metadata.FromIncomingContext` returns no
metadata or metadata whose `hasleader` values do not start with `"true"`. It stands in for the
generic `FromIncomingContext` triple in the proof, so the branch's condition is false and the
handler gets the same server end and context (`st' = st`, `ci' = ci`, which the contract allows).

*Why the branch is not proved.* The handler would need the wrapper's context to be a run
context (`isContext ci' cd' ∗ grpcRunCtx ci'`). Perennial's `WithCancel` over a general parent
(`wp_WithCancel_any`) gives a child whose `Value` is not related to the parent's, so
`grpcRunCtx` does not transfer: a Perennial limitation, whose general fix (a `WithCancel` spec
over any `isContext` parent keeping its `PDone` and delegating `Value`, from `wp_WithCancel_gen`
and `wp_propagateCancel_any_of`) is a Perennial change of its own, not made here (CLAUDE.md,
"Changes to Perennial"). And the wrapper is not a context at all: its `Err()` can be non-nil
while `Done()` is open (`issues/etcd-stream-interceptor-err-before-done.md`), so even that fix
would leave `isContext` of the wrapper false. Proving the branch would mean specifying a
non-context as a context.

*Why a premise, not a local axiom.* The fact is about the deployment, not about Go or grpc: no
client of the slice (the recipes, the cache, through `clientv3`) calls `WithRequireLeader`, the
only way the pair gets into a stream's outgoing metadata, and grpc carries a stream's metadata
from the client to `FromIncomingContext` (its transport, part of the trust base already). A
local axiom would claim it for every client of every server; as a premise of
`newStreamInterceptor.spec` and of `etcd_watch_served_etcd_chain`, it stays visible in the result
and in no TCB count, and a closed proof discharges it: the client-side derivation (W-C) shows the
slice's clients send no `hasleader` key, and the transport's metadata claim (the client's
outgoing metadata is the server's incoming metadata) carries that to the run context. The
premise is deliberately weak (a `hasleader` key with another value is allowed) so that the
API-version and metrics paths are proved for any metadata. *Rejected:* proving the branch with a
local `isContext` axiom for `cancellableContext` (false: the finding above); dropping the
branch's metadata path from the spec (the API-version check and the metrics run first and are
proved).

---

## The client's watch over the stream: per-stream answer and id tokens, run's dispatch cursor, premises for what the server does not yet state (unit W-C, 2026-10-15 · adopted)

- **A created response is the head's**: the client sends one create at a time (only the head of
  `resuming`), and the server answers each request at most once: `recvLoop` mints an exclusive
  answer token per received request (`ansTok`, from a pool named in the stream's auxiliary name)
  and hands it with the control response. `run` keeps the tokens of the answered positions, so a
  `Created` answers the one unanswered create. *Rejected:* a monotone "answered position" in the
  response model (a ghost field of `WatchRespM` and a send-order invariant in `sendLoop`: more
  W-S surgery for the same fact).
- **The stream's auxiliary name** (`StreamNames.aux`, `streamAuxTok`/`streamAuxIs`): the handler
  allocates its per-stream ghost state (the mvcc stream's names `γo`, the answer pool `γa`) after
  the stream specification is fixed, and publishes them once; the specification can then name
  them (`ctrlOk`'s `∃ γo γa, streamAuxIs γs (auxOf γo γa)`), and agreement makes every response's
  names the same. A new field of `StreamNames` and one premise of `grpcStreamMethodOk`: the
  stream interceptors' contracts are unchanged.
- **An announced id is new** (`idTok`, an exclusive token per id `watchStream.Watch` assigns,
  beside the persistent `idAssigned`): without it a second `Created` with an id `run` already
  registered (and whose substream the server's `Canceled` made it close) would let `run` send on
  a closed channel in the model; with `idLive` (an mvcc response's id is live after the responses
  before it: the send loop's `ids`) no response reaches a closed substream.
- **`run` dispatches with the contract's facts already established** (`recvElem`): each response
  sent to a substream carries `rangeWatchRespOk` relative to `run`'s dispatch cursor `γhi`, a mono
  list `run` extends at each successful send; the substream publishes it on `outc` with the
  contract's own cursor `γ.cur`. A failed send (the substream stopped: the select took `donec`)
  leaves `γhi` as it was, and later sends to it carry the stopped goroutine's exit flag instead
  (`γx`, published by `donec`), so the cursor never has to account for an undelivered response.
- **What the server does not state is a named premise** (S2 `srvProgressAllAnswers`, S3
  `srvEventIdsAssigned`, S4 `srvWatchCert`), each a fact of etcd's server that needs the mvcc
  channel invariant to name stream-level facts (S2, S3) or the commit point moved (S4); and
  `srvNoDupKeys` (no revision writes a key twice), which etcd's server does not guarantee
  (`issues/etcd-txn-check-intervals-sibling.md`). *Rejected:* weakening the clients' contract
  (it is fixed: the cache and the recipes rest on it).
- **The reconnection is excluded, not proved** (`noRetryableStreamErr`): `watch.go`'s resume can
  send on a closed channel (`issues/etcd-watch-resume-closing-substream.md`), so no proof of
  `run` covers it; the premise names the transport's codes `run` retries on.

## The watch client's server facts in the mvcc channel invariant (unit W-M2, 2026-10-16 · adopted)

- **Registration-time facts live in the channel's invariant**, the only thing `sendLoop` (which
  never takes `ws.mu`) can open, and they must be there before the first response for the
  watcher, which `notify` may send before `watchStream.Watch` returns. So `watchableStore.watch`
  takes a **registration callback** (`∀ w, ⌜w ≠ null⌝ -∗ |==> chanIdAssigned γc id w ∗ Back w`,
  the caller's `Back` returned): the store applies it as it adds `w` to the channel's registered
  list and keeps `chanRegFact γc w` (the watcher's fixed id assigned to it, not `-1`) for every
  registered watcher; the stream's caller supplies it from its id map's authority (the map is the
  channel's: `γo.ids = γc.ids`). *Rejected:* per-registration id tokens in `chanWatcher` (the same
  fact, more surgery in every lemma over `chanWatcher`); an explicit id (`watchStream.Watch` with
  `id ≠ 0`) — it can be a reused one (`issues/etcd-watch-id-reuse-stale-events.md`), whose
  watcher cannot be inserted; the stream's spec covers auto ids, the only ids the server under
  `watchReqOk` uses.
- **The progress fact is a saved proposition fixed at the channel's creation** (`prog`,
  `progFact g := ∃ Q, savedPropOwn g □ Q ∗ □ Q`): mvcc cannot name the gRPC stream's request
  queue, so the handler chooses what a response of id `-1` means (`NewWatchStream`'s `Q`, the
  server's `progQ γs := ∃ i, upAtW γs i .progress`), `recvLoop` provides it at
  `RequestProgressAll`, the channel invariant keeps it with every response of id `-1` sent, and
  `sendLoop` gets `Q` back by agreement (under a later, stripped because `progQ` is timeless).
  *Rejected:* an `IProp`-valued field of `WatchChanNames` (a parameter of every predicate over the
  channel's names, for no gain).
- **S4 stays a premise: a certificate issued at the seal is unsound for the server proof's
  reads.** The planned fix (an `idxCert` over a sealed-log mono list, so a watch event's revision
  is certified at the notify) would make every certificate a floor that `store.Read` no longer
  meets: `watchableStoreTxnWrite.End` notifies before `storeTxnWrite.End` bumps `currentRev`, and
  a read (`s.mu.RLock`, `revMu.RLock`, not the watchable store's lock) in between answers the
  previous revision. The clients' contracts allow it (serializable gets get no floor), but the
  server proof's `store.Read` (`log₀ <+: log`) and `rangeReplyOk` (`F <+: log`, serializable reads
  included) do not. Fixing it needs committed certificates for `store.Read` and its callers, no
  floor for serializable range replies, and a linearizable-read argument that a floor sealed
  before the request is committed when the read is served (the apply wait): the user's call.

## Sealed logs for the watch path, the clients' model over sealed logs (unit W-M2b, 2026-10-16 · adopted)

- **The watch path carries a seal, not a certificate.** `mvcc.idxSealed γ log` is `idxCert`
  without the committed log's lower bound (and the events' count): the history's lower bound and
  the log's well-formedness, both available at the seal (`idxWriter_seal`, from `IdxWf`). Two
  sealed logs are in prefix order through the history alone (`histOf_cmp_log`), which is all the
  watch facts and the clients' model's laws need. *Rejected:* a certificate issued at the seal
  (W-M2: every certificate is a read floor that `store.Read` does not meet in the gap between
  `notify` and `storeTxnWrite.End`'s commit); `idxSealed ∗ idxLogAuth ⊢ log <+: ilog` (false in
  the gap; the writer has `histOf_prefix_shape_log`).
- **Reads keep `idxCert`.** `idxCert` means committed; `store.Read`'s `log₀ <+: log`,
  `rangeReplyOk`'s `F <+: log` and every floor stay. The model's `etcdState` and `EtcdStep` are
  over sealed logs (`srvLog`): their laws are about one log's content and are not floors, and the
  read path reaches them through `idxCert_sealed` (`etcdState_of_cert` a corollary).
- **`etcdReachedAt` stays over certified logs** (superseded by unit W-M3: over `certOk`, with the
  floors from the clients' updates), against the brief's design: `etcdReached lo` is
  the floor of a later read (`floor_of_reached` into `rangeReplyOk`), so over sealed logs it
  would need the floor the W-M2 failure is about. What a watch event's `etcdReached e.rev` needs
  is therefore the narrowed premise `srvSealedReached` (a sealed log's revisions are reached),
  false in the gap as S4 was, now confined to reachedness. Its discharge is W-M2's server-side
  redesign (committed certificates for reads, no floor for serializable replies, a
  linearizable-read argument through the apply wait).
- **The size and no-duplicate premises move to sealed logs** (`storeSmall`, `srvLogsSmall`,
  `srvNoDupKeys`): their justifications (the store's size; a transaction's writes per revision)
  do not depend on the revision being committed.

## `etcdReached` as a committed KV certificate; floors from the committed state (unit W-M3, 2026-10-16 · adopted)

- **`etcdReached r` is a certified log's revision**: `srvReachedAt E r := ∃ log, certOk E.γ log ∗
  ⌜sint.Z r < log.length⌝`, where `certOk` (mvcc's caller's certificate, unit T1) is, for the
  server, the KV model of a committed raft prefix (`kvCertInv`, `kv_cert_read`). The apply thread
  mints it for an entry's log before applying the entry, and `watchableStoreTxnWrite.End` takes it
  (`certOkNext`) before it notifies, so a watch event can carry it (`mvcc.evLog`: `idxSealed` and
  `certOk`), and S4 (`rangeWatchEvOk`'s `etcdReached e.rev`) is a theorem (`ev_ok`).
- **Why not mvcc's certificate (`idxCert`) as the floor.** `idxCert` means committed in mvcc:
  every later read's log extends it (`store.Read`'s `log₀ <+: log`), serializable reads included.
  A notified revision is not yet committed in mvcc (etcd takes `revMu` only in
  `storeTxnWrite.End`, after `notify`), so a certificate at the seal (W-M2) or `etcdReached` over
  sealed logs (W-M2b) made a serializable read's floor false. The clients' model never asked a
  floor of serializable reads (`kvGetResult`: `serializable = false → lo ≤ r`), and the
  linearizable floor is a raft fact: a linearizable read linearizes at the committed KV state,
  which extends every log the server certified. So the floor moves from mvcc to the clients'
  atomic updates (T1/T2), and the specs' mvcc floor `F <+: log` stays as an mvcc fact for a caller
  that holds an `idxCert F` (in the derivations, the read side's first certificate).
- **The floor mechanism: a monotone counter in the client's invariant**, not a snapshot in the KV
  ghost state. A client holding `etcdKV` keeps it with `monoNatAuthOwn γm 1 σ.rev`
  (`kvClientInv`); at a request, opening its invariant and the server's (`kvInv`, `kvCertInv`,
  `srvRaftLogInv`), `etcdKV σ` agrees with the committed log's state, which extends the certified
  log (`kv_cert_floor`), so the counter's lower bound is at least the certified log's last
  revision (`kv_client_floor`); at the firing, the counter is at least that bound (every update
  moves it up, `kvOpStep_rev`), so the update's result is the floor (`kvAnyAu E γ`). *Rejected*:
  the brief's snapshot authority inside `etcdKV` (a mono list of the state's log in halves with
  `kvInv`, lower bounds minted with each certificate in `kvCertInv`): it changes `etcdKV`, `kvInv`,
  `KVNames`, `kvInv_alloc` and every firing of T1/T2 (`kv_prop_au`, `kv_noop_au`, `kv_fire_reads`,
  `kv_read_compose`) for what a client's own invariant gives without touching them; (a) the
  snapshot in `kvAu`'s atomic precondition (the same churn in every update's statement); (b) a raft
  index argument (`committedAtLeast` from `srvRLogLb`): the server's committed index lags raft's,
  so a certified log's raft prefix gives no `committedAtLeast`.
- **The update's state is the write's** (needed for the writes' floors): the proposer's witness is
  collected at the occurrence the reply is of, and the result now names the log the entry met
  (`resultIsW`, `appliedOk`, `entryWit` take `lb`; the apply thread builds `entryWit` at the entry's
  position after its applied raft log), so `EtcdServer.Put`/`DeleteRange`/`Txn` give `□ Q (kvStateOf
  x.log)`, T2's "refinement for the next unit". A read-only `Txn` takes a read deposit as `Range`
  (the same read loop): its linearizable floor is its read update's result at the state read.
- **A writing transaction with a lease** has no update (T3), so its premise
  (`kvLeasedCommitTodo`) is now stated in the clients' model (`txnCommitResultTok` from
  `etcdReached lo`), as `kvLeasedPutTodo` was.

## What a progress response covers (unit W-K, K1b, 2026-10-17 · in progress: K1b-1, K1b-2 built)

**The claim the client needs.** A progress response at revision `p` on a watch means: the watch
has received every event of its range up to `p` (the cache's `EtcdStep c p pfx []`). A per-watcher
progress response (`WithProgressNotify`, `progress(w)`) is for one watcher; a broadcast (id `-1`,
`RequestProgressAll`) is for every watcher in the stream's map `ws.watchers` when it is sent, and
the client applies it to every substream it has (`broadcastResponse`).

**Where the knowledge is.** mvcc knows the map `M` given to `progressIfSync` (its watchers all
synced, so delivered up to the store's revision: `synced_d` and K1a's `wlogQ_cert_prefix`); which ids
the stream assigned (`idsInv`) and which it cancelled (`Cancel` removes from `ws.watchers`); the
order of the channel (O1's sent list). Only v3rpc knows why a watcher was cancelled (a client
cancel request, `recvLoop`), and only the client knows its substream is live.

**The design (mvcc-centric).**
- *Registration index* (M1): a watcher registered on a channel records the channel's sent length
  then (`chanRegAt γc w n`, a persistent element of a ghost map whose authority is with the sent
  list's, keys among the registered watchers, values at most the sent length).
- *Cancellation record* (M2): `watchStream.Cancel X` records `cancelAt γo X n` (`n` the sent length
  then) with the caller's reason, a saved predicate fixed at the stream's creation (v3rpc: "the
  client sent a cancel request for `X`", `∃ i, upAtW γs i (.cancel X)`, which `recvLoop` has when it
  calls `Cancel`).
- *Coverage* (M3): every progress response at channel index `k` with covered set `C` (the map's
  watchers) carries, persistently in the channel invariant: (a) every `w ∈ C` has its deliveries
  before index `k` cover the revisions `[lo, rev + 1)`; (b) for id `-1`, every id `X` the stream
  assigned to a watcher `w` registered at an index `≤ k` has `w ∈ C` or was cancelled at an index
  `≤ k` (the stream's lock invariant: an assigned id is in `ws.watchers` until `Cancel`); (c) for a
  watcher's own id, its watcher is in `C`.
- *v3rpc*: `createdAfter` adds that the created watcher was registered before its snapshot `l0`
  (`recvLoop` takes `l0` after the registration); `mvccOk` exports a response's channel index and
  coverage.
- *Client* (K2): a broadcast at down position `j` after a substream's `Created` at `jc < j` has
  channel index at least the snapshot's length (O3: every id `-1` response before the snapshot was
  sent before `jc`, each response is sent once), so after the registration; the substream is live
  and never sent a cancel request for its id, so not cancelled (the reason predicate); so its
  watcher is in `C` and the response covers it.

*As built (K1b-2, 2026-10-17).* The registered watchers at the send are the channel's own
(`RespM.regs`, read in its invariant), so no caller names them. The cancellation reason is per
watcher through its range id (`rsnW`: `rsnFor γc.rsn r.id`), the stream's invariant keeping each
map entry's id, so `Cancel id` needs only `rsnFor γ.rsn id`. *Why the callers lend a resource
`CS` with a persistent extraction (`complW`, `complWS`) instead of a disjunction:* the stream must
get its close right back, and a disjunction returned as is loses which branch held it (a closed
stream has no close right, only "every watcher of the map cancelled"); with `CS` lent and
returned unchanged, and the branch of `progCompl` a Boolean parameter, nothing is lost.
*Rejected:* a cancellation record with a sent index (`cancelAt γo X n`): the reason is enough, a
watcher cancelled for its reason being one the client asked to cancel, so the client's live
substream is never one.

*Rejected:* the claim attached by `recvLoop` (its live set) after `progressAll` returns: `sendLoop`
may forward the response first. *Rejected:* a client-side fix (`issues/etcd-watch-progress-before-created.md`).

## The client's watch made complete with a second cursor (unit W-K, K2e, 2026-10-17 · adopted)

**The choice (the user's).** The client's channel contract (`rangeWatchElem`, `rangeWatchRespOk`)
keeps its cursor at the last event's revision and promises soundness only; the cache's
(`watchRespOk`) moves its cursor to a progress response's revision and needs completeness. The
client's element gains a completeness part with a second cursor; `rangeWatchRespOk` and its
consumers (recipes, Election, leasing, `waitDelete`) stay, changed only by one more pattern slot.
`isEtcdWatcher` is read off the second cursor. *Rejected:* one cursor with the new meaning (the
consumers' proofs redone for progress responses).

**What it rests on.** A watch never resumes onto another gRPC stream (the transport premise
`noRetryableStreamErr`), so completeness is per server stream. Under `s.mu` a progress revision
is the notified log's last (`rev()` is lent the lock's fraction of the committed log, K2e-1).

## The recipes are verified against the closed-watch fix (unit W-Q, 2026-10-16 · adopted)

**The rule and the precedent.** The verified etcd is upstream main plus the commits that make it
translatable plus bug fixes only ("No code changes unless a bug"): until now the one fix of
`cache-ready-after-retry` (`64313a1f8`). The recipes' closed-watch findings
(`issues/recipes-dequeue-closed-watch.md`, `issues/recipes-barrier-wait-closed-watch.md`) are bugs
(a reachable nil dereference in `Dequeue`, a false release in `Barrier.Wait` and
`DoubleBarrier.Enter`), so their fix qualifies. The user decided to fold it in: the fork commit
`0aa6c6af8` (branch `recipes-closed-watch-channel`) is cherry-picked onto `goose-lean` as
`0df483bee` (the conflict with the Gooseable rewrite of `waitEvents`' loop resolved by keeping the
rewrite and adding the fix's lines), the pin `etc/goose.py` names.

**Why not keep the premise.** The recipes' proofs took `isEtcdRangeWatcherOpen` (the range-watch
contract with the SPSC close predicate `False`) as a premise of the client bundle. The watch slice
(W-C) proved that etcd's client watcher meets only the closable contract `isEtcdRangeWatcher`
(close predicate `True`), and the Open variant is false of it: `watch.go` closes the channel when
the watch's context is done, on `Close()`, on a halting stream error, when the server cancels the
watch (a compaction past its start revision), on a failed create. It is not a corollary of
`isClientWatcher V w` under any persistent fact about `w`: what would make it true (a context never
done, no `Close`, a transport that never fails, a server that never cancels) is about the
environment's future, not the watcher. *Rejected: a refined premise* (a per-watch promise of no
cancellation and no close while a recipe waits, or a liveness premise on etcd's compaction): it
would be a premise on how the client is used and on the server's compaction policy, which the
code as shipped silently mishandles when it fails; stating it would not gain trust in any result
over the recipes' behaviour, only move the bug out of the statement. With the fix the premise is
unnecessary.

**The fix** (`watch.go`, `client.go`): `waitEvents` returns `(*clientv3.Event, error)`; a response
whose `Err()` is non-nil (a canceled watch: `ErrCompacted`, ...) returns `(nil, err)` before its
events are read; a channel that closes before the awaited events returns `(nil, ErrWatchClosed)`,
a new package error. `WaitEvents`/`WaitPrefixEvents` return that pair; their callers already
propagated `WaitEvents`' error (`Dequeue`: `"", err`; `Barrier.Wait`, `DoubleBarrier.Enter`/`Leave`:
`err`; `RWMutex.waitOnLastRev`: `false, err`).

**What the proofs now say.** `waitEvents.spec` is over the closable channel: `(ev, nil)` with the
awaited event (`waitedEvent`) and the consumer token back, or `(nil, err)` with `err ≠ nil` (the
consumer token not returned: a close consumes it, `spsc_rcv_au`; the callers drop it anyway). The
error branch reads `wresp.Err()`'s spec, whose precondition `statusErrOk` the element predicate
carries, and `ErrWatchClosed` from `recipesInit` (a fixed non-nil error, as the four others).
`WaitEvents`/`WaitPrefixEvents`: `(⌜err = nil⌝ ∗ waitedEvent …) ∨ ⌜err ≠ nil⌝`. The callers' specs
already had an error disjunct: they take it on a closed or canceled watch; none changed form. The
bundle `isEtcdRecipesClient` takes `isEtcdRangeWatcher`; `isEtcdRangeWatcherOpen` is deleted. So
the queue is end to end over etcd's real client watcher (`queue_end_to_end_client`: the watcher
contract from `isClientWatcher V w` by `isEtcdRangeWatcher_of_watcher`, at `V.R.E = E` and
`V.pfx = kp`), with no premise about the watch beyond the wire's (`watchConnFacts`).

## Retargeting raft in a parallel tree

**2026-10-15 · accepted (stage R0, branch `raft-retarget`)**

- **The target is v3.7.0 plus the read-index fix**, not upstream's tip and not v3.7.0 alone: v3.7.0
  is what etcd's `go.mod` links (`go.etcd.io/raft/v3 v3.7.0`), so the retargeted proof can discharge
  the server's raft contract (`isRaftNodeIfc`, today a premise) and retire `EtcdDeps/`; and v3.7.0
  still has the single-voter read-index shortcut of `issues/raft-readindex-singleton-stale.md`, which
  a spec could exclude only by restricting runs (stage F's reasoning, "Verifying a fork revision of
  raft"). The fix is rebased onto the pointer code as one commit (`509271dac`, branch
  `raft37-goose-lean` of the etcd fork), the same meaning as on `40f8be7`: the shortcut only at a
  voter leader with a commit of its term. *Rejected*: upstream's tip (etcd does not link it);
  v3.7.0 unfixed (the stale read stays reachable).
- **A parallel tree, not an in-place retarget.** The earlier attempt (2026-10-09, branch
  `raft-upstream-1c0011d2-wip`) showed that the retarget is a redesign of entry, message and
  snapshot ownership touching most of 100k lines; done in place, `lean` would not build for weeks
  and no other unit could merge. So raft v3.7 is translated into a module root of its own,
  `Raft37/` (`Raft37/{Code,GeneratedProof,Spec,Proof}`), the proof is rebuilt there file by file
  (copying and adapting the old one), and when it reaches the old proof's results the trees are
  swapped in one commit (`Raft37/*` becomes `Code/go_etcd_io/raft`, `Spec/...`, `Proof/...`; `EtcdDeps`
  retired; the server imports the verified raft). Both trees define `Perennial.go_etcd_io.raft.v3.*`,
  so no module imports both; `etc/proof_roots.py` runs Lean on each part root's roots apart, as for
  `EtcdDeps`.
- **A project with a root, not a `Part`.** A `Part` translates more packages of its project's own
  checkout (etcd's raft dependency, from etcd's module graph); raft v3.7 plus the fix is another
  repository revision. So `etc/goose.py`'s `Project` gained `root` (default `""`: `Code/`), the least
  change: `pieces()` emits it as the main piece's root, `etc/proof_roots.py` counts project roots as
  part roots, and `etc/verified-code.py` keys a rooted project's packages `<root>:<path>` so that its
  Go functions are counted apart from etcd-raft's (same Go paths). `etc/gen-link.py --raft37` is a
  Lean-first mode whose specs are looked up in `Raft37/Spec` only.
- **The model's data become pure records** (stage R0, provisional; `notes/raft-retarget-plan.md`, D1).
  The protocol model used gogoproto's Goose values (`raftpb.Entry`, `raftpb.Message`,
  `raftpb.ConfChangeSingle`) as plain data; in v3.7 those structs hold pointers and protobuf state.
  `PbModel.lean`'s `EntryM`, `MessageM`, `ConfChangeSingleM` keep the old field names, so the model
  ports by a type rename; porting `quorum`/`tracker` needed it because their shared definitions
  import the model. The names and the rest of the design are for the review of the plan.

---

## The protobuf runtime as raft's trust boundary

**2026-10-15 · accepted (stage R1 of the raft v3.7 retarget, branch `raft-retarget`)**

In raft v3.7 the raftpb messages are protobuf-go v2 structs: pointer fields read through
generated getters, plus three fields of protobuf's runtime (`state`, `sizeCache`,
`unknownFields`); marshalling, sizing, cloning and comparing go through
`google.golang.org/protobuf/proto` (names-only in the translation). The proof's boundary is
drawn there:

- **Translated and proved**: everything raftpb's own Go code does: the 40 getters, the four
  `Enum()`s, `Ensure*` (`raftpb/util.go`), the conf-change codec (`AsV1`/`AsV2`, `EnterJoint`,
  `LeaveJoint`, `MarshalConfChange`) and `ConfState.Equivalent`. None of it needs the runtime's
  internals: the getters read the pointer fields, the rest calls `proto.*`.
- **Axioms: exactly the `proto.*` calls raft makes, one spec per message type it makes them at**
  (nine: `Clone` of an `Entry`, `Snapshot`, `ConfState`; `Size` of an `Entry`; `Marshal` and
  `Unmarshal` of a `ConfChange`, `ConfChangeV2`; `Equal` of two `ConfState`s), stated over the
  `InvPb.lean` predicates (`Spec/google_golang_org/protobuf/proto/`), each justified in its
  docstring against protobuf-go v1.36.11 (`proto/merge.go`, `size.go`, `encode.go`, `decode.go`,
  `equal.go` and `internal/impl`): a clone is a fresh deep copy and only reads the source; a
  size is some non-negative `int` (no spec fixes one: `entsSize`/`limitSize` leave sizes
  unspecified, and proto2 presence makes the exact size depend on which fields are set); marshal
  cannot fail on proto2 `raft.proto` (no `required`, no `string`, a fraction excluding concurrent
  writers) and its output decodes back (the round trip is the postcondition, no pure encoder is
  claimed); unmarshal resets the message, never panics, copies the bytes out; `Equal` is record
  equality under the premises below. One spec per type, not a generic `proto.Message` spec: a
  generic one would need a reflective model of messages that nothing here uses. *Rejected*:
  translating protobuf's runtime (reflection, `unsafe`, atomics: Goose translates none of it).
- **The hidden fields are an invariant, not a field of the predicates** (Q4): `pbMsg T l uf`, one
  per object, persistent, made once at allocation (`pbMsg_alloc` from the fresh struct's zero
  fields) and taken only by the axioms. Because `proto.Size` (and `Marshal`) store the size cache
  atomically into the message (`internal/impl/encode.go:118-129`), on log entries that the
  unstable log, `MemoryStorage`, `MsgApp`s and `Ready` share read-only (`entsSize`, `limitSize`):
  a read-only entry fact (`entRO`, D2) holding `sizeCache` would contradict that write, and a
  fraction of it would not allow it. Inside an invariant the write is the runtime's business and
  every holder's fact stays persistent. *Rejected*: ignoring the hidden fields (the atomic store
  would be outside the model, i.e. a heap write the model says does not happen); owning them with
  the struct (makes every log entry fact non-persistent for a field verified code never reads).
- **What it replaces.** The old proof (gogoproto, `40f8be7`) had: the generated
  `raftpb.ConfChange{,V2}.{Marshal,Unmarshal}` as axioms, now `proto.{Marshal,Unmarshal}ConfChange{,V2}`
  (stating the same codec, `ccDecodeV1`/`V2` of `CCModel.lean`); `reflect.DeepEqual` on two
  `ConfState` values (`Equivalent`; "`ConfState.Equivalent`: `reflect.DeepEqual` is the axiom"
  above), now `proto.EqualConfState`, and with it the nil-versus-empty bookkeeping goes
  (`proto.Equal` treats them alike, so `wp_slice_append_nil_empty` is not needed);
  `gogoproto.Equal` (in `LeaveJoint`) with no replacement, since v3.7's `LeaveJoint` tests the
  getters; and the generated `Entry.Size`/`sovRaft`, translated and proved before, now the
  `proto.SizeEntry` axiom. The new `Clone` axioms have no old counterpart (gogoproto values were
  copied by value). The old axioms stay in the baseline until the swap (R6).
- **Unknown fields bear on `Equal`'s statement.** `proto.Equal` compares unknown fields, so
  `EqualConfState` could not honestly say "equal configurations give `true`" for conf states
  that carry some; it is stated for two conf states with none, which `csPts` records
  (`pbMsg raftpb.ConfState p []`), and with both `AutoLeave`s set (as `Equivalent` makes them;
  an unset optional `bool` is unpopulated, not `false`, to `Equal`). The restriction is a real
  one in the code: a `ConfState` with an unknown field (written by a newer raftpb) is "not
  equivalent" to the same configuration and `raft.restore`/`newRaft` panic
  (`issues/raft-confstate-unknown-fields-panic.md`, reproduced); the later `restore`/`newRaft`
  specs inherit it as a premise. Other messages' predicates keep their unknown fields
  existential (`entPts`, `msgPts`, ...): no axiom there compares them.

---

## The log layer over read-only entries: the storage contract of raft v3.7

**2026-10-15 · accepted (stage R3 of the raft v3.7 retarget, branch `raft-retarget`)**

Raft v3.7's log layer (`log.go`, `log_unstable.go`, `storage.go`, the size helpers) holds
`[]*pb.Entry` slices whose entries several holders share (the unstable log, `MemoryStorage`, the
slices `slice`/`Entries` hand out, `MsgApp`s, `Ready`), and `*pb.Snapshot`/`*pb.HardState`/
`*pb.ConfState` pointers. The decisions D2, D4 and Q6 of `notes/raft-retarget-plan.md`, as built:

- **An entry slice is its pointers plus a persistent fact per entry** (D2): `entsPts s dq es :=
  ∃ ls : List Loc, s ↦*{dq} ls ∗ [∗list] l;e ∈ ls;es, entRO l e` (`InvPbLog.lean`), `entsRO` at
  `□`. It replaces the old `s ↦*{dq} es` of gogoproto values one for one, so every predicate kept
  its shape (`ownUnstable`'s and `ownRaftLog`'s unstable suffix, `memstorageFields`' entries with
  the dummy, `scanClosure`'s pages, the specs' results) and every pure statement (`List EntryM`)
  its text; the slice reasoning (capacities, sub-slices, `append`, the adoption of a message's
  backing array in `truncateAndAppend`) is the old one on `List Loc`, and the big-sep, persistent,
  goes along with take/drop/append for free. The pointer list is existential: no spec names a
  location. *Rejected*: the `List Loc` in the records (a physical detail in pure state, against
  "Predicate indices"); a non-persistent per-entry fraction (raft never writes an appended entry,
  and `proto.Size` writes only the hidden size cache, `pbMsg`'s).
- **Snapshots are owned and cloned at every boundary** (D4), and the log's own copy is frozen:
  `unstable.restore` stores `proto.Clone(s)`, which nothing writes after (`nextSnapshot` and
  `raftLog.snapshot` clone it again), so `ownSnap`/`pendKsn` hold it as `ownSnapM p □ sv`
  (persistent, as the old `p ↦□ sv`). Every snapshot a spec returns is a fresh clone at full
  ownership (`raftLog.snapshot`, `unstable.nextSnapshot`, `MemoryStorage.Snapshot`/
  `CreateSnapshot`); every snapshot a spec takes is read at a fraction and given back
  (`raftLog.restore`, `unstable.restore`), except `MemoryStorage.ApplySnapshot`'s, taken at `1`
  because `EnsureSnapshot` writes its nil fields (Q5) and given back.
- **The storage contract models `MemoryStorage`** (Q6): `Entries` hands out the storage's own entry
  pointers, read-only and for good (`entsRO`, `cap = len` as before); `Snapshot` a fresh clone,
  owned, its id, conf-state lists and `AutoLeave` the storage's state's; `Append` keeps the
  caller's pointers, so it takes them as `entsPts` (each entry `entRO`). `InitialState` stays out
  of `isStorage` (as before): `MemoryStorage.InitialState` is specified for its single call at
  construction, on `ownMemoryStorage` and the application's `memStorMeta` together; it returns the
  storage's own hard-state pointer (`hsOpt`: `nil` until the first `SetHardState`) and lends its
  conf state at full ownership with its `AutoLeave` set, with a wand back.
- **`MemoryStorage`'s snapshot is the owner's, not the lock's.** In v3.7 `Snapshot()` writes the
  field (`ms.snapshot = EnsureSnapshot(ms.snapshot)`, `storage.go:212`) and `InitialState`, unlocked,
  reads it and may write its conf state's `AutoLeave` (132); `CreateSnapshot` writes the object's
  metadata in place (255-261). All four callers hold `ownMemoryStorage` (raft through
  `isStorage`'s `Snapshot`; the application for `ApplySnapshot`/`CreateSnapshot`, which need the
  owner's view anyway, and for `InitialState` at construction), so the field and the object went
  into `ownMemoryStorage` (`memSnapOwn`), and `memStorMeta` keeps half of `hardState` and the
  unlocked counter only. *Rejected*: halves of the snapshot between the lock and `memStorMeta` (the
  old design): `Snapshot()`'s store needs the whole field under the lock, without `memStorMeta`.
- **`EnsureSnapshot` returns its metadata set** (`ownSnapE`; stage R1's post was `ownSnapM`, whose
  metadata may be `nil`): `CreateSnapshot` writes `ms.snapshot.Metadata.Index` right after it.

**What the old contract promised that the new one does not**: the snapshot `Storage.Snapshot`
returned came with the storage's `ConfState` slices read-only for good (`ownCSL`), which raft put in
a `MsgSnap` and the message abstraction read; now the caller owns a fresh clone (strictly more
for the caller, but a `MsgSnap` holds its own copy, which R4's message predicates take into
account). `Append` copied the entry values (only the slice was lent); now the storage keeps the
pointers, so the entries must be frozen (`entRO`) before they are appended -- true of every batch
raft hands out (a `Ready`'s entries are the log's). `CreateSnapshot` read `cs`'s slices and kept
them; it now clones `*cs` (read at any fraction, given back) but keeps the caller's `data` slice,
whose bytes it now owns (`data ↦* bs`, full: the stored snapshot holds them; the old spec tracked
no data bytes). **The reverse**: `InitialState` now needs the owner's `ownMemoryStorage` besides
`memStorMeta` (it touches the owner's snapshot), and its spec is for construction only; the
snapshots and hard states are pointers with nil cases (`hsOpt`, `nil` from `CreateSnapshot`'s
error path, `nextSnapshot`'s `nil`).

## `raft.go` over pointer messages: the outbox owned, `Step` takes the message (stage R4 of the raft v3.7 retarget)

**2026-10-15 · proposed (stage R4, branch `raft-retarget`)**

Raft v3.7's `raft.go` builds every message as `&pb.Message{...}` with `new(x)` cells and `.Enum()`,
reads every field through a getter, writes into the message it is stepping (`stepFollower` sets
`m.To` and forwards `m`; `send` sets `From`/`Term`; `stepLeader` replaces slots of a proposal's
`Entries`), shares cells and slices between a request and its response (`To: m.From`, `Context:
m.GetContext()`, `Entries: req.GetEntries()`), clones a proposal's entries before stamping them
(`appendEntry`), and returns and takes `*pb.HardState`/`*pb.ConfState`/`*pb.Snapshot`. The
decisions D3 and D4 of `notes/raft-retarget-plan.md`, and Q2/Q3, as they are built for the raft
layer (`InvRaftPhys`, `InvMisc`, the `raft.go` specs):

- **The outbox holds owned messages** (D3, Q2): `ownRaftPhys`'s `r.msgs`/`r.msgsAfterAppend`
  are `List Loc` slices (capacities owned, as before) and `outboxRel o msgs msgsAA` is the old
  text with `msgAbs m a` replaced by `msgQ l a := ∃ st, msgOwn l 1 st ∗ ⌜msgAbs st a⌝`, where
  `msgAbs (st : MsgSt) (a : Option Msg) : Prop` is the old relation made pure (`mtypeOf = none ∧
  a = none`; `ty ≠ .snap ∧ a = some (absMsg ty st.msg st.ents st.ctx)`; `ty = .snap ∧ st.snap =
  some sv ∧ a = some (absSnap st.msg sv sv.Metadata'.ConfState'.lists)`: a queued `MsgSnap`
  carries its snapshot, as before). `outboxRel` is **no longer persistent**; the lemmas on it
  (`outboxRel_nil`, `_perm`, `send`'s append) are restated. `AAMsgOk id t (st : MsgSt)` and
  `OutTermOk pv t (m : MessageM)` are the old statements with `m.Entries' = slice.nil` as
  `st.ents = []` and `m.Context' = slice.nil` as `st.ctx = []`. No capacity is held for a queued
  message's `Entries` (`maybeSendAppend`'s slice is a prefix of the log's, whose slack is
  frozen): the application re-decodes what it receives. *Rejected*: fractions until
  `acceptReady` (Q2 chose the read-only `Ready` view, R5).
- **`Step` takes the message for good** (Q3), as a received message: `msgIn ml dqe st`, the
  struct at `1`, the `Entries` slice's elements at `dqe` (`1` for a `MsgProp`, whose slots
  `stepLeader` replaces; `□` otherwise) **and the slice's capacity at `1`** (a `MsgApp`'s array
  is adopted by `unstable.truncateAndAppend`, as in the old `Hents_cap`), the snapshot at `1`
  (`handleSnapshot`'s `EnsureSnapshot` and `restore`'s `EnsureConfState` write its nil fields,
  Q5). `msgIn` is `InvPb.lean`'s `msgPts` with the capacity conjunct (one definition
  `msgPtsC l dq dqe cap st` of which `msgPts` is `cap = false`, so the field lemmas are shared).
  The spec quantifies the pointer and the record's parts apart -- `(ml : Loc) (m : MessageM)
  (ents : List EntryM) (ctx : List w8) (sn : Option SnapshotM) (rs : List Loc)`, premise
  `msgIn ml dqe ⟨m, ents, sn, ctx, rs⟩` -- so that every pure premise and every abstraction
  (`m.Type' = ...`, `absMsg ty m ents ctx`) keeps its text. The `MsgSnap` premise is `sn = some
  sv` with the old `"#Hsnap"` facts on `sv` (`SnapScope sv cl` with `cl =
  sv.Metadata'.ConfState'.lists` where `ownCSL` tied the lists to the slices). Nothing of the
  message is given back; `stepLeader`'s `(⌜MsgProp⌝ -∗ ∃ ents', m.Entries' ↦* ents')` goes. The
  callee specs (`stepLeader`/`stepCandidate`/`stepFollower`, `handle*`) take the parts of
  `msgIn` they read, as the old ones took the slices: a forwarded message (`stepFollower`'s
  `MsgProp`/`MsgReadIndex`/`MsgTransferLeader`) is frozen to `msgOwn ml 1` and queued.
- **`send` takes `msgOwn ml 1 ⟨m, ents, sn, ctx, rs⟩`** and queues it: `SendOk id s m ents ctx out`
  is the old statement over `MessageM` (`ents = []`/`ctx = []` for `slice.nil`); the `MsgSnap`
  clause's `"#Hsnap"` becomes `⌜sn = some sv ∧ out = [absSnapFrom m id s.term sv
  sv.Metadata'.ConfState'.lists]⌝`. The cells `send` writes (`From`, `Term`) are fresh (`new`);
  the ones it reads are shared with the request that caused the message (`cellRO`, persistent).
- **Snapshots** (D4): `maybeSendSnapshot` puts `raftLog.snapshot`'s fresh clone (R3, owned at `1`)
  in the message; `restore` takes `ownSnapE sp 1 sv` (metadata set, as `handleSnapshot`'s
  `EnsureSnapshot` leaves it) and gives it back, the record unchanged (`EnsureConfState` may set
  a nil `AutoLeave` cell to `false`, which reads the same); `raftLog.restore` (R3) clones it. A
  snapshot whose metadata or conf state is nil is refused by `restore`'s first checks (index `0`,
  no id found), which the specs need not say.
- **Hard states** (D4): `hardState()` returns a fresh `hsRO p (hsOfSt (nodeHardstate s))`
  (`nodeHardstate` and `HardSt` move from the old `InvRawnode` to `InvRaftPhys`; `hardstateVal`
  becomes `HardSt → HardStateM`); `loadState` takes `hsRO`; `IsEmptyHardState`/`isHardStateEqual`/
  `MustSync` take `hsOpt`/`hsRO` pointers.
- **Conf states**: `applyConfChange` and `switchToConfig` return the tracker's fresh `csPts cs 1
  (ConfStateM.mk xs ls os lns c'.cfg.autoLeave) true` (R0's `ProgressTracker.ConfState` post);
  `newRaft`'s `InitialState` closure returns `(hp cs : Loc)` with `hsOpt hp hs`, `csPts cs 1 c
  true` and a wand back to `ownStorage` (the shape of R3's `MemoryStorage.InitialState`; the lists
  `c`'s replace `voters`), `newRaft` returning `cs` through the wand before it returns; `restore`
  reads the snapshot's conf state in place (`confchange.Restore` at a fraction, R2).
- **`appendEntry`** takes `entsPts es dq ents` at any fraction and gives it back unchanged: the
  log gets fresh clones, stamped then frozen (`entOwn_freeze`); the post's log state is the old
  `logAppend s.logst (ents.mapIdx (stamp ...))`.
- **The read-index queues hold frozen messages**: `pendingReadIndexMessages` (`ownRaftMisc`) and
  `readOnly`'s requests (`ownReadreq`) hold `msgOwn l □ st` (persistent, as the old `#Hpri_ents`
  and `ownReadreq`), with `st.msg`/`st.ents` the record's pair (Q8: `RdState.pend : List
  (MessageM × List EntryM)`) and `st.snap`/`st.ctx`/`st.resps` existential: nothing writes a
  stored request (`responseToReadIndexReq` reads `From` and shares `Entries`). The slice
  `pendingReadIndexMessages` itself is owned with its capacity, as before.
- **Shared definitions**: `InvConfChangeMsg` keeps `ccEntOk`/`ccEntsOk`/`CCData`/`ccEntryType`/
  `enterJointOf` over `EntryM` (`ownCCV1/V2/I` are R1's, `InvPb.lean`; `ccEntry`/`ccPropMsg`, the
  value builders of `ProposeConfChange`, are R5's); `InvRaftpb` is gone (`SortedW64` moved to
  `InvPb` in R1, `confStateDeepEq` with `reflect.DeepEqual`); `InvApplyConf(C)` port by the
  rename; `InvBig`, `Init` copy.

**D6 (2026-10-15, after phase 2): an entry's data is its bytes.** `EntryM.Data' : List w8` (it was
the Go slice `GoSlice`, D1's field-for-field rename). Why: v3.7's `appendEntry` clones each proposed
entry (`proto.Clone`, a fresh `Data` slice holding the same bytes) and appends the clones, so the
log's records would differ from the proposal's in their slice, while the model's propose step
appends the proposal's entries verbatim; and the ghost state already keys a proposal's deposit by
its bytes (`deposited γ d`, `d ↪[γ.reProps]□ γq`), the slice map `isPropData γ sl d` only recording
which bytes a slice holds. With bytes in the record a clone *is* its original, the propose step and
its 19k lines of model proofs stay, `isPropData`/`γ.reSl` go (`entDataIs` says `e.Data' = d`), a
conf-change entry decodes by its record alone (`ccEntOk` pure, `decOfData`'s `data` parameter
gone), and a `ReadState`'s context is bytes (`ReadStateM`, the model's; etcd matches read states by
`bytes.Equal`, so this is the right identity). Physically `entPts` holds `l.Data ↦{dq} ds ∗ ds ↦*□
e.Data'`: an entry's bytes are read-only from the moment it is built (raft never writes them; the
proposer's data must be frozen, which R5's `Propose` takes as its premise). Consequences: a
leader's own empty entry and a client proposal of empty bytes are the same record, so a proposal's
data must be non-empty (`entDataIs (some d)`: `d ≠ []`; a premise of `Propose`); `payloadSize`
returns the bytes' length. *Rejected*: the model's propose step admitting data copies
(`EntsDataCopy`), which changes the step rule every model theorem inverts and needs the clone's
slice registered in `isPropData` from inside `appendEntry`.

**D7 (2026-10-16, after phase 3): a snapshot's conf state may be frozen once its `AutoLeave` is
set.** `smPts`'s nested conf state becomes `csOptA pc dq c := ⌜pc = null ∧ c = zero⌝ ∨ csPts pc dq c
false ∨ csPts pc DFrac.discard c true`: nil, owned at the snapshot's fraction, or read-only for
good with its `AutoLeave` cell set. Why: `MemoryStorage.InitialState` returns the storage's own
conf-state pointer (`storage.go:132`), and `newRaft` uses it (`confchange.Restore`,
`assertConfStatesEquivalent`) while it also reads the log, which holds the storage (`ownRaftLog`'s
`HStorage`); so R3's lending of the conf state with a wand back to the storage cannot be met.
Nothing writes a snapshot's conf state in place once `EnsureConfState` has set its `AutoLeave`:
`EnsureConfState` writes only a nil `AutoLeave` (`raftpb/util.go`), `EnsureSnapshotMetadata` only
calls it, `CreateSnapshot` replaces the `ConfState` pointer with a clone (`storage.go:259`),
`ApplySnapshot` replaces the snapshot. So `InitialState` freezes the storage's conf state and
returns it persistent (`csPts cs □ (storCS σ) true`) beside `ownMemoryStorage` (no wand), and
`newRaft`'s `InitialState` premise returns `hsOpt hp hs ∗ csPts cs □ c true ∗ ownStorage`
at once. `EnsureConfState.spec` is generalized to `{{ csPts p dq c al ∗ ⌜dq ≠ DFrac.own 1 → al =
true⌝ }} … {{ csPts p dq c true }}` (no write when the cell is set; the old statement is the
instance `dq = 1`); `ownSnapM`/`ownSnapE`/`smPts` keep their signatures, so the log layer and the
`proto.*` axioms' statements do not change; proofs that destructure a nested conf state
(`Ensure*`, `SnapshotMetadata.GetConfState`, the `MemoryStorage` methods, `raft.restore`) gain the
third case. *Rejected*: a second fraction parameter on `ownSnapM` (every snapshot predicate and
spec changes); fractions lent by the storage (the storage would have to record a loan forever).

## The node layer over pointer messages: `Ready` hands the messages out, the pending steps owned (stage R5 of the raft v3.7 retarget)

**2026-10-16 · proposed (stage R5, branch `raft-retarget`)**

Raft v3.7's `rawnode.go`/`node.go` (`bootstrap.go` stays out of scope, as before: `Bootstrap` and
`StartNode` were never proved) differ from the old source in the representation only: `Ready`'s
`HardState`/`Snapshot` are nil-or-pointer (`hardState()` fresh, `nil` when unchanged; the
snapshot `nil` in scope), its `Entries`/`CommittedEntries` are `[]*pb.Entry`, its `Messages`
`[]*pb.Message` (aliasing `r.msgs`, extended by the `msgsAfterAppend` messages to others),
`prevHardSt` and `stepsOnAdvance` hold pointers, `acceptReady` aliases `rd.HardState` into
`prevHardSt`, the channels carry `*pb.Message`/`*pb.ConfChangeV2`/`*pb.ConfState`, `Propose` and
`confChangeToMsg` build their one-entry batch as a slice literal, `node.Step(nil)` is an error,
`node.ApplyConfChange` returns `nil` if `done` fires (unreachable: `done` never fires in scope).

- **D8, Q2 revised: `readyWithoutAccept` hands the messages out; abandoning gives them back.**
  R4 made the outbox owned (`msgOwn l 1`), and R0's Q2 proposed a read-only `Ready` view with the
  transfer at `acceptReady`. That cannot work for `node.go`: `run` sends the `Ready` on `readyc`
  *before* `acceptReady` runs, and the application may use the messages (etcd rewrites a
  `MsgSnap`'s snapshot) as soon as it receives them; the resource sent on the channel (`readyP`)
  must therefore carry full ownership, which only `readyWithoutAccept` can provide. So
  `readyWithoutAccept`'s post hands out `rd.Messages' ↦* mls ∗ [∗list] l;st ∈ mls;ms, msgOwn l 1
  st` with `isRaftMsg γ st` (pure `msgAbs` plus `isMessage`), `ownRaftPhysReady` keeps the
  queues' slices with the pure outbox relation and the `msgOwn`s of the self-addressed
  `msgsAfterAppend` messages only (those `acceptReady` moves to `stepsOnAdvance`), and the
  abandon wand (`Habandon`, `ownRawNodeReady_abandon`) takes the handed-out messages back to
  rebuild `outboxRel`. `acceptReady` with the messages handed out nils both queues as before.
- **The pending steps are owned messages**: `stepsOnAdvance` holds `[∗list] l;p ∈ steps;rs.steps,
  msgIn l DFrac.discard (pendSt id p) ∗ pendingRel γ id p` with `pendSt` the message record of a
  `Pending` (`.self`: existential `st` with `SelfMsgOk id st.msg`, `st.ents = []`, `st.ctx = []`,
  `st.snap = none`; `.appendAck t e`: `⟨appendAckM id t e, [], none, [], []⟩`; `.applyAck ce`:
  `⟨applyAckM id, ce, none, [], []⟩`), since `Advance` steps each with `raft.Step` (`msgIn`, Q3)
  and nils the slot. `pendingOwn` (the apply ack's `Entries` capacity) is inside `msgIn`: the
  committed entries' slice capacity comes from R3's `nextCommittedEnts`, as before.
  `newStorageAppendRespMsg`, `newStorageApplyRespMsg` and `needStorageAppendRespMsg` get specs of
  their own (Lean-first; the old proof inlined them).
- **`Ready`'s fields**: `rd.HardState'` is `hsOpt rd.HardState' h` (`nil` when unchanged, else
  `hardState()`'s fresh `hsRO`, which `acceptReady` stores in `prevHardSt` and the application
  may give to `MemoryStorage.SetHardState`, R3: the `Ready` hands it out, `readyData` includes
  it); `rd.Snapshot' = null` replaces `= zero_val` (scope: no pending snapshot); `Entries`/
  `CommittedEntries` are `entsRO` (R3's `nextUnstableEnts`/`nextCommittedEnts`); `ReadStates` as
  R4's `readStatesPts` (persistent), `readStateOk γ (st : ReadStateM)` over bytes (D6:
  `readOk γ st.RequestCtx' st.Index'`, no `isPropData`); `SoftState` as before (`↦□`).
  `prevHardSt` is a `Loc` with `hsRO` (never `nil`: `NewRawNode` sets it; `Bootstrap`'s
  `emptyState` is `hsRO` too, R4's `isInitialized`).
- **The node's channels** carry pointers: `propP γ pm` is `msgIn pm.m' 1 ⟨propMsgM,
  [⟨0, 0, 0, d⟩], none, [], []⟩ ∗ entData γ ⟨0,0,0,d⟩ ∗ …` (D6: the data bytes, `d ≠ []`, frozen
  inside the entry; no `propDataInv`, which is gone with `isPropData`) or `fwdP γ pm.m'`
  (`msgIn ml 1 st`, `st.msg.Type' = MsgProp`, `isMessage` of its abstraction); `netP γ id ml`
  is `∃ st, msgIn ml DFrac.discard st ∗ ⌜NetMsgOk id st.msg⌝ ∗ …` (the old facts over `st`);
  `confcP γ (v : Loc)` holds `ownCCV2 v DFrac.discard ccm` (R1) with the old mode facts;
  `confstateP γ (cs : Loc)` holds the fresh `csPts cs 1 c true` that `applyConfChange` returns
  (R4), with `confstateOk`/`confstateS` over `ConfStateM` lists (pure) — `node.ApplyConfChange`
  returns that pointer (its `nil` case needs `done`, which never fires). `readyP`/`readyData`
  as D8 says, with the hard state. `run` writes `m.From = new(r.id)` into a proposal from
  `propc` (the struct at `1`).
- **`RawNode.Propose`/`ReadIndex`/`confChangeToMsg`** build the entry in a slice literal
  (`wp_slice_literal_ex`, R3) from frozen data (`data_sl ↦*□ d`, the premise as before; D6's
  `d ≠ []` for a proposal), then `raft.Step` with `msgIn ml 1 …`; `confChangeToMsg` returns
  `msgIn ml 1 ⟨propMsgM, [ccEntryM o bs], none, [], []⟩` with `CCData o bs` (`ccEntryM o bs :=
  ⟨0, 0, ccEntryType o, bs⟩`, `propMsgM := {zero with Type' := MsgProp}`: R4 dropped the value
  builders `ccEntry`/`ccPropMsg`, which return here as records).
- **`NewRawNode`/`RestartNode`**: the storage's `InitialState` premise in R4's D7 shape
  (`hsOpt hp hs ∗ csPts cs □ c true ∗ ownStorage` at once); `prevHardSt := r.hardState()`.
- **What stays**: `RNState` (`delivered unpersisted : List EntryM`, by the rename), `Pending`
  (`applyAck (ents : List EntryM)`), `StepsOk`/`PendingOk`/`ApplyAckOk`, `RNMode`, the budget
  and tick machinery (`InvNode`), the run loop's invariants (`InvNodeRun`: `staleOk`, `freshOk`,
  `runHead`/`runMid` over the new `Ready` fields), `isNode`'s channel protocols, the ghost
  mode plumbing, `ownRawNode`'s pure facts, every spec's pure statement.

## The swap: one raft tree, the server over raft's own predicates (stage R6 of the raft v3.7 retarget)

**2026-10-16 · adopted (stage R6, branch `raft-retarget`)**

R5 took `Raft37/` past the old tree (257 of 327 functions against 251 of 323; `Results.lean`'s
`#print axioms` cover every result the old `Results.lean` printed). R6 makes it *the* raft tree.
Three trees named raft's Go path until now: the verified fork (`Code/go_etcd_io/raft/`, gogoproto
messages, 118 commits behind etcd's dependency), `EtcdDeps/` (etcd's dependency, raft v3.7.0,
types and names only, for the server's translation) and `Raft37/` (raft v3.7.0 plus the
single-voter read-index fix, everything translated). After the swap there is one.

- **D9: the server's raft is the verified one.** `EtcdDeps/` was a names-only translation of
  raft v3.7.0 so that the server could be translated at all; its 15 proofs (the raftpb getters
  the apply thread reads, `IsEmptySnap`, `IsEmptyHardState`, `isHardStateEqual`) restated what
  the Raft proof could not yet say about pointer messages. Now it can: the server's translation
  imports the full translation (`Code.go_etcd_io.raft.v3`, the same Go source but for the
  read-index fix, `issues/raft-readindex-singleton-stale.md`), its proofs link raft's own
  getter specs, and `EtcdDeps/` goes. The one difference from etcd's `go.mod`, the fix, is
  recorded here: the server is verified against raft v3.7.0 *with* the fix, which is what
  `ReadIndex`'s contract (`isRaftNodeIfc`'s read-index clause) needs to be true at all.
- **The server keeps its models, raft provides the points-tos.** The server describes the
  raft objects it reads with `entryAt e m` (`EntryModel`), `msgAt m to ty`, `hardStateAt p hs`
  (`HardStateModel`): field-level, persistent, written before the Raft proof had pointer
  messages. They are the same shape as raft's `entPts`/`msgPtsC`/`hsRO` (one `cellRO` per
  optional field, the data bytes read-only) minus the hidden-field invariant `pbMsg`, which the
  server cannot produce from nothing. So they become definitions over raft's: `entryAt e m :=
  entRO e m.toM`, `hardStateAt p hs := hsOpt p m.toM`, `msgAt m to ty := ∃ st, msgOwn m □ st ∗
  ⌜st.msg.To' = to ∧ st.msg.Type' = ty⌝` (the exact forms are the server files'). The server's
  own models stay: its ghost logs, `rnReadyP`, the request path's `InvRequest` (55 uses) and the
  exported `Results` are stated over `EntryModel`, and nothing is gained by renaming their fields.
  The point of defining the predicates over raft's is R7: `isRaftNodeIfc` discharged from
  `node.Ready`/`Advance`/`ReadIndex`'s specs hands raft's `entsRO`, `hsOpt`, `msgOwn` straight
  through.
- **The register is ported, not patched (R6b).** `examples/register` is this repository's Go
  code on raft's `Node` API, written for value messages (`send func([]pb.Message)`,
  `cc.Unmarshal(e.Data)`, `pb.ConfChange{...}` by value). Raft v3.7's API is pointers and
  getters, and `proto.Unmarshal`; the Go changes (ours to make: it is the example, not etcd), its
  `go.mod` moves to the fork's `raft37-goose-lean`, the translation is regenerated, and its
  6,000 lines of proofs (including the whole-program adequacy) are redone over the new node
  specs (`Ready` hands out owned pointer messages, D8; `Propose` wants non-empty frozen data,
  D6). Until R6b lands the branch is red at the register only; R6a and R6b merge together.
- **`isRaftNodeIfc` from the node specs is R7, not R6.** The plan's R6 row listed it; it is a
  proof-design task of its own (the server's `rnReadyP`, `committedAtLeast`, `E.RQ` against
  raft's `ownRawNodeReady` and the protocol's read-index results), independent of the swap.
- **Tooling: one project, no parts.** `etc/goose.py`'s project `etcd-raft` (the fork) goes and
  `raft37` becomes project `raft` in the root (`root=""`, `go.etcd.io/raft/v3=`); the etcd
  project loses its `EtcdDeps` part and maps `go.etcd.io/raft/v3` to the root. `etc/gen-link.py`
  loses the Rocq mode (every raft function is Lean-first now: `--raft` from
  `etc/link-lean-first-raft.txt`, the old `--raft37`); the server's and v3rpc's spec lookups no
  longer reach a second root. `etc/proof_roots.py`/`tcb-report.py`/`verified-code.py` are
  generic over parts and need no change; collection `raft37.txt` becomes `raft.txt`. The old
  tree's private trust boundary goes with it: `gogoproto.Equal`, `reflect.DeepEqual`, the
  gogoproto `Marshal`/`Unmarshal` axioms (protobuf-go's `proto.*` axioms replace them, R1).

## The server's raft contract discharged: the contract layer over raft's protocol (stage R7 of the raft v3.7 retarget)

**2026-10-16 · adopted (stage R7, branch `raft-retarget`)**

After R6 the server's raft is the verified one, but what the server assumes of it is still a
premise of its results: `isRaftNodeIfc` (`Ready`, `Advance`, `Tick`, `Stop`, `ReadIndex`),
`raftPropose` (`Propose`), `isRNMemStor` (the storage's `Append`), stated over the server's own
ghost log `srvRLog` and its atomic updates (`InvRequest.lean`, "Raft's committed log, at the
server"; `InvRaftNode.lean`). R7 proves them from raft's node and storage specs. The server's
contract was written (2026-10-12/14) as a copy of raft's protocol interface in the server's
terms, and the copy is nearly exact: `srvRLog`/`rLog` (the client's half of the committed log),
`srvRLogLb`/`isCommitted`, `srvRaftLogInv`/`raftCommitInv`, `srvPropFresh`/`propFresh`,
`srvIsProp`/`isProp`, `srvPropAu`/`propAu`, `srvNoopAu`/`noopAu`, `srvPropWits`/`prop_collect`,
`srvReadAu`/`readAu`, `srvReadWit`/`readWit` with `read_collect`; `EntryModel` is `EntryM` field
for field (`EntryModel.toM`). So the pattern is D9's again.

- **D10: the server's contract layer is defined over raft's protocol predicates; the three
  contracts become theorems.** `ServerRaftNames` gains raft's names (`raft : RaftNames`) and the
  log the server's view starts after (`pre : List EntryM`, with `ai0 = pre.length`: raft's
  `rLog` is the full committed log from index 1, the server's the entries after its start index;
  today the composition starts at `[]`, since raft's `RestartNode` takes an empty storage). Then
  `srvRLog γ L := rLog γ.raft (γ.pre ++ L.map toM)`, `srvRLogLb γ L := isCommitted γ.raft (γ.pre
  ++ L.map toM)`, `srvRaftN := raftN` (the server's updates are fired by raft at `⊤ ∖ raftN`),
  `srvRaftLogInv γ := raftCommitInv γ.raft ∗ isCommitted γ.raft γ.pre ∗ ⌜…⌝`, the fresh tokens,
  deposits and handles raft's (`rdFresh`, `deposited`, `isProp`, `isRead`); `srvPropAu`,
  `srvNoopAu`, `srvReadAu` keep their statements (the server's KV invariant builds them) and
  conversion lemmas turn them into raft's `propAu`/`noopAu`/`readAu` of the shifted predicate
  (`fun Lm => Q (ofM (Lm.drop |pre|))`, trivial when `pre` is not a prefix of `Lm`, which never
  happens); `srvPropWits` and `srvReadWit` are theorems (`node_collect`, `node_read_collect`,
  `£ 2` for the two laters). `RNNames` gains the node's names (`node : NodeNames`, its `id`, its
  pointer, static mode) and `rnDrv`/`rnBusy`/`rnReadyP`/`rnAppendRight`/`rnAppendReceipt` are
  `nodeDriver`/`nodeDriverBusy` (with `nodeCfg`)/`readyP γ.node`/`memAppendTok`-based;
  `rnReadyData` keeps the server's shape and `rn_ready_recv` becomes a fancy update that derives
  it (messages persisted, `E.C` from the committed log). `E` stays a parameter: the discharge
  takes `rnEnvOk E γ` (persistent, in `isRaftNode`): `E.T = tickCred γ.node.bud 1`, `E.M m` the
  persistent part of a handed-out message (`msgOwn m □ st ∗ isRaftMsg ∗ termLB`), `E.RQ id n Qr`
  raft's read registration of `beBytes id` (`isRead` and `readReq` at a log of length `≥ n`),
  and `□ (∀ L, srvRLogLb L ={⊤}=∗ □ E.C L)`, which the server's composition proves from its KV
  invariant (`srvC`'s workload facts are the KV invariant's, not raft's). *Rejected:* a bridge
  invariant holding `srvRLog` beside `rLog` (the server's updates must run at raft's commit
  step, under raft's mask, so they must be raft's updates); making `EntryModel` an abbreviation
  of `EntryM` (280 uses; the conversion is one function).
- **Four gaps on raft's side, closed in R7a.** (1) `readyData` says nothing of `rd.SoftState`,
  which the server reads: it gains `softStateRO rd.SoftState'` (nil, or `Lead`/`RaftState`
  read-only; `prevSoftSt` a read-only pointer). (2) `node.Propose`, `node.ReadIndex` and the
  `step*` chain are specified for `context.Background()` only; the server passes a context with
  a timeout: they take `nodeCtx ctx cd` (`Done()` nil, or Perennial's `context.isContext`), and
  say what the error is (`nil`, raft's `ErrStopped`, the context's). (3) The committed entries'
  indices: raft's protocol knows them (`cq_full`: `PlogWf base0 G`, entry `k` has index `k + 1`)
  but neither `isCommitted` nor the updates expose it, and the server's `srvIdxOk` needs it in
  the update (`srvPropAu`'s after-clause): `propAu`/`noopAu` gain `⌜uint.Z e.Index' = L.length +
  1⌝` in their after-clause (the firing step has `cq_full`), and `isCommitted_wf` states it for
  a committed log. (4) `rLog_committed` (the register's `reg_log_committed`) and the
  `MemoryStorage` instance of `StorageModel` (the register's `RegStorageInstance`) move into
  raft's tree, shared.
- **Two budgets the server did not pay, now paid where the premise belongs.** Raft's `Tick`
  spends a term-budget credit and `ReadIndex` a read credit, both from finite budgets (`< 2^64 -
  1`); the server's `start` took `□ |==> E.T` (a free tick), its `ReadIndex` no credit, and
  neither can be derived (`□ |==> tickCred 1` contradicts the budget invariant). The tick's credit
  comes with the tick: the ticker's channel payload is `E.T` (`isRNTicker E`; `time.Ticker` is a
  trust-boundary contract, and "fewer than `2^64 - 1` ticks in a run" is its premise). The read's
  credit comes with the request: `isRaftNodeIfc`'s `ReadIndex` clause, `raftNode.ReadIndex`,
  `isReadRaft` and the read loop take `rnReadCred` (`rdCred γ.node.raft 1`) per `ReadIndex`, paid
  by the request that wakes the loop (`readwaitc`'s payload, from `LinearizableReadNotify`'s
  caller: the premise moves to the gRPC layer, "fewer than `2^64 - 1` linearizable reads in a
  run"). The clause also takes the fresh-context token raft needs (`rdFresh γ.raft (beBytes
  id)`, minted by the server from the id generator's `idFresh`) and the context's bytes
  read-only (`sl ↦*□ beBytes id`: raft keeps them in the entry).
- **One premise stays, one is new.** `Stop` stays a premise: raft's model never stops (`run`'s
  stop case is vacuous, `done` never closes) and `node.Stop` has no spec; modelling stop touches
  `node.run` and every `<-n.done` case, a stage of its own (the user's decision, 2026-10-16).
  New: `Append`'s index bound. Raft's `MemoryStorage.Append` needs the appended entries' last
  index `≤ 2^61` (its arithmetic, and the storage contract's `Hbounded`), which raft's node layer
  cannot establish for the unstable entries it hands out (`|uents| < 2^63` only); the register
  checks it in Go (`fits`), etcd does not. So `isRaftNode` gains `rnLogFits γ` (persistent, a
  trust-boundary premise on the run: every `Ready`'s entries fit), recorded in `notes/STATUS.md`.
- **The committed index and the log.** `isRaftNodeIfc`'s `ReadIndex` takes `committedAtLeast
  E.γr n` and raft's needs a committed log of length `≥ n`: `srvCommittedInv` (the committed
  index's invariant) gains the log prefix the index was read from (`∃ L, srvRLogLb L ∗ ⌜v ≤ ai0 +
  |L|⌝`; its writer, the ready handler's `updateCommittedIndex`, has it from `srvC`).
- **Mode.** The node is in raft's static mode: the server's conf changes go through
  `EtcdServer.applyConfChange`, a trust-boundary spec (R6), so `Advance`'s dynamic-mode premise
  is vacuous.
- **Carried out (2026-10-16, R7a/R7b; `notes/STATUS.md`).** Three deviations from the plan
  above. (i) The read credit comes with the request *id*, not the request: `requestCurrentIndex`
  retries `ReadIndex` on a timer, unboundedly in the model, so a per-request credit cannot pay
  for the retries; each call has a fresh id, and the id budget (`2^48`) is below raft's
  (`2^64 - 2`), so the server's mint of read contexts (`srvRdFreshInv`) hands out raft's fresh
  token and credit with every `NextRequestID`: no new premise at the gRPC layer. (ii) The updates'
  after-clauses are the new entry's facts only (`srvPropAu`, `srvNoopAu`: raft gives the appended
  entry's index, not the whole log's), and `srvIdxOk`'s `2^64` bound on the delivered log is a run
  premise (`rnLogFits`, beside `Append`'s `2^61`). (iii) Two error-value facts stay premises
  (`rnCtxErrOk`, `rnPropErrOk`): raft's `nodeErr`/`propErr` do not name a context's `Err()` nor
  `Propose`'s result error; R7c retired them on raft's side the same day (`notes/STATUS.md`,
  "stage R7c"): `ctxErr` through this repository's `context.ErrDone` spec, `stepErr` through the
  proposal handoff.

## The server's start over raft's `RestartNode`: what etcd's bootstrap needs of the model (stage R8 of the raft v3.7 retarget)

**2026-10-16 · adopted (stage R8a first, then R8b; branch `raft-retarget`)**

After R7 the server's raft contract is proved from raft's node specs, but the *composition* of the
server's start with raft's `RestartNode` (the register does it in `Main`) is still open: R7a found
that a bare `MemoryStorage` without a snapshot is not an `ownStorage`. Reading etcd's
`bootstrapRaft` (`server/etcdserver/bootstrap.go`) shows the gap is wider: **none of etcd's three
start paths is raft's `RestartNode` as verified.** (1) A new cluster (no WAL, `NewCluster`) calls
`StartNode(c, peers)` with the member ids: raft's `Bootstrap` appends one conf-change entry per
member at term 1, marks them committed and applies them; neither was ever proved, and the
protocol's initial state has an empty log. (2) A member joining an existing cluster (no WAL) calls
`RestartNode` on a fresh `MemoryStorage`: the storage is empty, as raft's premise asks, but so is
its conf state, while raft's spec wants the voters known at start with this node among them (the
node learns its configuration from the leader's first snapshot, which the server's apply loop is
proved under a no-snapshot contract). (3) A restart from a WAL calls `RestartNode` on a storage
holding the WAL's snapshot, hard state and entries: crash recovery, which the model does not have.
(The comment in raft's `ApplySnapshot` about etcd applying a conf-state-only snapshot at index 0
describes no path of etcd's server.)

Under all three sits R7a's storage gap: a bare `MemoryStorage` has an empty snapshot until the
server's first `CreateSnapshot`, and raft's storage contract (`isStorageWith`'s `Snapshot` clause)
promises a non-empty one because `maybeSendSnapshot` panics on an empty snapshot. Real etcd is safe
because that path is reached only after a `term(pr.Next - 1)` failed: `ErrCompacted` only once the
storage has compacted (etcd compacts only after `CreateSnapshot`), `ErrUnavailable` only when a
peer's `Next` runs past the leader's log, which never happens. The proof does not know the second:
`raftLog.term`'s spec says so ("nothing in `ownProgress` bounds a peer's `Next` against the log").
The register sidestepped it with its own `Storage` wrapper (`Snapshot` answers
`ErrSnapshotTemporarilyUnavailable` while empty), which etcd does not have.

- **Decision (the user's, 2026-10-16): route A then B.** R8a admits the bare `MemoryStorage`
  without a snapshot as a `Storage` by proving the leader's progress bound; R8b models the new
  cluster's start (`StartNode`/`Bootstrap`: the cluster's initial log in the protocol), the one
  etcd start path the model can reach, and composes the server's start with it. The join path
  (an empty configuration installed by the first snapshot, and the server applying a received
  snapshot) and the restart from a WAL (crash recovery) stay out of scope. *Rejected:* a run premise
  on the server's side ("the leader never asks for a snapshot while uncompacted"): it cannot be
  stated as a resource the storage contract's `Snapshot` clause could consume, since the clause's
  postcondition is what fails; a conf-state-only snapshot at index 0 as the composition's storage:
  it composes with no etcd function.
- **D11: the leader's progress is within its log, and an uncompacted storage may have no
  snapshot.** Three parts, two sides.
  - *The physical invariant* (`Defs.lean`, `InvRaftPhys.lean`): `PrOk ls p` -- `1 ≤ p.next ≤
    logLast ls + 1`, `p.matched ≤ logLast ls`, `p.pendingSnapshot ≤ logLast ls` -- for every
    tracked peer of a leader (`PrvalsOk s`), a pure conjunct of the sealed `ownRaftPhys`, carried
    through its interface (`ownRaftPhys_intro`'s premise; a projection; an obligation on the
    lemmas that rebuild the struct at a changed role, progress or log). Established by `reset`
    (`Next = lastIndex + 1`, `Match = 0`, the node's own `lastIndex`: `raft.reset.spec` now
    states the values), kept by every progress update of `stepLeader` and the replication path
    (`MaybeDecrTo`, `BecomeProbe`, `BecomeReplicate`, `BecomeSnapshot` at an index at most the
    commit index, `SentEntries` of entries from `Next` on, `switchToConfig`'s fresh `Progress` at
    `max(lastIndex, 1)`), by a leader's log growing only (`appendEntry`), vacuous elsewhere (a
    follower's log may shrink, its progress is reset on winning). The one update that needs a fact
    from outside the node is `MaybeUpdate(m.Index)` on an accepted `MsgAppResp`: the ghost side.
  - *The ghost witness* (`Protocol/`): `ackIn γ t i` (`Ghost.lean`) -- `i` is `0` or at most the
    last index of a prefix of the term-`t` leader's log (`leadPrefix`) -- carried by an accepting
    `MsgAppResp` beside `isAcked` (`isMessage`, `GhostState.lean`), supplied where such a message is
    sent: `handleAppendEntries`' `lastnewi` from the `MsgApp`'s own `leadPrefix`, the leader's
    self-acknowledgement from its log, `handleSnapshot`'s replies from the `MsgSnap`'s `leadPrefix`
    (a restore or fast-forward) or by leader completeness (a stale snapshot acknowledges the commit
    index). At the leader (`ownRaftGhost_ackIn_le`, `Refinement.lean`): the witness names its own
    term log (`leadLogOwn`: every index in the term log is at most the last index, the campaign
    log a prefix of the log), so `i ≤ plastIndex`. `raft.Step`'s proof turns it into the pure
    premise `stepLeader` takes for `MaybeUpdate`.
  - *The storage contract* (R8a's second phase, after the two above): `isStorageWith`'s `Snapshot`
    clause promises a non-empty snapshot only once the storage is compacted (`σ.prev.index ≠ 0 →
    Index ≠ 0`); `memOwnStorage`'s premise weakens to the same implication, so `NewMemoryStorage()`
    is an `ownStorage` and so is `ApplySnapshot`'s result at any index; `raftLog.term` says which
    error is which (`ErrCompacted` below the boundary, `ErrUnavailable` past the last index);
    `raftLog.snapshot` and `maybeSendSnapshot` take the premise that the log is compacted, which
    `maybeSendAppend` establishes from the bound (`1 ≤ Next ≤ lastIndex + 1` leaves `ErrCompacted`
    as the only failure of `term(Next - 1)`, and that means `prev.index ≥ 1`). The register's
    `Storage` still meets the clause.
- **Carried out (2026-10-16, R8a; `notes/STATUS.md`, "stage R8a").** As designed, with four
  details. (i) `raftLog.term`'s spec needed no "which error" clause: its iff already negates the
  range, and the bound rules out the past-the-end side, so the error branch of `maybeSendAppend`
  gets `prev.index ≠ 0` from it directly. (ii) The bound is conditional on the role, so
  `maybeSendAppend`, `sendAppend` and `bcastAppend` take `s.role = .leader` (true at every
  caller) and, dually, `handleAppendEntries` and `stepFollower`'s `MsgApp` case take `s.role ≠
  .leader` (a follower's `maybeAppend` may truncate the log, which the bound forbids a leader).
  (iii) The stale replies (`appStale`, `snapStale`: the follower acknowledges its commit index)
  are proved by leader completeness (`commitIn_ackIn`), with `votesTbl` reached by opening the
  log invariant, so those three ghost steps became fancy updates at their callers' mask. (iv)
  `reset`'s spec now states the progress values its `Visit` closure writes (`ResetPr`), and the
  `confchange` package's `FreshPr` already stated `Next = max(LastIndex, 1)`. The R8b design
  study (2026-10-16) found one more blocker of the real composition, independent of R8b: etcd's
  `raftConfig` sets `CheckQuorum: true` and `PreVote` (on by default), both required `false` by
  `NewRawNode.spec`; `MsgCheckQuorum` and pre-vote are out of the model's scope.
- **R8b (planned; its design is written before its proofs):** the cluster's initial log. The
  protocol's initial state becomes the bootstrap log (`n` conf-change entries at term 1, committed,
  the same on every member), the ghost allocation at that log, the certification of the initial
  committed prefix by its presence on every node from the start, `newRaft` with an empty conf
  state, `Bootstrap` and `StartNode` proved; then the server's composition on the new-cluster path
  (`bootstrapRaftFromCluster` with the member ids, `pre = []`, the conf changes delivered first),
  with `newRaftNode` and `bootstrappedRaft.newRaftNode` translated with their bodies.

## The new cluster's start: the bootstrap log in raft's model (stage R8b of the raft v3.7 retarget)

**2026-10-16 · adopted (branch `raft-retarget`; from the design study of 2026-10-16, after R8a)**

etcd's new cluster starts its raft node with `StartNode(c, peers)`: `NewRawNode` on an empty
storage whose conf state is empty, then `RawNode.Bootstrap(peers)` -- `becomeFollower(1, None)`,
one `EntryConfChange` per peer at term 1 and indices `1..n` appended, `raftLog.committed = n`,
`applyConfChange` of each -- and `go n.run()`. Every member builds the same log, committed from
the start with no leader of term 1 ever existing (campaigns begin at term 2), and nothing is
applied: the application sees the conf changes through the first `Ready`. The verified
`RestartNode` starts at the protocol's initial state (an empty log, the voters known from the
storage's conf state), so neither `newRaft` at an empty conf state nor a committed initial log is
in the model. The user's decisions (2026-10-16): route B after A (D11), and etcd's `CheckQuorum`
and `PreVote` settings stay premises.

- **D12: the cluster's bootstrap log is a base case of the protocol, keyed on `RaftNames.reBoot`.**
  A committed prefix is justified by a commit quorum of a leader's log (`commitJ` → `cq` →
  `leadFull`), and a record (`isEntryR`) names the leader that created the entry; term 1 has no
  leader, and a phantom one is excluded by the vote history (`VoteHistOk`: a node with `Vote =
  None` holds no vote at its term). So the ghost state gets a pure field `reBoot : List EntryM`
  (`[]` for a cluster starting empty, so every existing definition collapses to today's) with a
  boot arm wherever a leader was needed: `isEntryR` (a record at index `i ≤ |reBoot|` is the boot
  entry there, its predecessor's term `0` at index 1 and `1` after), `commitJ`/`isCommittedIdx`/
  `committedJust` (`c ≤ |reBoot|` needs no quorum), `isCampK` (every campaign log starts with
  `reBoot`, and a non-empty `reBoot` puts campaigns at terms `≥ 2`), backed by three conjuncts of
  `ownLogGhost` -- `reBoot` a prefix of the full log, `|reBoot| ≤ commit`, `reBoot ≠ [] → 1 ≤
  term` -- kept by every step (a log is never truncated below its commit index, terms and commit
  indices only grow). Leader completeness keeps its statements; its walk down a log (`lc_adj_gen`)
  and `commit_extend`'s base gain the boot case. The allocation `ownRaftGhost_alloc_boot` (static
  mode) puts every node at `bootPState bootLog` (term 1, follower, `bootLog` committed) and hands
  the client `rLog γ bootLog`/`isCommitted γ bootLog` (`allocClientBoot`); `BootLogOk ccOk ps
  bootLog` says what the log is (entry `k`: type 1, term 1, index `k + 1`, bytes decoding to
  `AddNode ps[k]` and admitted by `ccOk`). *Rejected:* the boot entries below the base, as a
  snapshot at `(1, n)` (the physical log holds them, `NStateRel` would not match); a phantom
  leader of term 1.
- **Static mode.** The server runs raft statically (`rnEnvOk`); the dynamic start would need
  `CfgOk` of an empty `c0` and `RInv_init` with `applied < commit`. With `reCfg = peers` from the
  start the delivered `AddNode` of a member is a `CCNoop`, hence `CCShrink`, the static arm of
  `confcP`; `nodeCfg` never moves. A dynamic bootstrap is a later extension (~300 lines).
- **`newRaft` at an empty conf state, ending open.** `csm.Voters' ≠ []` is needed only by
  `confchange.Restore`'s spec (with no voter `chain` has no op and the tracker's own maps come
  back), `cv.ID' ∈ Voters'` only by `ownRawNode`'s `Hin`. New statements `Restore.spec_empty`,
  `newRaft.spec_empty`, `NewRawNode.spec_empty` leave the node open -- the `RawNode`'s fields and
  `ownRaftPhys ∅` -- rather than at `ownRawNode`, which demands the ghost's configuration;
  `Bootstrap` then walks the chain: `becomeFollower(1)` (its spec fits), the conf-change literals
  and `proto.Marshal` (`MarshalConfChange.spec`), the `Entry` literals, `raftLog.append` (its
  spec fits: `committed = 0 < 1`), the raw store `raftLog.committed = n` (new
  `ownRaftLog_setCommitted`: `prev ≤ n ≤ lastIndex`, `applied ≤ applying ≤ n`),
  `applyConfChange` per peer at a follower (`raft.applyConfChange.spec` at any configuration,
  the loop at `CfgM.simple (listToSet (ps.take k)) ∅`, fresh `Progress` at `Next = max(lastIndex,
  1) = n`), and closes with `ownRawNode_intro_static` over `ownRaftGhost γ id (bootPState
  bootLog)`: `toPState s = bootPState bootLog`, `applying = 0`, nothing unpersisted.
- **`StartNode.spec` is `RestartNode.spec`'s shape.** The conf state's record empty, the peers
  `ps` (`Nodup`, `0 ∉ ps`, `|ps| ≤ 2^62`, `cv.ID' ∈ ps`, `γ.reCfg = listToSet ps`), `γ.reBoot =
  bootLog` with `BootLogOk γ.reCCOk ps bootLog`, `ownRaftGhost γ cv.ID' (bootPState bootLog)` and
  `isCommitted γ bootLog` in place of `rnInit`/`isCommitted γ []`; the post is `RestartNode`'s:
  `isNode γn cv.ID' n ∗ nodeDriver γn cv.ID' n [] ∗ nodeCfg γn 0 (cfgState (listToSet ps) ∅)`.
  **The driver starts at `[]`** (`ownRawNode`: the delivered log's length is the `applying`
  index, `0`): the first `Ready` delivers the boot entries as committed entries (`applied = 0`,
  `allowUnstable` since storage writes are synchronous) beside `Entries 1..n` and the hard state
  `{1, 0, n}`. **The bytes**: `γ.reBoot` is fixed before the call, while `Marshal`'s spec gives
  only that its bytes decode to the change; `StartNode.spec` takes, as `RestartNode.spec` takes
  `InitialState`, a premise on `Marshal` at these inputs (`bootMarshal`: the bytes are the boot
  entry's), a trust-boundary fact of protobuf's determinism, discharged where the node is
  composed. *Rejected:* allocating the ghost inside `StartNode` (the members share one `γ`).
- **The server (R8b-C).** `bootstrappedRaft.newRaftNode` and `newRaftNode` (`raft.go`) are
  translated with their bodies and proved: the former's spec takes `b.peers ≠ []` (the new
  cluster's path; `RestartNode`'s branch is the join path, out of scope) and **`NewRawNode`'s
  premises on `b.config` as premises**, among them `CheckQuorum = false` and `PreVote = false`
  (etcd's `raftConfig` sets `CheckQuorum: true` and `PreVote` by default: the theorem does not
  cover etcd's own config; `MsgCheckQuorum` and pre-vote are out of the model's scope: the user's
  decision), and `raft.SetLogger`'s global write as a contract. `rnSnapOnce`'s `Voters' ≠ []`
  weakens to what `run` uses (the conf-state pointer is not nil; a fresh storage's snapshot has
  an allocated empty conf state). The server's `isConfChangeEncoding` (opaque) becomes raft's
  `ccDecodeV1 bs ≠ none` (one notion of a `ConfChange` encoding; `pbutil.MustUnmarshalMessage`'s
  axiom restated), so the boot entries pass `srvIdxOk` and `srvCCPolicy` matches
  `BootLogOk`'s `ccOk`. The composition: `isServerBuilt`'s raft rows (`isRaftNode`, the loop and
  apply tokens at `[]`, `rnSnapOnce`, `srvRaftLogInv` at `pre = []`) from `ownRaftGhost_alloc_boot`,
  `budget_alloc`, `memStorReg`, `NewMemoryStorage`, `StartNode.spec` and `newRaftNode`.
- **Carried out (2026-10-16, R8b; `notes/STATUS.md`, "stage R8b").** As designed, with these
  deviations. (i) `RaftNames.reBoot` is a derived function over an instance-free field
  `reBootRaw : List BootEntry` (`EntryM` needs `FfiSyntax`, which `RaftNames` does not take);
  every use reads `γ.reBoot`. (ii) One conjunct of `ownLogGhost` suffices (`|reBoot| ≤ commit`);
  the prefix and term facts are derived from the records and `TermsLe`. (iii) `NewRawNode.spec`
  itself ends open at `rawNodeFresh` for any conf state, `newRaft` and `confchange.Restore` drop
  `Voters' ≠ []` (`Restore`'s post a disjunction), and `RestartNode` closes the node; no separate
  `spec_empty` statements. (iv) The `InitialState` closure premise is not `□` where the function
  calls it once (`StartNode`, `setupNode`, `NewRawNode`, `newRaft`); `MemoryStorage.InitialState`
  consumes `memStorMeta`. (v) The budget enters at `termLB bud 1` (`budget_alloc_boot`). (vi) The
  wrapper is returned as a struct value (`rnBuilt`), since `NewServer` copies it, with an installer
  that yields `isRaftNode` once the transport is set. (vii) `rnSnapOnce` stays a construction
  premise: the server holds no `ownMemoryStorage` once raft owns the storage, and
  `MemoryStorage.Snapshot`'s spec does not state the clone's pointers non-nil. (viii) Raft's
  `SetLogger` is a contract (`rnSetLoggerOk`): raft's package initializer drops the logger
  globals' ownership. D12's risk 3 did not materialize.
- **Staging.** R8b-A (the protocol: `reBoot`'s arms, the three conjuncts, leader completeness's
  boot cases, `ownRaftGhost_alloc_boot`) and R8b-B (raft: `Restore`/`newRaft`/`NewRawNode` at an
  empty conf state, `ownRaftLog_setCommitted`, `Bootstrap`, `setupNode`, `StartNode`) in
  parallel over the pre-placed interface (`bootPState`, `BootLogOk`, `allocClientBoot`, the stub
  `ownRaftGhost_alloc_boot`); R8b-C (the server) after B's `StartNode.spec` exists.

## The server's construction: `NewServer` over `bootstrap`'s result (the server-construction unit)

**2026-10-16 · adopted (units N1 and N2 now, N3 and N4 later; branch `raft-retarget`; from the
design study of 2026-10-16, after R8b)**

Every server result rests on `isServerBuilt` (`InvStart.lean`), the premise `start` takes and
`NewServer` would discharge. R8b gave the raft rows a composition (`server_raft_node_start`). The
study of `NewServer` against the premise, row by row, found two things that shape the unit.

1. **The KV rows are false for the real server.** `srvReadBuilt` and `applyBuilt` use `txn.isKV`,
   which pins the server's `kv` to a plain `*mvcc.store`; `NewServer` sets `srv.kv = mvcc.New(…)`,
   a `*watchableStore`, whose write transaction is another type (`watchableStoreTxnWrite` over
   `watchWriter`, notifying watchers at `End`). `mvcc.New` is proved and the watch path states the
   truth (`watchSrvOk`); the request-path and apply results are thus proved for a server whose
   store has no watchers. The fix is an abstraction of `txn.isKV` (and `isApplyKV`, `kvOwn`) over
   the `KV` interface's `Read`/`Write` contracts met by both stores, the txn and apply proofs
   re-linked, `server_kv_backend` redone for `mvcc.New`, and the hook order (`NewServer` installs
   the backend's post-lock hook after creating the store; `server_kv_backend` wants it frozen
   before): **unit N4**, coordinated with the mvcc/watch session, after N1/N2.
2. **The workload clause of `rnEnvOk` is a cluster-wide premise.** `E.C = srvC …` asks of every
   committed log `entriesOk c₀ L x₀` (every request meets the apply premises, `rqOk`/`dispatchOk`,
   at the state it meets) and `batchWaitOk ρ E L` (its id is claimed under *this* server's
   generator); nothing produces either. For one server `entriesOk` needs log-independent bounds
   the deposit does not carry; for several members both are facts about the other members'
   requests (and `issues/etcd-request-id-member-prefix.md` shows id prefixes can collide). The
   honest form is a named premise `clusterWorkloadOk ρ E c₀ x₀ : □ ∀ L, srvRLogLb L -∗
   ⌜entriesOk c₀ L x₀⌝ ∗ batchWaitOk ρ E L`, from which the clause follows (N2); discharging it
   for one server is **unit N3** (may stay a premise).

- **D13: `NewServer` is translated with its body and proved over `bootstrap`'s result as a
  contract**, its postcondition `isServerBuilt` but a named residual. `bootstrap(cfg)` stays
  names-only; `NewServer.spec` takes `bOk b` (what the bootstrapped record carries: the
  consistent index `isCI`/`ciOwner` at `0`, the backend's `isBackendNH`/`plHook`/write tokens,
  the cluster `isRaftCluster`/`clusterCid`, the snapshotter, the WAL, `b.raft` with
  `NodeStartSpec`'s premises -- `CheckQuorum`/`PreVote` off among them, the user's decision) and
  the constructors' contracts (`lease.NewLessor`, `auth.NewTokenProvider`/`NewAuthStore` on a
  fresh backend giving `E.authOn = false`, `v3alarm.NewAlarmStore` giving no alarm,
  `v3compactor.New`, `stats.*`, `rafthttp.Transport`'s `Start`/`AddRemote`/`AddPeer`,
  `SetVersionChangedNotifier`, prometheus). The cluster-level ghost state is a premise too, as
  `NodeStartSpec`'s: raft's `γ` with this node's `ownRaftGhost` at `bootPState`, `isCommitted γ
  bootLog`, the commit invariant, the budget, and `allocClientBoot`'s continuation outputs
  (`rLog γ bootLog`, the `reFresh`/`reRdFresh` authorities, the read credits), from which N2
  builds `kvInv`/`etcdKV` at the boot log (`kvInv_alloc_boot`), `srvMintInv` and `srvRdFreshInv`.
  The per-server names are allocated inside (`∃` in the post): the applied and committed
  indices' invariants, the notifier, `kvCertInv`, `consInv`, the revision authority, the atomics'
  invariants, the id generator's names. The post is `isServerBuilt` with the rows no `NewServer`
  proof gives factored into one named residual `srvBuildGap` (the KV rows `txn.isKV`/`applyKV`/
  `isReadView`/`storeWTs` as stated today, `clusterWorkloadOk`, `rnSnapOnce`, the id budget `□
  |==> idCred`, `storeSmall`, `threadBound`), with `isServerBuilt_of_gap : built ∗ srvBuildGap ⊢
  isServerBuilt`; N3 and N4 shrink the gap. The raft rows come from `server_raft_node_start` at
  `r: *b.raft.newRaftNode(…)` (the struct value copied into the literal) and its installer at
  `srv.r.transport = tr` after `tr.Start()`. *Rejected:* a contract on `mvcc.New` claiming
  `txn.isKV` of its result (false); allocating raft's ghost state inside `NewServer` (the members
  share it).
- **Translation.** `NewServer`, the five `bootstrapped*` record types, `EtcdServer.restoreAlarms`,
  `EtcdServer.NewUberApplier` (if not yet with bodies), `AccessController`, with `math` in the
  imports; `bootstrap`, `bootstrappedServer.Close`, `addFeatureGateMetrics`,
  `newCorruptionChecker`, `ensureLeadership` and the constructors stay names-only. The two
  `defer` closures over the named results run only on error paths the spec excludes; the
  checkpointer closure is an opaque value under `lease.Lessor.SetCheckpointer`'s contract.
- **Staging.** N1 (translation, `NewServer.spec`, the literal and the field rows, the per-server
  allocations, `srvBuildGap`) and N2 (the cluster-level lemmas: `kvInv_alloc_boot`, the mints
  from the continuation, `consInv_alloc`, `kvCertInv_alloc`, the indices' allocations,
  `rnEnvOk_of_cluster` from `clusterWorkloadOk`) in parallel; then N3 (the workload clause for one
  server), N4 (the KV abstraction, with the mvcc/watch session).

**Addendum (2026-10-16, after the N0 survey; adopted).** D13 as first written cannot be carried
out: `newRaftNode` runs inside the `EtcdServer{…}` literal (`server.go:324`), before
`idutil.NewGenerator` (331) and `mvcc.New` (370), and `newRaftNode.spec` fixes the raft
environment's `C`/`T`/`RQ` in its channels' predicates at the call, while `isServerBuilt` needs
`Er.C = srvC ρ E …` over the generator's names, the store's `γ.idx`/`γ.cok` and `γrev`.

- **D13a: the names are chosen before the call (route B).** The proof allocates the ghost names
  first and passes them in: `idutil.NewGenerator.spec` and `mvcc.New`/`newWatchableStore`/
  `NewStore` take the caller's names (and `mvcc.New` returns the certificate authority
  `ghostMapAuth γ.cok 1 ∅` it now drops); a lemma gives `srvC ρ E = srvC ρ E'` when the two agree
  on `γ.idx`, `γ.cok`, `γrev` (the store's location is known only after `mvcc.New`).
  `isServerBuilt` and the `run`/`start` proofs are unchanged. *Rejected:* route A, a late-bound
  `C` through a one-shot saved predicate set after `mvcc.New` (changes `isServerBuilt`'s `%HEr`
  and the proofs that rewrite with it). The mvcc/idutil spec changes are coordinated with the
  mvcc/watch session.
- **D13b: `bootstrap`'s contract is a premise of `NewServer.spec`**, a triple in its
  precondition, not an axiom: `raftConfig` sets `CheckQuorum: true` on both bootstrap paths
  (`bootstrap.go:572`), and `NodeStartSpec` needs it off, so an axiom giving `bOk` would be false.
  The raft start result as proved thus does not cover etcd's actual configuration
  (`CheckQuorum` on); this was already a premise, now made concrete.
- **D13c: `clusterWorkloadOk` is a premise of `NewServer.spec`**, not part of `srvBuildGap`:
  the raft installer `NewServer` runs needs `rnEnvOk`, whose `E.C` clause is the workload clause.
- **D13d: `NewServer.spec` has an error case** (`srv = nil`, `err ≠ nil`): `NewTokenProvider`,
  `v3compactor.New`, `restoreAlarms`, `tr.Start` can fail, so their contracts do not promise
  success, and the proof steps through the two deferred closures (`b.Close()`,
  `newSrv.kv.Close()`).

## The KV over both stores, the hook installed late, the constructors' contracts (unit N4)

**2026-10-17 · adopted (branch `raft-retarget`; D14; after N1 stopped, `notes/STATUS.md`,
"Server construction, unit N1")**

`NewServer` sets `srv.kv = mvcc.New(…)`, a `*watchableStore`, creates the lessor and the store
before it installs the backend's post-lock hook (`server.go:412`), and calls eight names-only
constructors. N1 found the request-path and apply results stated for a plain `*store`
(`txn.isKV`), the stores' backend contracts needing the hook fixed at creation, and seven
constructor contracts false. D14 settles the three.

- **D14a: the KV abstraction, by the store's own two shapes.** The `mvcc.KV` value is either the
  plain store or the watchable store wrapping it; everything the txn and apply proofs read goes
  through the inner `*store` `s` and its names `γ` (the watchable store's `γw.st`), unchanged.
  * `mvcc.kvIs kv s γ` (persistent): `kv` is `*store` at `s`, or a `*watchableStore` `ws` whose
    embedded `store` is `s` (`ws.store ↦□ s`); with `isStore s γ`. `isReadView rv s γ` becomes
    `rv.kv ↦□ kv ∗ kvIs kv s γ` (a watchable store points its inner store's `ReadView` at itself,
    `newWatchableStore`): `readView.*`, `store.Rev` read through either (`Read` of the watchable
    store is the promoted `store.Read`, a wrapper lemma).
  * `txn.isKV kv s γ`: the plain store (`γ.watchQ = false`) or a watchable store over `s`
    (`∃ ws γw, kv = *watchableStore ws ∗ isWatchableStore ws s γw ∗ γw.st = γ`, so
    `γ.watchQ = true`). `isApplyKV` is unchanged in form (its read view is `isReadView`'s).
  * **The writer.** The watchable store's write transaction needs the sole writer of its notified
    log (`watchWriter γw L`: the certificate, every token, the writer's half of `γw.wlog`; K1a,
    final on the watch side) and notifies under `s.mu` at `End`. So the writer's resource grows a
    part that is empty for the plain store: `txn.wlogOwn s γ L` (`if γ.watchQ`: some watchable
    store over `s`, `γw.st = γ`, the half `ghostVar γw.wlog ½ L` and the certificate of `L`), and
    `txn.kvWriter s γ L := soleWriter γ L ∗ wlogOwn s γ L`. Which `ws`/`γw` the half belongs to
    is fixed by `s`: two watchable stores over `s` are the same (`s.ReadView ↦□ rv`,
    `rv.kv ↦□ ws`), and the transaction uses the names the writer's half carries.
  * **The txn specs.** `Put`, `DeleteRange`, `Txn` keep their token-and-certificate form (`m`
    tokens, a certificate of `log₀`, the pin) and add the writer's part: `wlogOwn s γ Lw` with
    `γ.watchQ → m + 1 = soleBudget Lw ∧ Lw.length + 4 ≤ 2 ^ 63` (a watchable store's writer is
    the sole writer), given back at the transaction's committed log. The sole-writer corollaries
    (`SoleWriterKV.lean`, `txn/Results.lean`) and the apply thread's `kvOwn` take `kvWriter`
    where they took `soleWriter`. `Range`/`Count` change only through `isKV`.
  * **The write transaction as an interface value.** The functions handed `kv.Write`'s result
    (`put`, `deleteRange`, `getPrevKV`, `checkAndGetPrevKV`, `executeTxn`/`txn` through
    `txnViewIs`) take `interface.mkOk tyX vX` with `mvcc.twWrap tyX vX mw`: the `*metricsTxnWrite`
    `mw` itself, or a `*watchableStoreTxnWrite` whose embedded `TxnWrite` is `mw`
    (`twl ↦□ {mw, ws}`: `isWatchTxnWrite`'s struct made read-only; Go never writes it after
    `Write`). Its `Range`/`Put`/`DeleteRange`/`Rev`/`FirstRev`/`Changes` are `mw`'s (wrapper
    lemmas, `KVView.lean`); `End` is the store's own (`metricsTxnWrite.End` or
    `watchableStoreTxnWrite.End`), taken at the top-level functions.
  * The watch session's predicates (`isWatchableStore`, `watchStoreBody`, `wlogQ`) are unchanged;
    `isWatchTxnWrite` (this unit's) changes only in its struct points-to.
  *Rejected:* a `StoreNames` field naming the notified log (ripples through every store);
  hiding the half in the watchable store's lock (changes `watchStoreBody`); the derived sole-writer
  statements only for the watchable store (the request path's statements cover both today).

- **D14b: the post-lock hook is a ghost slot the backend owns, frozen at install.** The store and
  lessor never call `LockInsideApply` during construction (`NewStore`, `restore`,
  `initAndRecover` take `LockOutsideApply`), but their persistent backend contracts name the hook
  `f` that `LockInsideApply` runs, and `f` is the closure `getTxPostLockInsideApplyHook` allocates
  at line 412 (its value is not known before). So the contracts name the slot, not the value:
  `isKeyBackendG`/`isBatchTxG`/`batchTxSpecG`/`storeBackend` (and the lessor's `leaseBackend`)
  take a ghost name `γhf` for `f`, and `LockInsideApply`'s triple quantifies the hook `g` with
  `dghostVar γhf □ g` in its precondition. The store's names get `γ.hookFn := d.γB.hook` for the
  real backend (`plHookRO d.γB g` is that `dghostVar`), its own frozen slot for mvcc's assumed
  backend (as now). `hookIs γ P f` keeps its meaning (`P`'s saved proposition and the frozen
  slot at `f`), so every caller's statement (`txn`, `apply`, the server) is unchanged; `NewStore`
  and `mvcc.New` over the real backend give the saved proposition only (`hookInv γ P`), and the
  holder of `plHookRO d.γB f` (after `SetTxPostLockInsideApplyHook` and `plHook_persist`) puts
  `hookIs γ P f` together. The bridge (`mvcc_NewStore_backend`) no longer takes `plHookRO`.
  *Rejected:* predicting the closure's value (it holds a fresh cell); a prophecy.

- **D14c: what `bootOk` adds.** The backend fresh beyond the `Key` bucket: the clients' view of
  the `Lease`, `Alarm`, `Auth` buckets empty or absent (a new cluster's backend: `bootstrap` on
  an empty data directory) with the auth flag unset; the backend's `isBackend`-level resources the
  constructors spend at construction (`bOpen` fractions, write-back tokens beyond `NewStore`'s
  two, reader tokens). Stated with the backend's vocabulary (`bView`, `bOpen`, `wbTok`, `rdTok`).

- **D14d: the constructors' contracts are axioms true of the Go code**, their apply-side clauses
  tied to the real batch lock and hook instead of `∀ P f`: a contract `C P f` becomes
  `□ ∀ f, backend.plHookRO γB f -∗ C Pk f` (`Pk` the backend's batch lock invariant,
  `isBackend γB P W Pk b`); each takes the backend resources it uses (`isBackend`, a `bOpen`
  fraction, write-back tokens) and the fresh-bucket facts of D14c. Their true shapes are N1's
  audit (`notes/STATUS.md`): `NewLessor` gives `lessorInv`/`lessorCfg`/`lessorExpiredC`/
  `lessorBackend` (with `leaseRevokeRate`'s default) and the empty live set, the derived
  contracts following (`lessorOk_of_lessorInv`, `isLessor_of_lessorInv`,
  `isApplyLessor_of_lessorInv`); `NewAuthStore` takes a non-nil token provider and the unset auth
  flag and gives `authInv` (`isReqAuth_of_authInv`, `isAuthStore` at `on = false`);
  `NewAlarmStore` the backend's `ForceCommit` resources and gives the alarm store at the real
  lock. `lessor.Revoke`'s and `Lookup`'s clauses of `isApplyLessor` stay premises
  (`isApplyLessor_of_lessorInv`), now at `kvWriter`.

- **D14e: the background goroutines, the cheap option (the user's decision, 2026-10-17).**
  Configuration premises turn them off or make them harmless; their full modelling is open work.
  `cfg.AutoCompactionRetention = 0` (no compactor: `v3compactor.New` and `Run` are not reached;
  also sidesteps `issues/etcd-compactor-periodic-tiny-retention.md` and
  `issues/etcd-compactor-started-before-start.md`); the `LeaseCheckpoint` feature off (no
  checkpointer installed: the lessor's `runLoop` never calls one, and a non-primary lessor's loop
  only takes its lock); the peers' URLs valid (`types.NewURLs` succeeds on each member's: no
  `AddRemote`/`AddPeer` panic). The transport's goroutines (inbound messages into `srv.Process`,
  the peers' senders) and the lessor's loop are stated as what they are: the transport's contract
  promises only what `NewServer` and `start` use (`Start` returns or errs, `AddRemote`/`AddPeer`
  return, `transportStarted`), under a named premise `transportEffectsOk` that its goroutines'
  calls into the server (`Process`, `ReportUnreachable`, `ReportSnapshot`, `IsIDRemoved`) are
  outside the model -- the cluster's message trust assumption, explicit.

- **Staging.** N4a (D14a: the abstraction, the txn/apply/server proofs over it, `server_kv_backend`
  for `mvcc.New`); N4b (D14b); N4c (D14c-e: `bootOk`, the contracts); N4d (`NewServer.wp_proof`,
  `srvBuildGap` without the KV rows).

**Addendum (2026-10-17, unit N4 stopped at N4c; D14f adopted 2026-10-17, the user's choice A).**

- **D14f (adopted 2026-10-17): the write contracts of the names-only stores take the backend's write
  budget.** Making
  the constructors' contracts true (D14d) found that every apply-side clause that writes the backend
  under its batch lock without going through the store -- `isApplyLessor`'s `Grant`/`Checkpoint`
  (`lease.leaseBackend`), `isAlarmStore`'s `Activate`/`Deactivate`, `isAuthStore`'s enable/disable
  and admin requests, `isCluster`'s writes -- asks only `csContract P f`, while the real backend's
  `LockInsideApply` needs an open share (`bOpen`) and its `Unlock` a write-back token (`wbTok`,
  the read buffer's `uint64` version). As stated they are not true of the model over the real
  backend, so the constructors cannot promise them. Proposal: `dispatch` hands its one write token
  per entry (`mvcc.storeWT E.γ`, today the KV methods') to every write method, whose contract
  clauses take it and lend the reader's open share (`mvcc.storeRT E.γ`, from `kvOwn`'s reader);
  `leaseBackend`'s `LockInsideApply` takes the same. Then D14d's constructor contracts (axioms of
  `NewLessor`, `NewAuthStore`, `NewAlarmStore` at the real `Pk` and `plHookRO`) are true. Independent
  of it: `schema.alarmBackend`/`authBackend` are axiomatized types (`schema.toml`), so no contract
  can say that `NewAlarmBackend(lg, be)` wraps the real backend; translate them with their fields
  (and `NewAlarmBackend`/`NewAuthBackend` with bodies), or state the link with abstract predicates.

- **D14g (adopted 2026-10-17, the user's choice (a)): the server's lifetime bound.** Unit N4 found
  the server's write budget unsatisfiable over the real backend (`notes/STATUS.md`, "unit N4,
  continued"): `bootOk` gave `2 ^ 64 + 3` write-back tokens and `start` took `2 ^ 64 ≤ N`, while the
  backend's batch lock bounds the tokens out below `2 ^ 40` (`backend.bgOk`). Now:
  * `bootOk γ id bootLog N b` (and `bootstrapContract … N`) gives the tokens the backend has, `N + 7`
    (within the cap: a premise of `NewServer.spec`, satisfiable for `N + 7` below the backend's
    budget): `N` for the applied entries, seven for the construction (`mvcc.New` two, `NewLessor`
    one, `NewAuthStore` two, `NewAlarmStore` one, each a write-back of its recovery's `Unlock`,
    and `SetTxPostLockInsideApplyHook` one);
    and the fresh-bucket tokens of the lessor's and the auth store's data (`bkFresh`, opaque: the
    model's readers' view cannot state a hook bucket's contents).
  * **`srvLifeBound ρ.raft N`** (`InvRun.lean`, persistent): every log raft commits after the
    start has at most `N` entries. A residual bound of the kind of `storeSmall` and the id
    budget, a workload premise of `NewServer.spec` (beside `clusterWorkloadOk`) and a premise of
    `run`, `start`, `Start` and `start_gives_views`, replacing `2 ^ 64 ≤ N`; `run` takes each
    batch's tokens by it (the committed log `A ++ ce` has at most `N` entries).
  * The write contracts take one token per write method (D14f). The backend's `Commit`/
    `ForceCommit` specs take a token each, but in Go they commit first and their `Unlock` finds no
    pending write, so it does not write back: the auth store's `Unlock` (`Unlock` then `Commit`) and
    `AuthEnable`'s `ForceCommit` write back once. The axioms say so.
  *Rejected:* raising the backend's `2 ^ 40` cap (it bounds the buffers' counters too,
  `cnt.e ≤ hookMax * (2 ^ 40 + 2)`; a `2 ^ 64` budget would still not cover `start`'s old premise
  with the construction's seven).

- **D14h (adopted 2026-10-17, the user's choice 1A): leases outside the workload for now.** The
  workload premise excludes lease requests: `apply.rqOk` is `False` for `LeaseGrant`,
  `LeaseRevoke` and `LeaseCheckpoint` (with no lease granted none expires, so the lessor's loop
  proposes no revocation and calls no checkpointer). So the `Revoke` clause of
  `apply.isApplyLessor` is never used: it is stated vacuously (`⌜False⌝` in its precondition), and
  `revokePre` carries `rqOk` (the `LeaseRevoke` appliers close by it); `lessor.Revoke` is not
  specified (no false spec of it), its proof with the range deleter recorded in the lessor's
  invariant stays with unit T3 (leases). `isApplyLessor`'s `Lookup` clause, called on every put
  by the auth layer's `checkLeasePuts` (`Lookup(0)` included), cannot be excluded with them: it
  is part of `lease.NewLessor`'s axiom (the lessor's lock read-locked; the model's reader slots
  aside, the Go `RWMutex` bounds readers by `2 ^ 30`). Leased puts and transactions need not be
  excluded: with no lease granted, `checkLeasePuts` finds none and the txn package's check fails
  with `ErrLeaseNotFound`, both in the model. `ckptEffectsOk` stays a premise of `NewLessor`'s
  axiom (a statement about the Go code, whatever the workload); under D14h it is never exercised.
  `NewUberApplier.spec` names the raft status and the snapshot server (the server itself) in its
  premise, which was undischargeable.
- **D14i (adopted 2026-10-17, the user's approval): the applier contracts carry the apply
  thread's ownership.** Two of `apply.backendOptsOk`'s contracts hid resources only the apply
  thread has, so no caller could establish them: `ForceSnapshot` writes `s.forceDiskSnapshot` (a
  plain store), and `ConsistentIndex` reads `ci.be` with the owner's share and may load the index
  (`SetConsistentIndex` from the backend). Now `apply.AEnv` has `FS` (the right to
  `ForceSnapshot`, the server's `srvFS s`) and `ciC` (the kind of resource `ConsistentIndex` reads
  under, the server's `srvCiC γ ci`: the apply protocol's state, not pending, with
  `applyBackend`); `isSnapshotServer ss E.FS` is `{{ E.FS }} ForceSnapshot {{ E.FS }}` and
  `isConsistentIndexer ci E.ciC` is, for every `C` with `E.ciC C`, `{{ C }} ConsistentIndex
  {{ C }}`. They are threaded as D14f threaded the write token: `E.FS` in the cluster methods'
  clause, `dispatch`, the uber-applier's `Apply`, `apply.Apply` and the server's apply thread
  (`applyEntryNormal`, `apply`, `applyEntries` take `srvFS s`; `applyAll` lends it out of its
  snapshot state); the consistent index's resources are lent out of the critical section's
  precondition `Pre` (`ciSplit E Pre`: `Pre` holds such a `C`, given back), a premise of the
  response methods' clause and, under `shouldApplyV3` (the only case they are called), of
  `dispatch`/`Apply`; the server's `Pre` (`applyEntryNormal`'s) holds `applyThread ∗
  applyBackend`. The server's fields record `srvEnvOk s γ ci E` (`E.FS = srvFS s`, `E.ciC = srvCiC
  γ ci`). The contract over the real index holds for a fresh cluster (`γ.m0 = (0, 0)`:
  `stLoaded` is the identity, the index loads `0`). With it, `NewServer` gives the uber-applier's
  rows (`applierFor`, `applyKV` at `bootKV`), with three constructor axioms strengthened, each
  true of the Go code: `NewAlarmStore` over a fresh alarm bucket gives `alarmFresh a`, under which
  `Get` returns no alarm, and its apply contract (`Activate`, the map's only writer) for the token,
  so `restoreAlarms` leaves the base alarm chain; `NewAuthStore` gives the enabled lock's reader
  slots (one for the auth applier, one for the KV's resources); `NewLessor` the lessor lock's
  reader slots (one for the store, one for the apply thread's lease owner).

## The client's construction: grpc's dial as descriptors, a trusted body (item 5, 2026-10-17)

**Dial options as descriptors.** A `grpc.DialOption` is an opaque closure; the axioms of its
constructors say what it does (`grpcDialOptIs o d`, `InvDial.lean`), and `NewClient`'s axiom
composes the connection from the descriptors as grpc does (the last `WithUnaryInterceptor`'s
interceptor, no chain, no default call options). An option no axiom describes has no descriptor,
so a dial holding one is simply not covered: no catch-all "harmless option" is assumed. The
caller's `Config.DialOptions` are excluded by a premise (empty) rather than modelled
(`issues/etcd-client-dialoptions-unary-interceptor.md`).

**Why `NewClient` asks for etcd's stream interceptor.** `grpcConn` (item 4's `InvGrpc.lean`,
not ours to change) records the unary chain only, and `ClientConn.NewStream`'s axiom assumes the
connection's stream interceptor is etcd's. `NewClient` therefore produces `grpcConn` only for a
dial whose stream interceptors satisfy `etcdStreamInterceptor`, a property only
`streamClientInterceptor`'s axiom introduces: a plain grpc client could not reach `NewStream`'s
axiom with an interceptor it does not describe.

**Why a trusted body for `dialWithBalancer`.** The pinned translator misnames grpc's
`resolver.Builder` there (`pkgRef`'s same-name fallback) and its output does not elaborate. The
alternatives were an axiom stating `dialWithBalancer`'s result directly (which would hide the
dial: `dial`, `dialSetupOpts`, the interceptors, all unused), or a fork change (not pushable
here). The translator's own output with the one type corrected keeps the proof over the real
body; the axiom is that this text is the method's body, `MethodUnfold`'s shape, with grpc
`resolver`'s `Builder.TypeAssumptions` (which `clientv3`'s assumptions lack, as `clientv3` does not
import the package). Both go when Goose is fixed.

**The resolver's state handed to grpc.** `etcdResolverOwn r eps` is exclusive: `SetEndpoints`
needs it, and `NewClient` consumes its grpc form (`grpcResolverAt`), so `grpcConn`'s address is
stable for good; after `New` nobody can call `SetEndpoints` (not in `New`'s postcondition), and
`autoSync` (which would) is turned off by a premise.

## Item 8: package initialization (2026-10-17, branch `construct`)

**How a package's initialization is proved.** `etc/gen-init.py` writes `Proof/<pkg>/Init.lean`:
`<pkg>.wp_initialize'` follows the translation's `initialize'` statement by statement (the
`GlobalAlloc`s of translated variables, the imports' `initialize'` in Goose's order, the
variables' initializers in Go's init order, the translated `init()` bodies). An untranslated
initializer `X.init` is an axiom of the translation, so what it does is a trust-boundary axiom of
the package: `opaqueInitsOk` (the listed ones run without panicking), `errorsNewVarsInit`
(`X = errors.New(msg)`, messages from the Go source) or `<X>_init` (what a fact reads of `X`).
Each is a triple about an uninterpreted constant, so a diverging `X.init` satisfies all of them:
they cannot make the logic inconsistent. Translating the initializers instead (Goose config)
would turn the `errors.New` ones into proofs; not done, to keep the translation unchanged under
three concurrent agents.

**A package fact states only its own variables.** A fact about another package's variable
cannot be proved by the package's initializer (`package.init` gives back only the import's
`isPkgInit` when it is already initialized). So the facts moved to their owners (`errorsInit`,
raft's `isInitialized`, `traceutilInit`, `schemaInit`, `mvccInit`, `rpctypesInit`,
`etcdserverpbInit`, `clientv3Init`, `backendInit`); the consumers' facts keep their copies, now
derived. A fact that names a predicate defined above the owner's `Base.lean` is restated below it
(`pbDescIs` for grpc's `grpcDescIs`; `OptsM`/`optsAt` moved to `BboltOptsDefs.lean`).

**Method sets are premises** (`EtcdGrove.ErrorStringLeaf`, `EtcdGrove.RpctypesEtcdErrorMethods`),
as Perennial's `context.ErrorStringIsError`: the semantics leaves method sets uninterpreted.

**Item 8: context's facts (a Perennial proposal).** Perennial's `context` fact (`isInit`) keeps
only that `Canceled` and `DeadlineExceeded` are typed errors, though its initializer stores
`errors.New("context canceled")` (`wp_New_errorString`, the exact `*errorString`) and
`deadlineExceededError{}`. `v3rpc` needs `Canceled` to be a pointer error (`togRPCError`'s
`errors.Is`) and `read` needs both as leaf errors with their messages. A package fact cannot be
strengthened after the fact (above), and an axiom `isPkgInit context ⊢ …` would be unsound
(`isPkgInit` is not sealed: a proof that allocates the variables' cells can assemble it), so the
fact is a premise here, `EtcdGrove.ContextCanceledPtr` (`v3rpc/Init.lean`). The general fix, to
propose to Perennial on its own: `context.isInit` records the values, `Canceled ↦□
interface.mkOk (ptr errorString) #x` with its message and `DeadlineExceeded ↦□
interface.mkOk deadlineExceededError.ty #()`. It unblocks `v3rpc`'s premise and, with a registry
model, `read`.

**`read` stays assumed** (superseded by D16, 2026-10-17: proved, the registration rights a
precondition). Its translated `init()` calls `prometheus.MustRegister`, which panics
on a duplicate name. A true spec needs the default registry's registered names, a resource the
whole program's initializers share; `wp_initialize'`'s shape (`ownInitializing` only) has no
place for it, so adding one means changing every importer's theorem. `etcdserver`'s and `v3rpc`'s
theorems take `read.initialize'.spec` as a hypothesis (`gen-init`'s `ASSUMED`).

**mvcc's counter contract.** `mvcc.counterSpec` said `Add(x)` returns for every `x`; Go's
`counter.Add` panics on a negative value. The contract now covers the arguments the code passes:
`float64(n)` of an unsigned `n`, and of a signed `n ≥ 0`. `scheduleCompaction`'s compacted-keys
count (an `int`) is shown non-negative by counting: the keys it deletes are distinct bucket keys
of the job's log up to the compaction revision (a cursor orders the batches), so no more than
that log's changes, fewer than `2 ^ 62` by the premise `mvcc.CompactSmall` (a physical bound,
as `storeSmall`), carried by `compactJobPre` and taken by `updateCompactRev`, `Compact` and
`compactLockfree`.

## Repeated proof blocks as file-local macros

**2026-10-17 · accepted**

A Go `if`/`select`/`switch` whose arms continue with the same code got the same tactic block
pasted into each arm of its proof (up to 350 lines, three times, in `closeSubstream`). The
duplication review (notes/STATUS.md, "Repeated in-proof blocks as macros") replaced them.

**Decision:** prove the shared continuation once when it is easy to state (a `have`, or merging
identical `cases` arms); otherwise a `set_option hygiene false in local macro` just before the
theorem, with a docstring naming the branches that use it, taking as arguments the values the
copies differ in (the pattern of `txn__Else.lean`). Copies that differ in more than a couple of
values stay copies. The cost: an error inside a macro is reported at its use, and a reader
expands it by eye.

- **Iris's frame `$H` inside a quotation.** In a macro's `` `(tactic| …) `` Lean reads `$H` as an
  antiquotation, so a block that frames a hypothesis does not parse as a macro body. The macros
  write ``$(frameH `H)``, which builds the node the parser makes for `$H`
  (`Proof/go_etcd_io/raft/v3/FrameH.lean`, beside `ProjSimps.lean`, the other generic tactic
  utility; at first each file had its own copy, 20 in all, moved there before merging). The
  general fix is in Iris-Lean, a frame syntax that works inside a quotation, to propose there
  as its own change (CLAUDE.md, "Changes to Perennial"); then `frameH` goes.
- *Rejected:* a global macro per block (they are one proof's), and an auxiliary lemma for every
  continuation (the statements, long Iris contexts, would be longer than the blocks).

## The verified configuration turns `CheckQuorum` and `PreVote` off: a patched `bootstrap` (D15, temporary)

**2026-10-17 · adopted, then **reverted** the same day (branch `raft-retarget`; the user's choice (b), a stopgap until (a) lands)**

**Reverted (2026-10-17, the user's decision once (a)'s `CheckQuorum` half was merged):** the patch
only ever changed `CheckQuorum`, which the raft proof now covers (merge of `raft-checkquorum`,
"`CheckQuorum` on"); `PreVote` comes from `cfg.PreVote` with no patch. So the etcd pin is back at
`goose-lean` (`09669450f`; the translation identical to before D15), `ServerConfig.DisableCheckQuorum`
is gone, `bootOk` states no `CheckQuorum` clause (the raft start result no longer reads it), and
`NewServer.spec` keeps only `cfg.PreVote' = false`, a configuration etcd's code allows (embed's
default is on). The fork branch `goose-lean-raft-cq-off` is no longer referenced.

The raft start result (`NewRawNode.spec`, `bootstrappedRaft.newRaftNode.spec`) requires
`CheckQuorum = false` and `PreVote = false`; etcd's `raftConfig` (`bootstrap.go:572`) sets
`CheckQuorum: true` and `PreVote: cfg.PreVote` (which `embed` sets on by default). `bootOk`, the
contract of the names-only `bootstrap` that `NewServer.spec` takes as a premise (D13b), claimed
both off whatever the configuration: false of etcd, so the adequacy example could never discharge
it. The user chose (a) to extend the raft proof to both on (branch `raft-checkquorum`, another
agent) and (b) meanwhile to verify a patched `bootstrap` that turns both off.

- **D15: a configuration field, not a direct edit.** The fork's branch `goose-lean-raft-cq-off`
  (`goose-lean` plus one commit, `e1e0193c2`, the etcd pin of `etc/goose.py`) adds
  `ServerConfig.DisableCheckQuorum bool` and sets `CheckQuorum: !cfg.DisableCheckQuorum` in
  `raftConfig`; both lines are marked TEMPORARY. Its zero value keeps etcd's behaviour (CheckQuorum
  on), and `PreVote` already follows `cfg.PreVote`, so the patch is one field and one expression
  and changes no default. A direct edit (`CheckQuorum: false, PreVote: false`) would have left the
  Lean side untouched but changed etcd's behaviour for every configuration; the field costs only
  two premises.
- **The statements.** `bootOk` takes the configuration and states what `raftConfig` does with it:
  `cv.CheckQuorum' = !cfg.DisableCheckQuorum'` and `cv.PreVote' = cfg.PreVote'` (true of the
  patched code for every `cfg`). `NewServer.spec` gains the premises
  `cfg.DisableCheckQuorum' = true` and `cfg.PreVote' = false`, which the adequacy example's
  configuration must meet (`PreVote` is false in a `ServerConfig` literal unless set).
  `bootstrap` stays names-only (its contract a premise); `raftConfig` is not translated with its
  body (the translation changes only in `config`'s struct).
- **Reverted once (a) lands:** the pin back to `goose-lean` (the fork branch dropped), the two
  premises of `NewServer.spec` and `bootOk`'s configuration parameter go, `bootOk` states
  `CheckQuorum' = true` and `PreVote' = cfg.PreVote'` as etcd's code does.

## prometheus's default registry: registration rights as an initializer's precondition (D16)

**2026-10-17 · adopted (branch `raft-retarget`, item 8: the read package's initializer)**

The read package's translated `init()` calls `prometheus.MustRegister` on its two counters, and
`MustRegister` panics when `Registry.Register` fails: in particular when a descriptor of the same
name (with other labels or help), the same descriptor ID or the same collector ID is already
registered. Whether it panics depends on what every package of the program registered before:
a resource, which item 8 left out (`read` assumed, `etcdserver`'s and `v3rpc`'s theorems taking
its spec as a hypothesis).

- **D16a: the right to register a name.** `EtcdGrove.prometheus.nameFree n`
  (`Proof/github_com/prometheus/client_golang/prometheus/Registry.lean`, an abstract resource:
  an axiomatized predicate, as bbolt's `ownDB`) is the exclusive right to register a collector
  whose one descriptor is `n`'s, label-free, with the default registry: nothing registered there,
  now or later by anyone but the holder, has a descriptor named `n`, or `n`'s descriptor ID, or
  that collector ID. `MustRegister.spec` (one collector `c`, `collectorName c n`) consumes it;
  `NewCounter.spec` gives `collectorName c (fqName ns sub name)` (and mvcc's `counterSpec`); the
  `CounterOpts` literal (`Opts` is an axiomatized type) is the axiom `wp_counterOptsLit`, over the
  axiomatized `counterOpts`. Each axiom is about uninterpreted constants, satisfiable whatever
  the semantics, and true of client_golang v1.24.1 (their docstrings say why).
- **D16b: the rights reach the initializer as a precondition.** `read.wp_initialize'` is
  `{{ ownInitializing g ∗ EtcdGrove.read.readRegPerm }} initialize' #() {{ ... isPkgInit read }}`,
  and so are the theorems of the packages whose import closure contains `read` (`etcdserver`,
  `v3rpc`): each passes the rights to the one import that leads there (`etc/gen-init.py`'s
  `PRE_RES`, which asserted there is one; since D19e any number may, the rights held until `read`
  is initialized). Program start (the adequacy theorem, item 9) owns the
  rights to every name no default collector has and gives each out once, so the cross-package
  freshness of the names is discharged there: two packages registering one name would need one
  right twice. What item 9 needs of the Go code is stated and checked now (`read.names_ok`'s
  docstring): only `read/metrics.go` names the two metrics (grep of the pinned etcd), and a Go
  program importing `embed` and `v3rpc` (all of etcd's server initializers) starts and has each
  registered once.
- **Why not a package fact.** A package's fact is persistent (`isPkgInit`), so it cannot hand
  out an exclusive right; an invariant holding the rights could be opened by any proof, so its
  rights could be taken before the read package runs. What makes Go register the names once is
  that a package's body runs once, which Perennial's `ownInitializing` knows (the package map,
  `ownGoState`) but does not expose to the body as a resource (half of a ghost variable, no
  fragments), and the other packages' `wp_initialize'` return an arbitrary map, so a ghost
  mirror of it cannot be kept. A general fix, for Perennial on its own: `wp_package_init` could
  give the body a once-per-package token (from the map's missing entry), out of which a package
  could take resources allocated for it at program start; the precondition here would then go.
- **The cost.** The three theorems are not in Perennial's `initialize'.spec` shape. A caller that
  ran `etcdserver.initialize'` twice would need the rights twice (the second call does nothing,
  but the triple cannot say so); on the path each is called once.
- *Rejected:* `{{ True }} MustRegister c {{ True }}` (false: a second registration panics);
  keeping `read` assumed (its spec is the same claim, unproved).
- **`context`'s errors** (`readInit` states `Canceled` a leaf `errors.New` error and
  `DeadlineExceeded` a leaf `deadlineExceededError{}`): a premise, `EtcdGrove.ContextReadErrs`
  (`read/Init.lean`), as `ContextCanceledPtr` was ("Item 8: context's facts"), which it replaces:
  `v3rpc`'s `Canceled` fact now follows from it.

## `srvBuildGap`'s rows: the lifetime bounds as workload premises, the cluster's version from its contract (D17)

**2026-10-17 · adopted for four rows; the fifth (`rnSnapOnce`) stopped for a decision (branch
`raft-retarget`; open-work item "srvBuildGap's rows")**

After D14i `srvBuildGap` (the rows of `start`'s construction premise no `NewServer` proof gave)
had five rows. Three are bounds that are not facts of the code (a process issues fewer than
`2 ^ 48` request ids, the store's sealed logs stay below `2 ^ 62` changes, the logic's thread
bound), one is a fact of the code behind a names-only package (`ClusterVersion()` monotone), one
is a resource the model cannot give (`rnSnapOnce`).

- **D17a: the id budget is a lifetime bound, not credits.** `idCred γi n` was `n` exclusive
  credits of the `2 ^ 48 - 1` `NewGenerator` handed out (an `Auth Nat` authority in `idGen`'s
  invariant), and `srvBuildGap` asked `□ |==> idCred ρ.ids 1`: an unbounded supply, which together
  with the authority proves `False` (mint `2 ^ 48` credits) -- the residual was unsatisfiable, and
  every result composed with it vacuous. The request path cannot thread a finite supply: the read
  loop issues an id per `ReadIndex` round, retries on timeouts, and runs forever. Now `idGen`'s
  invariant counts the ids issued (`γi.cred` a monotone counter, `monoNatAuthOwn`), and
  `idCred γi n := idLifeBound γi`, the persistent premise `□ ∀ k, monoNatLbOwn γi.cred k -∗
  ⌜k < 2 ^ 48⌝` (`n` unused, kept so the ~60 statements over `idCred` keep their form). `Next`
  counts one more id and gets `k + 1 < 2 ^ 48` from it, which is all the uniqueness argument used.
  `idNamesFresh` is the counter at `0` and the empty maps; `NewGenerator.spec` no longer returns
  credits. `NewServer.spec` takes `idLifeBound ρ.ids` (a premise of the kind of `srvLifeBound`,
  D14g, at names the caller chooses before the call, D13a) and gives `□ |==> idCred ρ.ids 1`
  (`idCred_supply`). *Rejected:* credits minted from an invariant (a fancy update, `|={E}=>`,
  where ~20 statements have `|==>`, and the same bound on the mints); threading credits per
  request (the read loop's ids are not per request).
- **D17b: `storeSmall` and the thread bound are workload premises of `NewServer.spec`.**
  `storeSmall E₀.γ` (it reads only the index names, which `E₀` fixes before the call) and
  `threadBound GF ≤ 2 ^ 31` (the adequacy theorem's `T`, its caller's choice). *Considered for
  `storeSmall`:* a change counter in mvcc's invariant bounded by the write budget `N` (D14g). A
  write token is spent per transaction, not per change, and a `DeleteRange` changes every live key
  in its range, so the bound needs the store's live keys counted against the puts (changes at most
  twice the puts, the puts at most `N` times the request's operations): an mvcc invariant change
  for a bound the adequacy example states as easily as `srvLifeBound`. Left as the premise.
- **D17c: `ClusterVersion()` from the cluster's contract.** `EtcdServer.ClusterVersion` is
  translated with its body (`nil` without a cluster, else `s.cluster.Version()`) and proved
  (`EtcdServer__ClusterVersion.lean`) over `clusterVersionMono cl γcv` (`InvStart.lean`): `cl`
  non-`nil` and its `Version()` `nil` until a ghost witness is owned, non-`nil` from then on.
  `bootOk` (`bootstrap`'s contract, a premise, D13b) gives it for `b.cluster.cl`, beside its other
  cluster contracts; `NewServer` builds `clusterVersionOk s`. True of the Go code: `RaftCluster.
  Version` reads `c.version` under the cluster's lock; it is set by `SetVersion` (non-`nil`) and by
  `Recover` from a snapshot's backend, which holds the version once the entry setting it is
  covered.
- **D17d: `rnSnapOnce` stays the residual (stopped; needs a decision).** `run` calls
  `s.r.raftStorage.Snapshot()` while raft's node goroutine owns the storage; Go serializes them
  with `ms.Mutex`, but the model puts the storage's snapshot field and object in
  `ownMemoryStorage` (raft's, exclusive), so no application-side triple for `Snapshot()` exists
  and no proof can establish `rnSnapOnce` as stated (strengthening `MemoryStorage.Snapshot.spec` and
  `proto.CloneSnapshot`'s axiom to state the clone's pointers non-`nil` is easy but does not help).
  The fix is a change to raft's `MemoryStorage` model: the snapshot under the lock with a ghost
  variable of its id/conf state split between the lock, the owner and an application token that
  `ApplySnapshot`/`CreateSnapshot` also take (`NewMemoryStorage` gives it). It meets `InitialState`,
  which reads `ms.snapshot` *without* the lock (`issues/raft-memorystorage-initialstate-unlocked.md`):
  with the snapshot under the lock its unlocked read has no ownership, unless the snapshot starts
  outside the lock and some locked call after `InitialState` deposits it, which the abstract
  `isStorage` contract cannot promise the application. The options (each changes raft's public
  `MemoryStorage` specs): (1) `InitialState`'s spec takes the application token, and the token
  lends the snapshot while no other goroutine runs (`StartNode` calls it before the node
  goroutine); (2) a trust-boundary premise that `InitialState` runs before any concurrent
  `Snapshot()`; (3) leave `rnSnapOnce` as the construction's premise. Not decided here.

  **2026-10-18 · option (1) adopted by the user and done** (branch `raft-retarget`; notes/STATUS.md,
  "D17d: `rnSnapOnce` proved"). How "the token lends the snapshot" is realized: an Iris lock
  invariant cannot be opened without the lock, so the snapshot (`memSnapOwn`) lives in an Iris
  invariant `memSnapInv` beside the lock, opened by **key sets**: the lock's key `lk` (in the lock's
  ghost state, `memInvGhost`) with the owner's `ok` (`ownMemoryStorage`'s `memSnapShare`: raft's
  `Snapshot`, `ApplySnapshot`, `CreateSnapshot`) or with the application's `ak` (`memSnapTok`: the
  application's `Snapshot`), or `ok` and `ak` together without the lock (`InitialState`). The
  taker deposits its keys and keeps a receipt (`sw`); any two key sets share a key, so a taker
  always finds the snapshot at home. The snapshot's id and conf state are a ghost value split half
  at home, a quarter the owner's, a quarter the token's (`memSnap_update` needs all three: the
  writers take the token). The invariant's contents are not timeless (protobuf's `pbMsg`
  invariants), so `memSnap_take` returns the snapshot under a later, stripped by the next pure
  step (credits would need `HasLC.hasLC`, which raft's specs do not fix). Two consequences beyond
  D17d's text: (a) `StartNode` must give the token back after `InitialState`, so `newRaft`,
  `NewRawNode`, `setupNode` and `StartNode` take a resource `R` that the `InitialState` premise's
  continuation returns and their posts carry (`RestartNode` instantiates `R = emp`: its premise is
  `□`); (b) `run` reads the clone's `Metadata.ConfState` pointers, so `EnsureSnapshotMetadata`/
  `EnsureSnapshot` now state the conf-state pointer set (`smPtsW`/`ownSnapW`) and the trust-boundary
  `proto.CloneSnapshot` spec gains a conjunct "the clone of a whole snapshot is whole" (true of
  protobuf-go: a non-`nil` message field is present and copied into a fresh destination field; no
  axiom added, the statement of an existing one strengthened). `bootOk` (bootstrap's contract)
  hands the fresh storage's token and states its `InitialState` closure with the token as an
  argument; `NewServer.spec`'s post gives `srvBuildGap` (`rnSnapOnce_of_tok`).

## A client's facts from persistent updates: monotone ghost state, a prophecy only for a general client (D18)

**2026-10-17 · proposed; 2026-10-18 · adopted by the user (the monotone route for the adequacy
example's Put-then-Get; the prophecy for a general client deferred)** (open-work item 9's "client-local
prophecy", `notes/STATUS.md`)

The client's end-to-end specs (`client_put_end_to_end`, `client_get_end_to_end`, ...,
`client/v3/Results.lean`) take `□ AU <{∃∃ σ, etcdKV γk σ}> <{etcdKV γk (kvOpStep op σ), COMM □ Q
σ}>` and return `∃ σ, □ Q σ`. The update is persistent because it does fire more than once: a put
resent after a per-attempt error is proposed twice and applied twice
(`issues/etcd-client-retry-put-ctx-error.md`), and a duplicate can commit after the put returned.
The adequacy example (one member, `clientv3.New`, `Put(k, v)`, then `Get(k)`; the pure conclusion:
no panic and the Get returns `v`) needs the client to hold `etcdKV` in its own invariant and get
"Get's value = Put's" out of these updates.

**What Perennial's Lean port has for prophecies** (pin `a54e1999f`): physical prophecy variables
only. GooseLang has the `NewProph`/`ResolveProph` primitives (`GooseLang/Lang.lean`), the state
interpretation carries iris-lean's prophecy map (`Iris.BI.Lib.ProphMap`, `prophMapInterp`), and
`GooseLang/Lifting.lean` proves `wp_new_proph` and `wp_resolve_proph` over the untyped `proph p
pvs` (a list of `val`); Go code reaches them through the trusted models of
`github.com/goose-lang/primitive`'s `NewProph`/`ResolveProph` and gokv's `trusted_proph`
(`TrustedCode/`), with no Go-level spec. There are no typed prophecies (Rocq's `typed_proph`), no
ghost (erased) prophecies resolvable by a view shift (Rocq Perennial's `GhostProph`-style
construction), and no prophecy-aware atomic-update lemmas.

**The options.**

1. **Monotone ghost state (implemented, `client/v3/PutThenGet.lean`).** The client's invariant
   holds its half of `etcdKV` with the state sorted by key and a monotone counter (`MonoNat`)
   that records "the put has fired"; once it has, the state's value of `k` is `v`. The client
   makes only two updates from it: the put's (`kvOpAu (.put (putKeyOp k v))`, result the
   counter's lower bound `1`: every firing writes `k ↦ v`, `kvOpStep_putKey`) and, holding that
   bound, a read update whose result is `(findKey k σ.kvs).map value = some v`. A put that
   returned `nil` gives the bound (its `□ Q`); the get's reply is its state's value
   (`client_get_value`), so a `nil` get returns `v` (`client_get_own`). Repeated firings, before
   or after the put returned, keep the invariant: the client is the only writer and every write
   is the same. Cost: one new file, no statement changed, no axiom, no Perennial change. Limit:
   a single writer of `k` (any other operation needs its own clause in the invariant: one that
   does not touch `k` keeps it as is), and the conclusion is about values, not revisions or which
   firing the reply is of.
2. **A physical prophecy in the example's Go code.** The example's `main` is ours, so it could
   call `primitive.NewProph`; but the resolution would have to happen at the linearization point,
   which is the server's apply thread (a raft commit), not the client's code. Resolving it in
   etcd's code means changing etcd; resolving it in the client after the reply is too late (the
   firings have happened). Not usable without changing the verified code.
3. **A ghost prophecy turning the persistent update into an ordinary one.** The client
   prophesies which firing the reply will be of (needs item 2: the reply tied to its firing's
   `σ`, `resultIs` naming the raft prefix), hands the server a persistent update that, at the
   prophesied firing, fires an ordinary `AU` the client holds, and at the others an "extra
   duplicate" update the client must accept. Two costs beyond item 2: (a) Perennial's Lean port
   has no ghost prophecies; adding them (an erased prophecy resource resolved by a view shift,
   with a soundness argument against the GooseLang adequacy theorem) is a general framework
   change, to be designed and reviewed in Perennial on its own (`CLAUDE.md`, "Changes to
   Perennial"), not done here; (b) the duplicates are real: a duplicated put bumps the revision
   twice, so even with a prophecy the client's ordinary `AU` holds only for histories that admit
   the extra writes; for linearizability checking (porcupine's model) that means a model where a
   put may be repeated, i.e. what the persistent update already says.

**Recommendation.** Option 1 for the adequacy example (done: `client_put_own`, `client_get_own`;
the example composes them under `putGetInv_alloc` after `kvInv_alloc`). Defer option 3: it buys a
general client spec only after item 2, needs a Perennial feature that does not exist, and cannot
remove the duplicate writes the persistent update reflects. If a general client is wanted, the
first step is item 2 (a write's `□ Q σ` tied to its reply), which also makes option 1 give
revision facts.

## Families of functions with the same body: one lemma over the body

**2026-10-17 · accepted (for the KV handlers only)**

protoc-gen-go-grpc's unary handlers (`_KV_{Range,Put,DeleteRange,Txn}_Handler`) have the same
body up to the method's name and its request and response types, and their proofs were the same
95-line proof, copied. The duplication review (notes/STATUS.md, "Proof families as lemmas")
replaced them.

**Decision:** `etcdserverpb/UnaryHandlerLemmas.lean` defines the common body as a function of what
differs (`unaryHandlerImpl srvTy reqTy repTy meth fullMethod`: one handler's translation with those
abstracted, copied by hand) and proves `wp_unaryHandler` once, stated as the handler specs are,
with the body taken as the `FuncUnfold` instance at those parameters. Each handler keeps its Spec
and Proof files and its `wp_proof`, now one application of the lemma at its method: the build
checks that the translated body is the lemma's body at those arguments (by unfolding both); a
regenerated handler of another shape fails to build, and no axiom or `sorry` is involved.

- *Tried and dropped* (the user's choice): the same for the client stubs `kVClient.<M>`
  (`wp_kvClient_unary`), clientv3's comparison builders (`Version`, ..., `LeaseValue`: `wp_cmpKey`)
  and `IsOptsWith{FromKey,Prefix}` (`wp_isOptsWith`). They built, but the copied bodies and the
  lemmas' statements were as long as the proofs they replaced (no saving in lines), and a copied
  Goose term is harder to read than the proofs; the handlers are kept because four 95-line proofs
  become one.
- *Not done*, because the shared part is not a short statement: the getters (`PutRequest.GetKey`,
  ...: 6-line proofs), `Op.Is{Get,Put,Delete,Txn}` and `*Response.OpResponse` (as short),
  `txn.Else`/`txn.Then` (two fields, a model projection and an extra test differ throughout;
  already a macro), `RWMutex.Lock`/`RLock` (they differ in an expression, the wait prefix
  `rwm.pfx` vs `rwm.pfx + "write"`), `Queue`/`PriorityQueue.Dequeue` (different callees and prefix
  throughout), raft's `MsgApp_lt`/`MsgHeartbeat_lt` and the `Resp_eq` pair (the step's type tests
  need the concrete message type; the files mirror the Rocq port's one-file-per-case structure).
- *Rejected:* one spec for the family (a spec statement per Go function stays, CLAUDE.md); a
  tactic macro (the user's choice: a named lemma with a docstring reads as the reasoning, a macro
  must be expanded by eye); deriving the generic body from the translation by a meta-program
  (more machinery than the copied term, which the build checks anyway).

## `CheckQuorum` on: one model rule for a leader's step-down at its term

**2026-10-17 · adopted** (branch `raft-checkquorum`, the user's decision "(a)": etcd's own
`raftConfig`)

`MsgCheckQuorum` makes a leader that heard from no quorum within the election timeout a follower
at its own term (`becomeFollower(r.Term, None)`). The model had no such step for a leader
(`Step.abandon` is a non-leader's).

**Decision:** one rule `stepDown` (a leader becomes `pbecomeFollower s s.term 0`) in `Step` and
`StepC`, and `StepR.stepDown` without its premise `id ∉ cfg.voters`, so that the reconfiguration
step-down (`switchToConfig` with `StepDownOnRemoval`) and the quorum check are the same rule. Its
ghost update is the one stage B5 proved for the removal step-down (`ownRaftGhost_step_stepDown`):
the leader voted for itself at its term, so it neither votes nor campaigns there again, and the
known-leaders table keeps its entry. `QuorumActive`'s answer is not related to the abstract state
(`RecentActive` is in no `Progress` record), so `stepLeader`'s spec allows either outcome; that is
all safety needs. `r.checkQuorum` is recorded (`NState.cq`), like `r.preVote` and
`r.stepDownOnRemoval`, rather than pinned.

- *Rejected:* dropping `Step.abandon`'s `role ≠ leader` premise instead of a new rule: the static
  ghost lemma for `abandon` uses it (`leaderWit`, `ownLogGhost_mono` for a non-leader), and the
  removal step-down already had its own rule in `StepR`.
- `ReadOnlyLeaseBased` (which `CheckQuorum` would make a legal configuration) stays out of scope:
  `ReadOnlyOption = ReadOnlySafe` remains a premise; etcd uses `ReadOnlySafe`.

**Pre-vote at the `RawNode` layer (adopted 2026-10-17, the user's approval of the ceiling design;
what it became is below):** `readyWithoutAccept`'s
`∀ m ∈ ms, m.Term ≤ rs.term` is false with pre-vote on (a `MsgPreVote` is at `term + 1`, a granted
`MsgPreVoteResp` at the requester's term). The proposal: a ghost term ceiling `tc` in `NGhost`,
raised by `RawNode` before a step, bounding every queued message (`OutTermOk`), exposed as
`RNState.tc`; `Ready`'s bound becomes `m.Term ≤ max rs.term rs.tc`, and `node.go`'s budget holds
`termLB` of the ceiling. A pre-candidate's win on a stale grant of its own term raises the term to
`term + 1` past the message's, so `ownRawNode` must keep `preCandidate → term + 1 ≤ tc`, which
needs a new `raft.Step` postcondition (`ownRaftPhys` cannot keep it: `reset` stores the term while
the role is still `preCandidate`). See notes/STATUS.md, "Raft: CheckQuorum and PreVote on".

As built (stage P): `Ready`'s bound is `m.Term ≤ rs.tc` (the ceiling is kept at or above the term,
`RNPv`, so this is the same as `max`); the ceiling is raised by the *client* (`ownRawNode_raise_tc`,
a ghost step: `node.go` raises it with the budget before a tick, to `tc + 1`, and before a network
step, to the bound `budget_step` gives) rather than inside `RawNode`'s methods, so the methods'
specs take it as a premise (`RawNode.Step`: `m.Term ≤ rs.tc`, a `MsgTimeoutNow`'s campaign within
it; `Tick`/`Campaign`: `rs.term + 1 ≤ rs.tc`). The pre-vote clauses of `OutTermOk`/`SendOk` (a
queued message's term at most the node's when pre-vote is off) went: the ceiling bounds both modes.
`raft.Step`'s new postcondition is `TermStep`'s `PreCandStep` (with `TickStep`'s, `hup`'s and
`LocalFrame`'s role facts). A received `MsgPreVote` at a node of term `0` would be rejected at term
`0`, which `send` refuses; `RawNode.Step` takes one only in a cluster started from a bootstrap log
(`γ.reBoot ≠ []`, whose nodes are past term `0`: `ownLogGhost_boot`), which `node.go`'s `netP`
carries. *Rejected:* proving "a node at term `0` has the empty log" for clusters without a bootstrap
log (`RestartNode` at the initial state): no ghost fact says the log's entries are of terms `≥ 1`;
the restriction costs nothing for etcd's server (`StartNode`) and the register example (no pre-vote).

## What a closed adequacy theorem may take as a hypothesis (D19)

**2026-10-18 · proposed (branch `raft-retarget`, open-work item 9); D19a, D19b, D19d, D19e, D19f
adopted by the user (D19d and D19e by the local route, below)**

The adequacy example (`examples/putget`, `notes/STATUS.md`, "Item 9: the adequacy example") was to
keep each undischarged premise of the server's construction as a named hypothesis of the closed
theorem. A hypothesis of a closed theorem quantifies over every instance of the ghost state
(`∀ [HeapGS …]`) and every ghost name; if a proof can refute it inside the logic, it is false and
the theorem says nothing.

- **D19a: the rule.** A named hypothesis is either a pure fact (on the execution, `n + 2 ≤ 2 ^ 31`;
  a method set; `transportEffectsOk`), or a Hoare triple of a function the program calls whose
  postcondition holds only fresh resources at fresh names (`bootstrapContract`, the names-only
  contracts `rnLoggerZapOk`, `rnNewStorageOk`, ...). Never an Iris statement about ghost state the
  proof itself allocates (`srvLifeBound`, `idLifeBound`, `storeSmall`, `rnLogFits`, `srvLogsSmall`,
  `clusterWorkloadOk`), nor an abstract exclusive resource from nothing (`⊢ |==> nameFree n`,
  `⊢ |==> netAddrFree a`), nor a contract that mints a bounded supply (`rnTickerOk`'s
  `tickCred`). Each of those is refutable (allocate or advance the same ghost state past the
  bound; use the minted resource twice), as D17a's credits were. **Adopted 2026-10-18** (the user).
- **D19b: the lifetime bounds from time receipts** (proposed; **adopted 2026-10-18** by the user,
  with the stage plan below). Perennial's receipts
  (`GooseLang/Receipts.lean`): every Go instruction step can raise a persistent `⧖ m`
  (`wp_GoInstruction_preceipt`), and `⧖ N ⊢ False` for the adequacy theorem's step bound `N`. Each
  counter behind a bound (ids issued by the generator, entries raft commits, ticks credited, changes
  sealed by the store, the watch logs) keeps `⧖ k` of its value in its invariant, raised at the step
  that increments it; the bound then follows from `N ≤ 2 ^ 40` (the tightest, the backend's
  write-back budget), a hypothesis on the length of the executions the theorem covers. Costs: the
  invariants of `idutil`, raft's budget and commit (`tickCred`'s minting moves into the ticker's
  receive), the apply thread, mvcc's sealed logs and the watch store take receipts at their
  increments; the premises go from `NewServer.spec`, `start`, `New`.
  *Adopted (2026-10-18): the stage plan.* Each bound becomes a count backed by as many receipts
  (`⧗ k`, exclusive) in an invariant, taken at a non-blocking Go step at the increment
  (`wp_go_step_receipt'` with `wp_bind`, or `sync.atomic.wp_AddUint64_receipt`), and its premise
  the pure fact `receiptBound GF ≤ 2 ^ k`, which the closed theorem discharges by its choice of
  `N` in `goose_adequacy` (D19a's rule). Stage 1 (done): `idLifeBound` (the generator's invariant
  holds `⧗ k` for the `k` ids issued; `Next` takes one from `AddUint64`'s resolution step;
  `idCred γi n := ⌜receiptBound GF ≤ 2 ^ 48⌝`). Stage 2 (done): `srvLifeBound` (a receipt per
  applied entry, from the apply loop's iteration, buys a token of a receipt-backed budget,
  `srvWTPool`: the count is of tokens taken, not of committed entries, so no statement about
  raft's log is needed; `run` no longer hands tokens per batch). Stage 3 (done): `storeSmall`
  (mvcc's index writer holds a receipt per change, `treeIndex.Put`/`Tombstone` take one; sealed
  and certified logs carry `logCh log < receiptBound GF`), the watch store's `srvLogsSmall`
  (derived from it already); `rnLogFits` is raft's, with the raft stage. Stage 4 (done): raft's
  tick/term budget (`budgetInv` holds receipts for the term bound, `tickCred bud n := ⧗ n` taken
  by a tick's caller from its own step, the ticker's payload `True`: `rnTickerOk` mints nothing).
  Left: `rnLogFits` (a receipt per entry raft appends: a raft model change). mvcc compaction's
  `2 ^ 62` premise (`CompactSmall`) done 2026-10-18 with no new receipt: the certificate the
  compaction's caller already passes (`idxCert`) carries stage 3's `logCh log < receiptBound GF`,
  and `isStore` the store's `receiptBound GF ≤ 2 ^ 48`, so the compaction job derives it
  (`CompactSmall_of_cert`); `store.Compact`, `updateCompactRev`, `compactLockfree` and
  `compactJobPre` lost it (no server caller of `store.Compact` took it: the compactor is off).
  *`rnLogFits` (stage 5, 2026-10-18): stopped for a decision.* What it bounds: a `Ready`'s
  unstable entries `es` (`e0.Index + |es| ≤ 2 ^ 61`, `MemoryStorage.Append`'s premise) and its
  committed log (`|d ++ ce| + 1 < 2 ^ 64`); both are positions in a node's log, which grows by its
  own creation (a leader's `appendEntry`: `Step.propose`, `Step.win`) and by entries other nodes
  created (`appAccept`, `snapRestore`, whose entries and base carry `isEntry`). So the bound has to
  be a fact about every *created* entry, recorded where it is created, and checkable by every
  node: the protocol layer's `isEntryR` (leader branch). The node layer alone cannot do it (a
  follower's growth comes from messages; a count kept per node at `node.run` pays one receipt per
  event, not per entry), nor can the server (a duplicated `MsgProp` makes raft append the same
  proposal twice, so deposits do not bound entries). Proposed design (P):
  (1) `isEntryR`'s leader branch gains `⧖ ((uint.Z e.Index').toNat - γ.reBoot.length)` (persistent);
  then every log's last index `L` (last entry's record, or the base's `isSnapMeta`, or `0`) has
  `⧖ (L - |reBoot|)`, and so do a `Ready`'s `es` and committed log;
  (2) `appendEntry.spec` takes `⧖ m` and returns `⧖ (m + |ents|)` (its clone loop takes one step
  receipt per entry, `wp_go_step_preceipt` at `proto.Clone`'s resolution); `raft.Step`'s branches
  start from the `⧖ (L - |reBoot|)` of their ghost state;
  (3) the creating rules get the receipt: the refinement is a pure relation (`StepC`, `StepR`,
  `StepCD`) checked once per `raft.Step` by a generic ghost update (`ownRaftGhost_stepC_in`,
  `ghost_step_recv`/`ghost_step_md`, `RefinementR`, `RefinementDyn`), and a derivation may create
  entries and then truncate below them (`propose; higherTerm; appAccept`), so no endpoint of the
  derivation bounds them. Options: (3a) a bound parameter `B` of the relations, with
  `plogLastIndexZ + |ents| ≤ B + |reBoot|` a premise of `propose`/`win` (and the dynamic ones), the
  generic update taking `⧖ B` (persistent, so both halves of `trans` share it); (3b) a monotone
  pure field of `PState`/`NState` (the highest index created, raised by `pappend` and `logAppend`)
  with `⧖ (hw - |reBoot|)` in `ownRaftGhost`, the generic update taking `⧖ (s'.hw - |reBoot|)`;
  (3a) changes ~200 constructor uses and ~150 statements mechanically, (3b) the `toPState`
  equations of every log-changing Go proof.
  (4) the protocol layer (`[AllG GF]` only) needs `[ReceiptGS GF]` throughout (`Protocol/*`, a
  section variable), a departure from the Rocq mirror;
  (5) `readyData` (raft's `InvNode.lean`) gains a persistent `∃ n, ⧖ n ∗ ⌜es`'s and the committed
  log's last index `≤ n + |reBoot|⌝` (from `ownRawNodeReady_handout`, which holds the ghost
  state, and the stale `Ready`'s case), and the server's premise becomes the pure
  `receiptBound GF + |reBoot| ≤ 2 ^ 61` (`|reBoot|` is the number of initial peers; the server has
  no bound on it yet: a pure premise on `NewServer`'s peers).
  Cost: a raft-model change across `Protocol/{Ghost,Refinement,RefinementDyn,StepC,StepR,Facts,
  LeaderCompleteness}`, the Go proofs of `appendEntry`, `becomeLeader`, `stepLeader`'s `MsgProp`,
  `raft.Step`'s branches (`MsgProp`, `MsgVoteResp`, `MsgHup`), `StepGhostMode`, the node layer
  (`readyData`, `freshOk`/`staleOk`) and the register example; no trust-base change expected. The
  user decides whether to do it, and (3a) or (3b).
  *Done (2026-10-18, option (3a) adopted by the user):* as (1)-(5), with two refinements: the
  receipt `raft.Step` starts from is the node's last index's (`lastRec`, persistent, read off the
  ghost state without consuming it), and only the two creating branches (`MsgProp` through
  `stepLeader`/`appendEntry`, `MsgVoteResp` raising once itself) carry a raised receipt out;
  every other branch is stated at any `B` and closed at `B` = the last index. `becomeLeader` passes
  `⧖ 0` to `appendEntry` and drops the result. `readyIdx` is persistent (no update: the server
  takes the receipt itself, `lastRec_receipt`); it is taken at the hand-out, so the stale `Ready`
  needs no case of its own. The server's premise is `|reBoot| ≤ 2 ^ 60`.
- **D19c: the workload clause** (`clusterWorkloadOk`, D13c): unit N3 for one server -- every
  committed entry is the bootstrap log's, a leader's empty entry, or a proposal of this server
  (the request path, and the names-only monitors `publishV3`/`monitorClusterVersions`, whose
  contracts then say what they propose) -- proved as an invariant on raft's committed log.
  **2026-10-18: adopted by the user, attempted, stopped** (`notes/STATUS.md`, "D19c: unit N3
  stopped"). The clause is not provable from the ghost allocations, and not as stated:
  (1) every committed normal entry after the boot log is fired by a deposit of `kv_prop_au`
  (`reqPropOk`) or `kv_noop_au` (`kvInv` holds the server's half of the log), so `entriesOk`
  must come from the proposals, and `reqPropOk` carries none of `rqOk`: `EtcdServer.Txn.spec`
  admits `Txn{Then: [DeleteRange [a, c), Put b IgnoreValue]}` (`txnPermit`: plain, no `[0]` range
  end), whose `TxnPre` fails at every state where `b` exists (`IgnOk`), and which panics the Go
  apply loop (only v3rpc's `checkIntervals` keeps it out; `issues/etcd-txn-delete-then-ignore-put.md`);
  the length/count clauses (`putOk`, `delOk`, `TxnPre`'s `< 2 ^ 56`) need the committed log's
  length bound inside `kvInv`'s updates (D19b's receipts). (2) `batchWaitOk` of the boot log's
  conf changes (id `0`, raft's `Bootstrap`; the log is the server's `L`, start index `0`) needs
  id `0` never claimed, which `idGen` allows when the prefix is `0`
  (`issues/etcd-request-id-zero-bootstrap-confchange.md`). (3) `publishV3`/`monitorClusterVersions`
  are names-only with `True` posts: their real proposals are outside the model. Options for the
  user: (a) a per-request premise "`rqOk` at every state and `dispatchOk`" in `reqPropOk` (new
  premises of `EtcdServer.Put`/`DeleteRange`/`Txn`, discharged at v3rpc from `checkIntervals` and
  `txnNoZeroEnd`) with `idClaim` and the bound from receipts, the facts kept in `kvInv` (which then
  takes `ρ.ids`, `E`); plus a pure premise `uint16(memberID) ≠ 0` from `bootstrapContract`;
  (b) keep the clause a premise of `NewServer` and state the adequacy theorem for the workload
  that satisfies it, as a pure property of the requests (out of D19a's rule as now written).
  **2026-10-18: option (a) adopted by the user and carried out** (`notes/STATUS.md`, "D19c:
  option (a), the workload clause proved but its size bound"):
  - The apply premise split (`WorkloadDefs.lean`): `rqSmall log rq`, the size clauses (room for a
    revision, a delete's range and a transaction's changes below `2 ^ 56`, the sorts' small logs
    and selections, `txn.txnSmall`/`txn.OpsSort`), and `rqShape rq` (`dispatchOk` in any auth
    mode, `rqOk` at every log where the size clauses hold; for a transaction `txn.txnShape`: its
    `IgnoreValue` puts find their keys unless missing at the start, its gets at revision `0` with
    valid sort targets and no limit-cut sort, `txn.OpsIG`). `rqOk_of`-style lemmas
    (`rqShape_of_plain`, `rqShape_of_txn`, `txn.TxnPre_of`), and a transaction's shape from its
    run's put keys none of which it deletes (`txn.opsIG_of`).
  - `reqPropOk` carries `rqShape` (both cases; the non-write case also no `[0]` range end);
    `txnPermit` carries `txn.txnShape`; put and delete permits give their shapes outright.
  - v3rpc discharges a writing transaction's shape (`CheckShape.lean`, `txnShape_of_check`) from
    `checkRequestOp` (sort targets), `checkIntervals` (`check_gives_nodup`), `txnNoZeroEnd` (no
    from-key delete) and the server permit's plainness, with two client premises added to
    `kvDepPre`: `ReqOp.siblingSafeL` of both branches (`check_gives_nodup`'s; stronger than
    `IgnoreValue` needs, which meets earlier deletes only) and `txn.OpsNoCut` (no get at any
    depth sorting cut by a limit). The client's `etcdTxnSpec` gives both for its transactions
    (`TxnModel.plain`: no nested transactions; `txnModelIn` now of every transaction, not only a
    read-only one).
  - `kvInv` keeps `kvWork γk L` of the committed log (`logShape L`: every entry's shape, a conf
    change's id `0`; every request's id claimed, `entryClaim`); `KVNames` has the ids' names
    (`ids`), `ReqNames.ids` is `ρ.rd.kv.ids`. `kv_prop_au` takes the proposal's `idClaim`;
    `kv_noop_au` and `kvInv_alloc_boot` keep `kvWork` (raft's own entries claim nothing).
  - The id `0`: `idGen` reserves it in the issued map for a prefix not `0` (`idReserved`,
    `idNoZero`, `idClaim_noZero`); `NewGenerator.spec` gives `⌜memberID ≠ 0⌝ -∗ idNoZero`;
    `NewServer.spec` takes the pure premise `uint.Z id % 2 ^ 16 ≠ 0`; `srvCCPolicy` (and
    `srvNoopEntry`) admit conf changes of id `0` only (the bootstrap's; a one-member cluster with
    no membership change of its own).
  - `publishV3`'s and `monitorClusterVersions`' contracts take `srvMonitorPermit`
    (`InvMonitors.lean`): the request path and `reqPropOk` for a member's attributes or a valid
    cluster version only, what their Go code proposes.
  - `clusterWorkloadOk` is restated at an update (`□ ∀ L, srvRLogLb L ={⊤}=∗ …`) and proved
    (`clusterWorkloadOk_of`, `BuildGap.lean`) from `kvInv`, `idNoZero` and the residual
    `clusterLogBound ρ c₀ x₀ := □ ∀ L, srvRLogLb L -∗ ⌜entriesSmall c₀ L x₀⌝` (`InvBuild.lean`),
    which replaces it among `NewServer.spec`'s premises. The residual is for D19b's receipts
    (stage 3): a bound on the store's changes, keys and revisions at every reachable state.
  **2026-10-18: the residual's move adopted by the user and carried out** (`notes/STATUS.md`,
  "D19c's move: the size clauses at execution"). `clusterLogBound` was not derivable from D19b's
  counters: they bound work already executed (sealed logs), while it was asked of every log raft
  will commit and of every run of `batchStep`, and a transaction's change count or a delete's
  range is known only as it runs. So the size clauses moved from the raft contract's `E.C` to the
  apply thread at execution, and the txn package's change-count premises to receipts:
  - *Where each bound comes from.* The store's write transaction holds a receipt per change
    (D19b stage 3's `idxWriter`), and `isStore` holds `receiptBound GF ≤ 2 ^ 48` (`NewStore`'s
    pure premise, as `NewServer.spec`'s): so its pending changes stay below the real backend's
    `2 ^ 56` puts per session (`storeTxnWriteIs_small`), at every change, without a premise on the
    transaction or the delete; and the state a transaction's get reads is small by the same count
    (`txnViewIs_small`, the sort's premise). The apply thread's log is the sole writer's, which now
    keeps a revision per change past `NewStore`'s two (`soleLog`; every commit is of a non-empty
    pending revision) and is certified, so it has fewer than `2 ^ 48` changes and revisions
    (`soleWriter_small`, `srvApplyKV_small`), and the remaining size clauses (`rqSmall`: room for a
    revision, `LogSmall`) hold at it (`rqSmall_of_small`).
  - *What the contract asks.* `srvC` (raft's `E.C`) and the apply specs take the entries' shapes
    (`logShape`) instead of `entriesOk` over every run; the apply loop derives each entry's
    `entryOk` at the log it meets (`entryOk_of_shape`). The txn premises lose their size parts:
    `TxnPre` (its third conjunct now `LogSmall log`, a read-only transaction's sort premise),
    `GetOk` (no `sortSmall`), `apply.delOk` (room for a revision), and every `putMax` premise of the
    txn and mvcc write specs.
  - *Why the receipts' bound lives in `isStore` and `soleWriter`* (pure facts at allocation): the
    leaf write specs (`storeTxnWrite.put`/`delete`) see only the store's resources, and the apply
    thread only its KV resources (`kvOwn`, the sole writer); a premise threaded through every spec
    between them would have changed many more statements. The constant stays `2 ^ 48`
    (`NewServer.spec`'s, D19b), below the `2 ^ 56` the backend needs and the `2 ^ 62` of the sort.
- **D19d: program-start resources once** (`nameFree`, `netAddrFree`). Options: (1) Perennial's
  `wp_package_init` gives the body a once-per-package token (D16's proposed general fix), from which
  a package takes what was allocated for it at program start: covers `nameFree`, not `netAddrFree`;
  (2) an FFI whose initial world holds the free addresses and an empty default registry, its
  `ffiGlobalStart` the rights (given once by `goose_init`), `nameFree`/`netAddrFree` defined as its
  ghost state instead of axioms: a Perennial FFI change (or a local FFI over the disk FFI);
  (3) the program-start rights as one exclusive token the theorem's proof gets from the initial
  package state, if Perennial's `ownGoState ∅` were split into fragments.
  **Adopted 2026-10-18 (the user): the local route, a trust-boundary adequacy axiom.** What
  Perennial offers was checked (`GooseLang/Adequacy.lean`): `goose_adequacy`'s `Hwp` receives the
  FFI's `ffiGlobalStart`/`ffiLocalStart` (the disk FFI's: `True` and the disk's points-tos; the
  Grove FFI's: the network's channels and the node's files: neither has a registry or free
  addresses, and the etcd proofs are generic in the FFI), `ownGoState σ.packageState` (needed by
  the initializers) and `threadTok` (needed by the main thread). None is a once-only resource the
  program does not otherwise need, and no axiom of the form `ownGoState ∅ ==∗ ownGoState ∅ ∗
  rights` is sound (usable twice). So the rights come from the adequacy statement itself:
  `EtcdGrove.goose_adequacy_start` (`Proof/runtime/Start.lean`) is `goose_adequacy` whose WP proof
  also receives `startRights Ns As` (`nameFree n` for each name of `Ns`, `netAddrFree a` for each
  address of `As`, both lists `Nodup`), for a program `e` with `prometheus.namesUnclaimed e Ns`
  (no code of `e` the proofs do not verify, and no default collector, registers a name of `Ns`)
  and `addrsUnclaimed e As` (no other process and no unverified code of `e` binds an address of
  `As`): axiomatized propositions, pure facts of the program and its environment (D19a's first
  kind), hypotheses of the closed theorem. *Why true of Go:* every registration of a name of `Ns`
  and every listen on an address of `As` is then made by verified code whose spec consumes the
  right, and each right exists once in the proof, so no name is registered twice and no address
  bound twice, which is all `MustRegister.spec` and `Listen.spec` assume. *Why once only:* nothing
  else produces `nameFree` or `netAddrFree` (axiomatized predicates; no axiom or definition gives
  one), and the axiom's conclusion is about executions (`goose_adequacy`'s), not an entailment: it
  cannot be applied inside a proof to obtain rights, only to the one WP proof of one run.
  *Satisfiable:* with `nameFree`/`netAddrFree` read as `True` (no axiom says either is exclusive)
  and the names-only `MustRegister`/`Listen` as diverging functions, premise and conclusion are
  `goose_adequacy`'s. *The adequacy example's facts* (checked 2026-10-18): over the 499 packages
  `examples/putget` builds (`go list -deps`), the read package's two metric names occur only in
  `server/etcdserver/read/metrics.go`, the address `127.0.0.1:23790` only in `putget.go` (and a
  test file of the standard library's `math/rand/v2`, not built); the program's run (`go test`)
  registers each name once (its initializers do not panic). So `Ns` = the read package's two
  names (`readRegPerm`), `As = ["127.0.0.1:23790"]`.
  *The Perennial proposal (independent of this repository):* option (2), an FFI (or an extension
  point of `FfiInterpAdequacy`) whose global world has the bound addresses and the registered
  metric names, with `Listen`/`MustRegister` as its operations (failing or panicking on a taken
  address or name) and `ffiGlobalStart` the ownership of the free ones; `nameFree`/`netAddrFree`
  become its ghost state and `goose_adequacy_start` follows from `goose_adequacy`. Option (1) alone
  does not cover addresses (no package owns one).
- **D19e: the read package's rights needed twice** (D16's cost met): a program that imports both
  `etcdserver` and `v3rpc` runs `v3rpc.initialize'` after `etcdserver.initialize'`; both theorems
  take `readRegPerm`. Options: (1) as D19d (1); (2) every `wp_initialize'` also returns its package
  map's entries (`gen-init.py`), so a local variant of `wp_package_init` (from Perennial's
  `wp_PackageInitCheck`) proves an initialized package's `package.init` without the body's proof,
  and the importers after the first take `isPkgInit read` instead of the rights.
  **Adopted 2026-10-18 (the user): option (2), locally.** (In putget's order `v3rpc` runs first,
  and runs `etcdserver` and `read`; `putget`'s own call of `etcdserver.initialize'` comes next.)
  Perennial exposes the map (`ownInitializing_unseal`: `∃ σ, ownGoState σ ∗ □ ...`, and the
  instructions' WPs `wp_PackageInitCheck`/`Start`/`Finish`), but every `wp_initialize'` returns an
  arbitrary map, so after any call a proof no longer knows `read` is initialized. Hence two forms
  (`Proof/runtime/PkgInit.lean`): `ownInitLb g σ0` (`ownInitializing g` whose map keeps `σ0`'s
  initialized packages initialized, `initLe`) and `ownInitRes g q R` (`ownInitializing g` holding
  `R` unless `q` is initialized), with local variants of `wp_package_init` proved from Perennial's
  instructions: `wp_package_init_lb` (keeps `ownInitLb g σ0`), `wp_package_init_res` (passes
  `R` on), `wp_package_init_res_self` (`q`'s own: the body gets `ownInitializing g ∗ R`), and
  `initRes_carry` (an import's `_lb` form passes `R` on). `etc/gen-init.py` now proves every
  generated package's `wp_initialize'_lb` (for all `σ0`), or, for a package whose closure contains
  `read` (`read`, `etcdserver`, `v3rpc`, `putget`), `wp_initialize'_res`; `wp_initialize'` (both
  of D16's shapes, unchanged statements) follows (`wp_init_of_lb`, `wp_init_of_res`). `PRE_RES`'s
  "one import leads there" assertion is gone: `R` is spent by the first initializer that runs
  `read` and every later one finds it initialized. `putget` is in the table (`ROOTS`; its fact
  `True`, `examples/putget/Base.lean`); `putget.wp_initialize'` takes `ownInitializing g ∗
  readRegPerm`. *The trust boundary:* Perennial's, raft's and the B-tree's initializers (18,
  the generated `ExternalInit` list, `Proof/runtime/PkgInitExt.lean`) have only Perennial's form;
  their `_lb` forms come from it by the axiom `EtcdGrove.initLb_of_spec`: a listed initializer
  meeting Perennial's spec also keeps the initialized packages initialized. True of Go and of the
  model: the map changes only by `PackageInitStart`/`Finish`, which Goose emits only in
  `package.init` (`Start q` after `PackageInitCheck q` found `q` not initialized), and
  initialization is sequential; stated of the listed initializers only (a raw `PackageInitStart`
  could reset an entry), it holds in every model where its premise does. *The Perennial proposal
  (independent):* Perennial's `wp_initialize'` theorems (and `wp_package_init`) in the `_lb` form,
  or a persistent witness `pkgInited p` (a fragment of a monotone view of the package map, given by
  `wp_package_init`) with a `wp_package_init` variant that skips the body given it; either makes
  `initLb_of_spec` a theorem. D16's once-per-package token (D19d (1)) is the alternative for
  resources a package's body needs.
- **D19f: `clientv3.New` without the watch facts** for a client that never watches: either compose
  `etcd_watch_served_chain` at the server's start (item 4's "not done"), or weaken `New`'s
  postcondition on the `Watcher` field so that its premise `watchAddrFacts` goes (a change to
  `New`'s spec). **Adopted 2026-10-18 (the user), the second:** constructing the watcher only
  allocates it (`NewWatchFromWatchClient`: the struct, an empty streams map; no goroutine, no call
  on the connection), and its lock's invariant (`watcherMu`, an empty map) needs no server fact, so
  the facts are needed only by `Watch`. `isClientWatcherCore V w` (`InvWatcherCore.lean`) is
  `isClientWatcher` with the stub on the connection (`watchStubAt`) in place of `watchSrvFacts`;
  `isClientWatcher_of_core` adds `watchConnFacts V`. `NewWatchFromWatchClient.spec` takes the stub
  instead of `watchSrvFacts`, `NewWatcher.spec` drops `watchConnFacts`; both give the core.
  `isNewClient`'s watcher is the core plus `grpcConn conn ep ics []`; `newClient.spec`/`New.spec`
  drop `watchAddrFacts V` and `V.addr = ep` (the caller still picks the watcher's environment `V`,
  any one); `isNewClient_watcher` (with `V.addr = ep`) gives the old form from
  `watchAddrFacts V`, to supply before the first `Watch`. `client_newWatcher_rangeWatcher`'s
  statement unchanged (its proof adds the facts). The watcher's environment is still fixed at
  `New` (the lock's invariant is stated over it); a client whose server is chosen later would need
  the invariant over an existential environment, not needed here.
- **D19g: `Main`'s local pieces and two clashes with `NewServer.spec`** (item 9, point 7;
  2026-10-18; proposed; (a) and (b) adopted by the user and carried out the same day, below).
  - *The feature gate's contract was false of Go* (a spec bug of this repository).
    `isFeatureGate` said `Enabled(f)` returns some boolean for every `f`. `featureGate.Enabled`
    panics on a feature it has not registered (its own comment says so; the `FeatureGate`
    interface's does not: `issues/etcd-featuregate-enabled-panic-undocumented.md`). As a premise
    of `NewServer.spec` it could not be met, and the trust-boundary spec of
    `NewDefaultServerFeatureGate` would have been a false axiom. Now `isFeatureGate`
    (`Proof/go_etcd_io/etcd/server/v3/features/Defs.lean`, moved there from `InvProposer.lean`)
    covers only `serverFeatures`, the keys of `DefaultEtcdServerFeatureGates`.
    `EtcdServer.FeatureEnabled.spec` takes `⌜f ∈ serverFeatures⌝`, and the seven call sites
    discharge it by `simp`.
  - *(a) `rLog` against `noopAu`: `NewServer.spec`'s ghost premises cannot all be met.* Raft's
    allocation for a new cluster (`ownRaftGhost_alloc_boot`) runs the client's continuation
    (`allocClientBoot`). The continuation must return raft's standing update `noopAu γ`, an
    atomic update over `rLog γ`, so `rLog γ` must be in an invariant. For the server that
    invariant is the KV invariant `kvInv`. But `NewServer.spec` takes `rLog γ bootLog` owned
    (with `srvReadNamesFresh`) and allocates `kvInv` itself (`NewServer.lean`,
    `kvInv_alloc_boot`). No caller can give `noopAu` to raft and also hand `rLog` to
    `NewServer`. The achievable allocation (`NewServerAlloc.lean`, `srvRaftBoot_alloc`)
    allocates the read names and `kvInv` inside the continuation and derives `noopAu` from it
    (`kv_noop_au`, then `srvNoopAu_to_noopAu_of`, which needs only `srvRaftLogInv`'s pure facts,
    since raft's commit invariant does not exist yet). To support it, raft's `allocClientGen`
    and `allocClientBoot` now also tell the continuation `γ.reCCOk = ccOk`. The noop update
    needs the conf-change policy (`srvCCPolicy`) inside the continuation.
    **The spec change to make:** `NewServer.spec` takes `"#Hkvinv" ∷ kvInv ρ.rd.raft ρ.rd.kv`
    and `srvReadNamesFreshNK ρ.rd` (the read names' rows without `kv.st`) in place of
    `"HrLog" ∷ rLog γ bootLog` and `"Hrd" ∷ srvReadNamesFresh ρ.rd …`. Its postcondition drops
    `etcdKV ρ.rd.kv …`, which the allocation gives `Main` (and `putGetInv_alloc_log` turns into
    the client's invariant). `NewServer.lean` drops its `kvInv_alloc_boot` step and unfolds
    `srvReadNamesFreshNK` instead of `srvReadNamesFresh`. The premises `ρ.rd.raft = ⟨γ, [], 0⟩`,
    `ρ.rd.kv.c0/ch0/log0/cok` stay; `srvBootOut` states the same equalities.
  - *(b) `v3rpc.Server`'s and `etcd_kv_started`'s premises are not in `NewServer`'s and
    `Start`'s postconditions.* `v3rpc.grpcCfgOk s C` needs, read-only, the configuration
    fields `QuotaBackendBytes`, `MaxTxnOps`, `WarningUnaryRequestDuration`, `Logger`,
    `Metrics`, `EnableDistributedTracing`, `TracerOptions` (with its slice) and
    `MaxConcurrentStreams`. It also needs `watchSrvOk s E γ wsl` (the watchable store, auth
    store, `raftStatusOk`, `watchVars`), `srvKVAddr s ↦□ wsIface wsl`, `srvIdsOk s`,
    `membership.localKept`, `srvStoppingAddr s ↦□ ch ∗ stopChan ch`, and the client premise
    `runsNoRequireLeader`. `srvBuilt` and `Start`'s postcondition give `raftKV` (from
    `isServerReq`/`isServerRead`), the logger, member id, lead, cluster, ticks, request size
    and feature gate, and nothing else of that list. `Server` also needs
    `srvCfgFieldAddr s "WatchProgressNotifyInterval" ↦ d` owned (with
    `sint.Z d ≤ 2 ^ 62`), `srvLgReader s`, `srvBemuReader s` and `srvGoRes s`. Each of the `N`
    `etcdGrpcSlot`s needs `etcdRunSlot` (a reader slot each of `leadTimeMu`, `lgMu`, the
    store's and the read loop's, plus `E.RD`), a further `leadTimeMu` slot and `E.RD`, and an
    `lgMu` slot. `Start` returns the read loop's slots (`actualMaxReaders` of them) and one
    `lgMu` slot. `NewServer`'s proof drops the rest: `leadTimeMu`'s slots
    (`guard_of_slots … with ⟨-, …⟩`), the `lgMu`, `bemu`, auth (`RD`) and store reader slots
    left after the construction (`replicate_take1 … ⟨…, -⟩`). **The spec change to make:**
    `NewServer.spec`'s postcondition gains a row `srvServeOut s E C K`. It holds `grpcCfgOk`'s
    configuration and watch facts for a `C` agreeing with `E` and `ρ` (as `srvGrpcFields`,
    persistent), the field `WatchProgressNotifyInterval ↦ cfg.WatchProgressNotifyInterval'`,
    and `K` request slots, each `srvLeadTimeReader s ∗ srvLgReader s ∗ mvcc.storeReader E.s E.γ
    ∗ E.RD`, with `K` the slots left (`actualMaxReaders` minus those the construction uses), and
    one `srvBemuReader`. `stopChan` and the `stopping` field's `↦□` come from `Start`, whose
    postcondition gains them. A lemma `grpcCfgOk_of_started` then gives `grpcCfgOk` from
    `srvServeOut`, `isServerReq` and `isServerRead` (`raftKV_server`), and
    `etcdGrpcSlots_of_started` gives the `N ≤ K` slots from `srvServeOut`'s slots and `Start`'s
    read slots. `runsNoRequireLeader` stays a premise of the closed theorem: a statement about
    the clients' metadata, of D19a's first kind.
- **D19h: the quota and the NOSPACE alarm** (audit phase B3, 2026-10-18; **option (B) adopted by
  the user, 2026-10-18; carried out for `NewBackendQuota` and `EtcdServer.Alarm`, not yet for
  `raftRequestAlarm`**, below). Three axioms on the `Put` path are false together (`notes/audit.md`): the quota's
  `Available` always answers true (`storage.NewBackendQuota`'s `isQuota`), and the two contracts
  that propose the NOSPACE alarm (`EtcdServer.Alarm`, for `quotaAlarmer.check` in v3rpc;
  `EtcdServer.raftRequestAlarm`, for `applyEntryNormal`'s goroutine on an `ErrNoSpace` entry)
  propose a request that the KV model does not admit (`plainReq` is `False` for `.alarm`), with no
  `reqPropOk`, id credit or reader slot. Go: `BackendQuota.Available` is false once
  `be.Size() + cost` reaches the quota (2 GiB by default; `storage/quota.go`); the quota applier
  then still applies the put, transaction or lease grant and only sets `ErrNoSpace` on its
  response (`apply/quota.go:36-42`); `applyEntryNormal` proposes `Alarm{ACTIVATE, NOSPACE}` once
  per such entry while no NOSPACE alarm is stored; v3rpc's `quotaAlarmer.check` proposes it and
  answers `ErrNoSpace` without proposing the request; once the alarm is applied the uber-applier's
  chain is the capped one, which rejects every put and lease grant and every transaction of
  positive `Cost` (`apply/capped.go`). Both options keep putget's theorem meaningful (`Main`
  ends without a check on any error); they differ in what the closed theorem covers and in cost.
  - *(A) Model the alarm.* `isQuota`'s `Available` answers some boolean; the quota layer's outcome
    is the inner one, or, for an applied write, the same log with `ErrNoSpace` (the client sees an
    error for a write that happened: the client specs' error case must allow it). The alarm
    proposals carry a permit (`srvAlarmPermit`, as `srvMonitorPermit`: the request path's for
    `quotaAlarmer.check`; for the apply thread's goroutine an id credit and reader slot it does
    not have today, one per `ErrNoSpace` entry). The KV model admits the NOSPACE `ACTIVATE` entry:
    the model's state becomes the log and the chain (`kvRaftOf` folds both; the alarm switches
    the chain to the capped one, the start's chain `kvExact` as now), which needs the alarm
    store's NOSPACE flag as a function of the log (`v3alarm` is names-only, an oracle today:
    `apply.alarmChain`'s `ns` is any boolean) and the capped layer deterministic (`Cost` of a
    transaction, names-only, decides it). Costs: the KV model (`KVModelDefs`, `KVModel`,
    `KVApply`, `kvInv`), the chain relation, the alarm store's model, the two permits, the client
    outcomes; several units. Gain: no premise; a closed theorem covers a run that fills the
    quota (its writes rejected after the alarm, each answered with an error).
  - *(B) A named workload premise, as `authRecordsFit`* (D19a's first kind; the audit's own
    suggestion for `NewBackendQuota`). `opaque backendUnderQuota : Prop` ("every `Available` of
    the run answers true: the backend's size plus a request's cost stays below the quota"), a
    premise of `storage.NewBackendQuota`'s axiom (which keeps `Available`'s `b = true`), so of
    `newQuotaApplierV3`/`NewUberApplier`/`NewServer.spec` and of v3rpc's `newBackendQuota` and
    the server construction above it. Then `quotaAlarmer.check`'s alarm branch is dead and
    `EtcdServer.Alarm`'s axiom leaves the link (one axiom fewer); `applyEntryNormal`'s `ErrNoSpace`
    branch is dead too (the quota layer never sets it, and the capped layer is not in the chain:
    the apply thread's chain is `kvExact`, `KVApply.lean`), once the outcome-to-error map shows a
    `kvExact` chain never answers `ErrNoSpace`, and `raftRequestAlarm` goes as well (one more).
    Costs: one unit, premises on two construction specs. Loss: a premise nothing checks, true of
    putget (one small key against 2 GiB) and false of a workload that fills the quota; the
    NOSPACE path stays outside the model, so the closed theorem says nothing of such a run.
  - *Recommendation:* (B) now, with the premise in the closed theorem's statement as
    `authRecordsFit` and `transportEffectsOk` are; (A) when a closed theorem should cover a full
    disk.
  - *Adopted: (B)* (the user, 2026-10-18); **(A) stays the later route** for a theorem covering a
    run that fills the quota. *Carried out:* `apply.backendUnderQuota` (opaque, `apply/Contracts.lean`)
    is a premise of `storage.NewBackendQuota`'s axiom (restated: true of Go given it), of
    `newQuotaApplierV3`, `newApplierV3`, `apply.NewUberApplier`, `EtcdServer.NewUberApplier` and
    `NewServer.spec` (a precondition `⌜apply.backendUnderQuota⌝`, as `authRecordsFit`), and of
    v3rpc's `newBackendQuota`, `NewQuotaKVServer`, `NewQuotaLeaseServer` and `Server`.
    `quotaAlarmer.check`'s alarm branch is dead (`Available` answers true), so
    `EtcdServer.Alarm`'s axiom is gone (its files removed; baseline one axiom fewer).
  - *`raftRequestAlarm` not yet removed* (still false; the one alarm axiom left). Its branch in
    `applyEntryNormal` is taken when `errors.Is(ar.Err, ErrNoSpace)` holds and the alarm store
    has no NOSPACE alarm. Under the premise Go never takes it (the quota never answers false, the
    capped applier is installed only with a NOSPACE alarm stored), but the model cannot show it:
    the apply package's answers do not determine the error for every kind the KV model admits
    (`dispatchAnswer` is `True` for the auth requests and `LeaseCheckpoint`, whose errors come from
    names-only stores whose contracts say only `applyErrIs`), the server's `errors.Is` spec
    (`Spec/errors/Is.lean`) answers some boolean (Perennial's has the tree facts), and the alarm
    store's `Get` and the chain's `ns` are separate oracles. Removing it is a unit of its own:
    (i) the answers' errors for every admitted kind (or the workload restricted to the kinds the
    proposers here send: put, delete, transaction, range, the monitors' member and version
    requests, whose answers are exact), (ii) Perennial's `errors.Is` spec and a lemma that none
    of those errors `Is` `ErrNoSpace`, (iii) at a `kvExact` chain no outcome is a NOSPACE one
    (`.rejected .noSpace`, `.applied _ true`); then the branch is dead.
    **The unit, stopped (2026-10-18): D19k.** (i) and (iii) hold up, and (ii)'s `errors.Is`
    spec is local, not Perennial's. But (ii)'s lemma needs the error variables told apart
    (`ErrNoSpace`'s pointer differs from the backend errors'), which no package fact gives.
  - *Carried out (2026-10-18, after clusterLogBound and rnSnapOnce landed).* (a):
    `NewServer.spec` takes `"#Hkvinv" ∷ kvInv ρ.rd.raft ρ.rd.kv` and `srvReadNamesFreshNK ρ.rd`
    (now in `InvBuild.lean`); its postcondition no longer has `etcdKV`, and `NewServer.lean`
    no longer allocates `kvInv`. So `srvRaftBoot_alloc`'s output (`srvBootOut`) meets the
    premises, and `putGetInv_alloc_log` turns its `etcdKV` into the client's invariant.
    `clusterWorkloadOk` lost its unused `c₀`, `x₀`. (b): `NewServer.spec`'s postcondition gains
    `srvServeBuilt srv E cfg 64` (`InvServe.lean`). Its persistent part `srvServeFacts` holds
    the KV field as the watchable store and `srvServeCfg`'s eight configuration fields. It also
    holds the owned `WatchProgressNotifyInterval` field, a `bemu` reader slot, and 64 reader
    slots each of `leadTimeMu`, `lgMu`, the auth store (`E.RD`) and the store (from the watch
    readers). The construction's proof used to drop these with `-`. `Start`'s postcondition
    did not need to change: `isServerRead` already holds the `stopping` field and `stopChan`,
    the logger field and the auth store's `isAuthStore`, and `isServerReq` holds the rest;
    `raftKV` comes from both through `raftKV_server`, and `srvIdsOk`/`raftStatusOk` from its
    `kvGetOk`. The lemmas are in `client/v3/ServeFromStart.lean`. `grpcCfgOk_of_started` gives
    `∃ C, grpcCfgOk s C ∗ ⌜C.A = srvKVAns s E ρ γr 0 [] .none ∧ C.E = E⌝`.
    `etcdGrpcSlots_of_started` gives `N` `etcdGrpcSlot`s from `2 N` slots each of `leadTimeMu`,
    `lgMu` and `E.RD`, `N` of the store and `N` of the read loop's (`Start`'s). `etcd_kv_started`
    and `etcd_watch_served_chain` are unchanged.
    **Premises left to `Main`:** `v3rpc.watchVars`, the package variables `watch.go` reads.
    They are not among `v3rpc`'s initialization facts (`v3rpcInit`); their natural home is
    there, as item 8 did for `metricsVars`, a `gen-init.py` change. `v3rpc.runsNoRequireLeader`
    is a statement about the clients' stream metadata, D19a's first kind.
    `membership.localKept c` is an axiomatized predicate that nothing produces (unit P3b). As a
    hypothesis `□ ∀ c, localKept c` it cannot be refuted, but it says nothing about Go, so it
    needs a decision before the closed theorem: define it from the cluster's members map and
    prove it for a single-member cluster, or keep it as the closed theorem's named
    assumption. Also the tracer options' slice (`↦*□`; `Main` passes `nil`).
- **D19i: the application's writes to raft's storage and to the backend's `meta` bucket**
  (audit phase B2, 2026-10-18; **proposed, needs a decision**). The three false axioms of B2
  (`notes/audit.md`) cannot be restated as true triples over the current model; each needs a
  model change. Nothing was changed in Lean.
  - *`EtcdServer.snapshot` and `EtcdServer.compactRaftLog`.* Go: every `memorySnapshotCount =
    100` applied entries the apply thread calls `MemoryStorage.CreateSnapshot(appliedi,
    confState, nil)` (the storage's snapshot becomes the applied index's) and `Compact(compacti)`
    (`compacti = 1` until `snapi` passes `SnapshotCatchUpEntries`, 5000 by default, so the
    first call drops entry 1 and later ones answer `ErrCompacted` until then), both under
    `ms.Lock()`, while raft's node goroutine keeps reading the storage. Raft copes in Go:
    `raftLog.firstIndex` asks `FirstIndex()` anew, `raftLog.term` returns `ErrCompacted` below
    it, `maybeSendAppend` falls back to a snapshot. The model does not: raft's view
    `ownMemoryStorage ms γs σ` is exact (`MemView`: the contents agree with `σ` on the boundary
    and the snapshot), `isStorage`'s `FirstIndex` answers `σ.prev.index + 1` and `Term`/`Entries`
    succeed on `[σ.prev, last]`, and raft's log predicate uses that exactness (`ownRaftLog`'s
    `LogStoreOk` `σ.prev = ls.prev`, `StoredSnapOk`, `Hsksn`, `LogPersistOk`). D17d's key sets
    let the application *read* the snapshot under the lock with its token; a *write* needs all
    three parts of the snapshot's ghost value (`memSnap_update`), the owner's among them. So any
    true spec of `CreateSnapshot`/`Compact` takes `ownMemoryStorage`, which the apply thread
    cannot have. (`KV().Commit()` is covered by `applyBackend`/`srvApplyKV`; the WAL's
    `SaveSnap`/`Release` by the WAL's model, which is stateless, `isRNWal`: they would be two more
    persistent triples there.)
    - *(A) Compaction under the lock, raft's view a lower bound.* The storage's boundary and
      snapshot move under the lock, as D17d moved the snapshot, and the application (its token,
      extended) may advance them, never above a floor raft publishes (a monotone lower bound of
      what raft has handed out to apply, which etcd's `appliedi` never exceeds) and only to
      snapshots raft may send (`ksn`, the A3 obligation `SnapObl` on the conf state). The
      `Storage` contract changes: `FirstIndex` answers at least the view's, `Term`/`Entries` may
      answer `ErrCompacted` below the current boundary, and raft's log layer is re-proved for
      that (`raftLog.firstIndex`/`term`/`slice`/`snapshot` and their callers: `maybeSendAppend`,
      `matchTerm`, `findConflictByTerm`, the scans of `hasUnappliedConfChanges`, ...; some 20
      files use `firstIndex`, 18 `LogStoreOk`), with `ownRaftLog`'s clauses restated against a
      boundary that only rises. Then the server: the token `memSnapTok` threaded from `run`'s
      one `Snapshot()` (`rnSnapOnce`; the call gives it back) to the apply thread
      (`applyBuilt`), `ep.confState` known to be the applied prefix's configuration, `appliedi`
      below the floor; `snapshot`/`compactRaftLog` restated (names-only: their bodies call the
      untranslated `verifyConsistentIndexIsLatest` and the WAL). Cost: large, raft first (its
      own unit, the write side of D17d). Gain: faithful; the server's theorems cover long runs.
    - *(B) The snapshot branch dead in the runs covered.* `snapshotIfNeededAndCompactRaftLog`
      returns at once while `appliedi ≤ memorySnapshotIndex + 100` and
      `appliedi - diskSnapshotIndex ≤ SnapshotCount` and no disk snapshot is forced. The first
      bound is a bound on the committed log: D19's rule rejects it as a hypothesis (a ghost fact,
      not a statement on the initial configuration; why `clusterLogBound` went), so it must be
      proved for putget from its proposers (the bootstrap's conf change, one empty entry per
      leader term, `publishV3`, the cluster version, the client's two requests), with the number
      of terms of a single voter bounded; and `forceDiskSnapshot` stays false only while the
      cluster version never goes down (`ForceSnapshot` on a downgrade, `apply/backend.go:283`),
      which `clusterVersionMono` does not say. Cost: a counting proof specific to putget. Loss:
      the server's specs take a premise that fails on any run of more than 100 entries; the two
      axioms leave the link (dead branch).
    - *(C) Leave both false and recorded* (the status quo): not sound for a closed theorem, the
      branch is within the model's reach.
    - *Recommendation:* (A), raft's side first.
    - **2026-10-18 · (A) approved by the user as part 1; stopped before any Lean change, needs a
      decision.** (A)'s floor was "a monotone lower bound of what raft has handed out to apply
      (`applying`), which etcd's `appliedi` never exceeds". Raft needs less: the compaction
      boundary at most **`raftLog.applied`**, as `Compact`'s documentation says (`storage.go:266`).
      `hasUnappliedConfChanges` (`hup`'s check, on every election timeout, `Campaign`,
      `MsgTimeoutNow`) scans `[applied+1, committed+1)` and `Panicf`s on `ErrCompacted`
      (`raft.go:995-1021`, `mustCheckOutOfBounds`); `nextCommittedEnts` alone would allow
      `applying`. And `applied` moves only at `Advance` (the `MsgStorageApplyResp` of
      `stepsOnAdvance`), which etcd's `raftNode.start` calls *after* `notifyc`, the signal on which
      `applyAll` snapshots and compacts at `appliedi - SnapshotCatchUpEntries` (`1` early). So in
      that window etcd compacts past `applied` whenever one `Ready` carried more than
      `SnapshotCatchUpEntries` committed entries (or `applied` is 0 at the first memory
      snapshot), and a `MsgHup` then panics raft: a Go bug, reproduced on raft by a Go test
      (`issues/etcd-compact-past-raft-applied.md`). So no restatement of `compactRaftLog` that keeps
      raft's invariants is true of the Go code as it is; (A) needs a Go fix first, which is the
      user's call (as D19i's `monitorStorageVersion` (A) fixes the backend in the fork).
      - *(A1) etcd waits for `Advance`* (fork fix 1 of the issue): `raftNode.start` closes
        `raftAdvancedC` after every `Advance` (today it sends on it only with a conf change, for
        `configure`'s waiter, which a close serves as well), and `applyAll` waits for it before
        `snapshotIfNeededAndCompactRaftLog`. Raft publishes **one** bound, its
        `applied`, at `Advance` (the storage-apply step), which then also bounds the snapshot
        (`appliedi` is the batch's last index, which `Advance` makes `applied`); the witness rides
        on `raftAdvancedC` (today a unit bag with no content, `InvRaftNode.lean`) to the apply
        thread. Smallest proof; the apply loop waits for the raft loop once per snapshot.
      - *(A2) etcd bounds the compaction by the batch's predecessor* (fix 2): `compacti` at most
        the applied index before the batch, which raft had applied before handing the batch out;
        the witness rides on the batch (`rnApP`: raft's `applied` at the `Ready`). But the snapshot
        is still taken at `appliedi`, above `applied`, so raft's contract needs a second bound
        for the snapshot (`applying`, or the committed prefix): more raft-side ghost state.
      - *(B)* (above) is unchanged by this; *(C)* stays unsound.
      - *Recommendation:* (A1).
      What raft's side is under (A1) or (A2) (decided by raft's code, the same in both but for
      the snapshot's bound), for the unit that carries it out: `StorState` gains the published
      bound `fl` (raft's, raised by a new law of `isStorageWith` at `appliedTo`, never above what
      the storage holds); `ownStorage`'s `σ` stays raft's *view* (`σ.prev`, `σ.ents`, `σ.ss`),
      the storage's true boundary between `σ.prev.index` and `fl` and its true snapshot newer
      than or equal to `σ.ss`; `FirstIndex` answers in `[σ.prev.index + 1, fl + 1]`; `Term(i)`
      and `Entries(lo, _)` answer as now or `ErrCompacted` with `i < fl` / `lo ≤ fl`; `Snapshot`
      answers `σ.ss` or a newer snapshot the application made, which needs the application's
      certificate for `ksn` (`raftSnapCert`, from `SnapObl` on `ep.confState`, which the apply
      thread does not yet track). Raft's readers re-proved against it: `raftLog.firstIndex`/
      `term`/`slice`/`snapshot` and their callers (`lastTerm` and `nextCommittedEnts` read at
      or above `applied`, so they still succeed; `matchTerm`, `findConflictByTerm`,
      `maybeSendAppend`, `hasUnappliedConfChanges`'s `scan` (from `applied + 1 ≥ fl + 1`) as
      Go does). `MemView` (`InvMemstorage.lean`) becomes the lower-bound relation, the
      application's `CreateSnapshot`/`Compact` specs take `memSnapTok` (extended with a share of
      the boundary) and a lower bound of `fl`, not `ownMemoryStorage`.
    - **2026-10-18 · (A1) chosen by the user; the fork fix landed (`06aa6e6e`, re-translated,
      `e71f853db9`); raft's side carried out on `d19i1-raft` (`36e58eb679`, `2bdfb191b7`); the
      publication stopped for a decision.** Carried out: the contract above (`StorState.fl`,
      `storCut`, `storFloor`, the floor law `Hfloor`; `MemoryStorage`'s model cuts its fields at a
      boundary, `memCut`, its history carries the floor, `CreateSnapshot`/`Compact` take
      `memSnapTok` and the floor's witness `memFloorTok`), raft's readers re-proved. **What is
      new:** `node.Advance` returns at the `advancec` handoff, *before* `run`'s `rn.Advance`
      moves `applied` (`node.go`), and etcd's apply thread may compact as soon as `raftAdvancedC`
      is closed, so the floor must be raised at the handoff, past `applied` for the instant
      between it and `rn.Advance`: raft's invariant is therefore `fl ≤ applying` (`FlOk`, with
      `applying < offsetInProgress`), `fl ≤ applied` only outside that window (`RNState.flw`,
      `RNFl`), a premise of the reads from `applied + 1` (`hasUnappliedConfChanges`, so `hup`,
      `Step`'s `MsgHup`/`MsgTimeoutNow`, `tickElection`, `RawNode.Campaign`/`Tick`/`Step`), and
      `ownRawNode_raise_floor` raises the floor to `applying` with the storage's witness. (The Go
      fix is right: in that window `run` does nothing but `rn.Advance`, which reads no entry at
      or below the floor.) **Stopped:** how the witness reaches the application at the handoff.
      `advancec` is a Perennial `isHandshake` whose reply `Q` is fixed and given by the receiver
      (`run`) when it commits its receive -- in the receiver-first case before it has the
      sender's payload (`recvAu`'s `Idle` case; a blocking `select` commits to the clause there,
      so raising the floor at that commit is sound) -- and the sender (`node.Advance`) must learn
      that the witness is for *its* committed log (`|ds|`), which no fixed `Q` relates without a
      ghost resource the two exchange each round. Options: (i) a local request/reply protocol for
      `advancec` in place of `isHandshake` (its own invariant and send/receive lemmas, proved
      here, like Perennial's handshake): the receiver deposits the witness with a fraction of the
      committed log's authority (`dlm`) that the sender reads at its commit, against its lower
      bound, and the receiver takes back; or (ii) a Go change so that the application asks raft
      for the bound it compacts to (`Status()`'s reply is `run`'s), which moves the publication
      to a channel whose reply `run` computes.
    - **2026-10-18 · (i) chosen by the user; carried out.** `advancec` gets its own protocol
      (`advInv`) over Perennial's rendezvous states, not `isHandshake`: at `RcvPending` `run` leaves
      its node with the means to raise the floor (`advDep`: the node, its `runCfg` with the
      committed log's authority, its `rof` half); the sender meeting it (`RcvPending →
      SndCommit`) absorbs its append receipt, raises the floor to `applying`, checks the committed
      log's authority against its own lower bound (`dlvLb`, so the witness covers its batch), and
      leaves the raised node (`advRet`), which `run` takes when its receive completes; at
      `SndPending` the sender leaves its payload and a request (`req`, its log's length), and `run`
      meeting it raises the floor itself and answers with the witness. **The `select` point**:
      Perennial's blocking `select` tries each case with `TryReceive(true)`, whose physical offer
      (`rcvPending`) is rescinded if no sender came; the receiver's atomic update is fired only by
      a sender's `TrySend` that finds the offer (`wp_TrySend_blocking`, `RcvWait`), which then
      fires its own (`RcvPending → SndCommit`) in the same critical section. So the logical
      `RcvPending` is entered only at a rendezvous, never by an offer later withdrawn, and the
      invariant needs no return of the deposit. The server: the witness rides on `raftAdvancedC`
      (`rnAdvChan c P`), `applyAll` hands it with the application's token (`srvSnapState`) to the
      restated `snapshot`/`compactRaftLog`; `ep.confState` is `epConfState` (`nil` or read-only,
      `CreateSnapshot`'s conf state), kept by `applyConfChange`'s contract.
  - *`EtcdServer.monitorStorageVersion`.* The model admits another goroutine's write under the
    batch lock: `LockOutsideApply` hands out the client's `W ∗ Pk` (the store's `lateW`/
    `writerRes`, the hook's `batchLockInv`/`metaTM`), as for mvcc's compaction, and none of them
    tracks `meta/storageVersion` (the hook's keys are the consistent index and term; the store's,
    the key bucket and `meta`'s compaction keys). A restatement would take a `bemu` reader slot,
    the backend's `isBackend` at the server's `W`/`Pk` with a `bOpen` fraction, a `ReadTx` reader
    token (`StorageVersion()`), a reader of `clusterVersionChanged`, a logger slot, and the
    cluster's and the WAL's persistent contracts, threaded through `NewServer.spec`'s
    postcondition and `Start`'s precondition. **But the Go body breaks the backend model's
    premise:** the migration from v3.5 to v3.7 puts `meta/storageVersion` three times in one lock
    session (`""`, `"3.6.0"`, `"3.7.0"`), which `UnsafePut`'s `wbDupOk` excludes, and in Go the
    read buffer then keeps all three and a `ReadTx` reads the first: confirmed at the pin
    (`issues/etcd-backend-duplicate-put-stale-read.md`, "An etcd caller"). So an axiom saying the
    body keeps the backend's invariants (`rtRes`: the read buffer's view is the newest value)
    would be false of the model itself.
    - *(A) Fix the Go code in the fork* (as the raft read-index fix): `writeback` deduplicates a
      non-sequential bucket on both branches (upstream etcd-io/etcd#21987 or #22298, open), the
      backend re-translated and `txWriteBuffer.writeback`'s proof redone; `wbDupOk` leaves
      `UnsafePut`'s premise (a simplification: `CindexBackend.lean`'s hook-window argument goes
      too). Then the restatement above, with the threading. Cost: one fork commit, the
      write-back's proofs, one threading round through `NewServer`/`Start`.
    - *(B) Model the duplicates:* the read buffer may hold several entries of a key, the
      readers' view the first, a stale value until the next commit; the backend's write-back
      and merge proofs and the view's clients restated. Then the restatement. Cost: larger than
      (A), and the stale view leaks into every reader's spec of a non-sequential bucket.
    - *(C) Restrict the monitor* to runs where it does not migrate: not available, putget's run
      migrates (the storage version is detected as 3.5 on a new backend).
    - *Recommendation:* (A): it fixes a real (if mild) Go bug with an open upstream fix and
      simplifies the backend's premise.
    - **(A) adopted (the user, 2026-10-18); part 2 carried out up to the restatement, which
      stopped for a decision.** The fork commit is `ea78ec948` on `goose-lean`: etcd-io/etcd#21987
      cherry-picked (`writeback`: `wb.dedupe()` in place of `sort.Sort(wb)` where the read buffer
      has the bucket), with the two reproductions as regression tests. Chosen over #22298, which
      makes the same one-line code change with a comment and its own test: #21987 is smaller and
      is the fix of the filed issue #21986. The translation changes only `txWriteBuffer.writeback`
      (and the line numbers after it). The backend's model drops the duplicate-key premise:
      `wbBucketOk` is `seq = some false ∨ entsSorted es` (a `put` bucket may hold anything),
      `WBuf.WfR` and `wbDupOk` are gone (`sessWf` has `W.Wf`), `UnsafePut` has no key premise,
      `txWriteBuffer.writeback`'s spec takes `W.Wf`, and its proof uses `dedupe`'s spec on both
      branches (`canon_append_canon`, `canon_isEmpty`; no more `sort.Sort`, `Len`/`Less`/`Swap`).
      The hook's side simplifies with it: `CindexBackend.lean`'s `hookRun` loses its "only this
      run's puts" clause and `hookRun_dup`, `InvHooks.lean`'s `hookSaveStep` loses `csDupOk`.
      `hookPre`'s last clause (every write-buffer bucket empty or with an empty read-buffer
      bucket) is kept, though no hook needs it now; dropping it would also drop the
      batch lock's `bgOk` clauses that prove it, a separate cleanup.
    - *The restatement of `monitorStorageVersion` stopped: a design decision.* Over the fixed
      model the write is admitted: `LockOutsideApply` gives `batchLocked ∗ W ∗ Pk`; `meta` is a
      hook bucket (`P.HB`), so `UnsafePut` of `storageVersion` (not a hook key, `P.hk` false)
      leaves `sData` and so the readers' view unchanged, and `Unlock`'s first branch
      (`viewSame`) gives `W ∗ Pk` back unchanged. But `Unlock` also takes a write-back token
      (`wbTok γ`, one per `Unlock`), and the monitor's loop is unbounded: it migrates whenever
      `StorageVersion()` (a `ReadTx` read of `meta`, about which the readers' view promises
      nothing) differs from the cluster version. Options: *(i)* a share of the time-receipt
      write-token pool (D19b: `srvWTPool`, `N + 7` of `wbInit` taken by `bootBackend`, the rest
      dropped), split between the apply thread and the monitor, each `Unlock` paid by a receipt:
      faithful, needs the pool's split threaded through `bootBackend`, `NewServer` and `Start`;
      *(ii)* a fixed number of tokens (from `wbInit`'s leftover), with the axiom promising at most
      that many migrations: not true of the Go code in general (a downgrade migrates again, and
      the model cannot show `StorageVersion()` reads what was written), so a premise on the run;
      *(iii)* the monitor's write access as part of `Start`'s precondition with an abstract
      per-`Unlock` token supply, left to the closed theorem. Besides the tokens, the threading
      needs (most of it already made by the construction): `isBackend` of the real backend at `lateW`/the
      server's `Pk` and `bF batchTx ↦□ t` (`BuildLemmas`), a `bOpen` share (`bootBackend`'s
      leftover `∃ qo`), a `bemu` reader slot, a `ReadTx` reader token for `StorageVersion()`,
      a `clusterVersionChanged` notifier reader, a logger slot, `isRaftCluster`, and the WAL's
      persistent contract (`UnsafeMigrate` reads `s.r.storage` for a downgrade's check).
      *Recommendation:* (i). The axiom stays as it was (false: it writes without resources).
    - **(i) adopted (the user, 2026-10-18) and carried out.** No split was needed: `srvWTPool` is a
      persistent invariant counting all the receipts spent on it, so the monitor draws from the
      apply thread's pool as `apply` does (`srvWTPool_take`: a fresh receipt gives a token). The
      contract (`EtcdServer.monitorStorageVersion.spec`, still a trust-boundary axiom: names-only)
      takes `isServerReq s E ρ ∗ srvSVRes s E.γ ∗ srvWTPool E.γ`, where `srvSVRes`
      (`InvStorageVersion.lean`) is: `E.γ.kb = some d`, `s.be ↦□ d.be` (the backend for good),
      a `bemu` reader slot, `isBackend d.γB d.P (lateW d.gx) Pk d.be`, a read token with an open
      share (`mvcc.bkRTx`: `StorageVersion()`'s `ReadTx` and `LockOutsideApply`'s open share),
      and an `lgMu` reader slot. Threading: `NewServer` makes `srvSVRes` (one more `bemu`, `lgMu`
      and store-reader slot of the leftovers; the read token from the store reader's `storeRT`)
      and returns it in its post; `Start` takes it, and `start`'s post gives the pool back
      (allocated there as before). `s.be ↦□`: `bemuP s q` now holds the field at `q.half`, and
      `NewServer` persists the other half before `bemu`'s `init_RWMutex` (nobody in the model
      writes `s.be`: `applySnapshot`'s backend swap is outside it). Not in the contract, as for
      the other monitors (`notes/audit.md`'s "suspect (minor)"): the reads of `s.cluster`
      (named by `isServerReq`), `s.clusterVersionChanged`, `s.stopping` and the WAL's
      `MinimalEtcdVersion` (a downgrade's check). Rejected: a separate pool for the monitor
      (another `N` tokens from `wbInit`'s leftover and a stronger `bootstrap` budget premise, for
      nothing the shared pool lacks); `bemuP` fixing the backend as a parameter (every holder of
      `srvBemuReader` would change).
- `rnSnapOnce`: D17d's option (1), started 2026-10-18 (the user).
- **The start-rights' two axioms kept (the user, 2026-10-18):** `EtcdGrove.goose_adequacy_start`
  (D19d) and `EtcdGrove.initLb_of_spec` (D19e) stay trust-boundary axioms of this repository for
  now; their Perennial proposals (D19d's FFI of bound addresses and registered names, D19e's `_lb`
  form or `pkgInited` witness) are to be made later, independently, and would make both theorems.
- `clusterLogBound`: the size clauses moved to the apply thread at execution, the txn package's
  change-count premises replaced by receipts (the user, 2026-10-18; STATUS, D19c's last bullet).
- `rnLogFits` (D19b stage 5): option (3a), a bound parameter on raft's creating relations, adopted
  (the user, 2026-10-18), to start after `rnSnapOnce` lands.
- `NewServer.spec`'s two gaps found by item 9's point 7 (`kvInv` in place of the owned `rLog`; the
  post extended for `v3rpc.Server`'s `grpcCfgOk` and slots): adopted (the user, 2026-10-18), one
  round after `clusterLogBound` and `rnSnapOnce` land.
- D19l and D19m: every recommendation adopted (the user, 2026-10-18). Sequenced: the fork fixes
  (D19l (i) `Reset`, (ii) `AuthInfoFromTLS`) as one batch with one re-translation; D19l (iii) the
  per-vector label facts after D19k (both edit `gen-init.py`); D19l (v) and D19m's four after D19i
  part 1 lands (it touches `run` and raft); D19l (iv) in phase C.

*Rejected:* stating the bounds as hypotheses anyway (the theorem would be vacuous); restricting the
conclusion to executions where the bounds hold (they are ghost facts, not observable in the
configuration `goose_adequacy` speaks of).

## `int64(f)`: a hypothesis class, not an axiom over every semantics (2026-10-18)

**2026-10-18 · adopted (branch `raft-retarget`; the axiom audit's first false axiom,
`notes/audit.md`)**

A fact about Go's semantics that Perennial lacks cannot be an axiom quantified over the semantics'
own parameters (`[GoLocalContext]`, `[GoGlobalContext]`, `[GoSemanticsFunctions]`): those are
structures any proof can build, and a statement about the step relation, the method table or
`underlying` fails at most of them. `convert_float64_to_int64` (`int64(f)` steps) gave `False` at
Perennial's own default `GoLocalContext` (`fun _ _ _ => False`); the two `dialWithBalancer` axioms
(its trusted body as a `MethodUnfold`, grpc `resolver.Builder`'s `TypeAssumptions`) gave `False` at
a `GoSemanticsFunctions` with constant `methods` or `underlying := id`. All three were checked in
Lean (a scratch file, not committed: `False` closed, from concrete instances of every class).

Perennial's own pattern is the fix: a semantic fact is a field of a hypothesis class
(`go.Semantics`, `Float64Semantics`, a package's generated `Assumptions`), which the proofs take
as an instance argument and a closed theorem as a premise on the initial state's local context. So:

- `EtcdGrove.Float64ToInt64Semantics` (`FloatToInt.lean`): the function `float64ToInt64` (a field,
  as `FloatOps`'s `int64ToFloat64`, so a real Go's conversion can satisfy it) and the step to it.
  `NewServer.wp_proof` takes it; `wp_NewServer` too.
- `go_etcd_io.etcd.client.v3.DialWithBalancerBody` (`DialWithBalancerBody.lean`): the two facts
  the generated `Client.TypeAssumptions` and grpc `resolver`'s `Assumptions` would hold.
  `Client.dialWithBalancer.wp_proof` takes it; `wp_dialWithBalancer`, `wp_newClient` and
  `clientv3.wp_New` too.
- `etc/gen-link.py`'s `SEM_PREMISES` lists the classes: a result takes one when its proof's file
  has it as a binder or a callee's result (here or in an imported Link) takes it.

D19a's rule admits each as a premise of a closed theorem: a pure fact about Go's semantics,
satisfiable by the real one. **Proposed to Perennial, on its own** (not done here): a
`float64ToInt64` field of `FloatOps` (and the other float-to-integer conversions) with its step
in `Float64Semantics`, which would replace `Float64ToInt64Semantics`; and the translator fix
for a type of a package the file does not import, which would make `dialWithBalancer`
translated and `DialWithBalancerBody` part of the generated assumptions.

## `membership.localKept`: the cluster's lock invariant keeps the local member (2026-10-18)

`membership.localKept c` and `localKept_persistent` were axioms: an axiomatized predicate that
nothing produced, a premise of `EtcdServer.IsLearner`'s spec (whose Go body,
`IsLocalMemberLearner`, panics when `c.members` has no entry for `c.localID`), of the two
interceptors' specs and, through `grpcCfgOk`, of `grpcCfgOk_of_started` as `□ ∀ c, localKept c`.

**Chosen:** the fact lives in the cluster's lock invariant. `rcLockInv c` gains `rcLocalIn c ms`
(`c.localID ↦□ lid` and `ms !! lid ≠ none`), so every holder of `isRaftCluster c` knows that
whenever the mutex is free the map has the local member; `localKept c` is defined as
`isRaftCluster c` (`localKept_of_isRaftCluster`), kept as a name for the specs that rely on it.
Persistent by construction; no ghost state. Where it comes from: `bootstrap`'s contract
(`bootOk`'s `isRaftCluster`, a premise of `NewServer.spec`), which for a new cluster is true (the
members are the boot peers, the local one among them: `NewClusterFromURLsMap`, `SetID`). Why it
stays true: the only writer that removes a member is `applyConfChange`'s `RemoveNode`, which B3
excluded (`ccApplyOk`: an `AddNode` of a member, `AddMember` of it, which keeps the entry); the
uber-applier's cluster writes (`UpdateAttributes`, ...) keep the map's keys; `Members` (proved)
restores the invariant as it found it. The local member's removal (general etcd, after which the
server stops) is outside the model. `grpcCfgOk_of_started` loses the premise: it has
`isRaftCluster` from `Start`'s views. No cluster size restriction is needed.

*Rejected:* (1) a separate `localKept` with its own `isMutex` over a stronger invariant:
two `isMutex` facts for one mutex with no agreement law; (2) a policy-parametric
`isRaftCluster c := ∃ P, isMutex (rcLockInv c P)` with `localKept` fixing `P`: keeps
`isRaftCluster` general, but every holder of the cluster (`InvStart`, `InvApplier`, `InvBuild`,
`srvServeBuilt`) would have to carry `localKept` separately to the serving lemmas, a
`NewServer.spec` change, for no proof that needs a cluster that may lose its local member;
(3) a tautological `localKept` (true from nothing): hides where the fact is assumed.

`RaftCluster.SetVersionChangedNotifier` (audit B4, false: an unlocked write of
`c.versionChanged` with only `isRaftCluster`) does not bear on this: the invariant describes only
the members map and the local id; its fix (the field's points-to from `bootOk`, given back by the
spec) is left to B4.

## `v3rpc.watchVars` as a `v3rpc` initialization fact: stopped for a decision (D19j, 2026-10-18)

The task (2026-10-18): make `watchVars` part of `v3rpcInit`, generated by `etc/gen-init.py` as
`metricsVars` is, and drop it from `grpcCfgOk_of_started`'s premises, with no new axiom. Its
conjuncts, by where `v3rpc`'s initializer could get them:

* **From facts already there** (no new axiom): `auth`'s four errors (`authErrVar` is
  `errVarLeaf`'s shape), `traceutil.Tracer` (`traceutilInit`), `context.Canceled`'s pointer error
  (already `ctxCanceledPtr`), and the progress interval's lock (`progressReportIntervalMu`,
  allocated by the initializer, `sync.init_RWMutex` over `progressReportInterval`, whose translated
  initializer stores `10 * time.Minute`, within `intervalP`'s bounds).
* **From a stronger fact of another package of this repository** (a `gen-init.py` change there,
  no new axiom): `mvcc.ErrEmptyWatcherRange`/`ErrWatcherDuplicateID` as leaves with `Error()`
  (`mvccInit` says only that they are set; their `errors.New` gives the rest under
  `ErrorStringLeaf`, as `etcdserver`'s `srvErrVars`); the six `rpctypes` errors' `Error()`
  (`msgErrVar`: `ErrCompacted` has `errorStringSpec`; the five `ErrGRPC*` are `status.Error`
  values whose `Error()` the `rpctypes` fact does not state yet).
* **Only from a new trust-boundary statement:** (a) `streamFailures` and the four
  `watchSendLoop*` histograms are `v3rpc`'s own untranslated initializers (`opaqueInitsOk`
  says only that they return): five `<X>_init` axioms (as `clientRequests_init`), the
  histograms' with `Observe` returning; (b) `io.EOF` a leaf typed error whose `Error()` returns:
  Perennial's `io` fact has only `Discard`, so a premise class here (as `ContextReadErrs` for
  `context`) with the general fix proposed to Perennial; (c) `reportEventOk`, the contract of
  mvcc's names-only `ReportEventReceived`: a function, not a variable, so a spec axiom in mvcc's
  link, not an initialization fact.

So "no new axioms" and "no premise left" cannot both hold. **Options:** (1) all of it: five init
axioms, the `io.EOF` class, `ReportEventReceived`'s spec axiom (six axioms, one class), and
`watchVars` leaves `grpcCfgOk_of_started`; (2) split `watchVars`: the derivable part into
`v3rpcInit` (no new axiom; the `mvcc`/`rpctypes` facts strengthened), the rest (`io.EOF`, the
five metrics, `reportEventOk`) a smaller named premise of `grpcCfgOk_of_started` that `Main`
must still meet, which it can only do from (1)'s statements. **Recommended: (1)**, the
statements being of the same kind as the existing `<X>_init` axioms and true of Go (prometheus
constructors return their collectors; `io.EOF = errors.New("EOF")`). Waiting for the user.

## `raftRequestAlarm`'s dead branch needs the error variables told apart: stopped (D19k, 2026-10-18)

The task (the user, 2026-10-18): D19h's last step. Under `apply.backendUnderQuota` Go never takes
`applyEntryNormal`'s `ErrNoSpace` branch, so the model should show it dead and
`EtcdServer.raftRequestAlarm` should leave the trust base. Stopped before any Lean change. D19h's
three steps checked against the code:

* **(ii) `errors.Is`: no Perennial change needed.** Perennial's `errors.Is.spec`
  (`Perennial/Spec/errors/Is.lean`) already has the strong postcondition: `err == target` when
  either is `nil`, and, for a non-`nil` `err` and a pointer target, `true` only if some error of
  the tree is the target or an `Is` method said so. The weak spec is ours: `Spec/errors/Is.lean`
  returns `RET #b; True`, and `Proof/errors/Is.lean` drops Perennial's facts. Restating it with
  Perennial's postcondition is a local change.
* **(i) the workload: narrowing is the smaller change.** The verified proposers send only puts,
  deletes and transactions (`EtcdServer.Put`/`DeleteRange`/`Txn`) and the monitors'
  `ClusterMemberAttrSet`/`ClusterVersionSet` (`monitorReq`). `plainReq`'s `_ => True` also admits
  the auth requests, `Authenticate`, `AuthStatus`, the downgrade requests, `LeaseCheckpoint` and
  `Range`, and the auth requests' answers say only `applyErrIs`. Narrowing `plainReq` to the
  KV, cluster and downgrade kinds with `needAdminPermission rq = false` (so `monitorReq` gains that
  clause, which the monitors' concrete requests meet) stays inside the server's KV files:
  `plainReq` is used only there.
* **(iii) the chain: provable.** `kvApplied` keeps `x.chain = γk.ch0 = alarmChain false false
  false`, so the chain has no capped or corrupt layer and auth is off. Then no outcome is
  `.rejected .noSpace`, `.corrupt` or `.auth`, and no applied outcome has `ns = true`: the quota
  layer is the identity and the backend's outcomes carry `false`. So `ar.Err` is `nil` or one of
  the backend's errors: for a put `ErrLeaseNotFound`/`ErrKeyNotFound` (`putOutcomeIs`); for a
  transaction `checkErrIs` (those two, mvcc's `ErrFutureRev`, `ErrCompacted`); for a range `nil`
  or `ErrFutureRev`.

**The gap: nothing tells the error variables apart.** The backend's errors are leaf
`*errorString`s, so `errors.Is(e, ErrNoSpace)` is `e == ErrNoSpace`, and showing it `false` needs
`e`'s pointer to differ from `ErrNoSpace`'s. No fact gives that. Each package fact says only
that a variable holds *some* `*errorString` `x` whose `Error()` returns its message
(`errorsNewVar`, `leaseErrVar`, the postcondition of Perennial's `context.wp_New_errorString`).
In the model two variables may hold the same `x`, and the `Error()` triples do not rule it out.
In Go each `errors.New` allocates a fresh `errorString`. D19h's "a lemma that none of those errors
`Is` `ErrNoSpace`" cannot be proved from the present facts.

**Options.**
* **(A) Carry `errors.New`'s field in the facts** (no new axiom). Perennial's `wp_New_errorString`
  already persists the `errorString.s` cell in its proof (`ipersist s`); its postcondition drops
  it. The change:
  - `errorsNewVarInit`/`errorsNewVar` (`Proof/errors/NewVar.lean`) carry `s ↦□ msg` for `x`, so
    `etcdserver/errors`' `errorsNewVarsInit` (and bbolt's, which share the abbreviation) are
    restated stronger and stay true of Go;
  - `lease`'s and `mvcc`'s initializers, which call Perennial's `wp_New_errorString`, get a local
    variant that returns the cell, and the general fix (the postcondition with `s ↦□ msg`) is
    proposed to Perennial;
  - `leaseErrVar` carries the cell;
  - the apply package's `applyErrVars` gains "`ErrNoSpace`'s error is none of `ErrKeyNotFound`'s,
    `ErrLeaseNotFound`'s, `ErrFutureRev`'s, `ErrCompacted`'s", proved from the different messages
    (two `↦□` at one cell agree).

  These Init files are generated, so this is an `etc/gen-init.py` change. Then (i)-(iii) above,
  the branch is dead, and `AlarmContract.lean` and its axiom go. Cost: one unit. It collides with
  the `gen-init.py` work now uncommitted in the shared worktree (`gen-init.py`, `apply/Init.lean`,
  `mvcc/Base.lean`), so it should come after that work lands.
* **(B) A workload whose answers carry no error.** Puts and transactions without ignore flags
  (`txn.needsPrev` false) and without failing checks, so every admitted answer's error is `nil` and
  Perennial's nil clause gives `false`. No init change. But the client's `Put` with
  `IgnoreValue`/`IgnoreLease` and such transactions leave the verified workload: `putPermit`,
  `txnPermit` and the v3rpc and client specs above them narrow. That is a loss of coverage D19h
  did not intend. Also `checkErrIs` would have to be made exact for plain transactions.
* **(C) Keep the axiom, restated true of Go.** It would be stated for the one request the
  goroutine proposes, `{Alarm: ACTIVATE NOSPACE}`. That request still enters the log, which the KV
  model excludes (`plainReq` is `False` for `.alarm`), so this needs D19h's option (A), modeling
  the alarm. Several units.

**Recommended: (A)**, once the `gen-init.py` edits in progress have landed. It is the same kind of
statement as the existing `<X>_init` axioms, made more exact about the Go line they describe.
**Adopted by the user (2026-10-18): (A), to start once D19j (`watchVars`, `gen-init.py`) lands.**

**Carried out (2026-10-18).**
- **The cells.** `Proof/errors/NewVarCell.lean` adds:
  - `errStrCell x msg` (`x.s ↦□ msg`);
  - `errorsNewVarInitC`, `errorsNewVarInit` with the cell. The two `errorsNewVarsInit` axioms
    are now stated with it, still true of Go;
  - `errVarCell X msg` (the variable's pointer and its cell) and `errVarCells`;
  - `errVarApart g h` (the two variables hold different errors) and `errVarApart_of`
    (different messages give it: two `↦□` at one cell agree);
  - `wp_New_errorString_cell`, Perennial's `context.wp_New_errorString` keeping the cell (the
    general fix to propose to Perennial: its postcondition with `s ↦□ msg`).
- **The facts.** The packages' facts carry the cells they need: `errorsInit` (`errVarCells
  errorsMsgs`), `leaseInit` (`ErrLeaseNotFound`'s), `mvccInit` (`ErrCompacted`'s,
  `ErrFutureRev`'s), each appended last. `applyErrVars` gains `errVarApart ErrNoSpace` of
  `ErrKeyNotFound`, `ErrLeaseNotFound`, `ErrFutureRev`, `ErrCompacted`, proved by the
  generated `apply/Init.lean`. All of it goes through `gen-init.py`.
- **`errors.Is`.** `Spec/errors/Is.lean` now has Perennial's postcondition.
- **The workload.** `plainReq` keeps the KV writes and the monitors'
  `ClusterVersionSet`/`ClusterMemberAttrSet`, with `needAdminPermission` false; `monitorReq`
  gains that clause. `plainReq_of_kind` takes the auth fields too.
- **The proof.** `NoSpaceDead.lean` shows:
  - `dispatchStep_start`: at the start's chain a plain request's outcome is the backend's
    rejection or applied without `ErrNoSpace`;
  - `applyResultIs_notNoSpace`: the result's `Err` is `nil` or a leaf other than
    `ErrNoSpace`'s;
  - `wp_Is_notNoSpace`: then `errors.Is` answers `false`.

  `applyEntryNormal` takes the start's chain from `kv_log_plain` and calls `wp_Is_notNoSpace`;
  the alarm branch is gone from its proof. Its callees in the link are unchanged (the Go code
  calls them; the proof does not need them). `EtcdServer.raftRequestAlarm` and
  `AlarmContract.lean` are removed: one axiom fewer.

## Audit B4b: the latent axioms and premise gaps restated; ten stopped for a decision (D19l, 2026-10-18)

Phase B4, part b (`notes/audit.md`, the Plan): the axioms false only in an instance no proof uses
(latent) and those missing a premise every caller meets (premise gaps). Each restated true of Go
by a premise its callers discharge, or a postcondition weakened. **Done** (the audit's rows say
how): `strconv.FormatUint` (base `2..36`), `monitorFileDescriptor` (`lg ≠ null`),
`storage.BackendQuota.Cost` (a non-nil request), `txn.WarnOfExpensiveRequest`/`WarnOfFailedRequest`
(the logger and the uber-applier's stringer, of a non-nil request), `addFeatureGateMetrics`
(`isFeatureGate`), `lease.lessor.Promote` (a positive `leaseRevokeRate` in `lessorCfg`, from
`NewLessor` of a non-negative one, restated), `mvcc.hashStorage.Store` (`hashStorageOk`, a
non-nil logger, from `NewHashStorage`, kept in `isStore`), `mvcc.kvHasher.WriteKeyValue`/`Hash`
(`kvHasherOk`, opaque as the type, from `newKVHasher`, restated, and `bucketKeyOk` of the key),
`bbolt.DB.Info_kv` (a live transaction of the database), `bbolt.Bucket.Cursor_kvw` (`ownWTx` comes
back only with the cursor). (`grpc.ClientConn.NewStream`, the twelfth latent one, is fixed by the watch session on `lean`,
`ba511d61f7`: left to it.)

**Stopped** (options below; nothing changed in Lean for them):

**(i) `time.Since`** (`Spec/time/Since.lean`: `0 < d`). The audit's suggested fix, `0 ≤ d`, is
not true either for an arbitrary `t` (a `t` without a monotonic reading, or a later one, gives a
negative duration), and it breaks `syncWatchersLoop`, whose `delayTicker.Reset(syncDuration)`
panics on `0`: the Go hazard of `issues/etcd-watch-sync-ticker-reset-zero.md` (upstream
etcd-io/etcd#22296). Perennial's time model has no monotonic clock (`runtimeNano` arbitrary), so
its proved `time.wp_Since` gives any duration (the local axiom is false in that model too).
- *(A) A named run premise* `time.clockAdvances` (opaque: "every `time.Since` of the run returns a
  positive duration"; etcd calls it only on earlier `time.Now()` results), a premise of the axiom,
  as a hypothesis class in gen-link's `SEM_PREMISES` (`[ClockAdvances]`: every result reaching
  `syncWatchersLoop` takes it, up to `wp_NewServer` and the closed theorem; cheap) or a
  precondition threaded `syncWatchersLoop` → `mvcc.New` → `NewServer.spec` (as
  `backendUnderQuota`). `scheduleCompaction` and the other callers move to Perennial's proved
  `time.wp_Since`. Loss: a premise false on a coarse clock, the very hazard filed.
- *(B) A local monotonic clock*: a persistent `nowStamp t` from a local `time.Now` axiom, `Since`
  of a stamped `t` at least `0` (true of Go), and (A)'s premise only for `syncWatchersLoop`'s
  positivity. Two or three new axioms; callers switch from Perennial's `wp_Now`.
- *(C) The fork carries the upstream fix* (`Reset` only for a positive `syncDuration`), as raft's
  read-index fix and D19i part 2: then Perennial's `time.wp_Since` suffices, the axiom goes, no
  premise. A retranslation (`etc/goose.py`) and a small change to `syncWatchersLoop`'s proof.
- *(D) Perennial* (separately): a monotonic clock in the time model; (B) without local axioms.
- *Recommendation:* (C); (A) with the class if the fork should stay at upstream's code.

**(ii) `auth.authStore.AuthInfoFromTLS`** (any context; Go panics on a peer whose `AuthInfo` is
not a `credentials.TLSInfo`: `issues/etcd-auth-tls-info-assert.md`). Its caller is the server's
request contract (`isReqAuth`'s `AuthInfoFromTLS` clause, `AuthReqDerive.lean`), for any context.
- *(A) A deployment premise* (opaque "etcd's gRPC servers are built with TLS credentials or
  none", so a handler's peer has no `AuthInfo` or a `TLSInfo`), as a class (gen-link
  `SEM_PREMISES`) or threaded through `isReqAuth`'s users (v3rpc's handlers) to `v3rpc.Server`.
- *(B) In grpc's model*: the serving axioms give each handler context a persistent fact of its
  peer's `AuthInfo` type, from the server's credentials (`grpc.NewServer`'s options);
  `isReqAuth`'s clause takes it. Larger (grpc's server-side axioms, v3rpc's handlers).
- *(C) The fork fixes the assertion* (`, ok :=`), the issue's proposed fix: the axiom true as
  stated.
- *Recommendation:* (C), else (A).

**2026-10-18 · (i) (C) and (ii) (C) carried out (approved by the user), one fork batch.** The
fork's `goose-lean` gains two commits on `06aa6e6e7` (local branch `goose-lean-d19l` of
`/shared/etcd`, worktree `/shared/etcd-fork-d19l`; not pushed): `5615016f6`, etcd-io/etcd#22297
cherry-picked with its test (`resyncDelay(syncDuration, last, now)`: the duration when the pass
made progress with watchers left and it is positive, else `watchResyncPeriod`), and `17c88a667`,
`AuthInfoFromTLS`'s two-result assertion (`nil` for a non-TLS peer) with the issue's
reproduction as a test (it panics without the fix). `etc/goose.py`'s pin and putget's
`go.mod`/`go.sum` follow (`v3.0.0-20261018175554-17c88a6678c3`); `mvcc.toml` translates
`resyncDelay` with its body. The translation changes only `syncWatchersLoop` (the two `Reset`s
become one `Reset(resyncDelay(...))`) and adds `resyncDelay` (plus source line numbers).
- (i): `resyncDelay` proved (`Proof/.../mvcc/resyncDelay.lean`: its exact result, positive for any
  `syncDuration`); `syncWatchersLoop` and `store.scheduleCompaction` use Perennial's
  `time.wp_Since` (any duration); the local `Spec/time/Since.lean` and its axiom
  `time.Since.wp_proof` are deleted (one axiom fewer; the mvcc, mvcc-compaction and server
  collections lose it).
- (ii): `AuthInfoFromTLS`'s axiom unchanged in statement (any context), now true of the fork's
  code; only its doc comment changes. No caller changes.

**(iii) prometheus `CounterVec.WithLabelValues`, `GaugeVec.WithLabelValues`,
`HistogramVec.WithLabelValues`, `GaugeVec.With`** (Go panics on a label count other than the
vector's, or a value that is not UTF-8). Nothing states a vector's label names today: the vectors
are package variables built by untranslated initializers (`prometheus.NewCounterVec(opts,
[]string{...})`).
- *(A) A per-vector fact* `promVecLabels v ls` (persistent, an initialization fact of each
  package's metric variables, `etc/gen-init.py`'s `SPECIAL`, trust-boundary axioms on the
  initializers as now), and the four specs taking `lvs ↦*□ vs ∗ ⌜vs.length = ls.length ∧ ∀ v ∈ vs,
  utf8Valid v⌝` (`With`: the map's keys `ls`). Nine call sites discharge it: constants (decidable),
  ids and versions formatted by `strconv`/`fmt` (UTF-8 by construction), the client's API
  version (v3rpc's interceptor checks `utf8.ValidString`, `interceptor.go:63,234`).
- *(B) Per-vector axioms*: each spec restated for the global vector its callers use, with the
  arity written in the axiom (`clientRequests`: 2, ...), and the UTF-8 premise. No init facts;
  the arity checked by reading the initializer (trusted).
- *Recommendation:* (A), after D19j's `gen-init.py` work lands (it edits the same script); the
  call sites are in v3rpc (D19j's files) and the server's request path.

**2026-10-18 · (iii) (A) carried out (approved by the user).** `prometheus.vecLabels v ls` is an
`opaque` proposition (no axiom: nothing proves it but the vectors' `<X>_init` axioms, which state
it with their `metrics.go` label names; pure, so persistent; `Labels.lean`). The four specs take
`⌜vecLabels v ls ∧ labelValuesOk ls vs⌝ ∗ lvs ↦*{dq} vs` (`With`: `labelMapOk ls M`, the map's
keys exactly `ls`, distinct, values UTF-8, `labels ↦${dq} M`) and give the values back.
`utf8Valid` is a definition (Unicode's well-formed sequences, which are Go's `ValidString`'s), so
constants are discharged by `decide`. The seven vectors the proofs read get the fact
(`gen-init.py`'s `promvec`; their package facts in `apply/Base.lean`, `BaseApply.lean`,
`v3rpc/Base.lean` carry it). The nine call sites discharge it; for the non-constant values seven
value-only specs say what they return (each still an axiom, now stronger and still true of Go):
`utf8.ValidString` returns `decide (utf8Valid s)` (the interceptors' check), `FormatBool`
`"true"`/`"false"`, `types.ID.String`/`String_ptr` (`FormatUint(id, 16)`) and
`AlarmType.String` (`EnumStringOf`: a descriptor name or a decimal) ASCII,
`semver.Version.String` a string starting with two decimal numbers each followed by a dot
(`semverStr`, `"%d.%d.%d"`), and `version.Cluster` of such a string ASCII (`"%d.%d"` after a
successful parse, else the first two `.`-fields joined: the two numbers). `start`'s
`ClusterVersionMetrics.With({"cluster_version": version.Cluster(v.String())})` needs the last two:
`utf8Valid` of an arbitrary `semver.Version.String()` is not true of Go (`semver.New` does not
check `pre`), so the fact goes through `semverStr`. No new axiom, no `sorry`; the baseline and the
collections unchanged.

**(iv) `backend.wBkt`, `wBkt_persistent`, `bbolt.Tx.DeleteBucket_kv`** (a persistent handle
outlives `DeleteBucket(n)`; after `CreateBucketIfNotExists(n)` the old handle, whose `nodes` bbolt
set to `nil`, passes `Put_kv`'s premises, and Go panics). A persistent fact cannot be revoked, so
the fix is in what `ownWTx` records.
- *(A) Generations*: `wBkt tx b n g`, `ownWTx` holding each bucket's current generation (a ghost
  map `n ↦ g` in the model); `DeleteBucket` bumps it, `Put`/`Delete`/`Cursor_kvw` need the
  current one. Every bbolt spec and backend proof that names `wBkt` (about 30 files).
- *(B) Deleted names*: `ownWTx tx γ D S X` with `X` the names deleted in this transaction;
  `CreateBucketIfNotExists_kv` requires `n ∉ X`, `DeleteBucket_kv` adds `n`. With
  `S.lookup n = none` after the delete, no old handle passes `Put_kv`'s premise, and the name
  cannot come back in that transaction (no verified proof deletes a bucket and re-creates it);
  the same files as (A), a smaller change.
- *(C) Keep, as now* (latent: no proof deletes and re-creates).
- *Recommendation:* (B), in phase C with the bbolt model (`notes/audit.md`, Plan).

**(v) `mvcc.store.restore`** (a `meta` bucket with a finished or scheduled compaction makes Go set
`compactMainRev`/`currentRev` otherwise and call `compactLockfree`; the spec fixes only the `key`
bucket). The store's backend contract (`isKeyBackendG`) does not model the `meta` bucket's
compaction keys, so no caller can state their absence.
- *(A) Model them*: the backend contract gains the compaction keys' view (the one
  `UnsafeSetFinishedCompact`/`UnsafeSetScheduledCompact` write), and `NewStore`'s precondition
  their absence, from the bootstrap's fresh backend (`bootOk`, `bkFresh`-like per key).
- *(B) A named premise* (opaque `mvcc.metaNoCompaction`: "the backend `NewStore` opens records no
  compaction"), a premise of the axiom threaded `NewStore` → `mvcc.New` → `NewServer.spec`, as
  `backendUnderQuota` (true of putget's fresh data directory).
- *(C) `restore` of a backend with data* (the index rebuilt): the general case, large.
- *Recommendation:* (B) now (one premise on three specs), (A) with phase C's backend model.
- **2026-10-18 · (B) carried out (approved by the user).** `mvcc.backendNoCompaction` (opaque,
  `InvStore.lean`) is a premise of `restore`'s axiom, threaded `NewStore` → `newWatchableStore` →
  `mvcc.New` → `NewServer.spec` (`%Hnocmp`) and the server's KV results. Why it is admissible
  (D19a's first kind): a fact about the program's environment (the data directory's bbolt file at
  startup), not about ghost state; nothing in the model proves or refutes it. True of putget's
  fresh data directory: the keys are written only by the compaction (`UnsafeSetScheduledCompact`
  in `store.Compact`, `UnsafeSetFinishedCompact` in its job), which needs a store, so no backend
  holds them before the first `NewStore`. False of a restart after a compaction, which the closed
  theorem does not cover; (A) remains the route for it.

**Found on the way, not fixed:** `apply.isQuota` (which `storage.NewBackendQuota`'s axiom gives)
has `Cost`'s nil-request gap in both its clauses (`Available` calls `Cost`): its callers
(`quotaApplierV3`'s `Put`/`Txn`/`LeaseGrant`) hold non-nil request facts, but
`v3rpc.quotaAlarmer.check`'s spec takes any `r`, so the premise would thread into v3rpc's quota
servers (D19j's files). A premise gap of the same kind, left for a later round.

## Audit B4a: the false etcd-internal axioms putget does not reach (D19m, 2026-10-18)

**2026-10-18 · four restated (taken: each true of the Go code at the pin), four stopped for a
decision (proposed).** Audit phase B4, part a (`notes/audit.md`): the eight false etcd-internal
axioms off putget's Go path.

- **Taken: the hash and downgrade monitors restricted to the configuration that turns them off.**
  `monitorKVHash` (`CorruptCheckTime ≠ 0`) and `monitorCompactHash` (`CompactHashCheck` on) would
  read the backend and may propose `Alarm{CORRUPT}`, which the KV model does not admit (an alarm is
  not `plainReq`: the same obstacle as `raftRequestAlarm`, D19h/D19k); `monitorDowngrade`
  (`DowngradeCheckTime ≠ 0`) may propose `DowngradeInfoSet`, which no permit covers. Giving them
  resources would need those requests in the model; putget's configuration leaves all three off
  (zero intervals, the feature at its default `false`), so each contract now takes the fact under
  which the body returns at once: the interval's field `↦□ 0`, or the feature gate's
  `featureIs fg "CompactHashCheck" false` (a new persistent contract of the gate,
  `features/Defs.lean`, which `NewDefaultServerFeatureGate`'s trust-boundary spec now also
  returns: the gate is not shared and nothing sets a feature, the argument its spec already made
  for `isFeatureGate`); `monitorDowngrade` also a reader slot of `lgMu` and the logger field
  (`NewMonitor(s.Logger(), …)` comes before the check). Threading: `NewServer`'s post gains
  `srvMonitorCfg s cfg` (the two fields and the gate field at `cfg`'s values, one more `lgMu`
  slot); `Start`'s pre gains `srvMonitorsOff s ∗ srvLgReader s`, which `srvMonitorsOff_of` gives
  from `srvMonitorCfg` for a configuration with both intervals `0` and the gate's `featureIs`
  (`InvMonitors.lean`; Main's proof, still to come, discharges it from putget's literal and
  `NewDefaultServerFeatureGate`). Rejected: a pure premise on `cfg` alone (the feature's answer is
  the gate's, not the configuration's); keeping the monitors' contracts unrestricted with a
  workload premise "no corruption, no downgrade" (a premise where a configuration fact does).
- **Taken: `RaftCluster.SetVersionChangedNotifier` with the field owned.** It writes
  `c.versionChanged` without the lock; the contract takes the field's points-to and returns it at
  `n`. `bootstrap`'s contract (`bootOk`, a premise, D13b) gives the field owned (`Hvcn`: the
  cluster is not yet shared; fresh, D19a), `NewServer` persists it after the call, and the
  cluster's apply contract `Hisc` (whose `SetVersion` reads the field under the lock) now takes
  the read-only field as a premise, so a model of `bootstrap` can prove both (`SetVersion`'s own
  truth, its notifier's `Notify` among it, stays that contract's row).
- **Stopped: `EtcdServer.revokeExpiredLeases`.** For a non-empty slice its goroutine proposes
  `LeaseRevoke`, which the KV model does not admit (`plainReq` excludes `leaseRevoke`; a revoke
  deletes the lease's keys); even an empty slice calls `ensureLeadership` (the read loop's
  `LinearizableReadNotify`, `raftStatus`, the tick mutex). `run`'s proof passes it whatever
  `expiredC` delivers (a bag with predicate `True`, `lessorOk`). In the model no lease ever
  exists (`plainReq` excludes `leaseGrant` and puts with a lease, the lease bucket is fresh:
  `bootOk`'s `bkFresh "lease"`), and in Go the lessor sends only non-empty slices of its expired
  leases, so the receive is dead -- but nothing says so. Options: *(A)* the lessor's map in the
  model: `NewLessor`'s contract (names-only `runLoop`) gives `expiredC` the predicate "a lease
  this lessor granted", `Grant`'s spec records the lease in a ghost set the KV invariant keeps
  empty (no committed `LeaseGrant`), so `run`'s receive yields `False` and the axiom leaves the
  link (as `Alarm` in B3); cost: the lessor's grant path and `kvInv`'s side, moderate. *(B)* A
  named workload premise "no lease expires" (D19a's first kind, as `backendUnderQuota`), under
  which `NewLessor`'s contract gives the bag `False`; cheap, but a premise where the model could
  prove it. *(C)* Leases in the KV model (`LeaseGrant`/`LeaseRevoke` as requests, the revoke's
  deletes): large. *Recommendation:* (A).
- **Stopped: `EtcdServer.Cleanup`.** It closes the KV, the auth store and the backend (bbolt
  closed) under `bemu`'s write lock after `s.wg.Wait()`, but request goroutines (not in `s.wg`)
  keep persistent views of all three. Reached in the model on `run`'s two exits (`<-s.stop`,
  `<-s.errorc`, bags with predicate `True`), not in putget's Go run (nothing stops the server).
  Options: *(A)* the exits dead: `s.stop`'s and `s.errorc`'s bags with predicate `False` in the
  runs covered (nobody calls `Stop`/`HardStop`: a fact of Main's proof; `errorc`'s senders --
  `stopWithDelay` on the member's removal, which `ccApplyOk` excludes, and the raft loop's
  fatal errors -- each shown not to send), `run`'s shutdown proof gone with `Cleanup`'s and
  `raftNode.stop`'s axioms from the link; cost: the senders' contracts. *(B)* A "server open"
  fractional token every request path holds and gives back, `Cleanup` taking the whole (the
  backend's `bOpen` shares, the store's closer, the auth store's): faithful for a server that
  stops, but the token threads through every request spec. *(C)* Closed states in the backend's
  and the stores' models (operations after `Close` return errors): largest. *Recommendation:* (A)
  for the closed theorem, (B) when a stopping server is in scope.
- **Stopped: `EtcdServer.createMergedSnapshotMessage`.** It commits the KV, takes a backend
  snapshot (a bbolt read transaction a goroutine streams), clones `*confState` and writes
  `m.Snapshot`, a message raft hands out read-only (`rnMsgOk`: `msgAt`, persistent). Reached in
  the model whenever `msgSnapC` delivers, never in a single-member cluster (raft sends `MsgSnap`
  only to a follower). Options: *(A)* the receive dead: raft's messages carry `to ≠ self` among
  the configuration's voters (`rnMsgOk`), the configuration stays `{self}` (`ccApplyOk` adds only
  members of it), so `msgSnapC` carries nothing; cost: a raft-side fact on `Ready`'s messages
  and the configuration's invariance through the server. *(B)* Its resources: the message owned
  through `msgSnapC`'s bag (raft's message ownership, `processMessages`), a backend snapshot
  model, the conf state's read: large, and only for multi-member clusters. *(C)* A premise "no
  `MsgSnap`" on the run. *Recommendation:* (A).
- **Stopped: `mvcc.store.Close`.** It stops the FIFO scheduler, but `isStore` (persistent) holds
  `schedLive` (the stop token given up for good, `NewStore`), so the triple lets a holder of
  `isStore` compact after `Close`, where Go's `Schedule` panics. Reached only on `NewServer`'s
  error paths after `mvcc.New` (`restoreAlarms`, `tr.Start()` failing), where in Go nothing
  schedules afterwards. Any true contract of `Close` needs the stop token, which `NewStore`
  gives up (its `restore` may itself schedule a compaction). Options: *(A)* a fractional
  "store open" token: `NewStore` keeps the stop token in an invariant with it, untracked
  `Schedule` (the store's `compact`, `updateCompactRev`, `compactBarrier`) takes a share,
  `Close` the whole; the apply thread holds a share for good; cost: mvcc's compaction specs and
  their callers. *(B)* `NewServer`'s late error paths dead: `restoreAlarms` and
  `rafthttp.Transport.Start` without errors on putget's configuration (a fresh alarm bucket, no
  TLS), and `Close`'s contract taking the stop token (vacuous after `NewStore`); cost: two
  trust-boundary contracts narrowed, premises on the configuration. *(C)* `NewStore` returns the
  stop token and the caller gives it up (`schedLive_of_stopTok`) on success, `Close` on error;
  needs `restore`'s scheduled compaction excluded (a fresh backend: none scheduled).
  *Recommendation:* (C), with `restore`'s case from the fresh backend `bootOk` gives.
  **2026-10-18 · (C) carried out (approved by the user).** `restore`'s scheduled compaction is
  excluded by D19l (v)'s premise (`backendNoCompaction`), not by `bootOk`. Two consequences of
  (C) that the option did not spell out: (1) `NewStore`'s caller (`newWatchableStore`) has no
  error path; the error paths are `NewServer`'s, after `mvcc.New`, so the token travels in the
  right to close (`storeCloser s γ`, inside `wsCloser s st γs`) up to `NewServer`, which drops
  it on success; meanwhile `isStore` must hold without `schedLive`: it now holds `isFifo`, and
  `schedLive` is in `compactRight`, `compactJobPre` and `compactBarrier`'s precondition (the only
  untracked `Schedule`s). (2) The stop token alone does not make `Close` true: a tracked
  `Schedule` needs only the queue, and `Scheduler.Stop`'s spec takes it too; so `storeCloser`
  holds the compaction jobs' queue (`compactQueue γ (-1)`) as well, and `NewStore` returns the
  compaction right's half of the revision's authority apart (`crevUB γ.idx ½ (-1)`): freezing
  needs only that (`crevFrozen_alloc`), and a caller that compacts makes the right from it and
  the closer (`compactRight_of_closer`, giving the token up). Compacting and closing are thus
  exclusive, as Go needs.

## Proof/Lib: facts that belong to no Go package (2026-10-18, branch `proof-lib`)

*The decision.* A fact about Perennial's, Iris's or Lean's own definitions -- not about a Go
package's code or its predicates -- lives once, in `Proof/Lib/`, and every package imports it
from there: `Iris.lean` (fractions `Qp`/`DFrac`, `Fractional` of an existential with agreeing
witnesses, ghost variables' and ghost maps' halves, `Persistent`/`Timeless` of an `if`),
`Heap.lean` (`ownMap` fractional and agreeing, the typed points-to at `q1 + q2`), `Sync.lean`
(an `RWMutex` guard from its reader slots, at least two readers), `GoString.lean`
(`go.GoStringLt` a strict total order, from Lean core's `List.lex_*`) and `List.lean` (the
`i`-th key of a duplicate-free list is not among the first `i`, the first `i + 1`, a prefix
with nothing past it). The modules are split by what they import, so that each sits low in the
import graph: `Iris` needs only Perennial's ghost state (the raft protocol's `Ghost.lean` imports
it without the heap), `GoString` only `Perennial.Golang.Defn.String`, `List` nothing.

*Carried out (2026-10-19).* Every fact moved to Perennial (`lean`, `8d53c9e0d`) or was deleted (unused, or a one-liner from Lean core), and
`Proof/Lib/` is gone (STATUS.md, "Proof/Lib: the package-independent facts"). A new fact of this
kind goes to Perennial directly, on a branch off its `lean`, not into a holding place here.

*Temporary, per fact.* `Proof/Lib/` was a holding place, not a library of this repository: each
fact is one Perennial (or Lean core) is missing, and a candidate for an independent Perennial
proposal under "Changes to Perennial" in CLAUDE.md (designed and reviewed on its own, not shaped
by a proof here). A fact goes from `Proof/Lib/` when its Perennial counterpart lands, its users
pointed at Perennial's name. Proofs of Go functions and package predicates never go there.

*Why there were copies.* Each original was proved inside a package's section, under that
package's `Assumptions` (`package_sem`) or in a module another package could not import without
pulling in that package's proof tree (or an import cycle: the client could not import the
server's `Base`). A second package needing the fact copied it under a new name (`lc_`, `lease_`,
`wait_`, `...W`, `...'`): `ownMap_fractional` six times, `qp_half_add` nine, the `x ∉ l.take i`
lemma seven, the `GoStringLt` order lemmas three times, `ite_persistent` seven.

*Names.* The shared lemma keeps the name of the copy in `EtcdGrove`'s namespace where there was
one; InvDemux's `ghostVar_halves` (any fraction, an equivalence) is now `ghostVar_split_half`,
because Perennial's `ghostVar_halves` (the whole, one direction) is public in namespace
`Perennial` and the `EtcdGrove` one shadowed it inside `EtcdGrove` (mvcc's own copy, the whole
as an equivalence, was used only one way and is now Perennial's). `ownMap_agree` takes
`[go.IntoValInj V]` (mvcc's copy took the injectivity as an argument; its users' value types
have the instance).

*Not moved (yet).* `Proof/go_etcd_io/raft/v3/FrameH.lean` and `ProjSimps.lean` (generic tactics:
`iframe ∗` with a hypothesis list, `proj_simps`) are of the same kind and candidates to move to
`Proof/Lib/` later; they stay for now because many files import them by their present names.
Facts copied only within one package (raft's private `ite_pos`/`ite_neg`, `uint_nat_eq`) or once
(`backend.strLt_total`, the `goStringLe_*` of `mvcc/BucketRange.lean`, mvcc's `wFractional_*`
combinators) are left where they are; they can move when a second package needs them.

## D19j carried out: `watch.go`'s package variables from `v3rpc`'s facts; `io.EOF` stays (2026-10-18)

The user chose D19j's option (1). Carried out, but for `io.EOF`:

* **`v3rpc.watchPkgVars`** (`v3rpc/Base.lean`, its pieces in `v3rpc/BaseWatch.lean`): everything
  `watchVars` held but `io.EOF` and `reportEventOk`, now a conjunct of `v3rpcInit`, proved by
  `v3rpc`'s initializer (`etc/gen-init.py`): `auth`'s four errors from `authInit`
  (`errVarLeaf_of_authErrVar`); `mvcc`'s `ErrEmptyWatcherRange`/`ErrWatcherDuplicateID` from
  `mvccInit`, which now keeps them as the `errors.New` errors they are (`errorsNewVar`, appended;
  `errVarLeaf_of_newVar`); `rpctypes`' `ErrCompacted` (its `errorStringSpec`) and five `ErrGRPC*`
  errors, which `rpctypesInit` now keeps (appended; five `<X>_init` axioms, `status.Error` values
  whose `Error()` returns); `streamFailures` and the four `watchSendLoop*` histograms (five
  `<X>_init` axioms, as `clientRequests_init`); `traceutil.Tracer` from `traceutilInit`;
  `context.Canceled`'s pointer error; and the progress interval's lock, initialized by the
  initializer (`sync.init_RWMutex` over `progressReportInterval`, `10 * time.Minute`, within
  `intervalP`'s bounds; `guard_of_slots`).
* **`mvcc.ReportEventReceived`**: a trust-boundary spec (`Spec/.../mvcc/ReportEventReceived.lean`,
  axiom `mvcc.ReportEventReceived.wp_proof`, linked in mvcc's Link and `@` in v3rpc's), a callee
  of `sendLoop`. Stated for `0 ≤ n`: its body's `totalEventsCounter.Add(float64(n))` panics on a
  negative value (prometheus' counter), so the old package fact `reportEventOk` (every `n`) was
  false; `sendLoop` passes `len(...)` of event slices it holds (`ownSlice_len` at its four calls).
* **`watchVars` = `eofVar ∗ watchPkgVars`** (`InvWatch.lean`), `watchVars_of_init : isPkgInit
  v3rpc ∗ eofVar ⊢ watchVars`; `grpcCfgOk_of_started` takes `isPkgInit v3rpc ∗ v3rpc.eofVar` in
  place of `watchVars`.

**`io.EOF` (not done as planned).** The planned premise class (`isPkgInit io ⊢ eofVar`, as
`ContextReadErrs`) holds in no model: Perennial's `io.isInit` keeps only `Discard`'s cell, not
`EOF`'s, so the entailment would conjure a points-to from nothing, the class would be
uninhabitable and every theorem taking it vacuous (`ContextReadErrs` is sound because
`context.isInit` has the `Canceled`/`DeadlineExceeded` cells). So `v3rpc.eofVar` stays a named
premise, of the intermediate lemma `grpcCfgOk_of_started`, not of a closed theorem: as a
points-to on a global it is not one of D19a's admissible hypotheses (pure facts, triples of
called functions), so it must be discharged before the closed theorem, by the Perennial change
below and a pin bump. True of Go: `io.EOF = errors.New("EOF")`, and Perennial's own
`io.initialize'` stores that value (`Perennial/Proof/io/initialize.lean` drops it).
**Proposed to Perennial, on its own:** `io.isInit` keeps `EOF ↦□ errors.New("EOF")`'s value with
its `errors.New` facts (as `context.isInit` keeps `Canceled`), from the `wp_New` its proof already
calls.

Axioms: eleven added (five `v3rpc` `<X>_init`, five `rpctypes` `<X>_init`,
`mvcc.ReportEventReceived.wp_proof`), each checked against the Go source (`notes/audit.md`,
"Added after phase A"). The ten `<X>_init` are in the generated `Init.lean` files, which no
linked result reaches yet (as the other `<X>_init`s): `etc/tcb-baseline.txt` gains only
`mvcc.ReportEventReceived.wp_proof` (322 axioms, 12 `sorry`s; the `cache-client`, `mvcc`,
`v3rpc` and `watch` collections too), updated with `--check --update` on purpose.

## D19m carried out: `Cleanup` unreachable; `revokeExpiredLeases` and `createMergedSnapshotMessage` stopped (D19n, D19o) (2026-10-18)

The user approved D19m's recommendations (2026-10-18). Carried out for `Cleanup`; the other two
need a further decision each (D19n, D19o below).

* **`EtcdServer.Cleanup`: (A), carried out.** `run`'s two exits are dead in the runs covered:
  - `s.stop`: `start` makes it a bag with predicate `False` (`srvRunFieldsAt`); its only senders in
    Go are `HardStop` (and `Stop`, through it), which the runs covered never call (any program that
    did could not be verified against these specs: a send needs `False`).
  - `s.errorc`: `NewServer` makes it a bag with predicate `False` (`srvRunBuilt`,
    `srvRunFieldsAt`). Its senders in Go: `stopWithDelay` (`server.go:1352`), called by
    `applyEntries` only when `apply` returns `shouldStop`, i.e. when `applyConfChange` removed the
    local member, which its contract excludes (`removed = false`, B3's `ccApplyOk`); `apply`'s spec
    now returns `shouldStop = false` (its loop keeps `sb = false`), `applyEntries`' branch is gone
    and with it `stopWithDelay`'s axiom. And the transport (`ErrorC: srv.errorc`,
    `server.go:426`): its peers' and remotes' stream readers and pipelines send
    `errMemberRemoved` there when a remote member answers that this one was removed. That is one of
    the transport goroutines' effects, which the named premise `transportEffectsOk` already assumes
    as a whole (the cluster's message trust assumption); its statement now says so explicitly (no
    well-behaved member says that of a member never removed; in a one-member cluster there is no
    peer). Not a new premise, but a stated reading of the existing one.
  So `run` never returns; its deferred shutdown proof (`run_shutdown`: `stopping` closed, the
  context cancelled, the scheduler stopped, `GoAttach` waited for, `raftNode.stop`, `Cleanup`,
  `done` closed) is gone, and with it `run`'s hypotheses `zap.Error`, `Logger.Warn`,
  `Scheduler.Stop`, `raftNode.stop` and `Cleanup`. **Two axioms fewer**: `EtcdServer.Cleanup` and
  `EtcdServer.stopWithDelay` (their spec and proof files removed, as `raftRequestAlarm`'s in D19k).
  `raftNode.stop` (proved) stays linked, now unused; the scheduler's `Stop` (an axiom of mvcc's
  list) leaves the server's collection. A stopping server (D19m (B), a "server open" token)
  remains the route when one is in scope. Trust base: `etc/tcb-baseline.txt` 320 axioms, 12
  `sorry`s (two fewer), the `server` collection three fewer, both updated with `--check --update`
  on purpose.

## The lessor's grants and `run`'s expired-lease receive (D19n, 2026-10-18 · (A) adopted, carried out)

D19m (A) for `revokeExpiredLeases`: `expiredC`'s bag predicate "a lease this lessor granted", with
a ghost record of grants kept empty because no `LeaseGrant` is ever applied (`plainReq` admits
none: `.leaseGrant` falls to `_ => False`, and a put's lease is `0`). Carrying it out showed the
missing piece: **who can refute the predicate in `run`.** The receiver is `run`, but the lease
state is the apply thread's (`leaseOwn γl L`, inside `kvOwn`'s `leasesLive`, `∃ L`, travelling
from job to job), and the lessor's ghost state (`γl`: the live set, a non-monotone ghost
variable, half in the lessor's lock, half the owner's) gives no persistent fact that `L` stays
empty: `run` holds nothing to combine a "granted" witness with. Every route needs a persistent,
server-level fact that the apply thread never grants, and so a change on the apply side; the
choice is where it lives.

* *(A) A grant guard of the lessor.* `lessorInv` (or `NewLessor`'s postcondition, through a
  saved predicate pinned in the lessor's ghost map as its location is) carries a persistent
  predicate `GA : w64 → IProp` chosen by `NewLessor`'s caller; `Grant` takes `□ GA id`; the lock
  keeps `∀ id ∈ L, GA id`; `NewLessor`'s axiom gives `expiredC` the predicate `fun _ => ∃ id, GA
  id` (true of Go: `runLoop` sends only leases of `leaseMap`, found under the lock). The apply
  environment (`apply.AEnv`) gains the guard and `LeaseGrant`'s spec its premise `□ E.GA id`; the
  server picks `GA := fun _ => False`, discharging the applier's `LeaseGrant` premise from
  `plainEntry` (the branch is dead in the server's applies), and `run`'s receive yields `False`:
  `revokeExpiredLeases` leaves the link (one axiom fewer). Cost: the signature of every lessor
  spec over `lessorInv` (about fifteen) or, with the saved predicate, only `NewLessor`, `Grant`
  and the derivations of the lessor contracts (`LessorContract`, `LessorDerive`, `LessorOk`); the
  apply package's `AEnv` and `LeaseGrant` (its three appliers); `NewServer`'s instantiation.
  Moderate.
* *(B) The live set pinned at the server.* The server's apply resources keep `L = []`
  (`leasesLive` at `[]`), which needs `apply.Apply`'s spec to say that a non-`LeaseGrant`
  request leaves the live set unchanged (its postcondition today is `∃ L' ⊇ L`), and an
  invariant shared with `run` holding a fraction of the owner's half at `[]` (so `leaseOwn`
  becomes fractional). Larger than (A), and it changes the txn layer's `leaseOwn` users.
* *(C) A named workload premise* "no lease expires" (D19m (B), as `backendUnderQuota`), under
  which `NewLessor`'s contract gives the bag `False`: cheap; a premise where the model can prove
  the fact.

*Recommendation:* (A), with the saved predicate (the lessor specs' signatures unchanged).
`revokeExpiredLeases` stays a false axiom until then (`notes/audit.md`).

## Raft's `MsgSnap` in a one-member cluster (D19o, 2026-10-18 · (A) adopted, carried out as D19p)

D19m (A) for `createMergedSnapshotMessage`: `msgSnapC` never delivers because raft sends `MsgSnap`
only to another voter and the configuration stays `{self}`. Two things stop it now:

1. **The receive is in `applyAll`**, whose proof D19i part 1 is changing on its own branch
   (`d19i1-raft`; `applyAll`, the snapshot path, `compactRaftLog`): dropping
   `createMergedSnapshotMessage` and `sendMergedSnap` from `applyAll`'s hypotheses must wait for it
   or be done there.
2. **The raft-side fact does not exist yet.** A `Ready`'s message reaches the server as
   `msgOwn ∗ isRaftMsg γ st ∗ termLB` (`rnEnvOk`, `rnMsgOk_of_raft`); `isMessage`'s `.snap` clause
   carries the leader and the committed prefix, nothing about `dst`. The pure model knows more:
   `maybeSendSnapshot`'s spec sends the `.snap` "from `id` to `to`" with `to ≠ id` (its only caller
   is reached from `bcastAppend`, which skips the leader), `to` a key of the progress map, which
   in the static mode tracks exactly `γ.raft.reCfg` (`InvNode`'s configuration facts). Options:
   * *(A) In the protocol.* `isMessage`'s `.snap` clause gains `⌜m.dst ≠ m.src ∧ m.dst ∈
     reCfg⌝` (static mode; with reconfiguration, the configuration at the term), proved at
     `maybeSendSnapshot` from the tracker's keys; the server's `E.M` then refutes a `MsgSnap` when
     `reCfg = {self}` (the server's start: `ccBootOk`'s one-member configuration; `ccApplyOk`
     keeps it). Cost: the raft protocol's message clause and its send sites (`maybeSendSnapshot`
     only), the static-mode tracker invariant if it is not already stated in that form; then the
     server side (`isRNMsgSnapC`'s predicate, `processMessages`, `applyAll`). Raft-side, but in
     `raft.go`'s send path, not in `node.go`'s `run`/`advancec` or `RawNode` (D19i's).
   * *(B) In the outbox* (`outboxRel`, physical): each queued message's `To` is a tracked peer
     other than the node; the same proof obligation at the send sites, carried through `Ready`
     (`RawNode`, D19i's area) instead of through the persistent protocol predicate.
   * *(C) A premise "no `MsgSnap`"* on the run (D19m (C)).

   *Recommendation:* (A), after D19i part 1 has landed (the `applyAll` side then a small change:
   the receive's predicate `False`, the two hypotheses dropped). `createMergedSnapshotMessage`
   stays a false axiom, and `sendMergedSnap` a suspect one, until then.

## D19n carried out: the lessor's grant guard; `revokeExpiredLeases` removed (2026-10-18)

The user chose (A), with the saved predicate. Carried out:

* **The guard** (`lease/InvLessor.lean`): the lessor's ghost map `γl` now pins, at `false`, its
  location *and* the name `γga` of a saved predicate (`LessorGV := (Loc × GName) ⊕ List w64`,
  `lessorPinG`; `lessorPin γl lp` is `∃ γga, lessorPinG γl lp γga`, so its users are unchanged).
  `lessorGuard γl GA`: the pin and `savedPredOwn γga □ GA`; `leaseGranted γl id := ∃ GA,
  lessorGuard γl GA ∗ □ GA id` (persistent). The lock's ghost component is `lessorAuth γl q lp L`
  (the authority and `□ [∗list] id ∈ L, leaseGranted γl id`), carried untouched by every method
  but `Grant` (`lessor_live_grant`, which replaces `lessor_live_update`). No other lessor spec's
  signature changed.
* **`Grant`** takes `leaseGranted γl id` (the guard and `□ GA id`, packed); the apply package's
  `isApplyLessor` `Grant` clause takes `lease.leaseGranted γ.leases id`; the guard reaches the
  appliers through the store's names (`E.γ.leases`), not a new `AEnv` field: the four `LeaseGrant`
  appliers' specs and `reqFacts` (now `reqFacts E m r`) take `∃ g, leaseGrantIs r g ∗
  lease.leaseGranted E.γ.leases g.id`. The chain's dispatch never reaches them anyway (`rqOk`'s
  `.leaseGrant => False`).
* **`NewLessor`'s axiom** takes the guard `GA` (its caller's choice) and returns `lessorGuard γl
  GA` and `lessorExpiredC lp GA`, a bag with predicate `∃ id, GA id`. True of Go: the loop's
  `revokeExpiredLeases` sends only a non-empty slice (`lessor.go:652`) of leases
  `findExpiredLeases` took from `leaseMap` under the read lock (`expireExists`, `lessor.go:706`),
  each of which the lock keeps as `leaseGranted` (agreeing with the pinned guard after a step);
  the map starts empty (fresh bucket, no `Recover`).
* **The server**: `srvGrantGuard` (`InvApplier.lean`, `fun _ => False`) is the guard `NewServer`
  gives `NewLessor` and the predicate of `lessorOk`'s `expiredC`; `run`'s receive yields `False`,
  and `revokeExpiredLeases` (spec and axiom) is gone. **The guard is the instance's choice**
  (the user, 2026-10-18): putget's workload keeps leases off; a lease-enabled instance will pick
  its own guard through the workload parameter a later unit threads through `plainReq`,
  `reqPropOk`, `kvWork`, `NoSpaceDead` and `srvGrantGuard`.

Trust base: one axiom fewer (`EtcdServer.revokeExpiredLeases`): `etc/tcb-baseline.txt` 319 axioms,
12 `sorry`s; the `server` collection too; updated with `--check --update` on purpose.

## D19o's raft half: a `MsgSnap` may go to a learner (D19p, 2026-10-18 · (A) adopted, carried out)

D19o (A) asks for `isMessage`'s `.snap` clause to gain `dst ≠ src ∧ dst ∈ reCfg` in the static
mode. **As stated it is false of raft**: `maybeSendSnapshot` sends to any tracked peer that needs
a snapshot, learners included, and the static mode admits learners (`InvNode`'s static-mode
configuration: `c.Voters' ≡ₚ reCfg`, `∀ k ∈ c.Learners', k ∉ reCfg`; `CCShrink` may only drop
them). Also, `isMessage` is a protocol predicate over `RaftNames`, which records the voters
(`reCfg`) but neither the mode nor the learners, so "in the static mode" cannot be said there.
`dst ≠ src` alone holds (the only caller is reached from `bcastAppend`, which skips the leader) but
does not let the server refute a `MsgSnap`. Options:

* *(A) The tracked set in the protocol's names.* `RaftNames` gains `reTracked : Option (GSet w64)`:
  `some T` in the static mode, `T` the voters and the initial learners (an over-approximation of
  every id the tracker ever holds there, as learners are only dropped), `none` in the dynamic
  mode; `.snap`'s clause gains `⌜m.dst ≠ m.src ∧ ∀ T, reTracked = some T → m.dst ∈ T⌝`, proved at
  `maybeSendSnapshot` from the tracker's keys (which the static node state ties to its
  configuration). The server then refutes a `MsgSnap` from its one-member, learner-free
  configuration (`T = {self}`). Cost: every construction of `RaftNames` (bootstrap, `StartNode`,
  `RestartNode`, the tests' instances) and the static-mode invariant's tie of the tracker's keys
  to `T`; still in `raft.go`'s send path and the protocol files.
* *(B) Voters only, learners excluded by a static-mode premise.* The static mode of the server's
  node has no learners (its bootstrap and `ccApplyOk`), so a static-mode node state with an empty
  learner set could carry `dst ∈ reCfg`; but the clause is protocol-wide, so the fact must live
  with the node (its outbox, `Ready`: D19i's area) rather than in `isMessage`.
* *(C) A premise "no `MsgSnap`"* on the run.

*Recommendation:* (A). Not started: a design decision (the user's (A) assumed voters only).

**(A) adopted (the user, 2026-10-18); carrying it out stopped on the file boundary.** The fact
`dst ∈ T` cannot be proved from `raft.go`'s send path and the protocol files alone:
`maybeSendSnapshot` knows `to ∈ domSet s.progress`, but nothing at the `raft.go` level bounds the
progress keys. The protocol's static configuration (`CfgStatic γ c`: `c.incoming = γ.reCfg`, no
outgoing) leaves the learners free (`CfgStatic.simple γ lrn` for any `lrn`), and every code proof
of a step builds `CfgM.simple γ.reCfg (domSet s.progress \ γ.reCfg)` from whatever the tracker
holds. Bounding it needs `domSet s.progress ⊆ T` as an invariant of the node in the static mode,
kept by `RawNode.ApplyConfChange` (whose static scope, `CCShrink`, only drops learners) and handed
to every `raft.Step` (`ownRawNode`, `InvRawnode`/`InvNode`, `RawNode__ApplyConfChange`): either
as a conjunct of `CfgStatic` (learners `⊆ T`, so every step proof discharges it from the node
state) or as a premise threaded from `RawNode.Step` down to `maybeSendSnapshot`. Both are in
`RawNode`'s files, which D19i part 1 is changing; so it waits for D19i part 1, with the server half.
The protocol half alone (`reTracked` in `RaftNames`, the `.snap` clause, the allocation's
argument) would leave the clause unprovable at its only send site, so it was not started either.

## D19q: the server's workload parameter (2026-10-18, carried out)

The user's choice (2026-10-18): parametrize the server by the request kinds admitted, so that
putget's instance keeps leases off (D19k's dead NOSPACE branch and D19n's guard `False` exactly as
before) and a later session can build a lease-enabled instance. Carried out, shape-preserving: no
axiom or `sorry` added or removed (319 / 12), no result renamed; statements now take the
workload, and the leases-off instance discharges its obligations with the earlier proofs.

**The parameter** (`SrvWorkload`, `KVModelDefs.lean`; pure):
- `admits : apply.IRRModel → Prop`, the requests the instance lets into the log. A plain request
  is now `plainReq W rq := plainCover rq ∧ W.admits rq`, where `plainCover` is D19k's `plainReq`
  unchanged (renamed): the requests the generic proofs cover (the KV model, `KVModel.lean`; the
  dead branch, `NoSpaceDead.lean`; the shapes, `WorkloadDefs.lean`), which stay stated over
  `plainCover` and so hold at every workload;
- `grant : w64 → Prop`, the lessor's grant guard; `srvGrantGuard W id := ⌜W.grant id⌝` is what
  `NewServer` gives `lease.NewLessor` and what `lessorOk W`'s `expiredC` carries;
- the instance's obligations: `admits_header` (admission ignores the header the server stamps,
  `apply.withHeader`: `reqPropOk_wire`), `admits_kv` (the KV writes `EtcdServer.Put`/
  `DeleteRange`/`Txn` propose are admitted: `putPermit_reqPropOk` and the delete and txn ones),
  `admits_cluster` (the monitors' `ClusterMemberAttrSet`/`ClusterVersionSet`:
  `srvMonitorPermit_of`).
- `SrvWorkload.noGrant W := ∀ id, ¬ W.grant id` (not a field: a premise, below).

**The instance** `putgetWorkload`: `admits` the kinds `putgetKind` (put, delete, txn, member
attributes, cluster version), `grant := False`; `plainCover_putget` (`plainReq putgetWorkload` is
`plainCover`: behaviour unchanged), `putgetWorkload_noGrant`.

**Where it lives.** In the KV names, `KVNames.wl`, beside the start values `c0`/`ch0`/`log0`: fixed
by whoever allocates the names (`srvReadNamesFresh_alloc`, `srvBootClient`/`srvRaftBoot_alloc`,
`srvBootOut`, `kvInv_alloc` take it), so every spec over `ρ`/`γk` is at `ρ.kv.wl` without a new
argument: `kvInv` keeps `plainLog γk.wl`, `reqPropOk γk` asks `plainReq γk.wl`. `lessorOk` takes
the workload (`lessorOk W l`), and so do `srvFieldsBuilt`/`srvFieldsBuiltNA` (at `ρ.kv.wl` in
`isServerBuilt`/`srvBuilt`; `srvFieldsAt` uses `ρ.kv.wl`); `lessorOk_of_lessorInv` and
`lessor_server_contract` take `W` and `W.noGrant`.

**The one design choice: `run`'s expired-lease receive.** With a non-`False` guard `run` receives a
slice of leases and calls `revokeExpiredLeases`, whose spec and axiom D19n removed. So `run`'s
proof needs, for now, that the workload grants nothing. Options were (a) a field
`noGrant` of `SrvWorkload` (no lease instance could then exist without changing the structure);
(b) a premise. Taken: (b), placed where it is used. `lessorOk W` carries `⌜W.noGrant⌝` (so `run`'s
receive refutes the bag's `∃ id, ⌜W.grant id⌝`), and `NewServer.spec` gains the premise
`ρ.rd.kv.wl.noGrant` (the only spec that changed beyond the threading). A lease instance is a
`SrvWorkload` as it stands; only the `run`/`NewServer` chain refuses it until the lease path is
proved.

**What a lease-enabled instance must provide** (the other session's unit; nothing of it built):
1. its `SrvWorkload`: `admits` including `LeaseGrant`/`LeaseRevoke` (and, if wanted, puts and
   transactions naming a lease), its `grant` (any pure predicate the appliers can establish for a
   committed `LeaseGrant`'s id; `fun _ => True` suffices for safety, since the `expiredC` bag's
   predicate is not tied to the slice), and the three obligations (`admits_header`, `admits_kv`,
   `admits_cluster`: immediate for a kind-based `admits`);
2. `plainCover` extended to the lease kinds (keeping `putgetWorkload` at the old set: give it its
   own predicate, or keep `putgetKind`, which already excludes the lease kinds, and add a lease
   clause per instance if leased puts are admitted), with the generic proofs over it extended:
   `backendStep_plain`/`chainStep_plain`/`applyStep_plain` (the KV model: a revoke deletes the
   lease's keys, so the model must know the lessor, or leased puts stay excluded and a revoke
   deletes nothing), `dispatchOk_of_plain`/`rqShape_of_plain` (and the apply package's `rqOk`,
   whose `.leaseGrant` clause is `False`), and NoSpaceDead's `dispatchStep_start`/
   `dispatchAnswer_notNoSpace` for the lease kinds' answers (their errors told apart from
   `ErrNoSpace`'s: `applyErrVars` already tells `ErrNoSpace` from `lease.ErrLeaseNotFound`, D19k;
   any other error the lease appliers return needs its message cell, through `etc/gen-init.py`);
3. the lease path: `revokeExpiredLeases` with a true spec (back in `run`'s callees, `etc/
   link-lean-first-server.txt`), `run`'s receive branch calling it, then `⌜W.noGrant⌝` dropped
   from `lessorOk` and `NewServer.spec`'s premise with it;
4. the appliers' `Grant` premise (`lease.leaseGranted E.γ.leases id`, D19n): from `W.grant id` of a
   committed `LeaseGrant` (the KV invariant's `plainLog W` gives `plainReq W` of each committed
   request).

## D19p carried out: raft's tracked bound; `createMergedSnapshotMessage` and `sendMergedSnap` removed (2026-10-18)

**The one-member restriction (the user, 2026-10-18):** kept for now (`bootOk`'s `reTracked = some
{id}`, a premise of `NewServer.spec`), until a first end-to-end result is closed (putget's adequacy
theorem). Then generalizing the server's proofs to a multi-member cluster is a priority: a real
`MsgSnap` path (`createMergedSnapshotMessage`/`sendMergedSnap` with true specs, raft's snapshot
receive), learners and membership changes beyond `ccApplyOk`'s add-an-existing-member, peers in
`transportEffectsOk`'s scope.

The user chose D19p (A); carried out after D19i part 1 landed, all of it (raft, protocol, server).

* **The protocol.** `RaftNames` gains `reTracked : Option (GSet w64)` and `reTracked_ok` (a bound
  covers the voters and is the static mode's). `TrackedOk γ c id` (`Protocol/Ghost.lean`): `c`'s
  voters and learners, and the node, within the bound. `isMessage`'s `.snap` clause gains
  `⌜m.dst ≠ m.src ∧ ∀ T, γ.reTracked = some T → m.src ∈ T ∧ m.dst ∈ T⌝` (the sender as well as
  the receiver: what lets a one-member bound refute the message; `dst ≠ src` is `SnapOk`'s). It is
  proved at the broadcast (`replOk_message`, `ownRaftGhost_step_send_apps`/`_win`) from a new
  premise of `StepC.sendApps`/`StepC.win` and `StepCF.sendApps`: a snapshot goes to a voter or
  learner of the step's configuration. `Step` (voters only) cannot state it: `step_of_stepC` stays,
  `stepC_of_step`/`step_iff_stepC` are gone, and so are `stepR_static` and `ownRaftGhost_stepR`
  (unused); the `Step`-form ghost steps (`ownRaftGhost_step`, `_step_0/1/1c`) take `StepC` at a
  static configuration within the bound. In the dynamic mode the bound is `none`.
* **The static-mode tracker invariant: a conjunct next to `CfgStatic`** (the choice asked for):
  `ghostRest .static c id` is `⌜CfgStatic γ c ∧ TrackedOk γ c id⌝`, `c` the tracker's configuration
  (so `domSet s.progress ⊆ T`, `ownRaftPhysC_dom`). Kept by every step at `c`
  (`ghost_stepCD`), by a snapshot's restore (`GMode.SnapOk`'s static clause gains the snapshot's
  ids within the bound; `RawNode` takes no `MsgSnap`), and by `RawNode.ApplyConfChange`'s shrinking
  change (`applyCC_of_shrink` now says the learners only shrink, `applyConfChange.specS` returns the
  new progress map's ids, `trackedOk_shrink`), whose ghost step is now a `StepC` at the new tracker
  (`applyCCOk_step`). `ownRawNode_static_open` hands it out; `ownRawNode_intro_static` takes it
  (`Bootstrap`, `RestartNode`: a tracker of voters only, `TrackedOk.of_sub`).
* **The code.** `ReplSends` gains the snapshot's peer (`m.dst ∈ domSet s.progress`, proved at
  `maybeSendSnapshot` from its `pr`); the branch lemmas that build `StepCF.sendApps`/`StepC.win`
  take `domSet s.progress ⊆ c.voters ∪ c.learners` (`ownRaftPhysC_dom`). Nothing in `node.go`'s
  `run`/`advancec` changed.
* **The allocation.** `ownRaftGhost_alloc_core` takes the bound; `ownRaftGhost_alloc_gen`/`_alloc`
  (the register, the dynamic results) give `none`, `ownRaftGhost_alloc_boot` (a new cluster)
  `some cfg`, the bootstrap peers.
* **The server.** `bootOk` gains `γ.reTracked = some {id}` (`"%Hone"`: a one-member cluster, what
  `alloc_boot` gives for the peers `[id]`; a new premise of `NewServer.spec` through `bootstrap`'s
  contract, pure, on the names). `srvEr`'s message predicate is `srvMsgNoSnap` (no `MsgSnap`),
  proved in `rnEnvOk_of_cluster` from `isRaftMsg_not_snap`; `isRNMsgSnapC`'s bag carries messages
  of type `MsgSnap` (`processMessages`' branch), so `srvApplyAllBuilt`/`isServerApplyAll` record
  that `msgSnapC` never delivers (`srvMsgSnapC_false`), and `applyAll`'s receive is dead: it no
  longer calls `createMergedSnapshotMessage`/`sendMergedSnap`, whose specs and axioms are removed
  (`sendMergedSnap` had no other caller).

Trust base: two axioms fewer (`EtcdServer.createMergedSnapshotMessage`, `EtcdServer.sendMergedSnap`);
`etc/tcb-baseline.txt` (325 axioms, 8 `sorry`s after the merged `lean` changes) and the `server`
collection updated with `--check --update` on purpose; the raft collection unchanged.

## Item 9, stage 3: the closed theorem's hypotheses beyond `io.EOF` (D19r, 2026-10-18 · proposed, stopped)

Stage 2 (`Main`'s WP, `examples/putget`) is proved over named premises
(`Proof/github_com/mit_pdos/etcd_grove/examples/putget/Defs.lean`, `putget.premises`). Stage 3
was to state the closed theorem through `goose_adequacy_start` with D19a's kinds of hypotheses
only, plus the one approved exception `EofFromIoInit` (`isPkgInit io ⊢ v3rpc.eofVar`, for the
proposed Perennial `io` change). Going through every premise `Main` passes on shows five more
that are not of D19a's kinds, two of them false of Go as stated, so a closed theorem taking them
would be vacuous. Nothing was changed for them; the closed theorem is not written. Each needs a
decision:

- **(A) `∀ n : Loc, rnStopOk n`** (`NewServer.spec`, from `NodeStartSpec`): `{{ True }}
  n.Stop() {{ True }}` for every location. False of Go: `(*node).Stop` on `nil` (or on memory
  that is not a node) faults. As a hypothesis it is not refutable inside the logic, but it does
  not hold in the model, so the theorem would say nothing. It is used only to build the raft
  wrapper's interface contract (`isRaftNodeIfc`'s `Stop` clause, `NodeBridge.lean`), at the node
  `StartNode` returned, which `raftNode.onStop` calls (on `<-r.stopped` and the loop's error
  exits). Options: (a1) restate the premise at started nodes only (`□ ∀ γ id nl, isNode γ id nl
  -∗ rnStopOk nl`, a triple of a called function whose postcondition is `True`); (a2) prove
  `node.Stop` from raft's model (its `run` loop's stop case); (a3) make `onStop` unreachable in
  the runs covered (as D19m did for `run`'s shutdown: `r.stopped` a bag with predicate `False`)
  and drop the clause. Recommendation: (a1), the smallest statement change.
- **(B) `bootstrapContract`'s `memStorReg`** (`bootOk`'s `"#Hreg" ∷ memStorReg bv.storage' γs`):
  the contract hands out a persistent element of the storage registry at the class-fixed name
  `MemStorReg.memStorRegName`, whose authority nobody holds. A triple whose postcondition adds an
  element to a fixed ghost name without its authority is not a frame-preserving update: false in
  the model (a frame may hold the authority at `∅`). It is not "fresh resources at fresh names"
  (D19a). Options: (b1) `bootstrapContract` takes the registry's authority (`memStorRegAuth M`)
  and gives it back with the new storage (as raft's `NewMemoryStorage` does for the register),
  `NewServer.spec` takes `∃ M, memStorRegAuth M`, and `Main` allocates the registry (as the
  register's `Main` does); (b2) `bootOk` gives the registry's name existentially (the wrapper
  already keys the node by `γn.reg`, `rnIsNode`), and `NewServer.spec` loses `[MemStorReg GF]`.
  Recommendation: (b1), smaller (two statements, the allocation in `Main`).
- **(C) `rnRaftStatusOk`** (`sync.isMutex (globalAddr raftStatusMu) (∃ f, raftStatus ↦ f)`):
  a fact about etcdserver's package variables, which no initializer theorem gives. Not a pure
  fact or a triple. Option: make it a conjunct of `etcdserver`'s package fact, proved by its
  generated initializer (`etc/gen-init.py`'s `SPECIAL`, as D19j did for v3rpc's progress
  interval lock, `sync.init_RWMutex`); the `init()` that registers the `expvar` closure is
  names-only, so the fact holds when the mutex is allocated, before it.
- **(D) `waitClosecInit`** (`pkg/wait`'s `closec`, a broadcast channel closed by its `init`):
  kept out of the package's fact because the broadcast idiom needs later credits (`HeapGS
  HasLC.hasLC`), which the package-fact instances (at any `HasLC`) do not have
  (`TimeList.lean`). Options: (d1) restate it with a closed channel's invariant, as Perennial's
  `context.isClosedchanInit` (`inv closedchanN (ownChan γ Unit (.Closed []))`, no credits), and
  prove it in `wait`'s initializer; (d2) the package-fact instances at `HasLC.hasLC` for this
  package.
- **(E) `context.isClosedchanInit`** (Perennial's `context`): "kept out of `isInit` because it
  is ghost state" (`Perennial/Proof/context/Base.lean`); Perennial's `context.wp_initialize'`
  does not return it. Of `eofVar`'s kind: a Perennial change (the initializer returns it, or
  `isInit` keeps it), proposed independently, and meanwhile a named Prop as `EofFromIoInit`
  (`isPkgInit context ⊢ context.isClosedchanInit`, false under the current pin).

Also to settle for the closed theorem's statement (not blockers):
- **(F) `bootstrap`'s contract's configuration.** `putget.premises` states it for every
  configuration with the scalar fields `Main` sets (`cfgOk`), but `bootstrap` reads the
  configuration's URL slices and peer map, which `Main` allocates: as a hypothesis true of Go
  it should take their read-only points-tos (the triple's precondition `True` then becomes those
  resources), and the member id and bootstrap log `BootFacts` names are what Go computes from
  them.
- **(G) `[go_etcd_io.etcd.cache.v3.Assumptions]`**: `wp_NewServer` (and the client lemmas
  `grpcCfgOk_of_started`, `client_Put_own`) take the cache package's assumptions (their files'
  section variables), although `putget` does not import the cache. Satisfiable (an extra
  package's translated bodies), but out of place in a closed theorem about `putget`.

**Recommendation:** (A) a1, (B) b1, (C) and (D) d1 as local units (no Perennial change),
(E) a second named Prop beside `EofFromIoInit` with the Perennial proposal; then the closed
theorem is mechanical (the ghost-state bundle `putgetGF` as `registerGF`, the package table of
`putget`'s closure, `goose_adequacy_start` with `Ns` the read package's two names and `As =
["127.0.0.1:23790"]`, `putget.wp_initialize'` then `putget_Main`).

Choices made in stage 2 (no decision needed, recorded): (i) `context.Background()` is not an
`isContext` (its `Done()` is `nil`), so the client's end-to-end `Put`/`Get` lemmas
(`client_put_end_to_end`, `client_get_end_to_end`, `client_get_after_put`, the putget forms) now
take `ctxOk` (a context with the model, or a quiet one), which is all their proofs used;
`background_ctx` gives Background's. (ii) `net.Listener` was an axiomatized type with `sorry`
instances; `Code/net.toml` now translates the interface (as `Addr`), since `Main` keeps the
listener in a local variable. (iii) `Main` is linked by hand in `putget/Results.lean` (its callees'
results are in three packages' Links under different namespaces, which no `etc/gen-link.py` mode
combines).

## D19r carried out: the closed theorem of the adequacy example (2026-10-18)

The user approved D19r's recommendations; carried out on `raft-retarget`, each restatement checked
against the Go source:
- **(A)** `rnStopOkStarted` (`NodeBridge.lean`): `□ ∀ γn, rnIsNode γn -∗ rnStopOk γn.nl`, `Stop`
  of a node `StartNode` returned (its `run` loop running: `Stop` sends on `n.stop` or finds
  `n.done` closed, then waits for `n.done`; no panic), in place of `∀ n, rnStopOk n` in
  `NodeStartSpec` and `NewServer.spec`.
- **(B)** `bootstrapContract` takes the storage registry's authority at `∅` and `bootOk` gives it
  back with the new storage (`"Hrauth" ∷ memStorRegAuth {bv.storage' ↦ γs}`); `NewServer.spec`
  takes `memStorRegAuth ∅`; `Main` allocates the registry. **One deviation from the recommended
  `∃ M, memStorRegAuth M`:** the contract at an arbitrary `M` is false of Go (if `M` already maps
  the new storage's location, no update can add it), so the authority is taken empty: true of Go,
  and enough for a program with one server (a second `NewServer` would need the registry's
  invariant over allocated storages, as the register's `regStorInv`).
- **(C)** `raftStatusMu`/`raftStatus` translated (`Code/go_etcd_io/etcd/server/v3/etcdserver.toml`);
  `srvRaftInit` ends with the mutex's invariant over `raftStatus`, proved by the generated
  initializer (`etc/gen-init.py`'s `SPECIAL`: `sync.init_Mutex` after the allocations, before
  the names-only `init()` that registers the `expvar` closure); `NewServer` derives
  `rnRaftStatusOk` from its package fact.
- **(D)** `pkg/wait`'s fact `closecClosed` (`etcdserver/apply/Base.lean`): `closec`'s channel in an
  invariant at `Closed []` (under `context.closedchanN`, no later credits), proved by its
  initializer; `waitClosecInit` is that form (`waitClosecInit_of_pkg`); `waitBcast` (what `Wait`
  answers) and the read loop's `ApplyWait` answer (`bcastOrClosed`, `bcastOrClosed_receive`)
  admit it beside the broadcast idiom; `NewTimeList.spec` and `NewServer.spec` lose the premise.
- **(E)** `putget.EofFromIoInit` and `putget.ClosedchanFromContextInit` (`putget/Defs.lean`): named
  Props, false under the current Perennial pin (docstrings say so); hypotheses of `Main.spec` and
  of the closed theorem.
- **(F)** `bootstrapContract cfg U ...` takes `bootCfgRO cfg U` (the peer and client URL slices and
  the initial-cluster map with its slices, read-only; `BootURLs`); `putget.premises` states it at
  `Main`'s URLs (`urlsOk`: `[http://127.0.0.1:23800]`, `[http://127.0.0.1:23790]`,
  `{putget ↦ [peer]}`), and `BootFacts`' id and boot log are what Go computes from them.
- **The closed theorem** `putget_adequate` (`putget/Adequacy.lean`; restated as `putget_safe` in
  `Results.lean`) through `goose_adequacy_start` with the read package's two metric names and the
  client address, over a ghost-state bundle `putgetGF` (as `registerGF`, the disk FFI) and the
  program's package table (`putget/PkgTable.lean`, generated by `etc/gen-init.py`: each package's
  `GetIsPkgInitProp` proved once, from its imports'). Hypotheses: pure facts (`BootFacts`, the five
  effect/workload Props, `namesUnclaimed`/`addrsUnclaimed`, `n + 2 ≤ 2 ^ 31`,
  `n + 7 ≤ backend.wbInit`), semantics classes (`go.Semantics`, putget's and the cache's
  assumptions, `ServerMethodSets`, `AsTarget`, `Float64ToInt64Semantics`, `DialWithBalancerBody`,
  `ErrorStringLeaf`, `RpctypesEtcdErrorMethods`, `ErrorStringIsError`, `DeadlineExceededIsError`,
  `log.NewModel`), the triples `putget.premises` at every ghost-state instance (`heapAt hG lctx`:
  at the semantics' local context), the two marked Props, and `ContextReadErrs` (item 8's premise
  class of the read package's initializer: an entailment from `context`'s fact to
  `Canceled`/`DeadlineExceeded`'s method facts, of the same kind as the two marked Props but
  argued true today, since `context.isInit` holds the cells; listed here so it is not missed).
- **Trust base:** the closed theorem reaches the package initializers' trust-boundary axioms
  (`opaqueInitsOk`, `errorsNewVarsInit`, `<X>_init`; 157 baseline entries newly reached, none
  added) and six `sorry`s, all Perennial's own initializer proofs (`crypto/rand`, `errors`'
  `errorType`, `log`, `math/big`, `math`, `time`), as the register's closed theorem does.

## Multi-member before D20 (b) (the user, 2026-10-19)

With `putget_safe` closed (item 9), the next unit is the multi-member generalization of the
server's proofs (D19p's "one-member restriction": `bootOk`'s `reTracked = some {id}`, a real
`MsgSnap` path, learners and membership changes, peers in `transportEffectsOk`). D20 (b) (at-most-once
firing of a write, through a one-shot delivery token per `MsgProp` in raft's environment model) comes
after it and is built on the multi-member model, not on the one-member one. The watch session carries out (b),
after the multi-member unit (the user, 2026-10-19).

## Multi-member generalization: scope and staging (D21, 2026-10-19 · (A) adopted for D21a–f)

A design pass only (no Lean change); the next unit after `putget_safe`, before D20 (b) (the user,
2026-10-19). The question: what removing the one-member restriction takes, so that
`NewServer.spec` and everything under it, and a closed theorem of `putget_safe`'s shape, hold for
an N-member cluster, the other members modelled through raft's protocol and the transport's trust
assumption. Go citations are at the pins (etcd fork `8a24be2a3`, read with `git -C /shared/etcd
show 8a24be2a3:<path>`; raft `509271d`, `.lake/go-src/raft`). Note: `.lake/go-src/etcd` is *not*
at the etcd pin (it is at `0df483bee6`; `server.go` after line 990 is off by 10, and `raft.go`'s
`raftAdvancedC` is sent once there, closed at the pin).

### What is already general

Less depends on one member than the restriction's footprint suggests:
- **raft's protocol** is N-node and network-agnostic: allocation gives `ownRaftGhost` for any id set
  (`ownRaftGhost_alloc_boot`, `Protocol/Facts.lean:1595`), `isMessage` is persistent, so loss,
  duplication and reordering are free (`ghost_stepCD`, `Step.drain`); the safety results are over
  any two nodes (`Protocol/ResultsDyn.lean`).
- **raft's code**: `node.Step` is proved for peers' messages (`stepP = netP ∨ fwdP`,
  `InvNode.lean:394-515`): every type but `MsgSnap` (`netStepTypes`, `InvRawnode.lean:482`), a
  forwarded `MsgProp` owned (`fwdP`); the read index for any number of voters (`readAck`'s
  `QuorumAcked`, `node__ReadIndex.lean:15`); `raft.Step`'s `MsgSnap` branch (restore) proved, but
  not reachable from `RawNode`/`node` (stage S, `notes/STATUS.md`, "Snapshots at the public API").
  Precedent for a cluster: the register example's three in-process replicas over `deliver`
  (`examples/register/Cluster.lean`, `deliver.lean`: the wire's copy of a message, owned, so the
  half-owned responses of D8 are no obstacle).
- **The server**: `bootOk` takes any peer list `ps` (non-empty, `Nodup`, `id ∈ ps`, `γ.reCfg =
  listToSet ps`) but for `"%Hone"`; `NewServer`'s `AddRemote`/`AddPeer` loops are proved for any
  list (`NewServer.lean:657-700`); `srvCCPolicy`/`ccApplyOk` admit the N bootstrap `AddNode`s
  (each an `AddNode` of an existing member with its JSON context, id `0`); `run`'s
  `updateLeadership` and `applyEntryNormal`'s `Promote` prove both the leader and the follower
  branch; the read loop and the proposal path allow every error (`ErrLeaderChanged`, `ErrTimeout*`,
  `ErrProposalDropped`: `applyErrIs`, `BaseApply.lean:244-305`) and assume neither leadership nor
  that a proposal commits.

### Inventory: where one member is used

Paths under `Proof/go_etcd_io/etcd/server/v3/etcdserver/` unless said otherwise.

1. **`bootOk`'s `"%Hone"`** (`InvBoot.lean:147-149`, `γ.reTracked = some {id}`). Buys: raft sends
   no `MsgSnap` (`isRaftMsg_not_snap`, `InvBuild.lean:86-104`: the `.snap` clause's `src ≠ dst`,
   both in the bound). Used by `rnEnvOk_of_cluster` (`BuildGap.lean:119-144`, `E.M :=
   srvMsgNoSnap`), `NewServer.lean:843`, putget's `premises`/`Alloc` (`putget/Defs.lean:116`,
   `Alloc.lean:53`). Multi-member: a different reason no `MsgSnap` is sent (D21c (A)), or the
   snapshot path (D21c (B)).
2. **`srvMsgNoSnap` / `srvMsgSnapC_false`** (`InvBuild.lean:72-136`), `srvApplyAllBuilt`/
   `isServerApplyAll` (`InvStart.lean:146-151`, `InvApplyAll.lean:66-75`): `applyAll`'s `msgSnapC`
   receive dead (`EtcdServer__applyAll.lean:168-200`), so `createMergedSnapshotMessage` and
   `sendMergedSnap` were removed (D19p). Multi-member: the same lemma from D21c (A)'s fact, or true
   specs of both (D21c (B)): `snapshot_merge.go:32-80` (commits the KV, a backend snapshot streamed
   by a goroutine that panics on a failed close, `ep.confState` cloned, `m.Snapshot` overwritten
   with `ep.appliedi`), `server.go:1854-1892` (`inflightSnapshots`, `transport.SendSnapshot`, a
   `GoAttach` goroutine; `compactRaftLog` skips while a snapshot is in flight, `server.go:2150`).
3. **The server's message predicate drops what a receiver needs.** `rnEnvOk`
   (`InvRaftNode.lean:236-246`) turns a `Ready`'s message into `E.M m` from `msgOwn □ ∗ isRaftMsg
   ∗ termLB`, and `rn_ready_recv` (`InvRaftNode.lean:476-524`) drops the `rdCred` raft's
   `readyData` gives with each `MsgReadIndex` (`InvNode.lean:531-546`); `srvEr` keeps only
   `srvMsgNoSnap`. Multi-member: `E.M` keeps `isRaftMsg`, `termLB` and the read credit, what
   `node.Step`'s `netP` takes at the receiver. A `MsgTimeoutNow` needs a tick credit
   (`netP`), which `Ready` does not give (the register has a transfer budget); the server never
   transfers leadership in the runs covered (`MoveLeader` uncalled, `TryTransferLeadershipOnShutdown`
   only on `Stop`, dead since D19m), so raft sends no `MsgTimeoutNow` (only on a `MsgTransferLeader`,
   `raft.go` `stepLeader`) -- a raft-side fact to state, or the register's budget.
4. **No inbound path.** `EtcdServer.Process`, `IsIDRemoved`, `ReportUnreachable`,
   `ReportSnapshot` (`server.go:699-731`) are not translated, specified or linked; the server's
   node interface has no `Step` (`isRaftNodeIfc`, `InvRaftNode.lean:358-380`). They hide in the
   opaque `transportEffectsOk` (`InvBoot.lean:91-105`), premise of the three `rafthttp` axioms
   (`Transport.Start`/`AddPeer`/`AddRemote`), of `NewServer.spec` (`Spec/.../NewServer.lean:152`)
   and of putget's `Main`/`putget_safe`. With peers this premise is **not tenable as an opaque
   Prop**: an inbound `Process` calls `node.Step`, which changes the raft node the verified server
   owns, and needs `stepP`'s resources (`isMessage`, `termLB`, credits) that only the senders'
   `Ready`s produce. Multi-member: the transport's contract carries messages from `Send` to
   `Process` (D21b). Go: `Process` rejects a removed sender and a mismatched `To` with `403`
   (`server.go:701-716`), counts `MsgApp`, calls `s.r.Step`; stream readers route `MsgProp` to
   `propc`, others to `recvc`, dropping when full (`rafthttp/stream.go:525-557`, `peer.go:174-205`);
   the pipeline handler calls `Process` and panics the connection on a non-HTTP error
   (`http.go:148-169`); the snapshot handler saves the db file, then `Process(MsgSnap)`
   (`http.go:279-330`).
5. **`transportEffectsOk`'s `errMemberRemoved` reading** (D19m: "no well-behaved member says that
   of a member never removed; a one-member cluster has no peer"; `errorc` a bag with predicate
   `False`, `InvRun.lean:317-327`). With peers this is **false as stated**: a `403` for a
   misaddressed message (`To ≠` the receiver) is read as `errMemberRemoved` too
   (`rafthttp/util.go` `checkPostResponse`; `pipeline.go:165-171`, `snapshot_sender.go:110-114`;
   the pipeline handler does not check `X-Raft-To`, the stream handler does), and `run` stops on
   it (`server.go:844-847`). Filed: `issues/etcd-rafthttp-misaddressed-403-member-removed.md`.
   Multi-member, static membership: true under a deployment fact (every peer URL is served by the
   member it names), which an in-process cluster's delivery axiom states (D21b); or a fork fix.
6. **The conf-change policy** `srvCCPolicy` (`InvRequest.lean:296-298`: v1, id `0`, `ccBootOk`),
   `srvNoopEntry` (`:398-400`), `ccApplyOk` (`:276`), putget's `ccOk id` (`putget/Defs.lean:62`,
   at `{id}`), the axiom `EtcdServer.applyConfChange` (`removed = false`), `apply`'s `shouldStop =
   false` (`Spec/.../EtcdServer__apply.lean:51`), `run` never returning (D19m: `Cleanup`,
   `stopWithDelay` removed), `membership.localKept` (`api/membership/Defs.lean:120-141`), raft's
   static mode at the server (`rnEnvOk`'s `RNMode.static`; `CCShrink` only, `NodeBridge.lean:312`).
   These are **static-membership** restrictions, not one-member ones: they hold for N bootstrap
   members as they are (`ccOk` generalizes to `ccOk ps`). Runtime membership changes (D21d (B)):
   a dynamic-mode server (raft's `Bootstrap`/`StartNode` are static-only, `S/StartNode.lean:23`;
   dynamic mode has only `RestartNode` on empty storage and needs `StepDownOnRemoval`, pre-vote off,
   explicit leave-joint), the policy beyond id `0` (a user conf change's id is claimed by its
   proposer, `configure`, `server.go:1759-1796`), `applyConfChange` for every type
   (`server.go:2012-2085`: `RemoveNode` of self returns `removed`, `transport.RemovePeer`/
   `UpdatePeer`, `cluster.PromoteMember`), the membership package's writers (`AddMember`,
   `RemoveMember`, `UpdateRaftAttributes`, `PromoteMember`, `ValidateConfigurationChange`: not
   translated), and a stopping server (D19m (B), the "server open" token) for the removal path.
7. **Cluster-wide resources owned by one server.** `srvBootOut`/`srvRaftBoot_alloc`
   (`NewServerAlloc.lean:190-205`) give one `kvInv` (`InvRequest.lean:1055`, holding raft's unique
   `srvRLog`), one client `etcdKV`, the whole read budget `rdCred γ (2^64-2)` and `reRdFresh`'s
   authority (`srvRdFreshInv`, `:574`), and `kvWork` (`:1039`)/`entryWaitOk` (`:1757`) ask an
   `entryClaim` under *this server's* generator for every committed entry. With N members every
   member's apply thread applies every entry, and other members propose too (each member's
   `publishV3` `ClusterMemberAttrSet`, the leader's cluster version: `server.go:1803-1852`,
   `2216-2236`), so the KV invariant and the claims are the cluster's, the read budget and fresh
   tokens split per member. Request ids are unique across members only if the members' ids differ
   in their low 16 bits (`issues/etcd-request-id-member-prefix.md`, `idutil/id.go:56-71`).
8. **The read index's singleton shortcut** (`issues/raft-readindex-singleton-stale.md`, the fork's
   fix): only matters for one voter; the multi-voter path (`readAck`, heartbeats) is already proved.
   Nothing to do, but the read loop's 500ms resend and its `leaderChanged` branch, dead in practice
   today, become live (proved already).
9. **raft's `RawNode`/`node` take no `MsgSnap`; `Ready.Snapshot = null`** (`netStepTypes`;
   `readyData`'s `rd.Snapshot = null`, `InvNode.lean:544`; `applySnapshot.spec` only for `nil`,
   `Spec/.../EtcdServer__applySnapshot.lean:26-35`; `srvSnapState` only at `0`). Multi-member with
   snapshots: raft's stage S (S1 certificate on the message, S2 `MsgSnap` at `RawNode.Step`, S3 a
   pending snapshot through `Ready`/`Advance`, partly unverified code), and the server's receive:
   `applySnapshot` (`server.go:1011-1159`: `OpenSnapshotBackend`, `consistIndex.SetBackend`,
   `lessor.Recover`, `kv.Restore` of a backend with data -- D19l (v)'s option (C) --, the backend
   swap with the old one closed in a goroutine, `restoreAlarms`, `authStore.Recover`,
   `cluster.Recover`, `transport.RemoveAllPeers`/`AddPeer`; no waiter triggered for entries the
   snapshot covers).
10. **Names-only goroutines whose N > 1 branch differs**: `adjustTicks` (axiom "returns";
   `server.go:467-527`: with peers it polls `ActivePeers()` up to 5s, then advances
   `ElectionTicks-2` ticks; still true as stated), `bootstrap`'s `isMemberBootstrapped`
   (`cluster_util.go:41-55`, a network call to the peers' `/members`; inside `bootstrapContract`, a
   hypothesis triple, still true: it returns on errors), `monitorClusterVersions` (leader-only,
   HTTP to members; axiom "returns" under `srvMonitorPermit`), the lessor's checkpointer
   (`ckptEffectsOk`, leader-only, lease feature off in putget).
11. **putget**: `urlsOk` (one-entry `InitialPeerURLsMap`, `putget/Defs.lean:84-86`), `ccOk id`,
   `BootFacts` (`BootLogOk (ccOk id) [id] bootLog`), `premises`' `reCfg = reTracked = {id}`, the
   allocation for `{id}`, and `clientCfgOk` (one endpoint).

Also found (Go, liveness only, not filed): a `MsgSnap` dropped because `msgSnapC` is full
(`raft.go:374-384`; 16 slots) or sent to a missing peer (`transport.go:409-418`) gets no
`ReportSnapshot(Failure)`, so the leader keeps that follower in `StateSnapshot` until it loses
leadership; `configure` blocks on `<-resp.raftAdvanceC` with no select (`server.go:1780`), which
hangs a conf-change caller if the raft loop exits on `r.stopped` between handing out the apply and
closing the channel. Neither affects safety, which is what the specs state.

### Decisions

**D21a. The closed theorem's shape.** Perennial's Lean port has no distributed adequacy (only
`grove_ffi_single_node_adequacy`, "distributed adequacy theorems would need a distributed-language
semantics", `GroveFfi/Adequacy.lean:1-7`).
- *(A) N servers in one Go program* (`examples/putget3`: `Main` starts three `etcdserver`s on
  loopback ports, as putget starts one, and runs the client against one of them), through
  `goose_adequacy_start` as `putget_safe` and the register's closed theorem (three in-process
  replicas). The per-member specs are what they would be in any composition; only the closed
  theorem composes them.
- *(B) One server per program, the peers an environment*: the network as an invariant of messages
  some well-behaved peer sent. The peers' ghost steps must then happen somewhere: an axiom that
  the network delivers only `isMessage` messages is not a statement about this program, nor a
  premise of D19a's kinds; the theorem would be vacuous or need peers' ghost states owned by an
  environment that nothing runs.
- *(C) Distributed adequacy in Perennial* (Grove's Rocq `dist_adequacy`): N programs, one per
  node, with a network semantics; proposed to Perennial on its own (CLAUDE.md, "Changes to
  Perennial"), then (A)'s per-member specs carry over.
- *Recommendation:* (A) now, specs stated per member so that (C) reuses them; (C) proposed
  separately.

**D21b. The transport.** `rafthttp` stays names-only (translating it means net/http, streams,
pipelines: far larger than the server).
- *(A) A trusted network contract*, replacing the opaque `transportEffectsOk`: a cluster-level
  ghost network (per destination, the messages sent to it: each carrying what `node.Step`'s `netP`
  takes, a forwarded `MsgProp` one-shot and owned, others persistent with their credit one-shot);
  `isRNTransport`'s `Send` puts each `rnMsgOk` message in (a new axiom, `Transport.Send`); the
  restated `Start`/`AddPeer` axioms take the receiving server's `Process` triple (the `Raft`
  interface value the transport calls, as `deliver` calls `Node.Step`) and promise only calls of
  it with a fresh owned copy of a message of the network for that server (unmarshalled from the
  wire: the register's wire copy), `ReportUnreachable`/`ReportSnapshot` at any time, and nothing on
  `errorc` (true for correctly addressed peers in a static cluster: the issue above; the
  in-process program's URLs are its own listeners). `EtcdServer.Process` translated and proved
  (`IsIDRemoved` false of every member -- static -- , the `To` check, `node.Step`), as
  `ReportUnreachable`/`ReportSnapshot` (raft's are proved, `Link.lean:1614-1634`).
- *(B) Verify `rafthttp`* over Perennial's network model: very large; later, if ever.
- *(C) Keep `transportEffectsOk` opaque*: unsound with peers (inventory 4).
- *Recommendation:* (A).

**D21c. Snapshots (`MsgSnap`).**
- *(A) Excluded by a run bound, with a raft-side reason.* etcd compacts raft's log at
  `appliedi - SnapshotCatchUpEntries` (default 5000), else at `1` (`compactRaftLog`,
  `server.go:2142-2170`; after every 100-entry memory snapshot, `shouldSnapshotToMemory`); the
  apply thread applies at most `N` entries (D19b's receipt bound, `receiptBound GF ≤ N + 1`). With
  `N + |bootLog| ≤ SnapshotCatchUpEntries` the leader's storage keeps every index `≥ 1` (its dummy
  at `1`), and raft sends a `MsgSnap` only when `term(pr.Next - 1)` or `entries(pr.Next)` is
  compacted (`maybeSendAppend`, `raft.go:618-648`), i.e. only for `pr.Next = 1`. A raft invariant
  of the leader's tracker -- `pr.Next ≥ 2` for every peer, since every log holds the committed
  bootstrap prefix (term 1), so no `MsgApp` at `prevIndex ≥ 1` is rejected below it and `Match ≥
  1` in `StateReplicate` (`MaybeDecrTo`, `BecomeProbe`, `tracker/progress.go:130-145, 236-249`) --
  plus a storage fact (first index `≤ 2`, from the server's compaction bound through D19i's
  floor) gives "no `MsgSnap`", replacing `"%Hone"` in `srvMsgNoSnap`. A new pure premise of the
  closed theorem (the run bound against the configuration's `SnapshotCatchUpEntries`, of D19a's
  kind, as `N` itself). Cost: medium-large on raft's side (the tracker invariant through every
  `raft.Step` branch that touches progress, and message clauses for `MsgAppResp`'s reject index
  and hint); the first step is a pen-and-paper check that the invariant holds (findConflictByTerm
  over a compacted index, `pr.Match` after a reject, the probe after `MsgUnreachable`).
- *(B) The snapshot path*: raft's stage S (S1-S3) and the server's sender and receiver (inventory
  2, 9), the `rafthttp` snapshot stream in D21b's contract (the db file a backend snapshot of the
  sender's at the snapshot index), `kv.Restore`/`lessor.Recover`/`authStore.Recover`/
  `cluster.Recover` of a backend with data. Very large; lifts the run bound.
- *(C) A premise "no `MsgSnap`"* on the run: not of D19a's kinds (as D19o (C)).
- *Recommendation:* (A) for the first N-member closed theorem; (B) as its own track (T-S below),
  which D19p's priority list names ("a real `MsgSnap` path").

**D21d. Membership.**
- *(A) Static*: the N bootstrap members, no runtime conf change. Every item of inventory 6 stays
  as it is, generalized from `{id}` to `ps`.
- *(B) Runtime changes* (add, remove, promote, update; learners): inventory 6's list, dynamic mode
  at the server, a stopping server for self-removal.
- *Recommendation:* (A); (B) as track T-M, after T-S (a member added late needs the log from
  index 1, or a snapshot).

**D21e. Request ids across members** (`kvWork`'s claims, the wait registry).
- *(A) One claims map for the cluster*, keyed by the full id, each member's generator claiming
  under its prefix, with a pure premise on the member ids (their low 16 bits distinct and nonzero:
  `BootFacts`, decidable for putget3's computed ids).
- *(B) A fork fix* making ids unique across members (the issue's suggestion), then no premise.
- *(C) Per-member claims*, a foreign id ignored by the wait registry: false of Go when prefixes
  collide.
- *Recommendation:* (A); (B) only if the issue is fixed upstream.

**D21f. Clients, watches and leases with several members** (from the session that owns those
proofs; each checked against the code):
- watch: one server per stream (`watchConnFacts`/`isClientWatcher V w`, `client/v3/InvWatch.lean:
  291, 611`: `V.R` at one address, `V.R.γ.st = V.R.E.γ`); `noRetryableStreamErr` (`:170`) excludes
  `run`'s reconnection and resume (`issues/etcd-watch-resume-closing-substream.md`); the cache's
  `etcdReached`/`etcdRead`/`startRead` (`cache/v3/InvEtcd.lean:76,103`;
  `mvcc/InvWatchStore.lean:632`) are stated over the committed log while a member's stream serves
  its own applied store (a follower lags); progress (`RequestProgress`) is member-local;
  `v3rpc.runsNoRequireLeader` (`v3rpc/InvStreamInterceptor.lean:76`) excludes `monitorLeader`'s
  cancellation of require-leader streams, live once leadership can be lost;
- leases: leader-driven (expiry, revoke, checkpoints, `Promote`/`Demote`); D14h/D19n's guard is
  one-member in spirit; a follower's `LeaseKeepAlive`/`LeaseRenew` forward to the leader over HTTP
  (`v3_server.go:488-572`, names-only), hidden by `leaseKAStreamOk` (`client/v3/InvLessor.lean:
  140`); lease ids come from the same generator (D21e);
- client: `clientCfgOk` (`client/v3/InvClientNew.lean:165`) is one endpoint; balancing and the
  retry interceptor's not-sent retry may change the member.
- *(A) Pin them*: the client on one endpoint (`clientCfgOk` unchanged), watches on that member,
  leases off (`putgetWorkload`'s `noGrant`), `runsNoRequireLeader` kept as the deployment premise
  it is. Member-local facts stay true, since the client talks to one member whose apply thread
  follows the committed log (its `etcdKV` reads at a read-index point are the cluster's).
- *(B) Multi-endpoint now*: balancing, member-local vs cluster facts for watches and the cache,
  the lease forwarding path.
- *Recommendation:* (A) for this unit; (B) as track T-C.

### Stages (static membership, snapshots excluded: D21a-f (A))

Each small enough for one agent; dependencies in brackets.

- **M0. Pen-and-paper check of D21c (A)** [none]: the tracker invariant `pr.Next ≥ 2` and the
  storage's first index against raft v3.7's code (`findConflictByTerm` on a compacted term,
  `MaybeDecrTo`, `BecomeProbe` from each state, `becomeLeader`'s reset, `MsgUnreachable`,
  `MsgSnapStatus`); and "no `MsgTimeoutNow` without a `MsgTransferLeader`". Output: a note, or a
  stop for (B). No Lean.
- **M1. The sender's message bundle** [none]: `rnEnvOk`/`rn_ready_recv` keep `isRaftMsg`, `termLB`
  and the `MsgReadIndex` read credit in `E.M`; `srvEr`'s `E.M` becomes `srvMsgNet ∗ srvMsgNoSnap`
  (the latter still from `"%Hone"` until M3); the transport contract's `Send` premise unchanged.
  Server files only (`InvRaftNode`, `InvBuild`, `BuildGap`, `raftNode__start`). Small.
- **M2. The network contract and `Process`** [M1]: D21b (A): the ghost network, `Transport.Send`
  (new axiom), `Start`/`AddPeer`/`AddRemote` restated with the delivery promise, `Process`/
  `ReportUnreachable`/`ReportSnapshot` translated (`etcdserver.toml`) and proved, `IsIDRemoved`
  of a static cluster (the membership package's removed set empty: a `bootstrap` contract clause,
  `rnClusterOk`), `isRaftNodeIfc` gains `Step` (raft's `node.Step`), `transportEffectsOk` reduced
  to what it still covers (or gone). Medium-large; the register's `deliver` as template.
- **M3. No `MsgSnap` without compaction** [M0]: the raft invariant and message clauses (raft
  files: `raft.go`'s progress branches, `InvRaftPhys`, the protocol's `appResp` clause), the
  storage's first-index bound from the server's compaction (`compactRaftLog`, `snapshot`, D19i's
  floor), `srvMsgNoSnap` from them; `"%Hone"` removed from `bootOk`, `NewServer.spec` taking the
  run bound. Medium-large; raft-heavy. *Amended by M0 (2026-10-19, "D21 M0" below):* `pr.Next ≥ 2`
  is false in raft v3.7 (`issues/raft-stale-term-appresp-index-zero-ack.md`). M3 waits for the
  user's choice of a fork change, (A1) raft's fix or (A2) no compaction while `appliedi ≤
  SnapshotCatchUpEntries`, and a re-translation. Its invariant is (N), `firstIndex ≤ Next ≤
  lastIndex + 1`, in the form the choice gives. Its premise is `receiptBound GF ≤
  SnapshotCatchUpEntries + 1`, through the apply pool's count (`ep.appliedi ≤` tokens taken).
  `putget3` configures `SnapshotCatchUpEntries` at least as large as the theorem's step bound.
- **M4. The cluster's resources split** [none]: D21e (A); `kvInv`/`etcdKV` allocated once for the
  cluster (`srvRaftBoot_alloc` over `ps`), each member's `NewServer.spec` taking its share (its
  generator's claims under its prefix, its slice of `rdCred` and of `reRdFresh`, its node's
  `ownRaftGhost`), `kvWork`/`entryWaitOk` over the cluster's claims. Server files (`InvRequest`,
  `NewServerAlloc`, `NewServer`). Medium.
- **M5. putget3 and its closed theorem** [M2, M3, M4]: the Go program (three members, the fork
  pinned as putget's), its translation, `Main`'s proof, `putget3_safe` through
  `goose_adequacy_start` with the new pure premises (D21c's run bound, D21e's prefixes, the peer
  URLs). Medium.
- **M6. D20 (b): at-most-once `MsgProp`** [M2; its raft half after M1]: see below.

Parallelism: M0, M1 and M4 at once (disjoint: M0 no files, M1 the raft wrapper's files, M4 the
KV/allocation files); M2 after M1, alongside M3 (raft-side) and M4; M5 last. Collections:
`etc/tcb-collections/server.txt` tracks M1-M4; add one for putget3 in M5.

**Trust base (estimate).** Added: `rafthttp.Transport.Send` (1); `Start`/`AddPeer`/`AddRemote`
restated (0 net); possibly `membership.RaftCluster.IsIDRemoved` (1, unless its contract comes
from `bootstrap`'s premise). Removed: none in M1-M5 (`createMergedSnapshotMessage`/
`sendMergedSnap` stay out under D21c (A)). The opaque premise `transportEffectsOk` shrinks to the
transport's delivery axioms (a premise fewer of the closed theorem if it goes entirely). New pure
premises of the closed theorem: the run bound against `SnapshotCatchUpEntries`, the members' id
prefixes distinct, (as now) `N`. Track T-S adds about eight trust-boundary axioms
(`SendSnapshot`, `OpenSnapshotBackend`, the three `Recover`s, `RemoveAllPeers`, the backend
snapshot's stream, `kv.Restore` with data unless proved) and restores `createMergedSnapshotMessage`/
`sendMergedSnap` as true specs (proved or 2 axioms); track T-M about seven (the membership writers
unless translated, `RemovePeer`/`UpdatePeer`) and restores `Cleanup`/`stopWithDelay` as true specs.

### Where D20 (b) fits

Today a proposal's update is persistent and fires at every committed occurrence (`propAu`,
`Protocol/GhostState.lean:937-945`; `prop_collect`, `Facts.lean:754-762`); the per-proposal
ticket (`propTok`, `firstOcc`) was removed at stage R. In one member, nothing duplicates a
proposal; with peers a forwarded `MsgProp` crosses the network, which may duplicate in the
protocol's model (persistent `isMessage`). So (b) is: the network contract (M2) delivers a
forwarded `MsgProp` at most once (`fwdP` already takes it owned; the ghost network's entry for it
one-shot -- true of `rafthttp`, which writes each message once on a stream or pipeline and never
retries); raft's leader appends a `MsgProp`'s entries once; a deposit's ticket comes back, so the
first committed occurrence fires the update and a later one (none, by the above, but the protocol
need not know) fires nothing; the server's write specs then fire an ordinary update at most once.
Raft's protocol half (the ticket) can start after M1, in parallel with M2; the server half after
M2 (and M4, whose claims it touches). Stage M6.

### Later tracks

- **T-S, the snapshot path** (D21c (B)): raft's stage S, the server's sender (true specs of
  `createMergedSnapshotMessage`, `sendMergedSnap`), the transport's snapshot stream, the receiver's
  `applySnapshot`; lifts M3's run bound.
- **T-M, membership changes** (D21d (B)): after T-S.
- **T-C, clients, watches and leases across members** (D21f (B)): the client's balancing, watches
  and the cache over member-local applied stores, resume, require-leader streams, the lease path
  with leader forwarding; independent of T-S/T-M, after M5.

*Asked of the user:* D21a-f (recommendations: (A) each, (C) of D21a proposed to Perennial
separately), and whether M3 (the run bound) is an acceptable first step before T-S.

**D21 adopted (the user, 2026-10-19):** (A) for all of D21a–f. Stages M0, M1 and M4 start in parallel.

## D21 M0: the no-`MsgSnap` argument checked (2026-10-19)

Stage M0 of D21: D21c (A) checked by hand against the code. No Lean changes. Citations: raft at
the fork's `509271dac` (`.lake/go-src/raft`); etcd at `8a24be2a3` (`git -C /shared/etcd show
8a24be2a3:server/etcdserver/<f>`).

**Verdict: D21c (A) as written is false.** The tracker invariant "`pr.Next ≥ 2` for every peer"
does not hold in raft v3.7. A leader can set a peer's `Next` to 1. Once its log is compacted at
index 1, it then sends a `MsgSnap`. etcd compacts at index 1 after 101 applied entries, whatever
`SnapshotCatchUpEntries` is. Reproduced with a Go test and filed:
`issues/raft-stale-term-appresp-index-zero-ack.md`. The rest of the argument holds: the storage
bound, the other progress transitions, the reject path and `MsgTimeoutNow`. Below are the exact
conditions, the counterexample, two corrected options (each needs a change to the fork) and a
recommendation. **Asked of the user.** M3 waits for the answer.

### When raft sends a `MsgSnap`

Only `maybeSendAppend` (`raft.go:618-661`) calls `maybeSendSnapshot` (`raft.go:666-690`), from
two places:
- `term(pr.Next - 1)` fails (`:623-629`). By `raftLog.term` (`log.go:387-413`), that happens iff
  `Next - 1 + 1 < firstIndex` (`ErrCompacted`) or `Next - 1 > lastIndex` (`ErrUnavailable`), or if
  storage loses the entry to a concurrent `Compact` between the check and `storage.Term`.
- `entries(pr.Next)` fails (`:639-648`). By `log.go:415-420` and `mustCheckOutOfBounds`
  (`:551-565`), that happens iff `firstIndex ≤ lastIndex` and `Next < firstIndex`.

`maybeSendSnapshot` then returns without sending if `!pr.RecentActive` (`:667`). Otherwise it
sends `MsgSnap` (`:686-689`), or panics if storage's snapshot is empty (`:680-681`). So the leader
needs, for every peer whose append is not paused,

> **(N)** `firstIndex_max ≤ pr.Next ≤ lastIndex + 1`

where `firstIndex_max` is the largest first index its `MemoryStorage` ever has. A pending
snapshot in `unstable` would also count (`log.go:300`), but none exists: no member ever sends a
`MsgSnap`, so none receives one. This is an induction over the cluster's run, part of the same
invariant.

### The storage side: `firstIndex ≤ 2` under a run bound (holds)

- Boot: a fresh `MemoryStorage` holds only the dummy at 0 (first index 1). `StartNode` →
  `Bootstrap` (`bootstrap.go:32-80`) appends the `B = |peers|` `AddNode` entries at term 1,
  indices `1..B`, and commits them. etcd's fresh path calls no `ApplySnapshot`
  (`etcdserver/bootstrap.go:726-735` calls it only for a WAL snapshot). `ep.appliedi` starts at
  the snapshot index, 0 (`server.go:804-807`).
- Writers of the first index: `Compact` in `compactRaftLog` (`server.go:2142-2170`), called only
  from `snapshotIfNeededAndCompactRaftLog` (`:1220-1228`), and `ApplySnapshot` for a received
  snapshot (`etcdserver/raft.go:277`), which does not happen here. `CreateSnapshot` (`:2112`)
  does not move the first index.
- The trigger: the in-memory snapshot fires every `memorySnapshotCount = 100` applied entries
  (`:116`, `:1235-1236`), whatever `SnapshotCount` is. `compactRaftLog` then calls
  `Compact(compacti)` with `compacti = 1` when `appliedi ≤ SnapshotCatchUpEntries`, and
  `compacti = appliedi - SnapshotCatchUpEntries` otherwise (`:2156-2160`). `Compact(1)` keeps
  index 1 as the dummy (`storage.go:268-288`): the first index becomes 2, and a later `Compact(1)`
  is `ErrCompacted`, returned silently.
- So: **if every member's `ep.appliedi` stays at most `SnapshotCatchUpEntries`, every member's
  first index is at most 2 throughout, and is 1 until its 101st applied entry.** The alternative
  the task suggested, a run with fewer than `SnapshotCount` entries, does not avoid compaction,
  because the in-memory snapshot ignores `SnapshotCount`. A bound below 101 entries would keep
  the first index at 1, but as a receipt bound it is far too small for the theorem to say
  anything. Restarts: D21 does not mention them. The argument assumes each member boots once
  from an empty data directory, as `putget3` does (a Goose program has no crash). After a restart,
  `ApplySnapshot` of a WAL snapshot sets the first index past 2.

### The tracker side: `pr.Next ≥ 2` is false

All writes to `Next` (`tracker/progress.go`; the protocol's callers in `raft.go`):
- `reset` (`raft.go:781-805`, from `becomeLeader`, `:937-948`): `Next = lastIndex + 1 ≥ B + 1`.
  Fine.
- `SentEntries` (`progress.go:164-187`): `Next += |ents|`, where `ents` comes from
  `entries(Next)`. This only increases `Next`, and keeps it at most `lastIndex + 1`.
- `MaybeUpdate(n)` (`:205-213`): `Next = max(Next, n + 1)`. This only increases `Next`; the upper
  bound below needs `n ≤ lastIndex`.
- `BecomeReplicate` (`:146-149`) and `BecomeProbe` (`:130-143`, outside `StateSnapshot`):
  `Next = Match + 1`. **This is 1 when `Match = 0`.**
- `MaybeDecrTo` (`:226-253`): in `StateReplicate`, `Next = Match + 1`. In `StateProbe`,
  `Next = max(min(rejected, hint + 1), Match + 1)`, applied only if `rejected = Next - 1`.
- `BecomeSnapshot` (`:153-158`): only from `maybeSendSnapshot`, which never runs (induction).
- Membership: `initProgress` (`confchange/confchange.go:263`, `Next = max(LastIndex, 1)`) runs
  only for a new id. In a static cluster, re-applying the boot `AddNode`s finds every id present
  (`makeVoter`, `:178-189`), so `Next` is untouched. `switchToConfig` (`raft.go:1971-2020`) only
  sends.

The counterexample is at `BecomeReplicate`, `raft.go:1519-1522`. In `stepLeader`, a non-rejecting
`MsgAppResp` with `pr.Match == m.Index && pr.State == StateProbe` moves the peer to
`StateReplicate`. A voter sends exactly such a response, `Index = 0` and not a reject, at its own
term, to answer a `MsgApp` or `MsgHeartbeat` of a lower term when check-quorum or pre-vote is on
(`raft.go:1133-1156`). etcd always enables check-quorum (`etcdserver/bootstrap.go:572`).

The run: leader 1 of term 1 sends a `MsgApp` to node 2, which is delayed. Node 1 wins term 2 with
node 2's vote. The stale `MsgApp` then reaches node 2, which answers `MsgAppResp{Term 2, Index 0}`.
That answer reaches node 1 before node 2's answer to node 1's term-2 probe, while node 2's progress
is still `StateProbe` with `Match = 0`. Node 1 sets `Next = 1`. The loop at `:1556-1561` calls
`maybeSendAppend`; `term(0)` is `ErrCompacted` once the first index is 2; `RecentActive` was set
by this response (`:1380`); so node 1 sends a `MsgSnap`. The issue's
`TestLeaderIndexZeroAckSendsSnapshot` reproduces it: the leader's progress becomes
`StateSnapshot match=0 next=4 pendingSnap=3` and it sends `MsgSnap` at index 3. Upstream's
`TestLeaderAppResp` (`raft_test.go:2243-2248`) expects this transition, from a probe at
`Next = 3`. In the protocol model the run needs only reordering and delay, which `isMessage`
already allows.

The rest of D21c's sketch holds, given that no `Index = 0` acknowledgement moves a peer to
`StateReplicate` (fix (1) below):
- **Replicate implies `Match ≥ 1`.** A peer enters `StateReplicate` either through
  `MaybeUpdate(n)` returning true, which needs `n > Match ≥ 0`, or (with fix (1)) only when
  `Next = Match + 1` already. `Match` never decreases within a term. So `BecomeProbe` from
  `StateReplicate` (`MsgUnreachable`, `:1621-1626`; a rejection in `StateReplicate`,
  `:1503-1507`) gives `Next = Match + 1 ≥ 2`. `MsgSnapStatus` returns at `:1604` outside
  `StateSnapshot`, so a `ReportSnapshot` at any time is harmless.
- **The reject path keeps `Next ≥ 2`.** Two facts about logs: every member's log has term 1 at
  indices `1..B`, since those entries are committed at boot, so they are never truncated, and
  `Compact(1)` keeps term 1 at index 1; and every entry at an index `≥ 1` has a term `≥ 1`.
  A follower answers an `m.Index < committed_f` with an ack (`:1788-1790`, `committed_f ≥ B`).
  For `m.Index ≤ B ≤ lastIndex_f`, both logs have term 1 at `m.Index`, so `maybeAppend` succeeds.
  So it rejects only at `m.Index > B`, giving `rejected ≥ 2`. Its hint (`:1815-1820`) is
  `findConflictByTerm(min(m.Index, lastIndex_f), m.LogTerm)` (`log.go:182-194`). With
  `m.LogTerm ≥ 1`, the walk stops at an index `≥ B ≥ 1` (term 1 there) with a term `≥ 1`.
  The leader's own walk (`:1406-1501`, `findConflictByTerm(hint, hintTerm)`) also stops at an
  index `≥ min(hint, B) ≥ 1`, or returns `hint` if `hintTerm = 0`. So `nextProbeIdx ≥ 1` and
  `min(rejected, nextProbeIdx + 1) ≥ 2`. (D21c's question "`findConflictByTerm` over a compacted
  index": the term check at the first index minus 1, here at most 1, is never reached, because
  the walk stops at `B` or above.)
- **Upper bound `Next ≤ lastIndex + 1`** (a new clause, not in D21c, needed against
  `ErrUnavailable`). It holds if every non-rejecting `MsgAppResp` of the leader's term has
  `Index ≤ lastIndex_L`. An accept (`:1792-1793`) answers this leader's own `MsgApp` (one leader
  per term), so `prev + |ents|` is at most the leader's last index then, and the leader never
  truncates its own log. A commit ack (`:1789`) carries `committed_f`, which is at most
  `lastIndex_L` by `leader_completeness` (`Protocol/LeaderCompleteness.lean`) with
  `raft_dyn_committed_agree`. The stale-term answer carries 0. `handleSnapshot`'s answers never
  occur.

### `MsgTimeoutNow` (checked: holds)

`sendTimeoutNow` (`raft.go:2049-2051`) is called only from `stepLeader`: at `:1565-1568`, when
`m.From == r.leadTransferee`, and at `:1652-1654`. `leadTransferee` is set only at `:1652`, in the
`MsgTransferLeader` case (`reset` and `abortLeaderTransfer`, `:2053`, clear it). A
`MsgTransferLeader` comes only from `node.TransferLeadership` (`node.go:604`) or
`RawNode.TransferLeader` (`rawnode.go:542`), or from a follower forwarding one it stepped
(`raft.go:1734-1740`). etcd calls `TransferLeadership` only in `MoveLeader` (`server.go:1248-1265`).
That is reached from `TryTransferLeadershipOnShutdown` (`:1286-1313`, on `Stop`) and from the
Maintenance gRPC `MoveLeader` (`v3rpc/maintenance.go:307-312`). The putget client calls neither,
and `Stop` is dead (D19m). So no `MsgTimeoutNow` is sent: a fact about the run, stated
in M3 (or M2) at raft's `Step` as "no `MsgTransferLeader` is stepped".

### Corrected options (D21c (A′); each changes the fork)

- **(A1) Fix raft in the fork**, issue fix (1): at `raft.go:1519`, take the shortcut only when
  `pr.Next == pr.Match + 1`. raft's suite passes except `TestLeaderAppResp`'s fourth case, which
  pins the current behavior; the fork updates that case. M3 then proves (N) as
  **`Next ≥ 2 ∧ (State = Replicate → Match ≥ 1) ∧ Next ≤ lastIndex + 1`** at the leader for every
  peer, plus `State ≠ Snapshot`. The message clauses it needs: a reject of term `T` has
  `Index > B`, `RejectHint ≥ 1`, and a `LogTerm` that is either 0 or the follower's term at the
  hint; a non-reject has `Index ≤ lastIndex` of term `T`'s leader. The storage side shows first
  index `≤ 2`. Cost: what D21c planned, plus the upper bound.
- **(A2) Never compact in the fork's etcd while `snapi ≤ SnapshotCatchUpEntries`**: return before
  `Compact` in `compactRaftLog` instead of compacting at 1. The first index then stays 1 under the
  run bound. (N)'s lower half becomes `Next ≥ 1`, which follows from `Match < Next`
  (`progress.go:37`). raft is unchanged, and `Next = 1` gives a `MsgApp` from index 0
  (`term(0) = 0` from the dummy), not a `MsgSnap`. M3 needs only the upper bound and the storage
  fact; the reject-path clauses go away. But the change has no purpose outside the proof: it
  keeps one entry in memory, and the raft bug stays in the verified code.
- **(B)** (D21c (B), T-S) stays as it was. **(C)**, a premise "no `MsgSnap`", stays rejected.
- *Recommendation:* **(A1)**. It fixes a bug that is reproduced and filed, and the fork has so
  far carried only such fixes (`issues/raft-readindex-singleton-stale.md`). The extra cost over
  (A2), the reject clauses, is what D21c had already planned. (A2) is the fallback if the user
  prefers not to change raft's behavior that upstream's test pins. Both need a re-translation
  (`etc/goose.py`) before M3.

### The premise the closed theorem needs

Each member applies one write token per entry (`srvWTPool`, `InvApplier.lean:653`: `a` tokens
taken, `a < receiptBound GF`). `appliedi` starts at 0, and each batch is contiguous and starts at
`appliedi + 1` (etcd panics otherwise). With an apply-thread clause
`ep.appliedi ≤ a` (new in M3), every member has `appliedi < receiptBound GF` throughout. So the
pure premise is

> **`receiptBound GF ≤ SnapshotCatchUpEntries + 1`**, the latter the configured value of every
> member (all equal in `putget3`).

The receipt clause on raft's log, D19b stage 5 design (P), would give the same bound in D21c's
form, `receiptBound GF + B ≤ SnapshotCatchUpEntries + 1`. The apply pool already exists and does
not involve `B`, so M3 should use it. With etcd's default (`DefaultSnapshotCatchUpEntries =
5000`, `server.go:85`, the value `putget` uses), this premise limits the theorem to executions of
at most 5001 receipts, likely too few to boot a server. So `putget3` should set
`SnapshotCatchUpEntries` to at least the step bound the theorem already assumes
(e.g. `1 << 40`, D19b's tightest). The premise then follows from the existing receipt
bound, and the program, not a hypothesis, pays for it. `SnapshotCount` does not matter.

### The M3 stage text, corrected

M3 now depends on the choice between (A1) and (A2) (and the fork change plus re-translation). Its
invariant is (N) in the chosen form, not `pr.Next ≥ 2` alone. Its premise is the one above. The
stage's text in D21 is amended to say so.

*M0 carried out (2026-10-19).* No Lean change. Output: this note, the amended M3 text, and
`issues/raft-stale-term-appresp-index-zero-ack.md`. Stopped on (A1)/(A2) for the user.

## The key-value store's porcupine test (2026-10-19)

**The example.** The register became a key-value store (the user's request: Put/Get/Append, a
randomized porcupine test proved never to fail, still several raft nodes, runnable). It keeps
the register's proof structure (minting, slots, the persistent proposal updates over raft's
log) with the store's state as the fold of the history; the encoding packs the key's length
into the header, so `opKey` and the freshness argument are unchanged.

**The library's atomic update in `Check`.** lintest's `applySpec` gives the library a one-shot
atomic update (Perennial's `<<{ }>>` triple) at mask `⊤ \ Eapp`; the store's specs take an Iris
`AU` at `kvMask`, which they may open and abort. Neither weakens to the other. Options: (a)
change `applySpec` to an Iris `AU` (`Run`'s proof changes); (b) change the store's specs to
one-shot updates (their proofs open the update inside raft's persistent proposal update, where
aborting is needed); (c) in `Check`, a copy of the store's state in an invariant with the
client's half, the store's `AU` built from the driver's update and committed with it. (c) is
taken: local to `Check`'s proof, no shared spec changes.

**Operation credits.** The register's `Put`/`Get` took an operation credit each (sequence
numbers below `2^64`); the driver passes nothing per call but the input. The Go code now stops a
replica at `maxSeq` (an infinite loop, as `fits` does for the log), so the specs need no credit.

**Perennial gaps** (to propose there, each on its own): `context`'s `isPkgInit` should contain
`isClosedchanInit` (then neither porcupine's nor raft's initialization is re-proved here); `allG`
should have a code for iris-lean's `NaInvF` (then the porcupine results lose `[NaInvG GF]`).
## D21 M1 carried out: the sender's message bundle (2026-10-19)

Stage M1 of D21, as staged; no design choice beyond the text. The server's `E.M` keeps, for each
message a `Ready` hands out, the message read-only, `isRaftMsg`, `termLB` and the read credit
(`srvMsgNet`, `InvBuild.lean`), with `srvMsgNoSnap` beside it (from `"%Hone"` until M3); the transport
contract's `Send` premise is unchanged in text (`[∗list] rnMsgOk E m`). One consequence the stage
text did not spell out: since the read credit is one-shot, `rnMsgOk` and `E.M` are no longer
persistent (`rnMsgOk E m := msgAt m to ty ∗ E.M m`; it was `□ E.M m`), so the wrapper's code
threads them: `processMessages`'s loop owns the not-yet-read messages' bundles, and `start`'s
leader send is a join that hands the bundles on to the follower's send. `msgSnapC`'s bag holds
them owned, `srvMsgSnapC_false` unchanged in statement. Not carried (M2's, and M0's
`MsgTimeoutNow` fact): `NetMsgOk` (the receiver's), a `MsgTimeoutNow`'s tick credit, a forwarded
`MsgProp` owned (`fwdP`). Trust base unchanged.

**D21c′ (the user, 2026-10-19): (A1).** Raft is fixed in the fork (the probe-to-replicate shortcut
only when `pr.Next == pr.Match + 1`; `TestLeaderAppResp` case 4 updated); M3 proves `Next ≥ 2`,
replicate ⇒ `Match ≥ 1` and `Next ≤ lastIndex + 1`, over the premise `receiptBound ≤
SnapshotCatchUpEntries + 1` (`putget3` sets `SnapshotCatchUpEntries` large).

## D21 M2: the network contract designed; stopped on the receiver's facts (D21g) and `Process`'s callees (D21h) (2026-10-19)

Stage M2 of D21, design pass and translation check; no Lean change. Two things D21b did not
foresee stop the stage, since both change specs or the trust base beyond D21b's estimate:
**D21g** and **D21h** below, asked of the user. Everything else is settled here, so the stage can
resume as soon as they are answered and M4 has committed (the regeneration rebuilds everything
above the etcd translation, and `NewServer.lean`/putget's `Main` are M4's while it runs).

### The translation (checked in a scratch copy, not regenerated)

Pinned translator, etcd at the pin, **no fork change needed**. Configuration changes (nine
generated files change, one new names-only package):
- `Code/go_etcd_io/etcd/server/v3/etcdserver.toml`: `translate` gains `EtcdServer.Process`,
  `EtcdServer.IsIDRemoved`, `EtcdServer.ReportUnreachable`, `EtcdServer.ReportSnapshot` and the
  promoted wrappers `raftNode.Step`, `raftNodeConfig.Step`, `raftNode.ReportUnreachable`,
  `raftNodeConfig.ReportUnreachable`, `raftNode.ReportSnapshot`, `raftNodeConfig.ReportSnapshot`
  (the `MethodUnfold`s down to `raft.Node`, as for `Propose`); `imports` gains
  `go.etcd.io/etcd/server/v3/etcdserver/api/etcdhttp/types` (`httptypes.NewHTTPError`, the two
  `403` branches).
- `etc/goose.py` (the etcd project's `packages`): `.../etcdserver/api/etcdhttp/types`, names-only,
  with `Code/go_etcd_io/etcd/server/v3/etcdserver/api/etcdhttp/types.toml` a copy of
  `v2stats.toml` (`translate = ["!*"]`). It joins etcdserver's imported packages, so
  `etc/gen-init.py` must cover it (no package variables expected).
- `Code/go_etcd_io/etcd/server/v3/etcdserver/api/membership.toml`: `RaftCluster.IsIDRemoved`, with
  its body (`c.Lock()`, deferred `Unlock`, `c.removed[id]`).

`Process`'s body (`server.go:699-721`) calls, on its live path: `s.Logger()` (translated),
`s.cluster.IsIDRemoved(From)`, `s.MemberID()` (translated), and for a `MsgApp`
`s.stats.RecvAppendReq(types.ID(From).String(), proto.Size(m))`, then `s.r.Step(ctx, m)`. The
`403` branches (`zap.String`, `lg.Warn`, `httptypes.NewHTTPError`, `http.StatusForbidden`) are
dead under the contract below.

### The contract (D21b (A), made precise)

Generic in what a message carries, so that D20 (b) plugs in without restating any axiom
(`Proof/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/Net.lean`, to be written):

- **The payload** `NetPayload GF`: `P : MsgSt → IProp GF` (persistent, what the receiver may
  rely on, read as often as the message is delivered), `O : MsgSt → IProp GF` (one-shot),
  `once : MsgSt → Prop` (delivered at most once), and `dup : ∀ st, ¬ once st → ⊢ |==> O st` (a
  duplicate of another message gets its one-shot part anew).
- **The network's names** `NetNames GF`: the payload `N`, a ghost name `g` for the members'
  slots, and the URL directory `dir : w64 → List GoString`. `netSlot γn id` (exclusive) is
  member `id`'s registration, allocated once for the cluster's ids (`netAlloc`, a ghost update in
  the closed theorem's allocation; putget's one member included).
- **A message sent** `netBundle N m`: `∃ st, msgOwn m □ st ∗ □ N.P st ∗ N.O st` (the sender's
  message read-only for good: the transport's writer goroutines marshal it after `Send` returns).
- **A message received** by member `id` at `ml`: `∃ st st', msgPtsC ml (own 1) (own 1) true st' ∗
  ⌜wireEq st st' ∧ st.msg.To' = id⌝ ∗ □ N.P st ∗ N.O st` -- a fresh copy (unmarshalled:
  `wireEq` is equality of the scalars, entries, context and snapshot, not of the `Responses`
  pointers), owned with its entries' slots and capacity (what `fwdP` and a `MsgApp`'s `netP`
  take), of a message sent into the network to `id`.
- **The receiver's handler** `netRaftOk γn id r` (persistent): `r`'s `Process(ctx, ml)` for
  `ctx` a context the node API takes (`nodeCtx`; rafthttp passes `context.TODO()` and the peer's
  `context.WithCancel(context.Background())`) and a received message, returning some error;
  `IsIDRemoved(id')`, `ReportUnreachable(id')`, `ReportSnapshot(id', s)` from `True`.
- **Axioms.** `rafthttp.Transport.Send` (new): `{{ transportStarted γn t ∗ sl ↦* msL ∗
  [∗list] m ∈ msL, netBundle γn.N m }} Send {{ True }}` (`isRNTransport`'s `Send` then derived for
  any `E` whose `E.M m` gives `netBundle`). `Start` (restated): `transportEffectsOk` replaced by
  `netSlot γn tv.ID' ∗ □ netRaftOk γn tv.ID' tv.Raft'`; what the axiom asserts of the Go code: the
  transport's goroutines call `tv.Raft'` only as `netRaftOk` admits (`Process` with a message of
  the network for `tv.ID'`, each sent message possibly lost, at most once if `once`, possibly
  duplicated otherwise; the reports and `IsIDRemoved` at any time) and send nothing on `ErrorC`.
  `AddPeer`/`AddRemote(id, us)` (restated): `transportEffectsOk` replaced by `ss = γn.dir id`.
- **Why true of rafthttp** (`transport.go`, `peer.go`, `stream.go`, `pipeline.go`, `http.go` at
  the pin): `Send` routes by `m.To` to the peer added for it, which posts to that peer's URLs;
  every write is attempted once (stream writer and pipeline drop on error or a full buffer, report
  `ReportUnreachable`, never retry), and a reader decodes each message once into a fresh
  `raftpb.Message`, so a message is delivered at most once; the receiving transport's handler
  hands it to its own `Raft.Process`. Realizable: per sent message, an invariant allocated at
  `Send` holding `O st` or the transport's delivery token. Nothing reaches `ErrorC` because no
  member says another was removed (static) and no message reaches the wrong member: the
  deployment fact that every URL of `γn.dir id` is served by the transport holding `id`'s slot,
  which excludes `issues/etcd-rafthttp-misaddressed-403-member-removed.md`'s run. It is stated
  where the handler is served (M5: `putget3` serves each member's raft handler on that member's
  own listener) -- in M2, with one member, no `AddPeer` or `AddRemote` runs.
- **`transportEffectsOk` goes** (from `InvBoot.lean`, the three axioms, `NewServer.spec`, putget's
  `Main` and `putget_safe`); `ckptEffectsOk` stays. `NewServer.spec` takes the member's slot and
  the network's names instead.

**The server's instance** `srvNet γ bud`: `P st := isRaftMsg γ st ∗ termLB bud st.msg.Term' ∗
⌜SentOk st⌝` (D21g), `O st := rdCred γ (if st.msg.Type' = MsgReadIndex then 1 else 0)`, `once st :=
st.msg.Type' = MsgReadIndex`, `dup` from `rdCred_zero_upd`. `srvEr`'s `E.M` gives `netBundle`.

**`Process`'s proof** (from the received message): `IsIDRemoved` is false (below), `To = id` by the
promise, so both `403` branches are dead; a `MsgApp` calls `RecvAppendReq` and `proto.Size` (D21h);
then `s.r.Step`, i.e. raft's `node.Step` with `stepP γ.node γ.id ml`: a `MsgProp` is `fwdP` (the
copy owned, `isMessage (absMsg .propose ...)` from `isRaftMsg`), any other type `netP` (`NetMsgOk
id` from `SentOk` and `To = id`; a pre-vote's `reBoot ≠ []` from `bootOk`'s bootstrap log;
`termLB`; the read credit `O st`; the tick credit `0`, since `SentOk` excludes `MsgTimeoutNow`).
`ReportUnreachable`/`ReportSnapshot` are raft's (`node.ReportUnreachable`/`ReportSnapshot`, proved).
`isRaftNodeIfc` gains `Step` (`{{ nodeCtx ctx cd ∗ stepP γ.node γ.id ml }} … {{ err, nodeErr cd err
}}`, from `node.Step.spec`) and the two reports. `netRaftOk` is proved at `tr.Start()` inside
`NewServer` from the fields `Process` reads, persisted there (`s.cluster`, `s.stats`, `s.lgMu`'s
logger, the member id, `s.r`'s embedded `Node`; `s.r.transport` is written later and not read).

**`IsIDRemoved` with no axiom**: `membership.rcLockInv` gains the `removed` map, empty
(`rcRemovedAddr c ↦ rm ∗ rm ↦$ ∅`); `RaftCluster.IsIDRemoved` is translated and proved `false`.
True of every writer in the run: only `RemoveMember` and `UnsafeLoad` (from `Recover`: a restart
or an applied snapshot) write `removed`, `cluster.go:258, 437`, all outside a static cluster
booted once without snapshots; the existing axioms that hold the lock
(`RaftCluster.String`, `SetVersionChangedNotifier`) and `bootstrap`'s contract
(`NewClusterFromURLsMap` makes the map empty) keep it. Their statements are unchanged in text; what
they assume grows by that clause, true of each.

### Where D20 (b) plugs in

The payload is the only server-specific part of the contract, so (b) changes the instance, not an
axiom: `once st` becomes `st.msg.Type' = MsgReadIndex ∨ st.msg.Type' = MsgProp`, and `O st` gains,
for a forwarded `MsgProp`, its one-shot proposal ticket (raft's half of (b): `readyData` hands out
the ticket with each forwarded `MsgProp`, `fwdP` takes it, the first committed occurrence fires
the update with it). `Send`, `Start`, `AddPeer`, `AddRemote` and `netRaftOk`'s shape stay;
`Process`'s proof passes `O st` on to `fwdP` as it passes the read credit to `netP`. `dup` is
unaffected (a `MsgProp` is then `once`, so the transport never duplicates it -- true of rafthttp,
as for every message).

### D21g. The receiver's `NetMsgOk`: where it comes from (asked of the user)

`node.Step`'s `netP` takes `NetMsgOk id st` (`InvRawnode.lean:501`): the type among
`netStepTypes`, and for a stamped type `To = id`, `Term ≠ 0`, `From ≠ 0`, `From ≠ id` for the
leader-to-follower types and rejections, an unstamped type at term `0`, a transfer request empty.
The register checks it at the transport (`deliverable`, `examples/register/cluster.go:40-64`);
etcd's `Process` checks only `To` (and the sender not removed). The sender knows the rest, but
raft's `readyData` does not say it: each message comes with `msgOwn`, `isRaftMsg` (its protocol
abstraction: `isMessage` gives `src ≠ 0` for some types, nothing about `To ≠ From` or the term
being stamped) and `termLB`. So does a `MsgTimeoutNow`'s tick credit, which no sender has: M0 found
that no `MsgTimeoutNow` is sent because nothing steps a `MsgTransferLeader`, a fact about the run
that raft's specs do not state. M1 left `NetMsgOk` "the receiver's"; with `Process` it cannot be.
- *(A) A raft-side outbox fact.* `readyData` gives, per message, `SentOk id st`: `From = id ≠ 0`,
  `To ≠ id`, the type one of `App`, `AppResp`, `Vote(Resp)`, `PreVote(Resp)`, `Heartbeat(Resp)`,
  `ReadIndex(Resp)`, `Prop`, `Snap`; `Term ≠ 0` but for `Prop`/`ReadIndex`, which are at `0`;
  never `MsgTimeoutNow` or `MsgTransferLeader`. Proved as a clause of `ownRaftPhys` beside
  `"%Hout_term"` (`OutTermOk`) and `AAMsgOk`, from `send` (it stamps `From = r.id`; `SendOk` gives `To ≠ id`
  for every message of `r.msgs`, and `readyWithoutAccept` hands out of `r.msgsAfterAppend` only
  those with `To ≠ r.id`, `rawnode.go:175-182`), carried through `readyWithoutAccept`/
  `acceptReady` and node's `readyData`; a response's term needs a fact of its own (the node's
  term is nonzero once it answers a stamped message). The transfer half needs a node mode with transfers off:
  `leadTransferee = 0` invariant, `MsgTransferLeader` excluded from what `Step` takes and
  `TransferLeadership` from the node API in that mode (the server calls neither: `MoveLeader` is
  uncalled, D19m), so `sendTimeoutNow` is dead. Raft's specs gain a clause (stronger
  postconditions); no trust-base change. Medium; in raft's files that M3 also edits
  (`InvRaftPhys`, `raft.go`'s proofs), so done by M3's agent or after it (stage **M2r**).
- *(B) Weaken `netP`*: `RawNode.Step` proved without `NetMsgOk`'s clauses, raft checking what it
  needs (it rejects local types and unknown responders, `rawnode.go`), the rest from `isMessage`.
  Larger: `raft.Step`'s proofs use the clauses (a `MsgApp` from itself, an unstamped term), and a
  `MsgTimeoutNow` still needs a credit, so the transfer half of (A) remains.
- *(C) A premise "every message raft hands out is `SentOk`"*: not of D19a's kinds; rejected as
  D21c (C).
- *Recommendation:* **(A)**, as stage M2r before M2's server half, sequenced with M3 (same files).

### D21h. `Process`'s live callees outside the estimate (asked of the user)

D21b's trust-base estimate (`Transport.Send` new; `Start`/`AddPeer`/`AddRemote` restated;
possibly `IsIDRemoved`, now 0, above) missed two calls on `Process`'s `MsgApp` path:
`v2stats.ServerStats.RecvAppendReq` (names-only; `v2stats/server.go:91-110`: its lock, the
leader's name and start time, `recvRateQueue.Insert` (`queue.go`, its own `RWMutex`, a
200-slot ring), the counter; no panic) and `proto.Size` of a `*raftpb.Message` (protobuf's
reflection; `proto.Size.spec` and `proto.SizeEntry.spec` cover etcdserverpb requests and raft
entries only).
- *(A) Two trust-boundary axioms*, of the kind already there: `v2stats.ServerStats.RecvAppendReq`
  "returns" (as `ServerStats.BecomeLeader`), and `proto.SizeMessage` (as `proto.SizeEntry`: a
  message at any fraction, returns `n ≥ 0`, the message back). +2.
- *(B) Verify `RecvAppendReq`*: translate `v2stats` with bodies (`ServerStats`, `statsQueue`,
  `RequestStats`, `NewServerStats`, `BecomeLeader`, `SendAppendReq`), the lock invariant over the
  stats and the queue, `time.Now`; `NewServerStats`/`BecomeLeader` become proofs. +1
  (`proto.SizeMessage`, unavoidable: protobuf is names-only), −2 (`NewServerStats`, `BecomeLeader`).
  Medium, independent of D21.
- *Recommendation:* **(A)** for M2; (B) later, if wanted, as its own unit.

### Trust base, revised estimate for M2

Added: `rafthttp.Transport.Send`, `v2stats.ServerStats.RecvAppendReq` and `proto.SizeMessage`
(D21h (A)); restated: `Transport.Start`/`AddPeer`/`AddRemote`; `IsIDRemoved` proved. Removed: the
premise `transportEffectsOk` (from `NewServer.spec` and `putget_safe`). Raft's specs strengthened
by D21g (A).

*Stopped (2026-10-19).* Asked of the user: D21g (recommendation (A), stage M2r with M3) and D21h
(recommendation (A)). Next, once answered and M4 committed: regenerate with the configuration
above, then M2 as designed here.

**D21g, D21h (the user, 2026-10-19): (A), (A).** Two more choices came up in M2's server half.
- **The transport's concurrency bound, (A).** `Transport.Start` takes `K = 2 ^ 29` copies of a
  resource `R` belonging to the receiver. The transport calls into the receiver's `Raft`
  (`Process`, `IsIDRemoved`, the two reports) at most `K` at a time; each call borrows one `R` and
  gives it back. The server's `R` is an `lgMu` reader slot (`srvLgReader`), because `Process`
  begins with `s.Logger()`. The transport gets `2 ^ 29` of `lgMu`'s `2 ^ 30` slots. The bound is
  true of Go only physically: each call is a goroutine with its own stack, and past `2 ^ 30`
  concurrent readers Go's `RWMutex` itself fails. rafthttp's structure gives no bound, since a
  cancelled pipeline post leaves its handler running.
- **The peer-URL directory.** `bootstrapContract`/`bootOk` take `dir : w64 → List GoString`. The
  remotes' records and a strengthened `Members()` triple give each member's URLs as `dir` of its
  id: the records bootstrap made name each member's own URLs, D21b's deployment fact.
  `NewServer.spec` takes `γn.dir = dir`, and putget's premises state the contract at its one
  member's URL.

The raft side (M2r, a separate agent) provides `SentMsgOk` as a conjunct of `isRaftMsg` under
`γ.reNoSnap`. It also provides `NetMsgOk.of_sent`, `SentMsgOk.ne_timeoutNow`/`ne_transferLeader`
and `isMessage_propose_ctx`. Leader transfer is off in the same mode, so `netP` takes
`MsgTransferLeader → reNoSnap = false`.

**D21 M4 carried out (2026-10-19):** D21e (A) as stated, with two choices the text left open, both
internal to the proofs (no spec's meaning for a client changes, no trust-base change):
- *How a generator shares the cluster's map.* The issued ids' map's authority is the cluster's
  (`idClusterInv`); a second cluster map records, per member prefix, the ids that member issued,
  and each generator owns its prefix's element, so it knows a new id is in no map (its prefix's
  ids are exactly its element's; the map's other prefixes differ). The premise's distinctness is
  what gives each member its own element.
- *Whose claimer's fact the apply thread reads.* The facts are per prefix (`Φs`, the cluster's
  choice): a member's own floor fact (`srvFloorFact E`) speaks of its own store's certificates,
  so another member's apply thread cannot use it. The apply thread uses the claim's floor for an id
  of its own prefix and the empty floor (`idxCert_nil`) for another's; a registered id is of the
  member's prefix (`reqWaitR`'s new clause, from `Next`), so the waiter's floor is the claim's.
  The other way, a cluster-level floor (a committed prefix the entry follows) would need raft's
  "a later proposal commits after a committed prefix" through the protocol, for no gain while the
  client talks to one member (D21f (A)).
The read budget splits `2 ^ 48` per member (fewer than `2 ^ 16` members, from the premise). Files:
`pkg/v3/idutil/` (`Defs`, `Lemmas`, `NewGenerator`, `Generator__Next`, and the two specs),
`etcdserver/` (`InvRequest`, `InvProposer`, `ProposerLemmas`, `BuildAlloc`, `NewServerAlloc`,
`NewServer`, `EtcdServer__applyEntryNormal`, `EtcdServer__processInternalRaftRequestOnce`, the
`NewServer` spec), putget's `Alloc` and `Main`.

**D21 M3 carried out (2026-10-19):** stage M3 as amended by M0 and D21c′ (A1): the fork's fix
pinned (`c8217eb9`), (N) proved in (A1)'s form, `"%Hone"` removed, the run bound
`receiptBound ≤ SnapshotCatchUpEntries + 1` taken through the apply pool's count. The text left
the following open; each choice is recorded here.
- *Where (N) lives: a mode, not an unconditional invariant.* (N) holds only of a cluster started
  from a bootstrap log whose storage is never compacted past index `1`, so it is conditional on a
  flag of the raft struct's ghost state, `NGhost.ns` ("no-snapshot mode"), set once by `Bootstrap`
  (`ownRaftPhys_set_ns`) and kept by every step. At a leader in the mode `PrLo` holds of every
  peer (`Next ≥ 2`, replicate ⇒ `Match ≥ 1`, not `StateSnapshot`), in `PrvalsOk` beside D11's
  `PrOk` (`Next ≤ lastIndex + 1`). The flag is the cluster's `RaftNames.reNoSnap` (`NsLink` in
  `ghostRest`, both modes; `reNoSnap_ok`: only with a bootstrap log), chosen at the allocation
  (`ownRaftGhost_alloc_boot`'s new argument). Outside the mode (the register, `RestartNode`, the
  dynamic mode) nothing changes.
- *The storage's first index: a cap on the `MemoryStorage`.* "First index `≤ 2`" is the storage's
  boundary at most `1`. The `MemoryStorage` gets a ghost cap (`MemStorNames.cap`, chosen at
  `NewMemoryStorage`, `2^64` for no cap): the boundary never passes it (`memCutInv`'s `Hccap`),
  so `Compact` and `ApplySnapshot` take `index ≤ cap` as a premise; `StorageModel` gains
  `storCap st k` (a persistent "never past `k`", `storCut_cap`), the register's `False`. Raft's
  struct keeps `storCap storage 1` in the mode (`NsCap`), which makes `maybeSendAppend`'s
  `ErrCompacted` branches dead (`storPast_cap`). The alternative, raft's `storFloor`/`storCut`
  alone, gives no upper bound.
- *The reject path.* As M0's "Corrected options" says, through a message clause: `isMessage` of a
  rejecting `appResp` in a cluster with a bootstrap log has `|reBoot| < Index` and
  `1 ≤ RejectHint ≤ Index`; the step relations (`Model.Step`, `StepC`, `StepR`, `StepCF`) take
  `RejHintOk` at `appReject` (the hint from `findConflictByTerm`, whose spec now states the walk
  stops at an index `≥ 1` when the log's term at `1` is at most the probe's term), and the leader
  side reads its term at index `1` (`ownRaftGhost_term1`: the boot entries' term `1`). The
  hint's term (`LogTerm`) is not needed: `findConflictByTerm` at the leader stops at `≥ 1` by the
  same term-at-`1` fact.
- *What raft promises a `Ready`'s messages.* `isRaftMsg` gains the clause `γ.reNoSnap = true →
  Type ≠ MsgSnap`, from the outbox's no-snapshot fact (`LogNsOk`, kept by `send`: `SendOk`'s
  `MsgSnap` clause takes `ns = false`, which `maybeSendSnapshot` has) through
  `outboxRelP_isRaftMsg`; `ownRawNodeReady` keeps it (`Hnsout`). The server's `srvMsgNoSnap` is
  then `isRaftMsg_not_snap` at `reNoSnap = true`.
- *Two raft premises the mode adds.* `raft.Step` takes `m.Type' = MsgSnap → ns = false` (its
  callers' messages are no `MsgSnap`: `NetMsgOk`, local types); `applyConfChange` takes "in the
  mode a leader's last index is `≥ 2`" (a peer it starts tracking probes at `Next = lastIndex`),
  which its callers get from the ghost state (`ownRaftGhost_leader_last`: the leader's campaign
  log holds the bootstrap log and is a strict prefix of its log). `handleSnapshot`/`restore`/
  `maybeSendSnapshot` take `ns = false` (dead in the mode).
- *The server's compaction (trust base: `compactRaftLog`'s contract restated).* The contract now
  names `SnapshotCatchUpEntries` (`scu`, read-only, which its body reads) and requires the
  compaction index its body computes (`snapi - scu` past `scu`, else `1`) to be at most the
  storage's cap: `Compact.spec`'s new premise, so the contract stays true of the code. The apply
  thread discharges it at index `1 ≤ cap`: `srvWTPool` gains a monotone counter of the tokens
  taken (`srvWTPool_take_at`, `srvWTPool_bound`), the apply thread keeps its lower bound at the
  applied index (`srvWTAt`, through `apply`/`applyEntries`/`applyAll`/`run`'s `applyRes`), so
  `ai < receiptBound ≤ scu + 1`. `isServerApplyAll` keeps `scu` with the bound; `NewServer.spec`
  takes `receiptBound ≤ (SnapshotCatchUpEntries, 5000 for 0) + 1` (D21 M0's premise; `start`
  sets the default); `start`/`Start` take `ai₀ = 0` (the counter starts at `0`);
  `monitorStorageVersion`'s contract is over the counted pool (its statement's ghost name only).
  The cap `1` is `bootOk`'s (`"%Hnosnap"`: `γ.reNoSnap = true ∧ γs.cap = 1`, in place of
  `"%Hone"`), a premise of `NewServer.spec` through `bootstrap`'s contract (`NewMemoryStorage`'s
  spec holds at every cap), and putget's `premises` give the contract at `γ.reNoSnap = true`
  instead of the tracked bound.
- *putget's configuration (a Go change).* With etcd's default `5000` the premise would limit
  `putget_safe` to about 5000 steps; `putget.go` sets `SnapshotCatchUpEntries: 1 << 48` (M0's
  recommendation for `putget3`, applied to putget), so the premise follows from
  `receiptBound ≤ 2^48`, and `putget_safe`'s statement is unchanged.
`reTracked` (D19p) stays in `RaftNames` and `isMessage`'s snapshot clause, unused by the server.
Trust base: the axioms and `sorry`s are the same by name (486, 8); two axioms' statements
changed (`compactRaftLog`, `monitorStorageVersion`), and `bootstrap`'s contract (a premise) says
`γs.cap = 1` and the mode instead of `reTracked`.

**D21 M2r carried out (2026-10-19):** D21g (A), raft's side, with M2 (the server's half) using it.
The text left the following open; each choice is recorded here. Trust base unchanged.
- *Where the promise is carried: `isRaftMsg`, not `readyData`.* `isRaftMsg` gains a second pure
  conjunct, `γ.reNoSnap = true → SentMsgOk st`. The server's `srvMsgNet` already carries
  `isRaftMsg` to the network, so `readyData`'s shape and the server's consumers did not change.
  Because `isRaftMsg` is also said of the self-addressed responses `acceptReady` queues,
  `SentMsgOk` has no `To ≠ id`. It has `From ≠ To` but for a `MsgReadIndex`, a vote or pre-vote
  response and an accepting `MsgAppResp`, which is what `NetMsgOk` asks at the destination. It has
  no `From = sender`: a forwarded `MsgReadIndex` keeps its requester (`send` stamps `From` only
  when it is `0`).
- *How it is proved: a per-message invariant of `ownRaftPhys`* (`XfOk s (msgs ++ msgsAA)`). In
  the no-snapshot mode every queued message is `SentMsgOk`, proved at `send` from `SendOk` and
  the node's term being past `0` (a new fact of the mode: `Bootstrap` sets it at term `1`, and
  the term only grows).
- *The transfer mode: the same cluster flag, a second per-node flag.* The flag is `reNoSnap`
  ("the server's mode": no snapshot, no transfer), since etcd needs both and the register
  neither. A separate cluster flag would add allocation plumbing for no client. The node keeps
  its own `NGhost.xf`, not `ns`, for this reason: setting the mode needs the queues free of
  `MsgTimeoutNow`/forwarded `MsgTransferLeader`, which nothing at `Bootstrap` can show (the
  queues are sealed and the abstract outbox drops those types). `xf` is therefore on from
  `newRaft`, whose queues are empty, and turned off by a ghost step (`ownRaftPhysC_xf_off`)
  outside the mode (`RestartNode`, `Bootstrap` at `reNoSnap = false`). Setting `ns` needs
  `xf = true` and an empty abstract outbox, which then empties the queues
  (`outboxRel_nil_types`). `NsLink` ties both flags to `reNoSnap`. With `xf` on: `leadTransferee = 0`;
  `send`'s clause (c), the model-less types, takes `xf = false`; `raft.Step` (`RestMsgOk`),
  `stepLeader` and `stepFollower` take `MsgTransferLeader` only with `xf = false`;
  `sendTimeoutNow` and the transferee's store take it too. `stepLeader`'s `MsgAppResp` branch
  (`From = leadTransferee`) is dead with `xf` on, since `From ≠ 0`.
- *The API's premises (D21g (A)'s "excluded in that mode").* `RawNode.Step`:
  `MsgTransferLeader → γ.reNoSnap = false`. `RawNode.TransferLeader` and
  `node.TransferLeadership`: `reNoSnap = false`. `netP`: its pre-vote pure conjunct became a
  pair with `MsgTransferLeader → reNoSnap = false`, so existing destructurings kept their shape.
  The register, outside the mode, records `reNoSnap = false` in `RegCC`/`isReplica`. `Main`
  derives it from the ghost state at allocation (nothing committed), as `RestartNode` does.
  Its exported results are unchanged.
- *The ghost steps keep the whole `NGhost`.* The `Hng` hypotheses (`ghost_stepCD`/`CDS`,
  `finish_branch`'s, `MsgSnap`'s posts) and `NetFrame.ns`/`LocalFrame.ns`/`HandleSnapResult.ns`
  now state `s'.gh = s.gh`, which they all had, so that `NsLink` is kept.
The interface M2 uses (agreed with it): `SentMsgOk`, `isRaftMsg_sent`, `NetMsgOk.of_sent` (all
but a `MsgProp`, which is `fwdP`'s), `SentMsgOk.ne_snap`/`ne_timeoutNow`/`ne_transferLeader`,
`isMessage_propose_ctx`.

## D21 M2 carried out: the network contract and `Process` (2026-10-19)

Stage M2's server half, as designed above with D21g (A) and D21h (A) and the two later choices
(the concurrency bound, the URL directory). The raft-side clause (M2r, a separate agent) gives
`SentMsgOk` inside `isRaftMsg`. The translation was regenerated with the configuration above
(`Process`, `IsIDRemoved`, the reports, the promoted `Step`/reports, `RaftCluster.IsIDRemoved`, the
names-only `etcdhttp/types`), and `etc/gen-init.py` was rerun for the new package.
- **The network** (`api/rafthttp/Net.lean`): `NetPayload`, `NetNames` (payload, slots, `dir`),
  `netSlot`, `netBundle`, `netRecv` (with `wireEq`), `netRaftOk` (each call borrows one of the
  receiver's `R`, `netProcSlots = 2 ^ 29`), `netTransport` (the started transport's `Send`/`Stop`),
  and `netNames_alloc`.
- **The axioms**, restated, not added. The started transport's `Send` lives in `Start`'s
  postcondition (`transportStarted γn t := netTransport ∗ isTransporter`, as `Send`/`Stop` did
  before), so D21b's "`Transport.Send` (new axiom)" is a restatement of `Start`, not a new
  declaration. `Start` takes the slot, `□ netRaftOk` and the `2 ^ 29` resources. `AddPeer`/
  `AddRemote` take `γn.dir id = ss`. `transportLive` is indexed by the network.
- **The server**: `srvNet` (the payload: `isRaftMsg ∗ termLB`, the read credit once for a
  `MsgReadIndex`) and `srvMsgNet_bundle` (`InvBuild.lean`). `InvNet.lean` holds `srvProcOk` (what
  the inbound path reads) and `stepP_of_recv` (a delivered message is `node.Step`'s `stepP`:
  `fwdP` for a `MsgProp`, `netP` otherwise, `NetMsgOk` from `SentMsgOk` and `To = id`).
  `EtcdServer.Process`/`IsIDRemoved`/`ReportUnreachable`/`ReportSnapshot` are proved (the two `403`
  branches dead), and so is `srv_netRaftOk` (`NetBridge.lean`). `membership.RaftCluster.IsIDRemoved`
  is proved `false` over `rcLockInv`'s new empty `removed` map.
- **Not `isRaftNodeIfc`**: the node's `Step` and reports are a separate contract `rnStepIfc`
  (`NodeBridge.lean`, from `node.Step`/`ReportUnreachable`/`ReportSnapshot`). The transport may call
  `Process` once it starts, which is before the server's committed index (needed by
  `isRaftNodeIfc`'s `ReadIndex`) and its wrapper (`isRaftNode`, which needs the transport) exist.
  For the same reason the wrapper's struct is split early (`rnFixed`, `rnFixed_split`: every field
  read-only but `transport` and `latestTickTs`), and `NodeStartSpec`'s installer takes the split
  form. `NodeStartSpec` returns `rnStepIfc` and the node field's value.
- **`NewServer`**: `NewServer.spec` drops `transportEffectsOk` and takes the network, the member's
  slot and `γn.N = srvNet γ bud ∧ γn.dir = dir`. `bootstrapContract`/`bootOk` take `dir` (remotes'
  `memberRO dir`, `Hmembers`: `Members()` returns members whose URLs are `dir` of their ids,
  `memberDirIs`). The proof builds `srvProcOk` before `Start`, reserves `2 ^ 29` of `lgMu`'s
  `2 ^ 30` slots for the transport, and derives the wrapper's `isRNTransport` from the network's
  (`isRNTransport_of_net`). putget allocates the network (`netNames_alloc`) for its one member,
  with `putgetDir`, and `putget_safe` loses `transportEffectsOk`.
- **Raft's half** (M2r, `19a919ec00`): `SentMsgOk` from `isRaftMsg`, `NetMsgOk.of_sent`,
  `SentMsgOk.ne_timeoutNow`/`ne_transferLeader`, `netP`'s transfer clause. `stepP_of_recv` reads
  `SentMsgOk` and unfolds `isMessage` of a proposal itself, without `isRaftMsg_sent` or
  `isMessage_propose_ctx`: their statements carry raft's `[StorageModel GF]`, which the server's
  sections do not fix.
- **Trust base**: +2 axioms (`v2stats.ServerStats.RecvAppendReq`, `proto.SizeMessage`, D21h (A));
  `rafthttp.Transport.Start`/`AddPeer`/`AddRemote` restated; `transportEffectsOk` gone (from the
  definitions, `NewServer.spec`, `Main.spec`, `putget_safe`); the existing axioms that hold the
  cluster's lock (`RaftCluster.String`, `SetVersionChangedNotifier`) and `bootstrap`'s contract now
  keep the empty `removed` map, and `bootstrap`'s contract (a premise) names the URL directory.
  `EtcdServer.applyConfChange`'s docstring was updated (its `AddPeer` of a known peer returns).

**M6 (D20 (b)) moves to this session (the user, 2026-10-19).** The watch session waits for it before
linkv's `Apply`. Its requirements: the client's `Put` takes an ordinary (not persistent) update
fired at most once, at the server's apply, returning its result on success (on error, fired once
or not at all, decided by linkv's prophecy at the commit); writes run with no retries (plan (β),
`withMax(0)`); reads unchanged; `putget_safe` needs only `□AU ⊢ AU`.

## D21 M6: D20 (b) designed; stopped on the no-retry configuration (D21i) and gRPC's at-most-once request (D21j) (2026-10-19)

Stage M6 of D21 (D20 (b)). This entry is a design pass with no Lean change. Plan (β), writes run
with no retries, was confirmed by the user (2026-10-19). Two choices that D20/D21 leave open stop
the stage. Each changes a spec's meaning or the trust base: **D21i** and **D21j** below, asked of
the user. The rest is settled here, in three sub-stages that can start once both are answered.

### Why raft's protocol must change (checked)

The server cannot get at-most-once firing by itself. `kvInv` holds the KV state as the model of
the *whole* committed log (`kvStateOf (kvModel γk L)`), and Go's apply does not deduplicate:
`applyEntryNormal` applies every entry, whatever its id. So a second committed entry with a
request's data changes `etcdKV` a second time, and only the client's update can do that. A
persistent wrapper around an ordinary update is stuck at a second firing unless the second firing
can be refuted. Refuting it needs a raft fact: a deposited proposal `d` occupies at most one
position of the committed log. In Go this holds (D20, "Can Go apply a forwarded Put twice?": no).
In the model it does not, because `isMessage` of a `MsgProp` is persistent, so a leader may step
it twice.

### M6a. Raft: a one-shot ticket per proposal (no trust-base change)

- `prop_deposit` (`Facts.lean:687`) also returns `propTok γ d`, which is exclusive. Its witness
  `propIdx γ d i` is persistent and agrees (`propIdx d i ∗ propIdx d i' ⊢ ⌜i = i'⌝`). Both come
  from one ghost cell per deposit, named in the proposal's slot.
- `entDataIs γ e (some d)` gains `propIdx γ d e.Index'`, so it is now a fact about *stamped*
  entries. A proposal's pre-stamp entries get their own predicate, today's `entDataIs` content
  (deposited, normal, non-empty). `isMessage .propose`, `propP` and `fwdP` use it. The one place a
  pre-stamp entry becomes a log entry is the leader's append (`Step.propose`; `entDataIs_stamp` at
  `Ghost.lean:958` is the conversion today). There the ghost step consumes each normal entry's
  ticket and mints `propIdx` at the stamped index.
- **`propAu`, `prop_collect` and the commit invariant keep their statements.** The persistent
  raft-level update is still fired at every committed occurrence. Each occurrence now hands the
  update `entDataIs γ e (some d)`, and with it `propIdx γ d e.Index'`. That is all the server
  needs to refute a second occurrence.
- The ticket travels with the `MsgProp` as the read credit travels with a `MsgReadIndex` (M1).
  The per-message one-shot resource `rdCred γ (if ReadIndex then 1 else 0)` (`readyData`, `netP`,
  the outbox invariants: about 127 occurrences in about 25 raft files) generalizes to `msgCred γ
  st`: the read credit, plus for a `MsgProp` the tickets of its normal entries. It takes these
  paths:
  - `node.Propose`/`RawNode.Propose`: the ticket is in `propP`.
  - `stepLeader`: appended, the ticket is consumed. `ErrProposalDropped` (no progress, the
    uncommitted-size limit, a transfer, which is off in the mode): the ticket is dropped.
  - `stepFollower`: forwarded, the ticket goes into the outbox with the message. No leader: dropped.
  - `stepCandidate`: dropped.
  - `fwdP`: it takes the ticket.
  - The register example threads it through `deliver`, which already delivers each message once.
- Large, and raft-heavy. It follows M1's pattern.

### M6b. The server (no trust-base change)

- `srvNet`'s payload (M2: "Where D20 (b) plugs in"): `once st := ReadIndex ∨ Prop` and `O st :=
  msgCred`. This is an instance, not an axiom. **The at-most-once delivery is already stated:**
  `Transport.Start`'s promise for a `once` message (D21b, M2's `NetPayload`). `Process`'s proof
  passes `O st` to `fwdP`.
- `reqPropOk`'s write case takes an ordinary `kvOpAu1 γk op Q`. A caller with the persistent form
  uses `kvOpAu_one : kvOpAu ⊢ kvOpAu1`. At the proposal, the proposer allocates a per-request cell,
  an invariant `inv (AU1 ∨ fired)`. Here `fired` is `srvRLogLb γ (L0 ++ [e])` and `propIdx d i`
  of the first firing, plus `Q σ` or the proposer's token. The raft-level persistent update that
  `kv_prop_au` (`KVLemmas.lean:198`) builds opens the cell:
  - Unfired: it fires `AU1` and stores `Q σ`.
  - Fired: the lower bound gives `|L1| ≥ i`, while `propIdx` agreement gives
    `|L1| + 1 = i`. That is a contradiction.
- The result `Q σ` is no longer persistent. The wait registry and `Qr` keep their persistent
  shape and carry "fired at `σ`, in cell `c`". The proposer's token takes `Q σ` out of the cell.
  It reaches the client in the reply's `Φ`, which is already one-shot on both sides of gRPC
  (`grpcHandlerOk`, `grpcInvokerOk`).
- Request ids (M4) and the wait registry: an id is claimed once by its member's generator. The
  request's bytes contain the id, so a deposit (`propFresh d`), and with it a ticket, is per
  request. `processInternalRaftRequestOnce` proposes once. Neither the claims nor the registry
  takes part in at-most-once firing. The ticket does that, and the registry only carries the
  result.
- Medium-large. Files: `InvRequest`, `KVLemmas`, `InvBuild`, `InvNet`, the proposer, `v3rpc`'s
  `Put`.

### M6c. gRPC and the client (D21i, D21j)

- `kv.Put` reaches `ClientConn.Invoke` through the retry interceptor. Its contract
  (`etcdInterceptorOk`, `InvKVConn.lean:752`) and the attempt contract (`grpcInvokerOk`, which
  `grpc.ClientConn.Invoke` promises) take the request's precondition as `□ ▷ Spec m Φ`. An
  ordinary update must cross both.
- `client_put_end_to_end` takes the ordinary update. It gives `Q σ` on success, and on an error
  nothing: the update fired once or not at all, and linkv's update, built over its prophecy,
  decides which. `client_Put_own`/putget pass `□ AU` through `□ AU ⊢ AU` (or a disjunct, D21i).
- The update still fires at raft's commit of the entry (the ghost commit). This is inside the
  call, and it is where the KV state changes. The apply thread only reads it.

### D21i. How plan (β) is realized (asked of the user)

`withMax(0)` is unexported, and `kv.Put` takes `OpOption`s, not call options, so a program cannot
pass it. The unary interceptor is built with `withMax(MaxUnaryRetries)` (`client.go:247-270`:
`0` means the default, `100`). With `max = 1` the loop makes exactly one attempt
(`retry_interceptor.go:54`; no backoff at attempt `0`). So:
- *(A) `clientv3.Config{MaxUnaryRetries: 1}`*, with no fork change. The client's proofs carry
  `max ≤ 1` from the configuration to `kvObjAt`. The interceptor's contract takes
  `□ ▷ Spec m Φ ∨ (▷ Spec m Φ ∗ ⌜max ≤ 1⌝)`, and so do `Put`'s specs: one spec, whose update
  premise is "persistent, or ordinary with the one-attempt configuration". putget keeps its Go
  program and passes `□ AU` (the left disjunct). linkv's `Main` sets `MaxUnaryRetries: 1`.
  *(A′)*: the ordinary update only, with every program configured for one attempt. putget.go and
  putget3 change and are re-translated.
- *(B) A fork change*: the interceptor never retries a non-repeatable call. There is no premise,
  but etcd's behavior diverges further from upstream (no retry of a write that was never sent).
- *Recommendation:* **(A)**.

### D21j. gRPC's unary `Invoke` delivers a request at most once (asked of the user)

`grpcInvokerOk`'s request precondition goes from `□ ▷ Spec m Φ` to `▷ Spec m Φ`: an attempt runs
the served handler at most once. This restates what the axiom `grpc.ClientConn.Invoke` promises,
through the definition; there is no new axiom. The server side (`grpcHandlerOk`, `grpc.serve`)
already hands each run an owned `Spec m Φ`.
- True of grpc-go: an attempt is one HTTP/2 stream, and the request is written once. A
  transparent retry happens only for a stream the server never handed to the application
  (`REFUSED_STREAM`, a `GOAWAY` past it). etcd's client configures no retry policy and no hedging.
  D20 audited this ("gRPC's unary `Invoke` runs a handler at most once").
- The kind is D21b's (a restated transport contract with an at-most-once delivery promise), but
  at a different boundary, so it is asked rather than assumed. There is no alternative: an
  ordinary update cannot otherwise cross gRPC.
- *Recommendation:* accept.

### Trust base (estimate for M6)

No axiom added or removed. Restated: `grpc.ClientConn.Invoke`'s promise (D21j), through
`grpcInvokerOk`. Unchanged: `Transport.Start` (its `once` is M2's). New premise: none under
D21i (A); D21i (A′) adds the configuration to `clientCfgOk`'s users.

*Stopped (2026-10-19).* Asked of the user: D21i (recommendation (A)) and D21j (recommendation:
accept). Next: M6a (raft), then M6b, then M6c. M6a does not depend on either choice and could start
at once. It changes raft's specs (`Propose` takes the ticket, the server's call of it follows) but
not the trust base or any client-facing spec.

## D21 M5 carried out: putget3 and `putget3_safe` (2026-10-19)

Stage M5 of D21: `examples/putget3`, three members in one Go program (D21a (A)), and its closed
theorem. The stage stopped once, because serving the raft handler over HTTP needs a trust-boundary
statement. **D21k (the user, 2026-10-19): (A), two new axioms.** (1) `EtcdServer.RaftHandler`
returns a handler `h` with a persistent `raftHandlerOf γn id h`; the etcdserver translation stays
unchanged (`RaftHandler` stays names-only). (2) `http.Serve(l, h)` takes the listener at `a`,
`raftHandlerOf γn id h` and `⌜"http://" ++ a ∈ γn.dir id⌝`, and its postcondition is `True`. These
axioms are where D21b's deployment fact gets stated. That fact is: every peer URL of member `id` is
served by the raft handler of the transport holding `id`'s slot. `Transport.Start`'s axiom needs it
(`issues/etcd-rafthttp-misaddressed-403-member-removed.md`). Until M5 it was only argued in
`Start`'s docstring.
- **The program** (`examples/putget3/putget3.go`): putget's `Main` with a helper,
  `startMember(name, peer, peerAddr, client, cluster, lg)`. The helper runs `NewServer` with putget's
  configuration at the member's name and URLs, then `net.Listen(peerAddr)`, then
  `go http.Serve(l, s.RaftHandler())`, then `s.Start()`. `Main` builds the three peer URL slices and
  the initial cluster's map, calls `startMember` three times (members `putget3-1..3`, peer addresses
  `127.0.0.1:2380{1,2,3}`), and then does putget's steps on the first member: client address
  `127.0.0.1:23791`, one endpoint. `go test` passes. `TestMemberIDs` checks that the low 16 bits
  of the three member ids are distinct and nonzero (`0x908a`, `0x4092`, `0xc2ae`). `TestPutGet3`
  checks that the Put took effect and that the cluster has 3 members, so a quorum was reached over
  the served handlers.
- **The two axioms** (`Spec/.../etcdserver/EtcdServer__RaftHandler.lean`, `Spec/net/http/Serve.lean`).
  Their terms are in `etcdserver/InvRaftHandler.lean`:
  - `raftHandlerOf` is `□` of an `opaque` predicate. It is not an axiom, and only `RaftHandler`'s
    axiom gives it.
  - `RaftHandler`'s precondition is `srvNetMember γn s id`: `srvProcOk γn s id` (M2's inbound
    facts, the member id among them), plus `s.r.transport ↦□ t` with `transportStarted γn t`.
    `NewServer.spec`'s postcondition gains it (a stronger postcondition). Its inner `RNNames`
    binder was renamed from `γn` to `γrn`, because `γn` shadowed the network. putget's `Main`
    drops the new conjunct.
- **Choices the D21 text left open** (none changes a spec's meaning beyond the two axioms):
  - *One storage registry per member.* D19r (B)'s `memStorRegAuth ∅` would be "enough for one
    server" if the registry were shared. Instead each `startMember` allocates a fresh registry,
    `letI : MemStorReg GF := ⟨γreg⟩`. putget's premise already quantified `bootstrap`'s contract
    over every registry. So `NewServer.spec` is unchanged and needs no registry invariant.
  - *The thread token.* `Start` takes the caller's `threadTok` and returns it inside `srvGoRes`.
    `Main` takes the token out of the first member's `srvGoRes` for the second member's
    `startMember`, does the same for the third, and puts the first member's `srvGoRes` back
    together for `v3rpc.Server`.
  - *The pure facts* (`putget3.BootFacts id₁ id₂ id₃ bootLog`). The low 16 bits of the ids are
    distinct and nonzero (D21e (A)). The bootstrap log is `BootLogOk (ccOk [id₁, id₂, id₃])
    [id₁, id₂, id₃]`, with the peers in the order `bootstrap` sorts them. The ids Go computes
    happen to be ascending in the members' order.
  - *The URL directory* is `dir3 id₁ id₂ id₃`: each member's one peer URL. Each member's
    `bootstrap` contract is a separate premise (`bootPremise`), at its own name and URLs, over the
    initial cluster's map with the three keys (`urlsOk`).
  - `startMember.spec`'s success postcondition is `memberUp`: `Start`'s postcondition plus the
    serving resources `NewServer` left (putget's).
  - `Main.wp_proof` runs with `maxHeartbeats 1000000`. The default timed out on the whole
    declaration.
- **Go module pins.** putget, putget3, linkv and register now replace `go.etcd.io/raft/v3` with
  the fork's `c8217eb9` (D21c′ (A1)), the raft pin. It was `509271dac`. The Go tests pass, and the
  translations are unchanged (`etc/goose.py --check`).
- **The closed theorem** `putget3_adequate` (`putget3/Adequacy.lean`), restated as `putget3_safe`
  (`Results.lean`), is putget's for this program. It goes through `goose_adequacy_start` with the
  read package's two metric names and four addresses: the three peer addresses and the client
  address. Its hypotheses are putget's kinds:
  - the pure facts above;
  - the triples `putget3.premises`: three `bootstrap` contracts, putget's raft wrapper contracts,
    `rnStopOkStarted` and `runsNoRequireLeader`;
  - the two marked Props.
  The package table is generated (`etc/gen-init.py`'s `PROGRAMS`, and `putget3` in its `ROOTS`).
- **Trust base: +2 axioms**, `EtcdServer.RaftHandler.wp_proof` and `net.http.Serve.wp_proof`
  (`etc/tcb-baseline.txt` updated with `--check --update`). Nothing else was added. The new
  collection `etc/tcb-collections/putget3.txt` is putget's plus these two.

**D21i, D21j (the user, 2026-10-19): (A), accepted.** D21i (A): `clientv3.Config{MaxUnaryRetries:
1}`. There is one `Put` spec, whose update is persistent, or ordinary when the client is
configured for one attempt. D21j: `grpc.ClientConn.Invoke`'s attempt contract (`grpcInvokerOk`)
takes the request's precondition as ordinary (at-most-once delivery), a restatement of the
axiom's promise. M6a-c proceed as designed above.

## D21 M6 carried out: at-most-once firing of a client write (2026-10-19)

Following the design above, with D21i (A) and D21j. Where it departs from the design:

- **Two deposit modes (raft).** The register retries the same request, so a re-proposal is not
  fresh and has no ticket to carry. A deposit therefore records a mode: `PropRec = GName × GName ×
  Bool` (the predicate's name, the ticket's `dghostVar`, once). Once-mode deposits mint a ticket
  `propTk` (`dghostVar` at `none`) that every copy of the entry must carry (`entTk`, `msgTks`).
  Multi-mode deposits carry `propMulti` and keep the old persistent `propAu`.
- **The refutation is raft's, not the server's.** The design had the server keep a per-request
  cell and refute a second firing with `propIdx` and `srvRLogLb`. Instead, the slot of a once-mode
  deposit holds an ordinary `propAu1` until it fires, and then `propOcc`. `fire_one` refutes a
  second committed occurrence: both entries carry `propIdx d i` (`entDataIs_idx`), so
  `propIdx_agree` and the log's index positions (`PlogWf`) give the same index. So the server needs
  no refutation cell, only a result stash for the ordinary `Q`. `kvRes γc Q σ` sits in the
  invariant `kvResN` until the proposer takes it with its `kvResTok`.
- **Tickets in the raft state.** `rdOwn` owns the outbox's tickets (`msgsTks γ s.outbox`). Steps
  that rearrange the outbox keep `propsOf` a sub-permutation (`rdOwn_mono`). A concrete message's
  tickets are `stTks`. `Ready` hands them out, and the server's network carries them in the
  one-shot part of `MsgProp` (`srvNet`'s `once` is ReadIndex ∨ Prop).
- **The client's one-attempt fact** comes from the configuration, not from a separate spec. The
  call options' retry bound is tracked as `optApplyMax`/`maxAfter`. With `MaxUnaryRetries: 1` the
  interceptor makes one attempt (`etcdInterceptorOk1`). That reaches `dial` (`isEtcdConn1`),
  `NewKV` (`kvOnce`) and `New` (`clientKVOnce`). There is one `Put` spec chain (`reqPre`,
  `kvReqPre`): the request's precondition is persistent, or ordinary on a one-attempt connection.
  `client_put_end_to_end` takes `putAuOk`.
- **Results.** `putReplied`'s `Q` is ordinary. Callers with a persistent update pass `□ Q`
  (`putAuOk_of_box`, `putReplied_mono`), so putget, putget3, `ServerKVPut` and `PutThenGet` keep
  their statements. No axiom or `sorry` changed: D21j restates `grpcInvokerOk`, a definition the
  `Invoke` axiom's promise is stated with.

## T-S: the snapshot path, scope and staging (D22, 2026-10-19 · proposed)

A design pass only (no Lean change); track T-S of D21 ("Later tracks"), D21c (B). Goal: lift D21
M3's run bound, so that `NewServer.spec` drops `receiptBound ≤ SnapshotCatchUpEntries + 1`,
`bootOk` drops `"%Hnosnap"` (`γ.reNoSnap = true ∧ γs.cap = 1`), and a cluster member may
compact its raft log anywhere, send `MsgSnap`s, and install a received snapshot. Go citations at
the pins: etcd fork `8a24be2a3` (`git -C /shared/etcd show 8a24be2a3:<path>`; `/shared/etcd`'s
checkout is at `bc8b52a50`, not a descendant of the pin, and `.lake/go-src/etcd` is at
`0df483bee6`), raft fork `c8217eb9` (`/shared/etcd-raft37-a1`). Constraint (the user): no edit
to the bbolt proofs (`Proof`/`Spec` under `go_etcd_io/bbolt`); bbolt-level facts become specs or
axioms at etcd's backend boundary (`server/v3/storage/backend`, `server/v3/storage`).

**What T-S buys, stated plainly.** `putget_safe` and `putget3_safe` already hold for every run of
their programs: the examples set `SnapshotCatchUpEntries: 1 << 48`, so the run bound follows from
the receipt bound and is no hypothesis (D21 M3). What T-S changes is *which program* is verified:
with it, the examples run etcd's defaults (in-memory snapshot every 100 applied entries,
compaction at `appliedi - 5000`), and the code production runs on every lagging follower --
raft's `MsgSnap` send and receive, `createMergedSnapshotMessage`, `sendMergedSnap`, the snapshot
stream, `applySnapshot`'s restore -- is covered instead of configured away. The theorem's
statement barely moves; its scope does.

### Inventory

Paths under `Proof/go_etcd_io/etcd/server/v3/etcdserver/` (server) and
`Proof/go_etcd_io/raft/v3/` (P), `Spec/go_etcd_io/raft/v3/` (S) unless said otherwise.

**Raft, sending** (all proved, no `sorry`, no snapshot axiom):
- `maybeSendSnapshot` (`raft.go:666-690`; P `raft__maybeSendSnapshot.lean:90`, S `:65`): premises
  `s.gh.ns = false` and `prev.index ≠ 0 ∨ storPast storage 1`. `maybeSendAppend` (`raft.go:618-661`;
  P `raft__maybeSendAppend.lean:292`) closes both snapshot fallbacks in the mode (`PrOkN`,
  `LogNsOk`, `storPast_cap` against `NsCap`) and calls `maybeSendSnapshot` outside it. `raft.send`'s
  `MsgSnap` clause takes `ns = false` (S `raft__send.lean:129-134`).
- The protocol's `.snap` message (`P/Protocol/GhostState.lean:242-256`): `isLeader src term`,
  `isSnapMeta`, **the snapshot's last entry in the leader's log at `m.term`** (`leadPrefix`,
  `plogTermAt … = some logterm`, `lpfull`), `commitIn … m.index m.term`, `isCommitted` of the
  covered prefix, `dst ≠ src` and both in `reTracked`. `SnapOk` (`P/Protocol/Model.lean:1527`).
  `raftSnapCert` (`P/SnapConf.lean:147`) and `LogState.ksn` exist and are used by nothing (stage S,
  2026-10-15, `notes/STATUS.md` "Snapshots at the public API (stage S)"; the on-message variant is
  on the remote branch `stage-s-msg-extension`, `8fdbfceb4`, not merged).
- The mode: `RaftNames.reNoSnap` (`P/Protocol/Ghost.lean:317`), `NGhost.ns`/`xf`, `NsLink`
  (`P/StepGhostMode.lean:241`: **`ns = xf = reNoSnap`**, one flag for "no snapshot" and "no leader
  transfer", D21 M2r), `isRaftMsg`'s `reNoSnap = true → Type ≠ MsgSnap ∧ SentMsgOk`
  (`P/InvRawnode.lean:939`), set by `ownRaftGhost_alloc_boot ns` (`P/Protocol/Facts.lean:1622`),
  the server's `NewServerAlloc.lean:221` with `true`.

**Raft, receiving:**
- `raft.Step`'s `MsgSnap` branch (`raft.go:1690`, `:1735`; P `raft__Step/MsgSnap.lean:53`),
  `handleSnapshot` (`raft.go:1837`; P `raft__handleSnapshot.lean:53`), `raft.restore`
  (`raft.go:1857`; P `raft__restore.lean:245`), `raftLog.restore` (`log.go:466`),
  `unstable.restore`: proved, with premises `ns = false`, `scfg.Has id` (the `!found` exit
  undescribed), `SnapScope`, `md.SnapOk`, `isMessage (absSnap …)` (S `raft__Step.lean:525-530`).
- Not reachable: `netStepTypes` has no `MsgSnap` (`P/InvRawnode.lean:482`); `ownRawNode`,
  `ownRawNodeReady`, `ownRawNodeIdle` hold `s.logst.snap = none` (`P/InvRawnode.lean:1281`, 19
  files read it); `readyData`/`RawNode.Ready` give `rd.Snapshot = null` (`P/InvNode.lean:552`,
  S `RawNode__Ready.lean:102`); `raft.Step` takes `MsgStorageAppendResp` only with no snapshot
  (S `raft__Step.lean:429`).
- **Unverified Go on the path** (no spec, not in `etc/link-lean-first-raft.txt`):
  `raft.appliedSnap` (`raft.go:766`), `raftLog.stableSnapTo` (`log.go:369`),
  `unstable.stableSnapTo` (`log_unstable.go:185`); `readyWithoutAccept` (`rawnode.go:139`) and
  `acceptReady` (`:400`) with a snapshot in progress.
- `MemoryStorage`: `ApplySnapshot` (premise `index ≤ γs.cap`, and it needs `ownMemoryStorage`,
  which raft's `ownRaftLog` holds: no handout exists for it, unlike `Append`'s
  `Hhandout`/`Habsorb`, `P/InvStorage.lean:494-496`), `Compact` (`ci ≤ γs.cap`, the application's
  `memSnapTok`/`memFloorTok`), `CreateSnapshot`, `Snapshot`: proved. `ReportSnapshot`/
  `MsgSnapStatus`: proved (`P/RawNode__ReportSnapshot.lean:39`, `stepLeader/Rest.lean:334`,
  server `EtcdServer__ReportSnapshot.lean:27`).

**etcd, the trigger** (`server.go:1220-1237`, `2088-2174`): `snapshotIfNeededAndCompactRaftLog`,
`shouldSnapshotToDisk`/`ToMemory` proved; `EtcdServer.snapshot` and `compactRaftLog` axioms
(names-only), the latter restated in M3 with `(if scu < snapi then snapi - scu else 1) ≤ γs.cap`
and silent on the `inflightSnapshots` skip (`:2150`); the cap discharged through `srvWTPool`/
`srvWTAt` (`InvApplier.lean:647-740`: `ai < receiptBound ≤ scu + 1`). `srvSnapState`
(`InvApplyAll.lean:93`) at `sl = 0`.

**etcd, the sender:** `applyAll`'s `msgSnapC` receive (`server.go:1002-1009`) translated, dead
(`#Hnosnap`, `srvMsgSnapC_false`, `InvBuild.lean:162`); `processMessages`' `MsgSnap` branch
(`raft.go:374-384`, the 16-slot `msgSnapC`) proved. `createMergedSnapshotMessage`
(`snapshot_merge.go:32-80`: `KV().Commit()`, `be.Snapshot()`, a goroutine streaming it through an
`io.Pipe` that panics on a failed close, `ConfState` cloned, `m.Snapshot` **overwritten** with
`(ep.appliedi, ep.appliedt, ep.confState)`) and `sendMergedSnap` (`server.go:1854-1892`:
`inflightSnapshots`, `transport.SendSnapshot`, a `GoAttach` goroutine releasing the count after
`CloseNotify` and `releaseDelayAfterSnapshot = 30s`): names-only, no spec since D19p (they were the
`True`-postcondition axioms of `aac0122b4b`, removed in `4b2744b8a5`).

**etcd, the receiver:**
- `raftNode.start`'s snapshot branch (`raft.go:219-283`: `proto.Clone`, `storage.SaveSnap`,
  `storage.Sync`, `notifyc`, `raftStorage.ApplySnapshot` with its error ignored,
  `storage.Release`): translated, proved only at `rd.Snapshot = null` (`raftNode__start.lean:158`,
  `410-437`).
- `applySnapshot` (`server.go:1011-1159`): translated; spec and proof only for the empty snapshot
  (`Spec/…/EtcdServer__applySnapshot.lean`, `taSnapshotAddr ap ↦□ null`). Its body: panic if the
  snapshot index `≤ ep.appliedi`; `<-notifyc`; `bemu.Lock`; `storage.OpenSnapshotBackend`
  (`server/storage/backend.go:63-72`: `Snapshotter.DBFilePath`, `os.Rename` onto the backend path,
  `OpenBackend` -> `newBackend`, a goroutine and a 10 s timer); `consistIndex.SetBackend`;
  `lessor.Recover` (`lease/lessor.go:600`); `kv.Restore` (`mvcc/watchable_store.go:207`, which
  moves every synced watcher to unsynced with `restore = true`, -> `store.Restore`,
  `mvcc/kvstore.go:292-314`: **closes `stopc` and stops the FIFO scheduler**, a new tree index and
  scheduler, `restore()` of a backend *with data*); `SetTxPostLockInsideApplyHook`; the swap
  `s.be = newbe` (under `bemu`, already a reader-slot `RWMutex` with `s.be` in its invariant,
  `InvApplyAll.lean:57-65`); `oldbe.Close()` in a goroutine; `restoreAlarms`; `authStore.Recover`
  (`auth/store.go:396`); `cluster.SetBackend`/`Recover` (`membership/cluster.go:247-302`:
  `UnsafeLoad`, `MustDetectDowngrade`); `transport.RemoveAllPeers` and `AddPeer` per member;
  `ep` reset to the snapshot; `NewUberApplier`.
- Status of the callees: `consistIndex.SetBackend`, `backend.Close`, `restoreAlarms` proved;
  `watchableStore.Restore` translated, no spec; `store.Restore`, `lessor.Recover`,
  `authStore.Recover`, `RaftCluster.SetBackend`/`Recover`, `Transport.RemoveAllPeers`,
  `OpenSnapshotBackend`/`OpenBackend` names-only, no spec; `mvcc.store.restore` an axiom for an
  **empty** key bucket under `backendNoCompaction` (D19l (v) (B)); `AddPeer`/`AddRemote` axioms.
- **The backend model** reads one bucket: `isKeyBackendG` (`storage/mvcc/InvStore.lean:992`), the
  rest opaque premises of `NewServer.spec` about the data directory at startup: `bkFresh`
  (lease/auth buckets empty, `InvBoot.lean:97`), `backendNoCompaction` (`InvStore.lean:210`),
  `backendUnderQuota` (`apply/Contracts.lean:520`). `backend.Snapshot()` (`backend.go:381`) and
  the `Snapshot` interface (`WriteTo`, `:86-90`) are not translated; `newBackend`/`New` are proved
  from `fileHolds cfg.Path D` (an axiom-level predicate of the bbolt boundary,
  `InvBbolt.lean:89`).
- **The KV invariant:** `kvInv` (`InvRequest.lean:1195`, the cluster's since M4: raft's `srvRLog`,
  the KV state as `kvModel` of the log), each apply thread's `kvApplied` (`:1344`, `srvRLogLb A`,
  `x.log = kvModel A`) and `appliedLogAt` (`:1552`), `loopOk` (`InvApplier.lean:98`, the
  consistent index's `ciEff`). Nothing relates a store installed from a snapshot.

**The transport:** `rafthttp` and `snap` are names-only (`translate = ["!*"]`). `Net.lean`
(`api/rafthttp/Net.lean`) is generic in the payload; `netTransport` has `Send`/`Stop`, no
`SendSnapshot`; the snapshot handler (`rafthttp/http.go:208-330`: decode the envelope, refuse a
non-`MsgSnap`, `Snapshotter.SaveDBFrom` -- temp file, fsync, rename to `<index>.snap.db`, **keeping
an existing file of that index** (`snap/db.go:37-90`) -- then `Process`); `snapshotSender.send`
(`snapshot_sender.go:66-140`: `ReportSnapshot(Failure|Finish)`, `CloseWithError`);
`Transport.SendSnapshot` (`transport.go:409-418`: a missing peer closes the message with
`errMemberNotFound`). `ReleaseSnapDBs` (`snap/snapshotter.go:45-70`, from `storage.Release`)
removes only `.snap.db` files *below* the released index, so a file `applySnapshot` will open is
never removed under it.

### Findings

1. **A Go bug, filed:** `issues/etcd-quota-stale-backend-after-snapshot.md`. The gRPC quota servers
   (`v3rpc/quota.go:53-95`) capture `s.Backend()` at construction; `applySnapshot` swaps `s.be`
   and closes the old backend, whose `Size()` is then frozen. If the old db was over the quota,
   every write through the member re-raises NOSPACE for the whole cluster until it restarts, through
   the documented recovery (compact, defragment, disarm). Reproduced by an integration test at the
   pin; the fix (read `s.Backend()` per check) passes it. For the proof: D22g.
2. **etcd's merged snapshot is not raft's `.snap` message.** `createMergedSnapshotMessage`
   overwrites the snapshot raft produced (the storage's, at the last memory snapshot `i0`) with
   `(ep.appliedi, ep.appliedt, ep.confState)` of the apply thread, `appliedi ≥ i0`. The receiver's
   raft restores that, and its `MsgAppResp` acknowledges `appliedi`. Two consequences:
   - the protocol clause's "last entry in the leader's log at `m.term`" is not what the apply
     thread knows: it knows its applied prefix is committed, not that the raft node is still leader
     at `m.term`;
   - **it can be false**: `msgSnapC` holds up to 16 messages and `applyAll` takes one per batch,
     so a `MsgSnap` of term `T` can be taken after the member has stepped down and applied entries
     committed by a later leader of term `T' > T`. The merged message then has `Term = T` and a
     snapshot whose last term is `T'`. A receiver at term `≤ T` restores it and holds a log whose
     last term is greater than its current term. Not a safety bug (by code reading): a quorum
     acknowledged an entry of term `≥ T'`, so its members have terms `≥ T'` and refuse any vote
     below `T'`, and the receiver cannot lead before `T'`; a stale `MsgApp` of term `T` cannot
     match at the snapshot's index (its `LogTerm ≤ T < T'`). Not filed. But the proof must state
     the `.snap` clause so that it holds of this message (D22a), and S-0 must check that no protocol
     invariant assumes "a node's last log term is at most its term".
3. **`store.Restore` stops the store's scheduler**, which needs the stop token D19m (C) gave up at
   `NewStore`'s success (`isStore` holds `isFifo` without `schedLive`; the closer `storeCloser` is
   dropped by `NewServer`). D22d.
4. **The single mode flag.** `NsLink` makes "no snapshot" and "no leader transfer" one flag
   (`reNoSnap`); lifting the first must not lift the second (etcd still needs `MsgTimeoutNow`
   excluded, D21 M0), and `SentMsgOk` (what the receiver's `NetMsgOk` comes from) is given only
   under `reNoSnap = true`. Stage S-a splits it.
5. **The applied index jumps.** After an install, `ep.appliedi = snapi` without this member's apply
   pool having paid a token per covered entry, so `srvWTAt`'s "`ai ≤` tokens taken" fails. What
   it bounds besides M3's cap (revision and counter overflow, D19b) needs a cluster-level source:
   the committed log's length (`rnLogFits`, D19b stage 5). D22h.
6. **The backend's other buckets.** The receiver reads, from the image, the `meta` bucket
   (consistent index and term, the confState, the compaction keys, the storage version), `lease`
   (`lessor.Recover`), `auth*` (`authStore.Recover`), `members`/`members_removed`/`cluster`
   (`cluster.Recover`), `alarm` (`restoreAlarms`). Today these are opaque premises *about the
   data directory at startup* (`bkFresh`, `backendNoCompaction`, `backendUnderQuota`); a received
   image is produced by the program, so they must be derived, not assumed (D19a). D22c.
7. Liveness only, not filed (as D21's): `raftStorage.ApplySnapshot`'s error is ignored
   (`raft.go:277`; unreachable: the storage's snapshot index is at most the applied index, below
   the incoming one); a stale merged snapshot whose file another sender's `SaveDBFrom` already
   wrote at the same index is dropped in favour of the first (`db.go`'s exists branch), harmless
   since both are the state at that committed index.

### Decisions

**D22a. The `.snap` message's content.**
- *(A) Split the clause: an envelope and a content certificate.* The envelope: `isLeader src
  m.term`, `src ≠ 0`, `dst ≠ src`, the tracked bound (what `stepFollower` reads: `lead = m.From`).
  The content: `isCommitted` of a prefix ending at `(index, logterm)` and the configuration's
  certificate (`raftSnapCert`, A3) -- no leader prefix, no `commitIn` at `m.term`. raft's sender
  builds both (it has them); an application that applied a committed prefix mints the content
  (`snapContent_mint`, from `kvApplied`'s `srvRLogLb` and raft's committed records) and replaces a
  message's content with it (`isMessage_snap_recontent`). The receiving `raft.Step` keeps its proof
  shape if the leader-prefix fact was only used to derive `isCommitted` (S-0 checks; the protocol's
  restore step, `StepC.snap*`, and `ownRaftGhost_step_snap*` read what?).
- *(B) A fork fix that drops a stale merged snapshot* (`applyAll` sends only when `ep.appliedt ≤
  m.Term` and the member is still leader): racy (leadership can end after the check) and not
  sufficient (an applied entry of term `≤ T` may still be missing from the leader of `T`'s log,
  the Figure 8 shape), so (A) is needed anyway.
- *(C) Keep raft's snapshot metadata* (no rewrite): changes etcd's protocol (the db image is at
  `appliedi`, not `i0`); no.
- *Recommendation:* (A), checked first by S-0.

**D22b. The certificate's carrier** (stage S's open "Left" 1).
- *(A) On the message*, as `stage-s-msg-extension` did (`Msg` gains the lists, `isMessage`'s
  `.snap` carries `raftSnapCert`), restated per D22a (A).
- *(B) Local to `RawNode`* (`ownRawNode` holds the certificates of `ksn`, `Ready` hands one out
  with each `MsgSnap`). With etcd's rewrite, the content the receiver gets is the server's, not
  `ksn`'s: a raft-local certificate of `i0` says nothing about `appliedi`, so the server would
  need the on-message form anyway.
- *Recommendation:* (A). It reverses the integration session's 2026-10-15 preference (avoid
  touching `Msg`/`isMessage`/`ownRaftGhost` when a local route exists), because for etcd no local
  route exists; asked of the user for that reason.

**D22c. What the image certificate says about the backend.**
- *(A) The key and meta buckets modeled, the rest by determinism.* `dbImage γ i D`: `D`'s key view
  is `kvModel` of the committed prefix of length `i` (with its compaction: D19l (v) (A), the meta
  bucket's compaction keys modeled), `D`'s consistent index and term are `i` and its term, its
  confState the static configuration; the other buckets are `bkRestAt i` -- the value every
  member's backend has at consistent index `i`, one trust-boundary axiom at the backend (the
  apply path writes those buckets as a function of the applied entries) under which the
  `Recover` axioms are stated, plus the facts `bkFresh` gave for putget's workload (no lease or
  auth writes: from the workload, as `noGrant`).
- *(B) Model every bucket the `Recover`s read* (lease, auth, members, cluster version, alarm,
  downgrade): faithful, large (four packages' backend contracts).
- *(C) Opaque premises per received image:* not of D19a's kinds (a fact about the program's own
  state); rejected.
- *Recommendation:* (A); (B) piecewise when a package's proofs need it.

**D22d. The store's stop token for `Restore`.**
- *(A) The apply thread keeps `storeCloser`* (`NewServer` stops dropping it): `Restore` takes it,
  stops the old scheduler, and returns a new one for the new scheduler (`store.Restore`
  translated and proved; it is short); the compaction right (`compactRight`, `compactQueue`) is
  re-made from it as at `NewStore`.
- *(B) `store.Restore` an axiom over `isFifo` only*: hides a real ownership transfer (a compaction
  job of the old scheduler running against the new backend is what Go's `Stop` prevents).
- *Recommendation:* (A).

**D22e. A cheaper intermediate first?** The run bound cannot be weakened short of T-S: compaction
past a lagging follower forces a `MsgSnap` (raft cannot know the follower is merely delayed), so
"compaction on, snapshots off" is not a reachable mode, and a bound on the followers' lag is not
of D19a's kinds; "the server's trigger off" buys nothing, since the in-memory snapshot ignores
`SnapshotCount` (D21 M0). The intermediate worth having is on raft's side:
- *(A) Raft's snapshot path end to end on `examples/kv` first* (stage S-r): the store's Go code
  compacts its raft log every `K` entries and puts its map, encoded, in the snapshot's `Data`;
  `kv_porcupine_safe` keeps its statement with snapshots live. It exercises S-b..S-d with a
  trivial application state, gives a closed theorem with raft's `MsgSnap` verified before any
  backend work, and de-risks D22a/b. Cost: a Go change in the example and its proofs (medium).
- *(B) Straight to etcd*: S-b..S-d tested only through putget3, after the server stages.
- *(C) Stop at M3's bound* (T-S later): nothing new verified.
- *Recommendation:* (A), in parallel with the server stages S-f..S-i (it gates nothing).

**D22f. putget3's configuration after T-S.** *(A) etcd's defaults* (`SnapshotCatchUpEntries`
`5000`, memory snapshot every `100`), the point of the track; *(B) a small value* (e.g. `5`) so
that snapshots happen in short runs (the theorem does not care; tests would). *Recommendation:*
(A) in putget3; (B) only in a test configuration.

**D22g. The stale quota (finding 1).**
- *(A) Fix in the fork* (the quota reads `s.Backend()` per check; the issue's patch) and verify
  the fixed code: the quota's contract is over the current backend.
- *(B) Keep upstream's code*: the quota's contract (`apply.isQuota`, D19j's `quotaAlarmer`) is
  over the backend captured at construction, closed or not (`Size()` of a closed backend is its
  last value); a refusal is an error path the request specs already allow, and the opaque
  `backendUnderQuota` must then speak of every backend a member opens or captured.
- *Recommendation:* (A), the fork's practice for reproduced bugs (`raft-stale-term-…`, D21c′), if
  the user agrees to carry it; else (B).

**D22h. The applied index after a jump.**
- *(A) A cluster-level bound*: `srvWTAt` replaced, where it bounds anything but M3's cap, by the
  committed log's length bound (`rnLogFits`) and a per-entry receipt of the proposer (the
  revision grows by at most one per committed entry, whoever applies it).
- *(B) Snapshot-carried tokens* (the sender passes the covered entries' tokens): there are none to
  pass (every member applies every entry with its own tokens).
- *Recommendation:* (A), its exact form from S-0's list of `srvWTPool`'s users.

**D22i. The mode flag** (finding 4). *(A) Split* `reNoSnap` into `reNoXfer` (no leader transfer,
`SentMsgOk`; on for the server) and `reNoSnap` (no snapshot, the cap; off after T-S), `NsLink`
into two links. *(B) Drop the no-transfer mode* and give `MsgTimeoutNow` a tick credit (the
register's budget). *Recommendation:* (A): mechanical, and etcd never transfers in the runs
covered.

### Stages

Each small enough for one agent; dependencies in brackets.

- **S-0. Pen-and-paper check** [none; no Lean]: (1) D22a (A) against the receiving raft's proof
  (which uses of the leader-prefix and `commitIn` in the `.snap` ghost steps survive), and whether
  any protocol invariant assumes "last log term `≤` term" (finding 2's stale case); (2) the sender's
  facts at the `msgSnapC` receive: the applied prefix committed, `ep.appliedt` its last term,
  `ep.confState` the static configuration, the db's consistent index `= ep.appliedi` after
  `KV().Commit()` (`applyEntryNormal`'s deferred `SetConsistentIndex`); (3) which entries write the
  buckets of finding 6 (D22c (A)'s determinism claim); (4) `srvWTPool`'s users (D22h); (5) the
  holders of a backend across the swap (`s.Backend()` callers, the quota, the hooks), with
  finding 1 as the one found so far. Output: a note, amendments to the stages.
- **S-a. Split the mode flag** [none; parallel with S-0]: D22i (A). Raft (`Protocol/Ghost`,
  `StepGhostMode`, `InvRawnode`, `RawNode__Bootstrap`, the allocation) and the server's `bootOk`/
  `InvBuild`. Small. Trust base unchanged.
- **S-b. The `.snap` message restated, its certificate on the message** [S-0]: D22a (A), D22b
  (A): the protocol clause, raft's sender (`maybeSendSnapshot`'s ghost step), the receiver's
  `raft.Step` premises derived from the message (`SnapScope`, `md.SnapOk`), the minting and
  re-content lemmas for an application. Raft files. Medium. Unchanged trust base.
- **S-c. `MsgSnap` at `RawNode.Step`/`node.Step`** [S-b] (stage S2): `netStepTypes`, `NetMsgOk`
  for `MsgSnap`, a pending snapshot in `ownRawNode` (the 19 files reading `Hsnap`), `node.Step`'s
  `netP`; `SentMsgOk` for `MsgSnap` (under `reNoXfer`). Medium-large. Unchanged.
- **S-d. A pending snapshot through `Ready`/`Advance`** [S-c] (stage S3): `appliedSnap`,
  `stableSnapTo` (both), `MsgStorageAppendResp`'s snapshot arm, `readyWithoutAccept`/
  `acceptReady` with a snapshot in progress; `readyData` with `rd.Snapshot ≠ null` handing out the
  content certificate; `RNState`'s delivered/applied jump; a handout protocol for the
  application's `MemoryStorage.ApplySnapshot` while raft holds the storage (beside
  `Hhandout`/`Habsorb`); `MemoryStorage`'s cap at `2^64` outside the mode. Large. Unchanged.
- **S-r. `examples/kv` with snapshots** [S-d] (D22e (A); optional): Go change in the example,
  its proofs, `kv_porcupine_safe` unchanged in statement. Medium. Unchanged (the example's own
  code).
- **S-f. The backend boundary** [S-0; parallel with S-b..S-d]: `backend.Snapshot()` and
  `snapshot.WriteTo` (axioms: the image written is the backend's committed state, as
  `fileHolds`'s abstract state), `storage.OpenSnapshotBackend` translated with its body over
  `Snapshotter.DBFilePath` and `os.Rename` (axioms here; `OpenBackend`'s goroutine and timer
  translated if Perennial's `time.After` suffices, else one axiom for `OpenBackend`), `newBackend`
  proved already; the `dbImage` certificate of D22c (A) and `bkRestAt`. Server and `storage`
  files only, no bbolt file. Medium. **+3 to +5 axioms.**
- **S-g. The store's restore with data** [S-0, S-f's `dbImage`]: D19l (v) (A) (the compaction
  keys in the backend contract, `backendNoCompaction` from the model instead of an opaque
  premise), `mvcc.store.restore` restated for a key bucket with data (the index rebuilt, the
  compaction finished or rescheduled), `store.Restore` translated and proved under D22d (A),
  `watchableStore.Restore` proved (watchers to unsynced with `restore = true`, against the watch
  invariants: `InvWatchSync`, the client's `isClientWatcher`). mvcc files. Medium-large. **0 net**
  (`restore` restated, one opaque premise fewer).
- **S-h. The sender** [S-b, S-f, S-i]: `createMergedSnapshotMessage` and `newSnapshotReaderCloser`
  translated and proved (the merged content minted from the apply thread's `kvApplied`, the image
  from `KV().Commit()` and `Snapshot`), `sendMergedSnap` translated and proved (the
  `inflightSnapshots` count, the release goroutine), `compactRaftLog`'s contract restated with the
  inflight skip and no cap, `applyAll`'s `msgSnapC` branch live (the message bundle from raft, as
  `srvMsgNet`). Server files. Medium. **+2 to +4 axioms** (`snap.NewMessage`/`CloseNotify` unless
  `snap/message.go` is translated, `io.Pipe` unless Perennial models it); the two removed in D19p
  come back as *proved*.
- **S-i. The snapshot stream in the network contract** [S-0; parallel]: D21b's contract extended:
  `netTransport` gains `SendSnapshot` (in `Transport.Start`'s restated postcondition: a merged
  message whose payload is a `.snap` with its content certificate and whose reader streams an
  image with `dbImage`); the receiver's snapshot directory as a ghost map, written by the
  transport before it calls `Process(MsgSnap)` (`SaveDBFrom`'s order, `http.go:279-330`), read by
  `OpenSnapshotBackend`; `ReportSnapshot` at any time (proved); `Snapshotter` at `bootstrap`.
  `api/rafthttp/Net.lean`, the transport axioms. Small-medium. **0 new declarations**
  (`Start` restated), +1 if `Snapshotter`'s constructor needs one.
- **S-j. The receiver** [S-d, S-f, S-g, S-i]: `raftNode.start`'s snapshot branch (`SaveSnap`,
  `Sync`, `Release` of the WAL storage: axioms unless already there; `raftStorage.ApplySnapshot`
  through S-d's handout), `applySnapshot` past the empty case: the backend swap under `bemu`'s
  writer side, `consistIndex.SetBackend` (proved), `lessor.Recover`, `authStore.Recover`,
  `cluster.SetBackend`/`Recover` (axioms under `bkRestAt`; `rcLockInv`'s empty removed map and
  `localKept` from the image), `kv.Restore` (S-g), `oldbe.Close` in a goroutine (the old
  backend's closer, which the server must keep), `restoreAlarms` (proved), `RemoveAllPeers`
  (axiom; the transport's peer set re-made) and the `AddPeer` loop, `NewUberApplier` (proved);
  the member's share of `kvInv` and `loopOk` re-established at `snapi`, D22h's bound. Large;
  splits into S-j1 (`raftNode.start` and the hand-off) and S-j2 (`applySnapshot`) if needed.
  **+6 to +8 axioms** (`lessor.Recover`, `authStore.Recover`, `RaftCluster.SetBackend`,
  `RaftCluster.Recover`, `Transport.RemoveAllPeers`, the WAL's `SaveSnap`/`Sync`/`Release` as
  needed).
- **S-k. The quota after the swap** [S-0; with S-j]: D22g, (A) a fork commit and re-translation,
  or (B) `isQuota` restated over the captured backend. Small. 0 net.
- **S-l. Lifting the bound** [S-a..S-k but S-r]: `bootOk` without `"%Hnosnap"` (cluster at
  `reNoSnap = false`, `γs.cap = 2^64`), `NewServer.spec` without `receiptBound ≤
  SnapshotCatchUpEntries + 1`, `isServerApplyAll` without `scu`'s bound, `srvMsgSnapC_false` gone,
  putget/putget3 at etcd's defaults (D22f (A)), their closed theorems re-checked
  (`etc/tcb-collections/putget3.txt`). Small-medium. 0 axioms; `compactRaftLog`/`snapshot`
  restated.

Parallelism: S-0 and S-a at once; then the raft chain S-b -> S-c -> S-d (-> S-r) alongside the
server's S-f, S-g, S-i (disjoint files: raft, backend/storage, mvcc, rafthttp); S-h after S-b,
S-f, S-i; S-j after S-d, S-f, S-g, S-i; S-k with S-j; S-l last. Track it with a collection
`etc/tcb-collections/snapshot.txt` (roots: `applySnapshot`, `createMergedSnapshotMessage`,
`sendMergedSnap`, `raft__Step`, the RawNode `Ready`/`Step`).

**Trust base (estimate).** Added: about 11 to 17 trust-boundary axioms (S-f 3-5, S-h 2-4, S-i 0-1,
S-j 6-8), more than D21's "about eight" because `OpenSnapshotBackend`'s and the merged message's
callees are counted one by one and the WAL storage's snapshot calls are new. Restated:
`Transport.Start` (the snapshot stream), `compactRaftLog`, `EtcdServer.snapshot`,
`mvcc.store.restore`, `isQuota` under D22g (B). Removed as premises: `backendNoCompaction` (S-g),
the run bound (S-l). Proved again: `createMergedSnapshotMessage`, `sendMergedSnap` (removed as
false `True`-postcondition axioms in D19p). The raft stages add nothing.

**What the collaborator's bbolt work could discharge later** (each stated here as an axiom at the
backend boundary, none touching `Proof`/`Spec` under `go_etcd_io/bbolt`): `backend.Snapshot()`'s
read transaction sees the committed state (bbolt's `DB.Begin(false)` isolation); `WriteTo`'s
bytes are an image of that state (bbolt's `Tx.WriteTo`); opening a file holding such an image
gives a database with the same state (`bolt.Open` of `Tx.WriteTo`'s output: the `fileHolds`
round trip, `newBackend`'s premise); closing the old backend while its read transactions finish
(`DB.Close`). `os.Rename` keeping `fileHolds` is a file-system fact, not bbolt's.

*Asked of the user:* D22a-i (recommendations: (A) each; D22b (A) reverses the 2026-10-15
preference for the local route, for the reason given; D22g (A) adds a fork commit), and whether
S-r (D22e (A)) is wanted before the server stages finish.

## D23: watchkv's watch path: the workload record, the watch run slots, the plan fixed at start (2026-10-20)

**Problem.** `watch_safe` (the closed theorem of `examples/watchkv`: a prefix watch from revision
1 over one member, writer goroutines, a check that the watched events are exactly the writes)
stopped on three findings (STATUS, "watchkv"): (1) nothing produced the watch service's run slot
(`v3rpc.watchRunSlot`: two watchable-store readers, an auth reader, a reader slot of v3rpc's
`progressReportIntervalMu`); (2) `srvNoDupKeys` (no key twice in a revision of a sealed log) was
not derivable from anything a program can choose; (3) the checks "every event a put", "gap-free
from 2" and "each event a Put some writer tried" need every revision of the log to be one of the
writers' Puts. The user chose (ii): fix 1, add a workload record for 2, keep all four checks.

**Options.** (1) The interval mutex's reader slots: (a) passed from v3rpc's initializer to the
program's `Main` (every program's generated `Init.lean`/`PkgTable.lean` would change, as would
the initializers' output shape); (b) pooled in v3rpc's package fact, borrowed by a thread for the
length of one `GetProgressReportInterval` call against its thread token. (2) The record: (a) a
server-side log of which client operation each committed entry carries (new ghost state in the
apply path); (b) a predicate on operations in the server's workload (`SrvWorkload`, D19q), which
every client deposit must satisfy and which the KV invariant's committed log then obeys. (3) The
"tried" check: (a) the writers' Puts recorded as they go (the plan then grows during the run, not
known to the workload at allocation); (b) all the Puts picked before the member starts.

**Choice.** (1b): `v3rpc.intervalPool` (`v3rpc/BaseWatch.lean`): `k` reader slots, `d` loaned
against `threadToks d` (`ownTokAuth`), `k + d = actualMaxReaders`; the generated v3rpc
`Init.lean` allocates it (`etc/gen-init.py`'s v3rpc entry, its only regenerated file);
`GetProgressReportInterval.spec` takes and returns the caller's `threadTok` and needs
`threadBound ≤ actualMaxReaders` (`2 ^ 30 - 1`): so `watch_safe`'s execution bound is `2 ^ 29`.
`NewServer.spec` exports 64 watch readers (`srvWatchReaders`). (2b): `SrvWorkload.writes : KVOp →
Prop` with `admits_write` (a write request is admitted when its op satisfies `writes`; `admits_kv`
removed); `kvOpAu`/`kvOpAu1` carry `⌜writes op⌝`; `putgetWorkload.writes := True` (every existing
instance's behaviour unchanged, every closed theorem's statement unchanged); the clients' model's
`srvStep` is certified (`certOk`), and `srvNoDupKeys` is stated over certified sealed logs (a
fupd), which `srvNoDupKeys_wk` derives for watchkv's workload (`workload P`: puts of a pair of `P`,
no lease, no flags) through `wk_log` (`kv_cert_read`: a certified log is the KV model of a
committed prefix, whose entries the workload restricts). (3b): `genAll` picks every Put before the
member starts, so `P = tried.map pairOf` is known when the cluster's ghost state is allocated
(`watchkv_alloc`). The Go program calls `cli.Watcher.Watch` (the method `cli.Watch` promotes,
through the embedded field: no client translation change) in a `WithCancel(Background())` context
(cancelled after `collect`): `isEtcdWatcher` needs `isContext`, which `Background()`'s value has
no lemma for. Premises kept explicit: `noRetryableStreamErr` (in `watchkv.premises`) and
`EofOkFromIoInit` (marked as putget's `EofFromIoInit`).

## Trusted initializers: `TrustedCode/`, no-op models for untranslated variable initializers (2026-10-20)

*The decision.* An untranslated package-variable initializer or `func init()` whose readers are
all untranslated is a goose `trusted` declaration with a hand-written model in
`TrustedCode/<pkg>.lean` (as Perennial's `Perennial/TrustedCode`, `948699d06`: a trusted
variable's `X.init` is its whole initialization, allocation included, and a trusted function's
`X.impl` unfolds through the package's `Assumptions`), not an axiom of the translation with a
trust-boundary axiom (`opaqueInitsOk`, `initFuncsOk`) saying it returns. The model does nothing
when Perennial's criterion holds (`errors.errorType`, `log.std`): Go's initializer cannot panic,
no translated code reads the variable, and a translated reader could not load it (no fact gives
a points-to for it). Where goose can translate the real initializer cheaply, it is translated
instead (raftpb's `file_raft_proto_goTypes`, `_depIdxs`), the trust ladder's higher rung.

*Why.* The axioms said only "this returns", about uninterpreted constants; the model says what
the code does as far as any proof can observe, it is reviewable (each docstring quotes the Go
and says why the no-op is faithful), and `etc/gen-init.py` steps through it (`wp_call`), so a
package's init proof rests on no axiom of its own. A no-op is less faithful than translating
when a translated reader exists; then the rung is translating (or a model that allocates and
the fact gives the cell, as `os.Stderr_init` states today).

*Where.* Done for raftpb and protobuf-go's `proto`, `protoreflect` and `internal/impl` (the six
init axioms of the kv adequacy theorem on this repository's translations). `os` and `strconv`
are Perennial's names-only translations: their four axioms (`os.opaqueInitsOk`,
`os.initFuncsOk`, `os.Stderr_init`, `strconv.opaqueInitsOk`) go by a Perennial change
(translating `strconv`'s tables and errors, trusted models for `os` with `Stderr`'s), which also
moves `os`'s fact out of raft's `Base.lean`: deferred (2026-10-20, the user's choice) because
it rebuilds everything and touches a file every raft proof imports. The other packages'
`opaqueInitsOk` (etcd's server, its dependencies; putget's and linkv's trust bases) can follow
the same scheme package by package.

## D19r (E) discharged: `io`'s and `context`'s facts keep `EOF` and `closedchan` (2026-10-20)

The closed theorems took three marked hypotheses, false under the Perennial pin `e81f4a6ce`
(D19r, (E)): `EofFromIoInit` (`isPkgInit io ⊢ v3rpc.eofVar`), `ClosedchanFromContextInit`
(`isPkgInit context ⊢ context.isClosedchanInit`) and watchkv's `EofOkFromIoInit`
(`isPkgInit io ⊢ client.eofOk`). The Perennial change, general and proposed on its own (branch
`init-facts`: `io.isInit` keeps its nine `errors.New` variables as `errors.newVar X msg`, a
persistent points-to of a fixed `*errorString` whose `Error()` returns `msg`; `context.isInit`
keeps `isClosedchanInit`, allocated by the initializer once it closes the channel), makes them
theorems, and they are deleted rather than kept as proved Props:

- `context.isClosedchanInit_of_init` (Perennial's) holds outright, so `Main.spec` loses the
  premise.
- `io.eof_of_init` gives `EOF`'s value with its message, not the method-set facts `eofVar` and
  `eofOk` state (leaf, no `Is`, no `GRPCStatus`, in `error`'s type set): those are about method
  sets, which the semantics leaves uninterpreted, so they stay the classes they already were
  (`ErrorStringLeaf`, `ErrorStringNoGRPCStatus`, `context.ErrorStringIsError`), hypotheses of every
  closed theorem already. `v3rpc.eofVar_of_init` and `client.eofOk_of_init` derive the facts
  from `io`'s package fact under those classes, and each `Main.spec` takes the classes in place of
  the Prop. A Prop premise in `Main.spec` would be more general (it is implied by the classes),
  but nothing is gained by it: the only caller is the closed theorem, which has the classes.
- The `isClosedchanInit` variant of `etc/gen-init.py` (D20, `CLOSEDCHAN`) is kept, with its
  `context` re-proof completed by the new conjunct; it is now redundant (the clean fix it waited
  for is in), and removing it is a separate simplification (`notes/STATUS.md`).


## linkv-txn B1: why the registration rides on a cluster registries' map (2026-10-20)

To show a delivered writing `Txn` ran its ranges (`skip = false`), the result the apply thread
hands `Trigger` must say "not waived" in every case the proposer can receive it. The apply thread
proves it at a *known* registration (`request_delivered`), so each committed entry must carry its
id's registration. Three constraints shaped where:
- The claim (`idClaim`, `srv_claim_mint`) is minted *before* `Register`, whose condition
  (`reqWaitR`) needs it; so the claim cannot carry the registration. The post-`Register` fact
  enters the log where the proposer builds the entry's `entryClaim`, in `kv_prop_au`.
- `entryClaim`/`kvWork` are shared by every member (one `kvInv`, `kvInv_congr`); a member's own
  registry name `ρ.wait` is meaningless to the others. And `ρ.wait` is fixed only in `start`
  (`{ρ with wait := γw}`), after raft's environment (`srvC`, `batchWaitOk ρ`) is fixed at
  `NewServer`. So the entry names the registry through a cluster table, prefix to registry
  (`IdNames.wn`), whose member entries `start` sets (a one-shot cell per prefix: ghost-map
  fragments cannot be updated without the authority).
- An entry of another member's id is never registered here: `reqWaitR`'s prefix clause makes
  `waitTrig` vacuous for it, so the loops pass `none` exactly for those (`entryRegd`'s new clause).
Rejected: fixing the registry name at boot (`wait.New` taking a pre-allocated name; every
example's `Main` replaces `ρ.wait`), and per-claim registration cells in the claims' facts (needs
the registry name in `Φs`, fixed before the registry exists). The fallback (no gets in writing
transactions) was the plan's alternative.

## D24: the partition hooks' axioms and the transport's remotes (2026-10-20, `notes/partition-plan.md` S1/S2)

**Problem.** The partition example (`examples/linkv3p`) cuts and mends links with etcd's own test
hooks, `EtcdServer.CutPeer`/`MendPeer`, which forward to rafthttp's `Transport.CutPeer`/`MendPeer`
(names-only: axioms). The plan's S1 stated them over `transportStarted γn t` alone, on the ground
that pausing a peer only loses messages, which the network model allows. Checking the Go code:
`CutPeer` also calls `Pause` on a *remote* of `id` if there is one, and `remote.Pause` stops the
pipeline, whose `stop` closes a channel unconditionally, so a second `CutPeer` of a remote without
a `MendPeer` in between panics ("close of closed channel"; reproduced,
`issues/etcd-rafthttp-cutpeer-twice-remote-panic.md`). The theorem quantifies over every
schedule, including one that cuts the same link twice, so the S1 axiom was false as stated.

**Options.** (a) Fix the fork (`remote.Pause`/`Resume` idempotent): the axiom is then true of any
started transport; needs the fork pushed and the etcd pin moved (every example's `go.mod`
replaces too), though no translation changes (rafthttp is names-only). (b) A per-link one-shot
"not cut" token, consumed by `CutPeer`, restored by `MendPeer`: its supply has to come from
`Transport.Start`'s axiom (one per possible id), and the partitioner would have to track cut links
(it could: skip a redundant step). (c) Track the transport's remotes in its ghost state: the
exclusive `transportLive γn t rs` records the ids `AddRemote` was called with (`Start` gives `[]`,
`AddRemote` appends, `AddPeer` keeps); giving it up yields `transportStarted γn t` and the
persistent `transportRemotes t rs`; `CutPeer`/`MendPeer` take `id ∉ rs`. `t.remotes` gets a key
only through `AddRemote`, and `transportLive` is exclusive and given up before the transport is
shared, so the list is complete.

**Decision: (c)**, with the server side closed by the bootstrap contract: `bootOk` already describes
a new cluster's bootstrap only (`Hnosnap`: raft started by `StartNode` with the members as peers,
which `bootstrapRaft` does for `!haveWAL && cfg.NewCluster` alone, where `bootstrapCluster` is
`bootstrapNewClusterNoWAL` and `remotes` is nil), so it gains `"%Hrms0" ∷ ⌜rms = []⌝`, true of the
case it describes. `NewServer`'s `AddRemote` loop is then dead (its body closed by contradiction;
`AddRemote`'s result stays a hypothesis of the linked proof), the transport is given up at `[]`,
and `srvNetMember γn s id` carries `transportRemotes t []`. The server's `CutPeer`/`MendPeer`
specs take `srvNetMember` alone (as `RaftHandler`'s axiom does), and their proofs apply the
transport axiom at `rs = []`. Nothing else changes: `transportStarted`, `srvNetMember`'s
signature, `NewServer.spec`, `RaftHandler`, the examples. (a) stays the right fix for etcd (the
issue says so); if the fork takes it, `id ∉ rs` can go. (b) was rejected for the plumbing through
`Start`'s axiom and the example.

**Trust base.** +2 axioms (`rafthttp.Transport.CutPeer`, `MendPeer`); `Transport.Start`,
`AddRemote`, `AddPeer` restated (the remotes list); `bootOk` (a premise, `bootstrapContract`)
stronger by `rms = []`.

## linkv-txn F: a write's commit at a state the model cannot answer; `call` per kind (2026-10-20)

**A write's update commits at every firing.** `write_ok_au` must commit `lintest`'s update when the
server fires it, with the `Output` `call` will return (`outAt i σ`); the model decodes the
output's revision as a natural number (`decOut`), so the commit needs the answer's revision below
`2^64`, which nothing at the firing gives (the server's state carries no bound; the reply's log
is below `2^63`, but the reply comes later). Committing nothing at such a state is not an option:
the state moves, and `LinkvOk`'s configuration must move with it. So at a state where the answer
does not fit, the update commits the write *as failed and applied* (`pSeq_errW_applied`: a write
that returned an error may have taken effect), and its result says so (`wQ`'s right side); the
reply, below `2^63`, contradicts it. The alternative, a bound in the invariant, would need every
deposited write to respect a budget nobody tracks.

**Reads commit at the prophesied revision only**, as linkv's gets: the read update is persistent
(fired at every committed state), the revision prophecy picks the one, and the revisions' map
(now of whole states: lists and read-only transactions read every key) makes every firing at
that revision see the committed state. A state's revision determines it because every server
step keeps the state or moves to the next revision (`kvOpStep_cases`).

**`call` split per kind** (`callGet`, …, `callTxn`, with `cmpsFor` and `txnRes`): the Go program
is this repository's own, and one function per kind gives each its own spec and proof file
(the spec/proof discipline) instead of one proof of five branches, two loops and the txn builder.

**Empty transactions are out of `Apply`'s input** (`GenIn`), not handled: etcd serves them
without the read index (`issues/etcd-txn-empty-serializable.md`), and the client's model agrees
(`txnSerializable` vacuously true), so no read update fires for them; `Gen` never makes one.

## linkv-txn E: the model's inputs and outputs as plain values, and what `ioOk` carries (2026-10-20)

porcupine's model receives an operation as boxed Go values (`OpV`), and `ModelSpec.M` must decode
it purely (`decOp`, from the values alone). A struct holding slices (stage D's `Input.Cmps`,
`Output.Res`) is a value holding pointers whose contents are in the heap, so no pure function of
it is the model's input. Hence `Input`/`Output` were made plain values with bounded, unrolled
fields (at most one comparison, three then- and one else-operation, three results and three
key-values, each with a count), which is all `Gen` produces and all the workload's replies carry
(three keys); robustness's model is no wider on these histories (`TestDifferential` unchanged).
Rejected: decoding through a ghost table of the slices' contents (the model would no longer be a
function of porcupine's operations).

The decoder reads an output by its input's kind (`decOut`), so `outEqual` was narrowed to compare
only those fields (`resEqual`): otherwise a reply equal to the model's answer but differing in an
unread field (a put result's `R`) would be rejected by `Step` and allowed by `pM`, and `Step`
would not refine the model.

`ioOk` carries `ValidIn x` (the input decodes, its keys the workload's): `Step` runs `mstep` on any
input, while `pM` has no step for one that does not decode; `Apply` delivers `ioOk` and knows its
input is `Gen`'s. The configurations' invariant `Bounded n` (`Steps.lean`) carries the pending
inputs' validity for the same reason (a pending write takes effect through `mstep`), and the
revision plus the pending count, so that `mstep`'s revision stays far from overflow: each step
adds at most one to that sum, a pending write taking effect nothing, and porcupine's index stays
below `2^60`.

## linkv3p over linkvtxn's workload: in place, and what moved where (2026-10-20, `notes/linkv3p-txn-plan.md`)

`linkv3p` switched its workload to linkvtxn's in place (its Go `Apply`/`Check` call package
`linkvtxn`), not through a fourth example: linkvtxn's workload includes linkv's (Puts and Gets are
two of its kinds), so the new `linkv3p_safe` implies the old one; everything partition-specific
(`startMember`, `newClient`, `partitioner`, the transport's axioms, `cluster3_alloc`, `Main`'s
structure) is reused unchanged; and `linkv`/`linkv3` keep the plain Put/Get workload as the
simplest end-to-end results. Rejected: a copy `examples/linkv3ptxn` (about 2.7k lines of proof
duplicated) to keep the Put/Get partition theorem beside the new one.

What the swap took: the members keep etcd's `DeleteRange` and `Txn` registrations
(`memberServed`), `clientOk` is linkvtxn's `Apply` premises, `linkvInv_congr` unfolds linkvtxn's
`linkvInvBody` too, and `Apply`/`Check` restate linkvtxn's triples over a slice of clients. No
server, client or raft proof changed, and the trust base is the same (`etc/tcb-collections/
linkv3p.txt`, 463 axioms): linkvtxn's results rest on exactly linkv's. The ghost-state bundle stays
linkv's `linkvGF` (the same functors as `linkvtxnGF`), so the closed theorem's statement is
unchanged. Go: a dependency's `replace` directives do not apply, so `examples/linkv3p/go.mod`
repeats linkvtxn's `go.etcd.io/etcd/tests/v3` replace.
