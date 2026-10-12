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

**Decision:** `build-report.py build` makes `.lake/build-report/sysroot/`, symlinks
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

**Specs are stated for the case reached, not in general.** `joint` only for a `nil`
outgoing map, `nilAwareDelete` only for a `nil` map, `apply`/`Simple` only for
`[AddNode id]` with `id ≠ 0`, `symdiff` with a postcondition that says only "at most 1
under the two inclusions `Simple` establishes" (the exact count would need a bound on
the maps' sizes to rule out `n++` wrapping, which nothing on this path has). Widening
them is ordinary proof work when a reconfiguration path needs it.

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
is verified (`getTxPostLockInsideApplyHook`). *Rejected:* axiomatizing "the applier advances
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
