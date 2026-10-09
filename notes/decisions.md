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

**2026-10-09 · accepted**

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
  `rev + 1` does not overflow.

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
The `unstable` proofs open the predicate with `open_unstable` (the record destructured
first, so that `offset`/`offsetInProgress` are substituted by the value's) and close
it with `close_unstable`/`ownUnstable_intro`. The `raftLog` callers split the field off
with `raftLog_split_unstable` -- the `AccessStrict` macro `split_unstable` is gone,
since every `unstable` method now hands back a value the caller has not seen -- and
rebuild `ownRaftLogCore` at `{ lv with unstable' := uv' }` (`close_unstable_log`,
`ownUnstable_reopen`, `reopen_unstable`).

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

**Tried and reverted: `ownRawNode rn id s rs` as `ownRawNode rn id rs`** with the node's
`NState` as `RNState.raft` (2026-10-08, reverted the same day). It removed nothing: every
node fact in the `RawNode` specs became `rs.raft.*` (the comparisons `nodeHardstate s =
rs.hard` became `nodeHardstate rs.raft = rs.hard`), the update `{ rs with raft := s' }`
hid which layer changed, and the proofs destructured the record again. The rule is about
loose state *arguments*; two cohesive records for two layers (the raft node's `NState`
and the RawNode's own `RNState`) stay two indices.

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
   `InvMisc`, `InvRawnode`, `InvReadylog` and `RawNode.Ready`'s spec; eleven that branch
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
`RNState := { delivered, unpersisted, steps, advanceable }` -- the committed log handed
out so far (`isCommitted γ rs.delivered` inside), the entries `Ready` handed out for the
application to `Append`, the queued local steps (opaque), and the gap flag below. `Ready`
returns `ce` with `isCommitted γ (rs.delivered ++ ce)`; messages carry the opaque
`isRaftMsg γ m`; `HasReady` says nothing about its answer (liveness only); `Ready`'s soft
state, hard state and `MustSync` facts are gone (no spec used them; there is no crash
model), and so are `RNState.soft`/`hard`. `ownRawNode_persist` lends the storage for the
application's `Append` and returns `{ rs with unpersisted := [] }`.

To keep `delivered` across `Propose`/`Advance`, `raft.Step`'s postcondition gained
`LocalStepOk` (for `MsgProp`, `MsgStorageAppendResp`, `MsgStorageApplyResp`: term,
`inprogress`, `unpersisted`, `snap` framed, `applying` kept unless the apply ack moves it).
`PstepCommitMono` is proved (`Step.commit_mono`, `Protocol/Facts.lean`), and Rocq's
`ready_stable_ok` (the append ack is stable once the application appended) too.

**The gap -- to be closed.** `Advance` steps `rn.stepsOnAdvance` through `raft.Step`, and
`raft.Step`'s spec needs facts of each message that nothing records for the
**self-addressed responses** `msgsAfterAppend` queues (a candidate's own vote, a leader's
own `MsgAppResp`): `To = id`, `Term ≠ 0`, the `Entries`' capacity, a non-rejecting self
`MsgAppResp`, and for a `MsgPreVoteResp` a term bound at the state the earlier steps
left, which `Step`'s postcondition does not carry. So `Advance` is proved only for queues
without them, and the specs say so without protocol terms: `Ready` returns
`advanceable` (true exactly when no self response was queued, not stated in the spec),
and `Advance` requires it (and `unpersisted = []`). Consequence: a candidate, and a leader
after any `Ready` with new entries, can neither `Advance` nor `Ready` again; a running
leader is covered only across Readys without new entries, and a one-node cluster commits
nothing through the verified API. **Closing it**: record the per-message facts for the
self responses (in `ownRaftPhys`'s description of `msgsAfterAppend`, or in `pendingRel`),
and carry the term bound through `Step`'s postcondition (or step one's own responses with
dedicated lemmas); then `advanceable` goes and `Advance` takes any queue `Ready` left.
