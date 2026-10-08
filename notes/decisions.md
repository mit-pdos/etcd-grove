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
  through those `IntoValTyped` instances for every field access.
