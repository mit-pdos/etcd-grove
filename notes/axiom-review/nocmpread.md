# `mvcc.kbNoCmp_metaNone`: refuted (2026-10-29)

**Reviewed:** the axiom `mvcc.kbNoCmp_metaNone`
(`Proof/go_etcd_io/etcd/server/v3/storage/mvcc/NoCmpRead.lean:38`, `origin/lean` at `b1712c2187`;
added by the restore plan's R4 option 1, `a90066a654`, and given the `keyReadSnapC` case by R5c, `5793036593`), with the definitions it is stated in
(`InvStore.lean`: `kbNoCmp`, `keyReadSnap`, `keyReadSnapC`, `metaReadSpec`). etcd at the pin of
`etc/goose.py`'s project `etcd` (the fork's `249d76bea`). First raised by the backend stage's
review round 6 (`backend-cmp:notes/spec-first-study/backend-review-6.md`, R6-1).

**Verdict: refuted, by a proved counterexample.** The axiom is false of the Go code. A program
that panics in Go has a triple, with no `sorry`, saying it returns, from this axiom and mvcc's
proved specs alone. Not fixed: a restatement is proposed below, for the user.

## The claim

```
axiom kbNoCmp_metaNone (γ : StoreNames) (RT : IProp GF) (Del : GoString → IProp GF)
    (rt : GoInterfaceOk) (m : Bucket) (L : IProp GF) :
    kbNoCmp γ.kb γ.bucket ⊢
      (keyReadSnap (bucketView γ) RT Del true rt m L ∨ keyReadSnapC (bucketViewC γ) RT rt m L) -∗
      □ metaReadSpec rt true
```

In plain words:
- `kbNoCmp γ.kb γ.bucket` is one backend's token that its `Meta` bucket holds neither
  compaction key. For the real backend, `storage.OpenBackend`'s axiom gives it for a file
  without them (`noCmpData`). `NewStore` takes it, and `store.restore` consumes it.
- The premise: `rt` is a read transaction over the store's view, with the lock right `L`.
- The conclusion, persistent: every `rt.UnsafeRange(Meta, k, nil, 0)` at a compaction key `k`
  returns no key and no value, at any time, from precondition `True` (no lock).

## The gap

The premise does not tie `rt` to the backend.
- `keyReadSnap View RT Del rng rt m L` is `□ ∀ q, {{ L ∗ View q m }} rt.RLock() {{ … }}`
  (`InvStore.lean:706-709`), and `keyReadSnapC` has the same shape.
- With `L := False`, the triple's precondition is false, so both hold of **any** `rt`,
  whatever its `RLock` does (`keyReadSnap_false` below, three tactics).
- So from one backend's token the axiom gives `□ metaReadSpec rt true` for every value `rt`:
  any reader, of any backend, at any later time, finds no compaction.

Go does find one. `baseReadTx.UnsafeRange` (`server/storage/backend/read_tx.go`) reads the
`Meta` bucket's key from the read buffer or bbolt and returns it when it is there. The store's
compaction writes `finishedCompactRev` (`UnsafeSetFinishedCompact`, in the compaction job
`kvstore_compaction.go`), so the same backend that had the token finds the key after a
`Compact`. A second backend over a file holding the key finds it too.

The conclusion's persistence is a second, independent fault: even for the store's own reader,
the fact is true only until the store compacts (M2's compaction mode would make it false that
way).

## The counterexample

**Go** (`examples/axiomcx/nocmpread/nocmpread.go`):

```go
func Check(tx backend.UnsafeReader) {
	if _, found := mvcc.UnsafeReadFinishedCompact(tx); found {
		panic("kbNoCmp_metaNone: a finished compaction is recorded")
	}
}
```

**It panics** (`nocmpread_test.go`, `GOTOOLCHAIN=go1.27.3`, etcd at the pin through
`examples/go.mod`'s replaces). The test:
1. opens a new backend (`betesting.NewDefaultTmpBackend`), whose file records no compaction:
   the state `OpenBackend` gives `bkNoCmp` in, and `NewStore`'s premise;
2. runs a store over it (`mvcc.NewStore`): two `Put`s, then `Compact(2)`, waiting for the job;
3. calls `Check` on the backend's own `ReadTx()`, under `RLock`.

Every run:

```
=== RUN   TestCheckPanics
    nocmpread_test.go:42: Check panicked: kbNoCmp_metaNone: a finished compaction is recorded
--- PASS: TestCheckPanics (0.00s)
```

**The proof**
(`Proof/github_com/mit_pdos/etcd_grove/examples/axiomcx/nocmpread/Check.lean`, goose project
`axiomcx-nocmpread`). For every store `γ` and every reader `rt`:

```
{{ isPkgInit nocmpread ∗ mvcc.kbNoCmp γ.kb γ.bucket }} Check(rt) {{ RET #(); True }}
```

- `Check.wp_proof` takes the axiom's statement (verbatim, `kbNoCmp_metaNone.stmt`) and
  `mvcc.UnsafeReadFinishedCompact.spec` as hypotheses. It instantiates the axiom at `L := False`
  (`keyReadSnap_false`), and `UnsafeReadFinishedCompact`'s spec at `nc = true` gives
  `found = false`.
- `Check.wp_axioms` instantiates the hypotheses with the axiom and mvcc's linked
  `mvcc.wp_UnsafeReadFinishedCompact` (proved; through `BytesToRev`, `BytesToBucketKey`).
- `lake build` of the module passes.

`#print axioms`:
- `Check.wp_axioms` prints exactly `Check.wp_proof`'s list plus `mvcc.kbNoCmp_metaNone`.
- `Check.wp_proof`'s list is 1093 names: Lean's three; the opaque declarations of the imported
  translations (`net.*`, `crypto.tls.*`, `google_golang_org.*` types, `fmt.pp`, ...), which make
  no claim; and one of this repository's, `backend.optsAt`, an opaque predicate declaration
  reached through mvcc's definitions, also no claim.
- No `sorryAx`, and no other trust-boundary spec.

The precondition `kbNoCmp` is a ghost token, not a Go fact, so the theorem is not closed. The
token is what every caller of `NewStore` holds: `OpenBackend` gives it over any file without the
keys, and the server's closed theorems obtain it that way. The test is that situation, then a
compaction.

## What rests on it

From `etc/tcb-report.py`'s data (`backend-cmp`'s `.lake/tcb.json` at `7c7097a342`, which
differs from `lean` only by the backend stage, not here), 41 roots use the axiom. The exported
ones:
- `putget_safe`, `putget_Main`, `putget3_safe`, `putget3_Main`;
- `linkv3p_safe`, `linkv3p_watch_safe`, `linkv3p_Main`, `linkv3p_MainWatch`;
- `linkvtxn_safe`, `linkvtxn_Main`, `watch_safe`, `watchkv_Main`;
- `cache_safe`, `cachekv_Main`, `k8setcd3_safe`, `k8setcd3_Main`;
- `authkv_startServer`, `common.wp_StartMember`;
- `server_kv_backend_hooks`, `server_kv_watchable`, `mvcc.watchableStore.wp_Restore`.

**Their uses are of true instances.** The axiom is applied twice, both in
`store__restore.lean` (`:85`, `:596`), to the store's own `ReadTx()` with the `L` its
`ReadTx` spec returned. That is right after the backend was opened, before any store over it
can compact, where Go indeed finds no key. No result's conclusion is known to be false. But they
rest on a false axiom.

**Inconsistency was not attempted.** A closed adequacy theorem of a program that opens a backend
(`OpenBackend` gives the token) and then calls `Check` on a reader whose `UnsafeRange` returns
the key would contradict GooseLang's own semantics. That would make Lean derive `False` under
the closed theorem's premises. Probably feasible, not done.

## Proposed restatement (not applied; the user's)

**The first proposal is false too (found 2026-10-29, when asked to apply it).** It was the
reviewer's (a′): anchor `rt` to the backend's own read transaction (`rtHeld`), hold the fact only
under the reader's lock, and consume the token in one read. But the backend's proved
`batchTx.UnsafePut` (`Spec/.../backend/batchTx__UnsafePut.lean`) lets any holder of the batch lock
(`btW`) put any key into `Meta`. The model tracks no compaction key: `Meta` is a hook bucket,
outside the readers' view `vd` (`keyView`), and the compaction keys are not hook keys
(`hkData`).

So a program can falsify (a′):
1. open a backend over a file without the keys (`OpenBackend` gives `bkNoCmp`);
2. put `finishedCompactRev` into `Meta` through the batch transaction and unlock;
3. `ReadTx().RLock()`, then apply (a′) to the backend's own held reader.

(a′) claims the read finds nothing; Go finds the key. A token about the data at open cannot
survive writes the model does not forbid. Any true statement must make a write of a compaction
key incompatible with the token.

**A true design (recommended): the backend tracks the compaction keys' absence.**
- **Ghost state.** The backend gets a two-halves ghost `fk : Bool`:
  - the backend's invariant keeps one half, and states that `fk = true` means no state it
    holds has a key of `P.FK` (the `Meta` compaction keys, a new `BParams` field). That covers
    the committed data, the buffers, and every reader's snapshot (`H`).
  - the client holds the other half.
- **`OpenBackend`'s axiom** gives the client's half, at `true` when `noCmpData D`, at `false`
  otherwise. Its claim is about the file at open, as today.
- **Puts.** A put of a key in `P.FK` takes the client's half at `false`.
- **Reads.** Under the client's half at `true`, a held reader's `rtRange` at those keys is
  empty, as a lemma of the backend (proved, no axiom).
- **mvcc.** `bkNoCmp d.γB` becomes the half at `true`, defined rather than opaque.
  `kbNoCmp_metaNone` becomes a theorem of the bridge over the reader's lock token, and
  `metaReadSpec` takes that token and lends its slices (`backend-cmp`'s batch, question 3).
- **Who flips the token.** `restore` turns the half to `false` after its reads and hands it to
  the store, where the compaction's `Meta` puts (`metaPutCap`, `backend-cmp`) take it.
- **Cost.** The `axiom` is gone, but `OpenBackend` (a trusted statement), the backend's model
  and its put/commit proofs, both bridges, and `store.restore` (the restore track) all change.

A cheaper true alternative: drop the "nothing found" claim, and prove `restore` over a `Meta` that
may hold the keys (Go's other path: `compactMainRev`, `currentRev`, `compactLockfree`). That
needs the keys' value form in the backend (`BParams.VI`) and the restore path's compaction:
larger in `restore`, smaller in the backend.

Until the user picks one, the axiom stays, with this report as its audit row.

**Fixed (2026-10-29, `backend-cmp` `2e49ff1aa9`, the user's choice):** the backend tracks the compaction
keys' absence (a monotone flag, half the client's); the axiom is deleted and `store.restore` reads
through its reader's proved clause. Reviewed in `backend-cmp`'s rounds 7-9. On `lean` the axiom stays
until `backend-cmp` merges.
