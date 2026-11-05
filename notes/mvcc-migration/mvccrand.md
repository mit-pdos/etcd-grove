# mvcc's randomized tester (`examples/mvccrand`) over mvcc's frozen API: hand-off

Branch `mvcc-api`. The task (the coordinator, 2026-11-05): specs and proofs of the tester's
functions over the frozen API (`Spec/go_etcd_io/etcd/server/v3/storage/mvcc/Api.lean`,
`ApiState.lean`), its top-level result, and every API statement too weak for a check it makes.
The tester's design: `notes/mvccrand.md`. Files: `Spec/github_com/mit_pdos/etcd_grove/examples/
mvccrand/`, `Proof/github_com/mit_pdos/etcd_grove/examples/mvccrand/`.

## Done

- `Base.lean`: the package fact (`mvccrandInit`: `keys` and `extraEnds` hold read-only slices of
  `keyList`, `extraEndList`) and its `isPkgInit` instance. **For the coordinator**: the package's
  `Init.lean` (`wp_initialize'`) is `etc/gen-init.py`'s, which has no entry for `mvccrand` (its two
  variables are composite literals: a `SPECIAL` entry giving `mvccrandInit`); outside this track's
  paths.
- `check` (spec, proof), `inRange` (spec over `inRangeM`, the tester's model of a range, which is
  mvcc's `inRange` off the single-key case; proof), `rng.next` (some number), `rng.intn` (in
  `[0, n)` for `n > 0`), `checkKV` (returns when the key-value is the model's record, `kvMatches`;
  the struct's points-to kept by the call, the slices given back). All proved, no `sorry`.
- `Model.lean` (pure): the tester's maps against mvcc's states (`stMatch`, `kvOfRec`), and the
  probe of the read contract, **`answers_keys_eq_match`** (proved): for a log with `txn.LogOk`
  (which `Txn.Range.contract`'s `LogWf'` and change-count facts give, `txn.LogOk.of_cert`), the
  keys `rangeAnswers` answers at a revision, through which `rangeOutcomeC` gives the count, the
  limit's cut and the key-values in order, are exactly `checkRange`'s `match` (the tester's keys in
  its order, in its map and in the range). Imports txn's `Lemmas` (`rangeAnswers_keys`), which
  imports only mvcc's `ApiState`. And `covers_eq_inRangeM` (proved): the range `Watch`
  registers (`watchRangeOf`, its affine `covers`, through which `wsRecvOk` selects a watcher's
  events) is the tester's `inRange` for non-empty keys.
- `checkRange`: the spec (`Spec/.../checkRange.lean`: from `rangeOutcome` at a well-formed log
  whose states match the tester's maps up to `cur`, and `res ≠ null`, it returns). Its proof is
  in progress outside the tree (`~/.claude-D/jobs/e4ba2bf8/tmp/mvccrand-wip/checkRange.lean`, not
  committed: it has a `sorry`): done, the context-error arm excluded, the future arm (its
  `err == ErrFutureRev` through `mvccInit`'s `errorsNewVar`, G2), the result's two shapes merged and
  split into fields, `rev := rangeRev`; left, the match loop (`slice.forRange` over `keys`, invariant
  `match = (keyList.take i).filter …`, giving `matchKeys`), `n`/`taken`/`total` against
  `rangeTotal`/`rangeTaken` (txn's `rangeTotal_stateAt`, `rangeTaken_eq` with
  `answers_keys_eq_match`), and the key-value loop (`rangeKvs`' `i`-th element, `kvPtrIs` to
  `kvMatches` through `stMatch`, then `checkKV`).

## The checks against the API (2026-11-05, by reading; each to be proved)

Every check the tester makes of mvcc, the API statement that justifies it, and the client-side
argument (all over one invariant holding `mvccState γ σ`, the stream's `wsState ι S`, the history's
ghost copy and the published revision; `σ.crev = -1` throughout: the tester never compacts, and
only `Compact`/`Restore` move it).

| Check (Go) | Justified by |
|---|---|
| `kv.Rev() == 1` after `New` | `New.spec` (`mvccState γ mvccStart`), `KV.Rev.contract` |
| writer: `tw.Rev() == p.rev-1`, `tw.Rev() == cur` (txn) | `KV.Write.contract` (the update at `σ`, nothing pending), `Txn.Rev.contract`; the writer is the only one stepping `σ` (the invariant's half of the log) |
| writer: `checkHook(i)` after `Write` | `hookRun P f Pre Q` with the tester's closure's triple (`Pre`: `applying ↦ i`, `saved ↦ s ≤ i`), `Q` back in `Write`'s post |
| `tw.Put(...) == p.rev` | `Txn.Put.contract` (`W64 σ.log.length`) |
| `tw.DeleteRange`: count, revision | `Txn.DeleteRange.contract` (`ds`, `writeRev`); `delKeys` in key order = the tester's `keys` order |
| `len(tw.Changes()) > 0` iff the model's | `Txn.Changes.contract` (`k.pend.length`, `0 ≤ sint.Z`) |
| `kv.Rev() == want` after `End`, then publish | `Txn.End.contract`'s two updates (`σ.notify pend`, `commitPending`), `KV.Rev.contract` |
| readers: `floor <= cur`, `cur < len(history)` (`seen`) | `KV.Read.contract`/`KV.Rev.contract`: the update fires at the invariant's `σ`, `published ≤ σ.rev < σ.log.length ≤ len(states)` (the writer appends before `End`, publishes after) |
| `tr.FirstRev() == -1` | `Txn.FirstRev.contract` (`W64 σ.crev`), `σ.crev = -1` |
| `checkRange`: `ErrFutureRev`, `Count == -1`, `Rev`, no key-values | `Txn.Range.contract`'s `rangeOutcomeC` at `c = -1` (`rangeOutcomeC_neg`): the future arm |
| `checkRange`: `err == nil`, `Rev == cur` | the third arm; the context-error arm is excluded by `todo = true → r ≠ null` (`rangeCtx true` of `context.TODO()`) |
| `checkRange`: `Count` (count-only, limit, total) | `rangeAnswers`/`rangeTotal` at `stateAt`, through txn's `rangeAnswers_stateAt`, `rangeTotal_stateAt` (need `LogOk`: the contract's `LogWf'` and change-count facts, gap A of txn's track) |
| `checkKV`: key, create/mod revision, version, value, lease; keys-only: no value | `rangeKvs`/`kvPtrIs` (full: every field; keys-only: `Value' := slice.nil`) at `stateAt`, the tester's `kvRec` the client model's `putKv` |
| read-only txn: `tw.Rev() == cur && len(tw.Changes()) == 0` | `NewReadOnlyTxnWrite.spec`, `Txn.Rev`, `Txn.Changes` (`.read`: no pending) |
| `GetLease(k) == lease` | `isLessor`'s/`lessor.GetLease.spec` over `leaseOwn γl L (pendItems σ.log [])` = `leaseItemsOf (stateAfter σ.log)` (`pendItems_nil`) |
| `Watch`: empty range fails with `ErrEmptyWatcherRange`, `-1`; else no error | `WatchStream.Watch.contract`: its first arm exactly the empty range (`e ≠ [] ∧ ¬ GoStringLt kk e`), the second at an open stream `nil` (the tester's stream is open until the end: `S.closed = false` in the invariant). (`notes/mvccrand.md`'s first obstruction is gone.) |
| `receive`: `CompactRevision == 0` | `wsRecvOk` part 1 (`compactRev ≠ 0 → 0 < compactRev ≤ σ.crev = -1`) through `wsRecv_ok.law` |
| `receive`: a progress response's revision written | part 1 (`compactRev = 0 → rev < σ.notifiedLog.length ≤ len(states)`) |
| `receive`: a watcher's progress after its changes up to `P` | part 3 (`r.id = id`), `onceUpTo` vacuous at `σ.crev = -1` |
| `receive`: an event's watcher known, `r <= resp.Revision`, the next expected change, its type and fields | part 1 (a `-1` response has no events; an id the stream has, `c.watchers` = `S.ws`'s domain under `c.mu`), part 2 (`recvEvs = watchEvents …`: the events exactly the range's changes from `lo`, in order), `evIs`/`kvPtrFixed` (all fields), `evOfKv` (a delete: `zeroKv` at the revision) |
| `kv.Close() == nil` | `KV.Close.contract` (`RET nil`) |

So for every check of mvcc itself the frozen contracts are exact enough. What blocks is below.

## Found: API statements too weak for the tester

**G1 (blocking every write; found 2026-11-05). `backendRest` is opaque (`iprop(True)`) with no
law.** `Api.lean`:

```
opaque backendRest (γB : backend.BNames) (P : backend.BParams) (K : backend.BNames → IProp GF)
  (b : Loc) (D : backend.Data) : IProp GF := iprop(True)
```

`mvccBackendFor_open.law` consumes the whole `backend.newPostKP γB P (fun _ => mvccW gx) Pk K b D`
(which holds `plHook γB func.nil`, `rbOwn γB (rbData P D)`, `K γB`, `isStopChans γB b`,
`rdPool γB P b`) and gives back only `mvccBackendFor … ∗ backendRest γB P K b D`, from which no law
gets anything. So after the law:

- the client has no `plHook γB f`, so it can neither call `SetTxPostLockInsideApplyHook` (its spec
  takes `plHook γ f`) nor freeze the hook (`plHookRO`): **no `hookIs B f` for any `f`, so no
  `KV.Write.contract` (hence no `Put`, `DeleteRange`, `Txn` write, `checkHook`), no lease
  `Revoke`/`Grant` (they take `hookIs B f`)**. The tester sets its hook after `mvcc.New`, as the
  server does (`getTxPostLockInsideApplyHook`);
- it has no `rbOwn`, so no `rbPart γB S r` for `lease.NewLessor.spec` (the tester and the server
  call `NewLessor` between `backend.New` and `mvcc.New`; the law cannot be applied after
  `NewLessor` either: `NewLessor` gives back `rbOwnIn γB S (r.insert "lease" ∅)`, not the
  `rbOwn γB (rbData P D)` `newPostKP` needs), nor the lease bucket's part for `Grant`/`Revoke`;
- `K γB` (the client's write-back tokens and open token, which `NewLessor`'s `wbTok`/`bOpen`, the
  hook's `wbTok` need) is lost too, unless split off before (it is inside `newPostKP` as well).

The docstring already says what `backendRest` holds ("its stop channels, its hook's exclusive half
at `nil` (to set, or to freeze at `nil`), its other buckets' rights …, the reader pool, and `K`").
**Minimal strengthening**: define it (transparent, `@[expose]`) as what `newPostKP` has beyond the
store's part, or add the law

```
abbrev backendRest_open.law : Prop :=
  ∀ γB P K b D, backendRest (GF := GF) γB P K b D ⊢
    backend.isStopChans γB b ∗ K γB ∗ backend.plHook γB func.nil ∗
    backend.rbOwn γB (backend.rbData P D) ∗ backend.rdPool γB P b
```

(the tester needs the first four. The server's boot, which also sets the hook and makes the lessor
after `backend.New`, would need the same of its `bootBackend.law`'s `backendRest`; not checked.)

**G2 (latent: holds today only through mvcc's internals; found 2026-11-05). The API states no fact
of mvcc's error variables' values, which a client's `==` on them needs.** The contracts give an error
as `globalAddr ErrFutureRev ↦□ err` (`rangeOutcome`'s future arm), `globalAddr ErrEmptyWatcherRange
↦□ err` (`WatchStream.Watch.contract`), `ErrCompacted`, `ErrWatcherNotExist`. The tester compares
(`err == mvcc.ErrFutureRev` in `checkRange`, `err == mvcc.ErrEmptyWatcherRange` in `register`), and
Go's interface `==` panics on a non-comparable dynamic type (Perennial's `go_eq_interface`:
`CheckComparable i1.ty`), so the proof needs the variables' dynamic type. Today it unfolds
`isPkgInit mvcc` to `mvccInit` (`isPkgInit_access`; `errorsNewVar`: an `*errors.errorString`), as
the migrated server does (`applierV3backend__Compaction.lean`, `DispatchKVL.lean`): `mvccInit` is in
mvcc's `Base.lean`, in `etc/api/mvcc.txt`'s debt group, so sealing `isPkgInit mvcc` breaks every
such client. **Minimal strengthening**: a law in `Api.lean`, e.g.
`errVars.law : isPkgInit mvcc ⊢ errorsNewVar ErrCompacted "…" ∗ errorsNewVar ErrFutureRev "…" ∗
errorsNewVar ErrEmptyWatcherRange "…"` (or a weaker `∃ x, globalAddr X ↦□ interface.mkOk
(PointerType errorString.ty) #x` per variable; `ErrWatcherNotExist`, which `Cancel` returns, has
no such fact even in `mvccInit`, only `∃ e, globalAddr … ↦□ ok e`).

## Blockers outside mvcc's API (for the top-level result)

- `lease.NewLessor.spec` (an axiom) takes `lease.clusterOk cl`, a non-nil cluster; the tester
  passes `nil` (safe in Go: `cluster` is read only by `shouldPersistCheckpoints`, from `Checkpoint`
  and the promoted loop, neither reached). As `notes/mvccrand.md` (2) found.
- `backend.New.spec` allows a panic unconditionally (`notes/mvccrand.md` (6)).
- `be.Close() == nil` and `le.Stop()`: shutdown out of scope (decision 1, 2026-11-03): `KV.Close`
  gives nothing back of the backend. So `Run`'s last check is not provable; the top-level result
  must stop before `kv.Close()`'s successors (as decided: "proved up to them, or `Main` without
  them").
- Iris premises of the closed theorem: `fileHolds "mvccrand.db" D` (fresh), `keySized`
  (`mvccBackendFor_open.law`'s `□ ∀ γ b', keySized γ P b'`), `ckptEffectsOk`.
- Not examined in depth (the lease package): `Lookup`'s exactness (`lessor.Lookup.spec`'s
  `lookupView`) for "a revoked lease is gone" / "a live lease is found", `Lease.Keys`' `keysPre`.

## Left

- `checkRange`'s proof (above); the specs and proofs of the rest: `rng.genKey`/`genEnd`/`genRange`,
  `copyState`, `pending.put`/`del`, `history.*`, `writer.*` (the write paths over `KV.Write`,
  `Txn.*`, `Txn.End`; the hook's triple for `hookRun`), `reader`, `watchCheck.*` (`receive` over
  `wsChan_recv.law` and `wsRecv_ok.law`), `itoa`, `Run`, `Main`.
- The invariants (one design, by the table above): an invariant holding `mvccState γ σ` (with
  `σ.crev = -1`, `σ.pending` the writer's), `wsState ι S` (`S.closed = false` until `Run`'s
  `ws.Close()`), a ghost copy of the history (`states`, `changes`) with `σ.notifiedLog`'s
  revisions a prefix of it, `published ≤ σ.rev`; the writer's half of the log; `c.mu`'s lock
  invariant tying `c.watchers` to `S.ws`'s domain and each watcher's position to its received
  events; the ticks channel's values `≥ 1` (`intn(pub + 1)`).
- `Init.lean` (gen-init.py, the coordinator's), `Link.lean`, `Results.lean`, and the closed
  theorem, which cannot be stated as "`Main` does not panic" until G1 is fixed (every write),
  `lease.NewLessor`'s `clusterOk` admits `nil`, and with `be.Close()` out of scope.
- No placeholder (`M1-REPLACE`) committed: nothing proved rests on a gap yet.
