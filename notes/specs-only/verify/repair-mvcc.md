# Repair: group `mvcc` (storage/mvcc, pkg/v3/adt; snippets mvcc, mvccwatch, adt)

Reports worked from: `A10-storage-provability.md` (3e PASS, 3f FAIL W1), `A10-storage-completeness.md`
(3e/3f PASS with open decisions; F2 touches 3e's `New`), `A11-bbolt-completeness.md` S1, and the
sentinel-error item (A3-provability F4, brief item 3). A grep of every other report for mvcc,
`watchableStore`, `keyBackend` found nothing else addressed to this group (A9's `leasesLive`/`rdOk`
items are 3a's/2d's; A7's `KV.Rev.contract` mentions are "not checked", no finding).

## Findings

### A10-provability W1 (first tier): no law excludes `wsClosed` while `wsOpen` is held: **fixed**

- `ApiWatch.lean`: new law `wsOpen_closed.spec : ∀ ι, wsOpen ι ∗ wsClosed ι ⊢ False`, listed in the
  header's Laws; the `wsOpen` resource entry now says it excludes `wsClosed` and gives the intended
  realization (a ghost variable owned whole, which `Close` discards; `wsClosed` is its discarded
  fraction, so the law is a plain entailment, no invariant opening).
- `watchStream__Watch.lean`: the docstring names the law; a `Changes: verify-round:` line. The triple
  itself is unchanged: it does not take `wsOpen`, because v3rpc's receive loop calls `Watch` while
  `sws.close()` on the handler goroutine may close the stream (`v3rpc/watch.go`), so a caller
  without the token must still see the `wsClosed` arm. (Chose the law over the alternative of a
  `wsOpen`-taking second spec: one spec per function.)
- Snippets: the `Specs:` lines of every `mvccwatch` snippet that calls `Watch` (lifecycle, history,
  progress) now cite `wsOpen_closed`; they hold `wsOpen` from `NewWatchStream` until their
  `defer ws.Close()`, so the refusal of a valid range is refuted.

### A10-provability S2 (second tier): `recvEvents` panics on a stream-wide progress: **fixed**

`examples/specreq/mvccwatch/history.go`: `recvEvents` skips responses with `WatchID == -1` (as
`nextNonProgress` does), header comment updated. `wsRespOk` admits such a progress at any time.

### Sentinel errors (brief item 3, A3-provability F4): **fixed** (mvcc already used the encoding; completed)

- `Api.lean` `init.spec` already gave `ErrCompacted`/`ErrFutureRev` existentially (`∃ x1 x2,
  globalAddr … ↦□ interface.mkOk (*errorString) x`, the `s` field's message, `x1 ≠ x2`), which is
  realizable from `errors.wp_New_errorString` at initialization. Added `ErrRevisionNotFound`
  (`key_index.go:25`): the internal `keyIndex.get`/`tombstone`, `treeIndex.Get`/`unsafeGet`/
  `Tombstone` specs take `globalAddr ErrRevisionNotFound ↦□ e` and their callers test `err == nil`,
  which needs `e ≠ nil`; nothing gave it a source before. Distinctness is now `[x1, x2, x3].Nodup`.
- `ApiWatch.lean` `watch_init.spec` (`ErrEmptyWatcherRange`, `ErrWatcherNotExist`,
  `ErrWatcherDuplicateID`): already existential and non-`nil` (`errMsgOk`); added `⌜[e1, e2,
  e3].Nodup⌝` (true: three fresh allocations), so a caller can tell them apart with `==`.
- adt has no error variables. No Lean constant stands for an mvcc error anywhere.

### A10-completeness F2 (first tier, 4a's; affects 3e's `New`/`NewStore`): mvccrand's boot without `Meta`: **snippet added; spec fix requested of backend-schema**

mvcc's side already supports it (`mvccStorageFor` makes `Meta`'s existence conditional,
`mvccImage_empty` holds either way), so nothing changes in `Spec/.../mvcc`. New snippet
`examples/specreq/mvcc/boot.go` `ReqBootNoMeta` (`mvcc.New` over a fresh backend with no
`CreateMetaBucket`, then `Rev() == 1`, `FirstRev() == -1`; users `examples/mvccrand/mvccrand.go:809-811`).
It is provable once 4a's `keyBackend_intro` has the case below (request).

### A11-bbolt-completeness S1 (second tier): compaction deletes keys its own range returned: **snippet added**

`examples/specreq/mvcc/compact.go` `ReqCompactDeleteReturned`: under `LockForSafeRangeDelete` and
`LockOutsideApply`, `UnsafeRange(Key, start, end, 1000)`, then `UnsafeDelete(Key, keys[i])` with
the returned slices themselves, checking after each delete that no returned key or value changed,
then that a second range has none of the deleted keys (`kvstore_compaction.go:31-71`). It is served
by `keyBackend`'s rows: `rangeLent` against a share of `kbLive`, the delete row giving the key's bytes
back, `D.keys k = D0.keys k` (no put in the session). Through etcd's backend it rests on 4a's
`keyBackend_intro` (whose lock rows are A10 B1, backend-schema's) and bbolt's `txLive`/`txBytes_acc`.

### Not fixed (not first tier, or not this group's)

- **A10-completeness O1** (`KV.Restore.contract` takes the whole `mvccRestoreGate γ 1`, which 2d
  cannot collect from unsynchronized hashers): a recorded open decision (open-questions A8); it
  needs the user's choice (a scope restriction in 2d, or A8's alternative). Not changed.
- **A10-completeness O3** (`Watch`'s id fixed to `0`): recorded scope restriction
  (`issues/etcd-watch-id-reuse-stale-events.md`). Not changed.
- **A10-completeness S1** (2b's `v3rpc/ApiWatch.lean` text on reader tokens is stale): grpc-v3rpc's
  file; request below.
- **A10-completeness S2** (no spec file for the promoted wrappers `storeTxnRead.{Rev,FirstRev,Range}`,
  `storeTxnWrite.FirstRev`): internal, served by the `storeTxnCommon__*` specs through
  `Txn.*.contract`; left as is (not cheap: four new files that only restate the delegate's triple;
  say if wanted).

## Requests to backend-schema

- **`Spec/go_etcd_io/etcd/server/v3/storage/backend/MvccStorage.lean`, `keyBackend_intro`** (A10
  completeness F2): add the case where `Meta` does not exist yet: when `C.made metaBkt = false`,
  `Meta`'s existence cell is in mvcc's footprint (`mvccFp ∪ Fp.made metaBkt`) and `keyDataOf`'s
  `metaMade := V.made metaBkt` (today fixed `true`, `:110`), with the premise `beMade γ metaBkt`
  dropped in that case. Why: `examples/mvccrand` calls `mvcc.New` on a fresh backend without
  `schema.CreateMetaBucket` (`NewStore` makes it, `kvstore.go:121-123`); the snippet
  `mvcc/boot.go ReqBootNoMeta` depends on it, and the old tree served it (`etcdStorage_open.law`).

## Requests to grpc-v3rpc

- **`Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/ApiWatch.lean:86-91`** (A10 completeness
  S1): the "Open (3f's reader tokens)" paragraph is stale: cite 2d's `srvReader_mvcc.spec` for the
  `mvccReaders γ 1` of `Range`, `Rev`, `Watch`, `RequestProgress` in the sendLoop/recvLoop sketches.
- **recvLoop's sketch**: with the new `Mvcc.wsOpen_closed`, a valid create is answered as created
  only where the receive loop can refute `wsClosed ι`; if the handler's `close()` may run
  concurrently (it can: `watch.go`'s `Watch` closes the stream when either loop ends), recvLoop's
  sketch must take the `wsClosed` arm as a possible outcome (the stream is being torn down; the
  response is not sent to a live client) or hold a share of the stream's open state. Check the
  sketch says which.

## New decisions

None. (`wsOpen_closed` is a law the realization meets as planned; the sentinel encoding is the
brief's.)

## Build

`etc/specs-build.sh --dir Spec/go_etcd_io/etcd/server/v3/storage/mvcc`: OK (184 modules).
`etc/specs-build.sh --dir Spec/go_etcd_io/etcd/pkg/v3/adt`: OK (31 modules; no file changed there).
`go vet ./specreq/mvcc/... ./specreq/mvccwatch/... ./specreq/adt/...`: clean; `gofmt -l`: nothing.

## Second pass (coordinator's list, `second-pass.md`)

### `wStep`'s events, outside the `exactFrom` guard (client-watch's request): **fixed**

`ApiWatch.lean` `wStep`, events case: new unconditional conjunct `∀ e ∈ r.evs, ∃ rv ev, ev ∈
h.eventsAt rv ∧ e = evOf rv ev ∧ e.kv.modRevision = W64 rv ∧ W.keeps rv ev` (a kept history event:
key in the watcher's range, no filter drops it, `ModRevision` its revision), mirroring 1b's
`watchStep`. True at every compaction state: `syncWatchers` reads backend records of real
revisions and `kvsToEvents` keeps those `w.contains`; `notify` passes the committing txn's own
changes; `watcher.send` applies the filters; a delete's `ModRevision` is patched to its revision.
Docstring updated. 2b's chain can now take it from here.

### `ctxErr_not_errIs` (apply-txn's request 1): **fixed, and a soundness bug found on the way**

`rangeResOwn`'s `.ctxErr` case said `context.isCtxErr err` (the context's own `Canceled`/
`DeadlineExceeded` value). That is **false of the code**: `rangeKeys` returns
`fmt.Errorf("rangeKeys: context cancelled: %w", ctx.Err())` (`kvstore_txn.go:121`), a fresh wrapper.
Now it gives a new opaque persistent `rangeCtxErr err` (`Api.lean`), with laws
`rangeCtxErr_persistent`, `rangeCtxErr_ne_nil` and `rangeCtxErr_fresh` (no `*errorString` whose `s`
is another message than the format `rangeCtxFmt`; true in Go, where the value is a `*fmt.wrapError`,
and in Perennial's `Errorf` model, an `*errorString` of the format). With `Mvcc.init`'s messages it
excludes mvcc's sentinels; with the other owners' shapes theirs (request to apply-txn/server-core
below). `storeTxnCommon__rangeKeys.lean`'s sketch and Changes updated. Trust note: Perennial's
`fmt.Errorf.spec` requires `ArgsWf` (basic-typed arguments), which an error argument is not, so the
`rangeKeys` proof rests on the `Errorf` model there (a `notes/perennial-changes.md` entry is owed by
the coordinator: this group does not edit notes outside its report). No user relied on
`isCtxErr` from this case (grep: none outside mvcc).

### `rrOwn`'s `kvFits` (apply-txn's request 2): **already met; their text is stale**

`Model.lean`'s `kvSortOk` (inside `kvsFit`, which `rangeResult` gives for every key-value a range
returns) already includes `-2 ^ 63 ≤ kv.lease ∧ kv.lease < 2 ^ 63` (added at integration I5), so
txn's `kvFits` follows from it field by field. `txn/executeRange.lean:14`'s "kvsFit bounds the
revisions and the version only" is stale (request below).

### `Mvcc.init`'s sentinels against server-core's `sentinelAt`: **aligned (the lease way)**

`Mvcc.init.spec` already gives each global's value existentially with its message (the brief's
encoding). Of server-core's two options I chose the lease one: the tie `globalAddr ErrCompacted ↦□ v
⊢ srvErr v .compacted` (and `.futureRev`) goes in `etcdserver/errors/Api.lean`, because mvcc is a
lower layer and its API should not import the server's error vocabulary (`errors/Api` already
reaches mvcc's `Model`/`ApiStorage` through lease; it does not reach `mvcc/Api`, so `errors/Api`
importing `mvcc/Api` is acyclic). `init.spec`'s docstring says so. Request below.

### `Proto.norm` survival (grpc-v3rpc's request): **nothing to add**

mvcc and adt own no relation over `Proto.Content`: the only message-shaped one, `InternalStore`'s
`kvDecodes vb m`, relates bytes to a `KeyValueM` model (a content never appears), and the
`KeyValue` relation it is realized with is 3h's `keyValueHolds`, already in `holds_norm`. mvccpb's
vocabulary is client-core's/3h's, not this group's.

### Requests to server-core (second pass)

- **`Spec/go_etcd_io/etcd/server/v3/etcdserver/errors/Api.lean`**: add `public import
  Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api` and
  ```lean
  def mvccErr_srv.spec : Prop := ∀ (g : GoString) (e : EtcdErr) (v : GoInterface),
    (g, e) ∈ [(go_etcd_io.etcd.server.v3.storage.mvcc.ErrCompacted, EtcdErr.compacted),
              (go_etcd_io.etcd.server.v3.storage.mvcc.ErrFutureRev, EtcdErr.futureRev)] →
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ globalAddr g ↦□ v ⊢
      srvErr v e
  ```
  (realizable from `Mvcc.init`'s concrete `*errorString` and message, as `leaseErr_srv`).
- Optionally, `srvErr_rangeCtx.spec : ∀ err e, Mvcc.rangeCtxErr err ∗ srvErr err e ⊢ False`, if
  `srvErr`'s realization carries the `*errorString` and rpctypes' message (then it follows from
  `rangeCtxErr_fresh`); it lets txn's `ctxErr_not_errIs` cover lease's and `errors`' sentinels in one
  step.

### Requests to apply-txn (second pass)

- `txn/executeRange.lean:11-15` and `txn/Api.lean:74-76`: both items are met. `ctxErr err` is
  realized from `Mvcc.rangeCtxErr err` (wrapped again by `executeTxn`); `ctxErr_not_errIs` from
  `rangeCtxErr_fresh` with `Mvcc.init` (mvcc's sentinels) and the other owners' sentinel shapes (or
  server-core's `srvErr_rangeCtx`, above); `kvFits` from `kvsFit`'s `kvSortOk`.

### Build (second pass)

`etc/specs-build.sh --dir Spec/go_etcd_io/etcd/server/v3/storage/mvcc`: OK (184 modules), after waiting out a parse error in backend-schema's in-progress `schema/Api.lean`. `go vet` of the mvcc, mvccwatch, adt snippets: clean (no snippet changed in this pass). `rangeResOwn`'s signature is unchanged, so its importers (txn) see only the `.ctxErr` case's new conjunct.
