# Batch 3f, review round 1 (provability and completeness)

Reviewer of batch 3f: mvcc's watchable store (`watchable_store.go`, `watchable_store_txn.go`,
`watcher.go`, `watcher_group.go`) and `pkg/v3/adt`. Commit under review: `7be7104958` (HEAD of
`specs-only`). I read the Go code, 2b's and 1b's statements that consume 3f, 3d's and 2a's adt uses,
and `examples/mvccrand`. The snippets vet (`go vet ./specreq/mvccwatch/ ./specreq/adt/`: clean). I
did not build the Lean files.

Go paths below are under `.lake/src/server/storage/mvcc/` unless another path is given. Spec paths
are under `SpecPlan/Spec/go_etcd_io/etcd/server/v3/storage/mvcc/` (`S/`) or `SpecPlan/Spec/go_etcd_io/etcd/pkg/v3/adt/`
(`A/`).

## What is good

* **`wsRespOk` follows what the code does on the main paths.** Each response carries persistent
  facts against a reached history (`mvccLb`). Positions advance only on the watcher's own responses
  or on a stream-wide progress after its stamp. I checked the following against the code and found
  them right:
  * **Whole revisions.** `notify` sends exactly one revision (`watchable_store.go:484`). The
    1000-revision cut happens at a revision boundary (`watcher_group.go:55-60`), with the header at
    `curRev` (`watchable_store.go:401`) or `minRev-1` for a victim (`:308`). Both satisfy
    `c' ≤ r.rev ≤ h.rev`.
  * **Filtered-out batches.** A batch whose events were all filtered out is never sent
    (`watchable_store.go:624`), and `wEvents` filters the same way.
  * **Stream-wide progress.** A `-1` response is sent only when every watcher in `ws.watchers` is
    synced and `rev ≥ startRev` (`:535-541`), under `ws.mu`. That makes the stamp/`wsCanceled`
    reading of the `-1` case right, including a `Cancel` racing it: after `cancelWatcher` the watcher
    is out of `synced`, so `progressIfSync` sends nothing (`watcher.go:153-176`).
  * **Exactness at the compaction revision.** Only revision `h.compacted` can lose sub-revisions:
    a tombstone at `atRev` is kept (`key_index.go:276-283`) and starts below the compaction get the
    compaction response. So the stated `exactFrom` is sufficient. It is stronger than needed, but it
    is the form the user approved.
* **Copied event structs.** `newWatcherBatch` copies each event struct per watcher
  (`watcher_group.go:89-93`). So `evOwn`'s "struct owned, `Kv` read-only" is true, and v3rpc's
  `events[i].PrevKv = ...` write (`v3rpc/watch.go`, `sendLoop`) touches only the watcher's own copy.
* **Gating on the compaction condition, end to end.** 1b's `watchStep`/`wireStep` now take
  `exactFrom` (`client/v3/ApiWatch.lean:203, 300, 307, 425`). 2b's `srvWireStep` is 1b's
  `wireStep`, so the chain 3f → 2b → 1b is gated on one condition, and the direction is right: the
  client's `exactFrom σ.kv lo` implies 3f's `exactFrom h lo` for any `h` that `σ` extends.
  **Open question 1 of `batch-3f.md` is stale at HEAD.**
* **The stream's tokens match v3rpc's goroutines:**
  * `wsCtl` belongs to the receive loop (`Watch`).
  * `wsCons` belongs to the send loop (the receive, the drain, the final `range`).
  * `wsOpen` belongs to the handler (`close`).
  * `Cancel`, `RequestProgress`, `RequestProgressAll`, `Rev` and `Chan` take only the persistent
    `wsAt`. That is right: `RequestProgress` comes from the send loop while the receive loop runs
    (`v3rpc/watch.go:594`).
  * The drain law's empty case (`n ≤ rs.length` for a `wsSentLb ι n` taken before) together with
    `Watch`'s stamp is exactly what the fork's drain-before-`Created` fix needs.
* **The store's specs reuse 3e's contracts.** `Restore`, `Close`, `Write`, the transaction `End`
  and `New` are 3e's contracts at `*watchableStore`. `Close`'s sketch returns the loops' parked
  reader slots into `mvccClosed` (`oneshot-close.md`). Restore's premise `σ.kv.revs <+: σ'.kv.revs`
  is also what keeps `chooseAll`'s panic (`watcher_group.go:244-250`) unreachable for unsynced
  watchers without the `restore` flag. The sketch does not say so; it should.
* **adt: one spec per function over the key kind `Cmp`.** This replaces the old string/bytes/`_gen`
  families. I checked three claims against the code and found them true:
  * `Intersects` "exact for any query": the CLRS descent is correct with affine keys and empty
    entries.
  * `Visit`/`Stab` exact for `queryOk` queries: with a non-empty query, the `v > 0` pruning branch
    cannot skip an overlapping entry.
  * `Contains` stated as coverage of every key: the greedy scan over the begin-sorted stabbed
    entries decides coverage, empty entries included.

  The three adt snippets are provable from the specs.

## First tier

### F1. The compaction clause is false after `Restore` (unsound; affects 3f's `wStep`, 1b's `watchStep`, 2b)

`wStep`'s compaction case (`S/ApiWatch.lean:206-209`) states `p + 1 < cr`, where `p = posOf …`
counts progress responses. `wsCmpSendable` (`S/WatchInternal.lean:39, 170`) says the same.

The code compares `cr` against `w.minRev` (`watcher_group.go:255`), and a progress response never
raises `minRev`:

* `progressIfSync` sends a progress response without touching `minRev` (`watchable_store.go:528-554`).
* `notify` raises `minRev` only for watchers that had events (`:483-503`).
* `Restore` moves synced watchers to `unsynced` with `minRev` unchanged (`:215-219`).

A run that breaks the clause:

1. A watcher registers at revision 10 from the current revision, so `minRev = 11`.
2. Its key does not change. A `RequestProgress` at revision 100 gives `posOf = 100`.
3. The member restores a snapshot whose history extends the old one and whose compaction revision
   is 50. 3e's Restore premise admits this: the old compaction revision 0 is ≤ 50.
4. `syncWatchers` → `chooseAll` sends `CompactRevision = 50`, because `11 < 50`.
5. The spec claims `101 < 50`.

1b's `watchStep` makes the same claim, `∀ c, p.done = some c → c + 1 < cr`
(`client/v3/ApiWatch.lean:291`). 2b's request item 3 asks for it too (`req/..._storage_mvcc.md`,
"from 2b").

**Go behavior.** After a snapshot restore, a watch that had been told by progress notifications
that nothing changed up to `P` can be cancelled as compacted at a revision `≤ P` that it no longer
needs. Kubernetes enables progress notification and would relist. A lagging follower that receives
a snapshot is enough to reach it.

**Not recorded.** I did not write the issue (read-only); it needs a Go test, and none of
`issues/`/`nonissues/` has it. The mvcc-level test: `New`, `Watch` from 0, writes of other keys,
`RequestProgress`, then `Restore` onto a backend compacted between the watcher's `minRev` and its
progress revision. The author or coordinator should write it, `blocks-proof: no` once the spec is
weakened.

**Fix.** State the compaction clause against a position that `minRev` bounds: `posEvOf`, the fold
of `posOf` without progress responses. It satisfies `posEvOf + 1 ≤ minRev` on every path:
registration, `notify`, `syncWatchers`, the batch cut, `moveVictims`. Then:

* `wStep`'s compaction case says `posEvOf W id rs + 1 < cr ∧ cr ≤ h.compacted`.
* 1b weakens `watchStep`'s compaction arm the same way (a second position in `WatchPos`), or to
  `cr ≤ σ.kv.compacted` alone. Check 1g's users of the compaction revision first.
* Correct the realization sentence in `WatchInternal.lean:15` ("a synced watcher's … `minRev` is
  past the notified revision"). It is false: a synced watcher with no events keeps its
  registration `minRev`.

### F2. `Watch` and `Rev` are not ordered against earlier facts (2b's floor; two snippets unprovable)

* `watchStream.Watch.spec` gives `W.pos = h.rev` for some `h` with `mvccLb γ h`.
* `watchStream.Rev.spec` gives `r = h.rev` for some `h` with `mvccLb γ h`.

`mvccLb` is only an upper-side fact (`h` is a prefix of the current notified history). Nothing ties
`h` to the state at the time of the call, nor two results to each other. The consequences:

* **2b cannot prove the floor.** 1b's `WatchPos.init` floor is "events from at most `floor + 1`"
  (`client/v3/ApiWatch.lean`, `watchStep` events arm, `lo ≤ f + 1`), where the floor is the
  `Created` header from `Rev()` called after `Watch` (`v3rpc/watch.go:342, 360`). 2b needs
  `W.pos ≤` that `Rev()` result, which these posts do not give.
* **`ReqFromCurrent` is unprovable.** Its check `got[0].Kv.ModRevision != rev` needs `W.pos ≥` the
  state's revision at the call; a stale `h` lets an older change of `k` come first.
* **`ReqDrainBeforeCreated` is unprovable.** Its check `resp.Revision < rev0` has the same gap.

**Fix.** Either of:

* (a) Give `Watch` and `Rev` a read atomic update in 3e's form (`KV.Rev.contract`: fired at the
  state read, unchanged; `Watch` reads under `s.mu`, where nothing is pending). 2d's realization
  of `srvWatchable` instantiates it with the apply invariant.
* (b) Take an `mvccLb γ h0` in the pre and give `histLe h0 h`.
  * For `Watch` this is sound for any `h0`: `s.mu` waits for a pending `End`.
  * For `Rev` it is **not** sound for an `h0` that includes a pending revision: `Rev` reads the
    committed revision through a read transaction (`kv_view.go:32-36`), which can begin between
    `notify` and the bump. So `Rev` needs a committed lower bound, or `Watch`'s result marked as one.

  Option (a) avoids the new distinction.

### F3. Reader tokens versus thread tokens: 2b's statements cannot call 3f's (a caller not served)

3f's `Watch`, `Rev`, `RequestProgress` and `RequestProgressAll` each take `mvccReaders γ 1`. 2b's
`serverWatchStream.recvLoop.spec`/`sendLoop.spec` hold only `threadTok` and say they dropped
`mvccReaders` (`v3rpc/serverWatchStream__recvLoop.lean:44, 78`; `watchServer__Watch.lean:40`).
2c/2d's `srvWatchable` (`etcdserver/ApiReq.lean:341-348`) hands out no reader token.

As stated, the composition fails. One side must change:

* Either 3e/3f's owner turns a `threadTok` into a reader slot inside the store's invariant. This is
  CLAUDE.md's bounds rule: a spec in between takes its `threadTok` and the owner's handle.
* Or 2b/2d thread `mvccReaders`. Then the server needs a pool for unboundedly many streams, which
  `mvccTokN` cannot be without exactly that conversion.

This is open question 4 of `batch-3f.md`. It is a decision for the user, with 3e first. Until then
both statements stand, and they cannot compose.

### F4. Snippet checks the specs do not give

Each item below is a check in a snippet that does not follow from the specs, with what the users
need and the fix.

**(a) Ids.** `recvEvents`'s "a response of a watcher this stream does not have" (every history
snippet uses it), and the foreign-id checks of `ReqProgressAll`, `ReqDrainBeforeCreated` and
`ReqRestore`.

* `Watch` gives only `n ≤ id`, and no law bounds a `wsReg ι id W` by `wsCtl`. So an unknown
  registered id cannot be excluded.
* A real user relies on the same thing: `examples/mvccrand/mvccrand.go:716` ("a watch response for
  an unknown watcher") keeps a map of the ids `Watch` returned.
* The code makes ids consecutive with auto ids (`watcher.go:128-133`).
* **Fix:** `sint.Z id = n` in `Watch`'s success post, and a law
  `wsReg ι id W ∗ wsCtl ι n ⊢ ⌜0 ≤ sint.Z id < n⌝`.

**(b) Unrequested progress.** `wsRespOk` admits a progress response of a watcher (`evs = []`,
`progStep`) at any time. So the direct receives in `ReqWholeRevision`, `ReqFilters` and
`ReqCompaction`, which expect events or a compaction first, are unprovable.

* No real caller needs "no unrequested progress": 1b admits progress at any time.
* **Fix:** in the snippets (skip progress responses, as `recvEvents` does). Do not strengthen the
  spec.

**(c) `ReqEmptyRange`.** `Watch`'s success disjunct does not exclude an empty range.

* **Fix:** add `⌜¬ (endk ≠ slice.nil ∧ e ≠ [] ∧ ¬ GoStringLt k e)⌝` to it. This is true of the code
  (`watcher.go:118`), and mvccrand relies on it too (`mvccrand.go:755-756`).

**(d) `ReqClose`.** "A watch on a closed stream" and "a cancel on a closed stream" do not follow:
`Watch`'s success and `Cancel`'s success are not excluded after `wsClosed`.

* 2b asked for it ("afterwards `Watch` and `Cancel` fail", item 4), but its proofs need only "no
  panic, no send".
* **Fix:** either drop those two checks from the snippet and tell 2b that this part of item 4 is
  not given, or add a closed flag to the pre of `Watch` and `Cancel` (`if cl then wsClosed ι`,
  then an error).

**(e) `ReqCancel`.** "No event of a write after the cancel" needs to know that a response sent
before the `c`-th send cannot carry a revision committed after the cancel. `wsRespOk`'s `∃ h`
records no send time.

* No caller relies on it: v3rpc retires the id itself through its `ids` map.
* **Fix:** restate the snippet to what `wsCanceled` gives (every response of `id` is among the first
  `c`).

### F5. adt's red-black helpers have no specs (verified functions dropped)

They are called by the exported functions, and all twelve have linked proofs in the old tree
(`specs-ref` `Proof/go_etcd_io/etcd/pkg/v3/adt/Link.lean:101-177`). PRINCIPLES' "A smaller API is
not a narrower scope" requires a spec for each; an internal helper's spec may mirror its code.

* `intervalNode.color`, `intervalNode.min`, `intervalNode.successor`, `intervalNode.updateMax`,
  `intervalNode.visit`;
* `intervalTree.find`, `intervalTree.createIntervalNode`, `intervalTree.insertFixup`,
  `intervalTree.deleteFixup`, `intervalTree.rotateLeft`, `intervalTree.rotateRight`,
  `intervalTree.replaceParent`.

(`intervalNode.height` and `Height` have no old proof; leaving them out is fine.)

**Fix.** Add `A/Internal.lean`: node predicates, subtrees and zipper contexts over the shared
sentinel, ported from `specs-ref`'s `Tree.lean`/`Ctx.lean`/`CtxAt.lean` as opaque internal
predicates. Add one spec file per helper. Without the file, `A/Api.lean`'s header cites a
nonexistent "`Internal.lean`'s `RbT`".

### F6. Error identity not given (a user not served)

`mvccrand.go:756` checks `err == mvcc.ErrEmptyWatcherRange`. `Watch`'s error disjunct gives only
`errMsgOk err "mvcc: watcher range is empty"` (`S/watchStream__Watch.lean:68`), and `watch_init`
gives the global's value without relating it to `Watch`'s `err`. `Cancel` has the same shape.

**Fix.** Give `globalAddr ErrEmptyWatcherRange ↦□ err` (and `ErrWatcherNotExist` for `Cancel`),
as 3e's `Compact` does with `ErrCompacted`. `errMsgOk` then follows from `watch_init`.

## Second tier

* **S1. `mvccLb`'s laws versus its stated realization.** `mvccLb_le` and `mvccLb_get`
  (`S/ApiWatch.lean:320-327`) are a plain `⊢` and `|==>` over `mvccState` alone; they cannot open
  the store's invariant.
  * `ApiWatch.lean`'s header and the `req/` item 4 put the monotone authority "in the store's
    invariant beside 3e's half". From there neither law is provable.
  * The authority, or a fractional half of it, must be part of `mvccState`'s own realization.
  * Say that in the header and in 3e's `req/` item; it is a realization constraint on 3e.
* **S2. The `nextID` bound has no source in a statement.** `Watch`'s sketch bounds `nextID` "by the
  receipts … at its owner".
  * `NewWatchStream.spec` and `Watch.spec` carry no `ReceiptBoundLe` binder, unlike `New.spec`.
    Check how the stream's invariant gets the bound.
  * Without one, `n ≤ id ∧ id ≠ -1` is false after `2^63` creations on one stream.
  * Uncertain: it depends on how Perennial's time receipts reach an invariant allocated without the
    instance.
* **S3. Two `exactFrom`s.** `Mvcc.exactFrom` (with `evKey`) and `ClientV3.exactFrom` (with
  `Event.key`) are separate definitions.
  * 1b's docstring calls its own "the one statement … 1b, 2b and 3f cite".
  * Move one to W0's `EtcdModel` and cite it from both. 2b would otherwise prove the two equivalent.
* **S4. `exactFrom`'s margin.** Only revision `h.compacted` matters (`key_index.go:276-283`; see
  F1's reasoning). Say so in `wStep`'s Margin, keeping the approved form.
* **S5. 2d's bridge is not relayed.** `srvWatchable` gives `∃ γs, watchableAt w γs`, with no bridge
  from `mvccLb γs h` to the cluster's `etcdLb` and no reader tokens (F3).
  * `batch-3f.md` lists this under "not written".
  * It must reach `req/go_etcd_io_etcd_server_v3_etcdserver.md`, or 2b's facts have no anchor.
* **S6. The context of `Watch` (uncertain).** `Watch` takes `Context.ctxOk ctx`. v3rpc passes the
  context from `traceutil.Tracer.Start(gRPCStream.Context(), …)` (`v3rpc/watch.go:331-339`). Check
  that 2b's or 4b's otel boundary gives `ctxOk` for it.
* **S7. Minor.**
  * `A/Api.lean` names a law `ivt_agree`, which is the second conjunct of `ivt_fractional`.
  * `batch-3f.md` lists `intervalNode.height` among the helpers left out, but it was never proved.

## Completeness: the users and their patterns

| Pattern | Call site | Covered |
|---|---|---|
| 2b receive loop: `Watch` (auto id, normalized end, filters, start ≥ 0), `Rev` for headers, `Cancel`, `RequestProgressAll` under `sws.mu` | `v3rpc/watch.go:342, 360, 377, 400` | yes, except the floor (F2) and the tokens (F3) |
| 2b send loop: receive in a `select`, the drain before `Created`, the final `range`, `RequestProgress` from the ticker, owned events (`PrevKv` write), `Kv` read-only | `v3rpc/watch.go:516, 536, 425, 594` | yes |
| 2b handler: `NewWatchStream` through `WatchableKV`; `Close` once, concurrent with the receive loop | `v3rpc/watch.go:179, 668` | yes |
| server: `mvcc.New`, `Restore` (`applySnapshot`), `Close` (`Cleanup`), the lessor's range deleter through the watchable `Write` | `etcdserver/server.go:366, 1094, 950`; `watchable_store.go:107` | yes (3e's contracts); the `srvWatchable` bridge is not relayed (S5) |
| examples: `mvccrand` (unknown-id check, error identity, empty-range refusal, progress meaning, delete event fields) | `examples/mvccrand/mvccrand.go:701-770` | partly: ids (F4a), error identity (F6), empty range (F4c) |
| 2a `checkIntervals` (string keys: `Insert`, `Intersects` of points, `Union` over `["\x00", "")`, empty delete intervals possible) | `v3rpc/key.go:237-317` | yes |
| 3d permission cache (bytes keys, `nil` end as top, `Contains` on proper ranges, `Intersects` of points, read-only for good) | `auth/range_perm_cache.go:30-110` | yes (`ivt_persist`; `ivlMem` gives "no interval holds the empty key" by computation) |
| mvcc's watcher groups (`Find` then mutate the value's map, `Insert`, `Stab` of points, `Intersects`, `Delete` must succeed) | `watcher_group.go:167-295` | yes |

No user of the watch API outside these exists in the pinned server: `grpcproxy` goes through
clientv3.

## Ranking (most need of revision first)

1. **`ApiWatch.lean` with `watchStream.{Watch,Rev,Cancel}`** (F1, F2, F4a/c, F6, S1). F1 also needs
   1b's matching change.
2. **The reader/thread token coupling with 2b and 2d** (F3, S5): a decision for the user, 3e first.
3. **The `mvccwatch` snippets** (F4b/d/e: restate them to what the callers rely on).
4. **`pkg/v3/adt`** (F5: the internal helper specs); its exported specs and snippets are sound.
5. **The store's canonical instances** (`New`, `newWatchableStore`, `watchableStore.*`,
   `watchableStoreTxnWrite.*`, `ChanBufLen`): sound as instances of 3e's contracts. Mention the
   chooseAll/Restore premise in the sketch; S2 is open.

## Verdict

Not ready. The watch vocabulary is in the right shape and most of it is true of the code. But the
compaction clause is false after a snapshot restore (F1, which reaches 1b and 2b). `Watch` and `Rev`
lack the ordering 2b's floor needs (F2). The token kinds disagree with 2b (F3). Several snippet
checks, and one real user (`mvccrand`), need facts the specs do not give (F4, F6). Twelve verified
adt helpers have no specs (F5). Every fix is local: a weaker compaction position, a read update (or
a lower bound) in `Watch`/`Rev`, `id = n` with a registration law, error identities, adt's internal
file, and a token decision.
