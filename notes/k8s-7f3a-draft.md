# k8s 7f-3a: the statements (S2 Draft, 2026-11-13; branch `k8s-7f5`; for etcd-grove-81)

`WithPrevKV` through the watch stack, and `WithRequireLeader` over a caller's context (T5-a).
Scope: `notes/k8s-7f5-scope.md` §4.2 (T5-a, "7f-3's texts"), §6 row 7f-3a, §8 (Q1, Q2, Q5).
Parent: `notes/k8s-7f-scope.md` §2.3 1-2, §5.1.

**Where the Lean is.** `Proof/go_etcd_io/etcd/client/v3/Draft7f3a.lean`: every new statement,
under the old name with a `P` suffix (`WithRequireLeader.specGen` for T5-a), built. Nothing imports
it and no linked definition changes (Q1: no `sorry` under a linked result). 7f-3b/3c swap each old
definition for its new form and re-prove the users. The pure laws between the two forms are proved
there (`isRangeWatch_eq`, `prevKvOk_noPrev`, `prevKvOk_null`, `watchStateElemP_elem`,
`watchReqOk_P`). No `sorry`, no axiom.

In place, with no change of meaning: `EvModel` (`cache/v3/InvStore.lean:185`) gains
`prevKv : Loc := null`. The default keeps every model built so far (`client.evModelOf`), and no
statement reads the new field yet.

## 1. The statements, old → new

| # | Old (file:line) | New (`Draft7f3a.lean`) | In words |
|---|---|---|---|
| S1 | `OpFull.isRangeWatch` (`cache/v3/InvEtcdTxn.lean:1231`) | `OpFull.isRangeWatchP` | A range watch may ask for `WithPrevKV`. The other excluded options (fragment, filters) stay excluded. `isRangeWatch = isRangeWatchP && !prevKV`. |
| S2 | none (`eventIs`, `client/v3/WatchStateDefs.lean:102`, says nothing of `PrevKv`) | `prevKvOk o σ ev pk` | An event's `PrevKv` pointer. Without `WithPrevKV` it is `nil`. With it, it is `nil` (always admitted, Q5), or, for an event that is not a create, a `*KeyValue` holding the key's record at revision `r - 1` (`σ.at (r-1) !! key`). |
| S3 | `respAt` (`InvStore.lean`) | `respAtP` = `respAt ∗ eventsPkAt` | The consumer can read each event's `PrevKv` field (read-only). |
| S4 | `watchStateRespOk` (`WatchStateDefs.lean:117`) | `watchStateRespOkP` = old `∗` per-event `prevKvOk` | As before, and each delivered event's pointer is `prevKvOk` of the state's event it is. This is vacuous for a response without events. |
| S5 | `watchStateElem` (`WatchStateDefs.lean:194`) | `watchStateElemP` | It uses `respAtP` and `watchStateRespOkP`. `watchStateElemP ⊢ watchStateElem`. |
| S6 | `watcher.Watch.spec` (`Spec/.../client/v3/watcher__Watch.lean:72`) | `watcher.Watch.specP` | `isRangeWatchP` and `watchStateElemP`. Everything else is unchanged: the context is still `watchCtx`, and so are the auth row and the size bound. |
| S7 | `client.rawRespOk` (`WatchStateDefs.lean:261`) | `client.rawRespOkP` + `prevKvLogOk` | The server-level form. The events are the log's up to their `PrevKv` pointers. Each pointer is `nil`, or, for a non-create event, `kvPtrFixed` of `mvcc.findKey key (mvcc.stateAt L (r-1))`. |
| S8 | `v3rpc.watchReqOk` (`v3rpc/WatchMsgModel.lean:113`) | `v3rpc.watchReqOkP` | The server's restriction `prev_kv = false` is dropped. `watchReqOk → watchReqOkP`. |
| S9 | `v3rpc.swsMu` (`v3rpc/InvWatch.lean:262`) | `v3rpc.swsMuP` | The `prevKV` map may hold entries (`recvLoop` records `creq.PrevKv`). `fragment` stays empty. |
| S10 | `WithRequireLeader.spec` (`Spec/.../client/v3/WithRequireLeader.lean`; `Background()` only) | `WithRequireLeader.specGen` (T5-a) | Over any `watchCtx` parent: the result is a `watchCtx` at the same descriptor. For every key of a type other than grpc's `mdOutgoingKey`, `Value` answers as the parent does, in both the WP form and the chain form (`ctxValue`). |

The text of each is in the Lean file. Its docstrings give the Go code (`watch.go:442-455` for S2/S7,
`:342-349` for S9).

**Current users keep working (S1, S5, S8).** At `prevKV = false`, `isRangeWatchP` holds whenever
`isRangeWatch` did, and `prevKvOk` is `⌜pk = null⌝` (`prevKvOk_noPrev`). The new element gives the
old one (`watchStateElemP_elem`). But an SPSC channel's element predicate is an invariant, so the
old spec does not follow from `specP` by weakening. In 7f-3c each user (watchkv, cachekv, linkv3p
`MainWatch`, the compactor, `etcdstart.Collect`, `Election.observe`, recipes, auth `RootWatch`/
`WorkCalls`) is re-pointed at `specP` and applies `watchStateElemP_elem` where it reads an
element. That is mechanical, about 5-20 lines per user.

**Convergence with the SpecPlan** (`SpecPlan/Spec/go_etcd_io/etcd/client/v3/ApiWatch.lean`,
`WatchReq.prevOk`). The two agree:
- the previous record is the key's record at `rev - 1`;
- `none` is always possible on a client's channel (`prevLoose` stays true across reconnects; ours
  admits `nil` always);
- without `prevKV`, `none`.

Ours is a little stronger in one respect: a create never carries a non-`nil` `PrevKv` (the server
skips creates). The SpecPlan's `WithRequireLeader.spec` (`ctxOk`, `ctxWithValues`,
`ctxRequireLeader`) matches S10's shape, with `watchCtx` in place of `ctxOk`. S10 leaves out the
metadata's content (its margin says why). No spec defect was found, so there is no ledger entry.

## 2. Translation config (done, `etc/goose.py --check` passes)

- `Code/go_etcd_io/etcd/client/v3.toml`: `WithPrevKV`, `WithRequireLeader` translated.
- `Code/google_golang_org/grpc/metadata.toml`: `NewOutgoingContext`, `Pairs`, `MD.Copy`, `MD.Set`,
  `copyOf`, `mdOutgoingKey`, `rawMD`, with `imports` `context`, `strings`, `fmt`.
- Regenerated:
  - `etc/goose.py --project etcd`: client `v3.lean` and `chunk0.lean`, metadata Code and
    GeneratedProof;
  - `etc/gen-init.py`: metadata's `Init.lean` and 17 `PkgTable`s;
  - `etc/gen-specs-pkginit.py`: metadata's PkgInit only. The generator also rewrites `wal`,
    `nettrace`, `httptrace`, `runtime/trace` and others. That drift was already on lean, it is not
    gated, and I left it alone.
- The existing axiom `WithRequireLeader.wp_proof` still stands, now over a translated function.

## 3. Finding: Q2's "translate, no new axiom" does not hold

Proving `WithRequireLeader` from its translation, even `specGen` without the metadata content,
needs these trusted changes:

1. **`context.WithValue.spec`** (the repository's axiom, `Spec/context/WithValue.lean`) covers only
   five key types. `NewOutgoingContext` calls it at `mdOutgoingKey{}`. It needs that key added,
   and a post that gives the `valueCtx`'s fields (`vctxField q ↦□ parent`, `key`, `val`), so that
   `metadata.outgoingCtxOkC_ownKey` and `context.ctxValue_valueCtx` apply. It also needs `watchCtx`
   preserved, not only `isContext`/`txnCtx`, since the parent is only a `watchCtx`.
2. **`metadata.builtRawMD`** (opaque, trusted, `Proof/context/LibKeys.lean:65`) has no intro law. A
   law is needed: a `rawMD{md}` whose map is read-only for good (`md ↦$□ m`) and whose keys are
   distinct up to case is `builtRawMD`. "Distinct up to case" cannot be proved, because
   `strings.ToLower` is trusted only to return some string, and `Pairs`/`MD.Set` lower-case through
   it. So either the law drops that condition (its users must then not need it), or `ToLower` gets
   a stronger local spec. That would be a fourth trusted change.
3. **`metadata.FromOutgoingContext.spec`** (axiom) takes `context.isContext ctx cd`. Over a
   `watchCtx` parent the premise must weaken to `outgoingCtxOk ctx` alone (Go reads only
   `Value(mdOutgoingKey{})`). A trusted text restated.

**The fallback** (Scope §4.2 T5-a) is one trusted text: `WithRequireLeader.wp_proof` restated from
`Background()` to `specGen`, in `withVersion.spec`'s pattern (that twin axiom is identical code,
also names-only). Its all-keys clause is exactly the T-h..T-k lesson. Go evidence would extend
`examples/premisefix/watcherctx` (the S1 review asked for `TestWithRequireLeaderValues`,
`TestWithRequireLeaderNoAlias`, a non-trivial `Cause`). Today's `Background()` clauses
(`libCtxOk`, `outgoingCtxOkC` after `WithCancel`) become a corollary, and the lessor's caller
keeps working.

**Trust-base effect.**
- Translation route: the axiom count is unchanged or +1. `WithRequireLeader.wp_proof` goes, the
  `builtRawMD` law comes, and two axioms are restated. `withVersion.wp_proof` could then go too
  (the same body), for -1.
- Fallback: the count is unchanged, with one axiom restated.
- The 7f-3 statements themselves (S1-S9) add no trusted text.

## 4. Finding for 7f-3b: the send loop writes `PrevKv` into mvcc's events

`sendWatch` does `events[i] = evs[i]; events[i].PrevKv = r.KVs[0]`, so it writes the
`*mvccpb.Event` the mvcc response carries. mvcc's API gives each event read-only for good
(`mvcc.evIs`, `InvWatchBatch.lean:355`: `e ↦□ {...}`, "events are shared by the batches of all
watchers").

In Go this is safe. `newWatcherBatch` (`watcher_group.go:89-93`) copies each event per watcher, so
a response's events belong to its receiver. But the proof needs the API to say so: the `Chan`
response contract must hand over the `PrevKv` field, owned, for each event. That is an mvcc
API change (sealed, with an interface diff) through `newWatcherBatch`, `watcher.send`, the victim
batches and the channel. The send loop's range uses mvcc's `Range` contract at a revision
(`Api/RangeApi.lean`).

## 5. Proof plan (7f-3b, 7f-3c) and estimate

1. 7f-3b, mvcc: event ownership (§4) through the batches, victims and `Chan`, and the API's
   `WResp` events with an owned `PrevKv` field. 300-500 lines.
2. 7f-3b, v3rpc:
   - `recvLoop` records `prevKV[id]` (`swsMuP`);
   - `sendLoop`'s branch: `IsCreateEvent`, mvcc `Range` at `ModRevision - 1`, `KVs[0]` into
     `PrevKv`, with the `nil`/error arms;
   - `rawRespOkP`'s events (the client pipeline's server contract), and `watchReqOkP` in `upOk`.

   700-1100 lines.
3. 7f-3c, client:
   - `watchGRPCStream.run`/`serveSubstream`/`dispatchEvent` carry the pointer (the client copies
     the `*Event` pointers, so `PrevKv` is the server's);
   - the server-to-state step (`rawRespOkP` to `watchStateRespOkP`): `stateAt L (r-1)` is
     `σ.at (r-1)` at a log's state (`kvStateOf_at_kvs`);
   - `watcher.Watch.specP`, then the swap and the users (§1).

   1000-1600 lines.
4. T5-a: after 81's decision (§3). Fallback: about 150 Lean lines and a Go test. Translation
   route: 300-500 lines plus the three trusted changes.

Total 2000-3500 lines (the Scope's estimate stands), 3-5 agent contexts. `run`'s checks use
`--fast --split`.

## 6. Decisions needed

- **D1, T5-a route** (§3). (a) Translation with three trusted changes, maybe four; (b) the
  fallback, one restated axiom. **Recommended: (b).** It is less trusted text, and the same
  statement either way. Revert `WithRequireLeader` from the translation (keep `WithPrevKV`). Or
  keep it translated with the axiom over it, which `etc/verified-code.py` counts as assumed. The
  metadata helpers' translation then serves nothing and can be reverted too.
- **D2, mvcc's event ownership** (§4): an mvcc API change in 7f-3b, reviewed at its interface
  diff. **Recommended: yes.** It is true of the code (`newWatcherBatch` copies).
- **D3, `specGen` without the metadata content** (S10's margin). **Recommended: yes.** No user
  reads it.
