# v3rpc's watch server onto mvcc's API (strict M1): hand-off

Branch `mvcc-api`. The task: v3rpc's watch `Spec/` files restated as
`notes/mvcc-api-clients/WatchSpecs.lean` drafts them (frozen), the watch server's proofs over the
API's `WatchStream.*` contracts, `WatchableKV.NewWatchStream` and the laws (`wsChan_recv`,
`wsRecv_ok`, `wsSentLb_zero`, `persistent`, `excl`, `shapes`), no mvcc internal in v3rpc's watch
path. Only the watch path: the KV, lease, auth and maintenance parts of v3rpc are other tracks'.

## Layout

- `Proof/.../v3rpc/WatchApi.lean` (new): everything of the watch path that sees mvcc, over the API
  only (it imports `Spec/.../mvcc/Api.lean`, txn's `RangeModel` for `LogSmall` and the cache's
  `EtcdModel` for `etcdKeyMax`; nothing of the server, so it is checked on its own): the draft's
  §1 (`SrvW`, `srvPeek`, `srvWOk`, `srvOnce`), §2's `RegInfo`, §3's ghost state (`regIs`, `idTok`,
  `rcvLb`, `closeTok`, `wsN`; the run's invariant `wsInvG` and the snapshot `rcvSnapG`, generic in
  the client's cancel requests `cq`), and §7's obligations, proved.
- `InvWatchStream.lean`: the message models re-keyed (`WatchRespM.src : Option (Nat × WResp)`,
  `mvccResp n x h`, `sentEvsOf`/`fwdEvs`/`fwdIdx` by id); `watchAuthed` at the auth tag (W2).
- `InvWatch.lean`: `WSrv.tag` (W2), `watchSrvOk s E tag` (no `isWatchableStore`, no watch-token
  pool), `upOk`/`watchUp` (draft §5), `WRun` (the draft's `WRunA` with the fields it keeps), `auxOf`,
  `wsInv r := wsInvG ..`, `rcvSnap r := rcvSnapG ..`, `mvccOk`, `ctrlWatcher`, `createdAfter`,
  `ctrlOk`, `watchDn`, `watchStreamSpec` (draft §4), `ctrlP r ci`, `swsIs sws r Up Dn st ci cd`
  (draft §6), `watchRunSlot R := R.E.RD ∗ ⌜threadBound …⌝`, `watchSpec R W tok`.
- The draft's names drop their suffix (`WatchRespM2` → `WatchRespM`, `mvccOk2` → `mvccOk`,
  `WRunA` → `WRun`, `swsIs2` → `swsIs`, `idTok2` → `idTok`, `upOk2` → `upOk`, ...).
  `ctrlAnswers`/`watchRespMsg` are today's on the new model (the draft's `.wire` projection is
  the identity on the fields they read).

## Done

- **The statements** (draft §6): `recvLoop`, `sendLoop`, `close`, `watchServer.Watch` as drafted;
  `isWatchPermitted`, `newResponseHeader` (swsIs's new parameters), `NewWatchServer` (W2: `tag`).
- **The obligations, proved** (`WatchApi.lean`, no sorry): `watch_au` (O1), `cancel_au` (O2),
  `close_au` (O3), `rev_au` (`Rev`'s update, `Q := True`), `snap_after_recv` (O4, with the registry
  entries the caller holds placed in the snapshot's `S`, as the probe), `drain_poll` (O5's poll),
  `rcvSnapG_dup`, `wsInvG_alloc` (the run's invariant from `NewWatchStream`'s `wsState ι wsStart`),
  `regFacts_of`, `rel_register`.

- **The pure models, checked** (`lake env lean`, they import the API only): `WatchMsgModel.lean`
  (the message models, split out of `InvWatchStream.lean`), `WatchSendModel.lean` (re-keyed by id:
  `SendInv`, `send_claim*` over `WResp`), `WatchSendHist.lean` (re-keyed: a source's index in place
  of `RespM.idx`, `srcOf rcv S` the sent sources, `fwdEvs`/`fwdIdx` by id).
- **Proofs rewritten, not yet checked** (they sit over `InvWatch.lean`, whose imports
  `apply.Contracts`/`AuthClass`/`InvRequest` reach `txn.Writer`, red at the time of writing: the
  server and txn tracks' migration): `serverWatchStream.close` (`Close`'s contract through
  `shapes.law`, `close_au`), `watchServer.Watch` (`NewWatchStream`'s contract at the watchable store
  from `shapes.law`'s per-type conjunct, `wsInvG_alloc`, both loops forked with thread tokens),
  `serverWatchStream.recvLoop` (`Watch`/`Rev`/`Cancel`/`RequestProgressAll` through `shapes.law`,
  `watch_au`/`rev_au`/`cancel_au`; the registered case's `ctrlWatcher` from `Watch`'s commit),
  `isWatchPermitted`, `newResponseHeader` (the new parameters). Check each with
  `etc/lean-check.py` once `InvWatch.lean` builds, and fix.

## Left

- **`sendLoop`** (`serverWatchStream__sendLoop.lean`, 2100 lines, not migrated): the plan.
  - `sendSt r idsL pendL rcv D`: `rcv : List WResp` with `wsRecv r.ι rcv ∗ monoListAuthOwn r.γr 1
    rcv` in the loop's resources (in place of `watchConsumer`); `D.filterMap src = srcOf rcv S`
    (`WatchSendHist.srcOf`); the registry entries of the announced ids, `□ [∗map] X ↦ i ∈ M, regIs
    r.γreg X i` with `IM`'s ids in `M` (from each created response's `ctrlWatcher`, kept when it is
    sent), for `snap_after_recv`'s `M`; `rcvOk` replaced by `□ ∀ n x, rcv[n]? = some x → ∃ σ S,
    rcvSnap r (rcv.take (n+1)) σ S` (the snapshot right after each receipt).
  - A receipt (`Chan()`'s case: `wsChan_recv.law`'s blocking `recvAu`; the drain: its
    non-blocking arm, `drain_poll`): `monoListAuthOwn_update_app` for `γr`, then
    `snap_after_recv` (a ghost step at `⊤`, no credit) with `M`.
  - A response sent: `mvccOk r j m` from the snapshot at its index, `send_claim_*` (id-keyed),
    `fwdEvs_*`, `fwdIdx_*`; for a `-1` (sent at once), the clause "every id live after `L` is in
    `S`" from `snap_after_recv`'s second conclusion and `M ⊇` the live ids.
  - The drain before a created response (`createdAfter`): the poll at the watcher's stamp
    (`ctrlWatcher`'s `wsSentLb ι i.k`; `wsSentLb_zero.law` for a refused create), the empty arm's
    `k ≤ |rcv|` and `rcvLb r.γr rcv` (from the authority), every `-1` among `rcv` sent (today's
    `sendSt_neg1`).
  - `RequestProgress` (the ticker): its contract takes a thread token, the loop's own.
- `Results.lean`, `Link.lean`: the linked results (`etc/gen-link.py --v3rpc`), once the proofs
  check; the watch callees are now the API's laws (`shapes`, `persistent`, ...), taken by the link as
  mvcc's results.
- `HistoryModel.lean`, `ClientModel.lean`, `WatchStep.lean`, `WatchClass.lean`: the client model's
  server log (`srvLog`, `histLog`) over `mvcc.evLog`/`idxSealed` (the server draft's `srvLogA` over
  `histLb`) and `ctrlWatcher_authorized` (over the old `watcherIs`): not migrated.

## Placeholders (`M1-REPLACE`)

None.

## What v3rpc assumes of the server

Everything is a premise of `watchServer.Watch.spec`, `srvWOk W R.wsl wsN` (the draft's §1, verbatim),
which the server must give for the `W` it builds:
- the tie `⌜W.kv = wsIface wsl⌝` (xreview §6c; the server draft's `srvKVInvsA`'s `E.kv = wsIfaceA wsl`);
- `isMvcc W.kv W.γm`;
- the peek `srvPeek W` (the server draft's `kvPeek.law` at `kvsN`), its namespace outside `mvccN`
  and disjoint from `wsN`;
- `histLb`'s laws: persistence, agreement, prefix closure, and the model facts
  `LogWf' ∧ length < 2^63 ∧ LogSmall ∧ LogPutsLe etcdKeyMax` (the server draft's `histLb_model.law`'s
  first conjunct);
- `crevOk`'s persistence.
`srvOnce W` is the client's premise (client/v3), not v3rpc's.

## Findings

**F1 (the draft unprovable as written; minimal fix applied, local to v3rpc).** The draft's
`swsIs2` holds `swsF sws "watchStream" ↦□ wspIface r.wsp ∗ isMvccWatchStream (wspIface r.wsp) ..`
with `WRunA.wsp : Loc`: it fixes the mvcc stream's dynamic type to `*watchStream`. The API's
`WatchableKV.NewWatchStream.contract` returns `∀ ws, (∃ ι, isMvccWatchStream ws γ ι ∗ ..)` for an
arbitrary interface value `ws`, and `shapes.law` gives only `ws = mkOk ty v ∧ isWatchStream ty v`
for some `ty`. So `watchServer.Watch` cannot establish `swsIs2`. Minimal fix: `WRun.ws :
GoInterface` (the value `NewWatchStream` returned) in place of `wsp : Loc`, `swsIs` at `r.ws`; the
stream's methods are called through `shapes.law`'s `isWatchStream ty v` (the contracts). No client
sees the field (`auxOf` publishes ghost names only). (The alternative, the API's `NewWatchStream`
at `*watchableStore` saying it returns a `*watchStream`, changes the frozen API.)

**W1 (unchanged, outside the API):** `watchServer.Watch.spec` takes the handler's `threadTok`
(`Close` takes one); grpc's stream-handler contract does not lend one today.
