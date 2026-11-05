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
  `close_au` (O3), `rev_au`, `snap_after_recv` (O4), `drain_poll` (O5's poll), `rcvSnapG_dup`,
  `wsInvG_alloc`, `regFacts_of`, `rel_register`, `wp_ws_receive`; (third session) the instance
  `wrespIs_persistent` (the API's `wrespIs` unfolds to persistent parts).
- **The pure models** (`WatchMsgModel`, `WatchSendModel`, `WatchSendHist`, `WatchSendPure`).
- **Checked, third session (2026-11-05)**, every module from `WatchApi` to the six proofs, with no
  `sorry`: `InvWatchStream`, `InvWatch`, the seven spec files (`serverWatchStream__{close,
  isWatchPermitted,newResponseHeader,recvLoop,sendLoop}`, `watchServer__Watch`, `NewWatchServer`),
  `WatchLemmas`, and the proofs of `close`, `newResponseHeader`, `isWatchPermitted`,
  `watchServer.Watch`, `recvLoop`, `sendLoop`. **Checked with `lean` against stubs, not yet by
  `lake build`** (see "How it was checked"). `WatchClass` restated (below), checked the same way.
  Fixes made: `watchSrvOk` at `apply.isAuthStore`'s restated parameters (`∃ Pk f BT`, the
  server track's `isAuthStore st Pk f BT RD M RW`); `swsIs_persistent hP` (an mvcc law makes
  `isMvccWatchStream` persistent, so `swsIs` is persistent only under `persistent.law`: the proofs
  install it before `wp_start`; `newResponseHeader` and `isWatchPermitted` take `swsIs` spatially
  and need no law); `wsInv`/`rcvSnap` are `abbrev`s (the generic `wsInvG`/`rcvSnapG` unify with
  them); after `rw [Hsi]` the stream argument of a callee is `_`; the loops' returns frame
  `threadTok`; `Cancel`'s error by cases; the registration's `histLb` spatial (persistent only by
  `srvWOk`'s law); a dangling docstring in `InvWatchStream`.
- **`WatchClass.lean`, restated over the API** (draft: the watcher is the run's registry entry):
  `watchAuthed_on tag γa ..` (at the mode's tag, W2), `ctrlWatcher_authorized r tok γa c m h :
  modeTag r.srv.tag (.on γa) ∗ ctrlWatcher r tok (.create c) m ⊢ ∃ i info j st,
  ⌜createRangeOk c m.watchId i.rg⌝ ∗ regIs r.γreg m.watchId i ∗ authStateAt γa j st ∗
  infoBoundT r.srv.s (.on γa) tok info ∗ ⌜c.bound ≤ j ∧ (… ∀ x, i.rg.covers x → …)⌝` (was over
  `mvcc.watcherIs`/`idAssigned`). `Results.lean`'s `watch_registered_authorized` restates it
  (coordinator's file: its statement must follow).
- `ServerKV.lean` (the KV path, not this track's, red for its own reasons): `w64_rev_ne_zero` and
  `writeRev_ne_zero` take `+ 3` (the server's `appliedHdr` bound, coordinator's request).

## Built of record (fourth session, 2026-11-05)

`lake build` (under the lock) of `WatchApi`, `InvWatchStream`, `InvWatch`, the seven spec files,
`WatchLemmas`, the six proofs and `WatchClass`: all build. `#print axioms` of the six `wp_proof`s and
`ctrlWatcher_authorized`: no `sorryAx`; beyond `propext`/`Quot.sound`/`Classical.choice`, only the
Goose packages' axiomatized types and Perennial's `time.Now.wp_proof`. Fixes: `persistent.law`
gained `storageReq`'s persistence (fifth conjunct), so `mvccState`/`wsState`'s timelessness are
`hP.2.2.2.2.2.1`/`hP.2.2.2.2.2.2.1` (`WatchApi`); `mvcc.api.BkRef` → `mvcc.KBReal` (`InvWatch`'s
`watchSrvOk`, `apply.isAuthStore`'s binders). The scratch stubs below are obsolete.

## How it was checked before (the server was red; superseded by the above)

`InvWatchStream` imports `AuthReqDerive`, `InvWatch` imports `ReadOn`, the spec of
`isWatchPermitted` imports `AuthBound` (→ `AuthGuard`); all four import the server's `InvRead`,
which does not build under strict M1 (`txn.isKV`, `AEnv.s`, `AEnv.P`, `MvccName.idx`; also red:
`KVApplyOn`, `InvApRes`, `apply.AuthFuel`, `apply.AuthApplyLatest`, `AuthApplyRes`). The watch path
uses eight names of them: `infoBoundT`, `srvAuthLb`, `srvAuthLb_off`, `srvAuthLb_rangeCheck`,
`principalBoundI`, `principalBound_of_ctxBoundOrTLS_gate`, `infoBoundT_of_principalBoundI`,
`authInfoIs_pointsto`. Outside the repository (`/tmp/v3rpc-scratch`, never committed): a frozen copy
of the build outputs of the watch path's import closure, `AuthReqDerive` verbatim without its
`InvRead` import (it compiles: **the server can drop that import**), `AuthBound`'s watch names
verbatim, and `ReadOn`'s `srvAuthLb*` and `AuthGuard`'s `authInfoIs_pointsto` as stubs on a scratch
axiom. `#print axioms` of the six proofs: no `sorryAx`; beyond Perennial's and the Goose
packages' axioms only the scratch stubs' axiom (from `srvAuthLb`, `authInfoIs_pointsto`). **To
check of record** once `InvRead` builds: `lk.sh lake build` the six proof modules and
`WatchClass`.

## The proofs' hypotheses (final order, for `Link.lean`)

- `serverWatchStream.close.wp_proof (hShapes : mvcc.api.shapes.law) (hP : mvcc.api.persistent.law)`
- `serverWatchStream.newResponseHeader.wp_proof` (none)
- `serverWatchStream.isWatchPermitted.wp_proof (hAI : EtcdServer.AuthInfoFromCtx.spec)
  (hAS : EtcdServer.AuthStore.spec)`
- `serverWatchStream.recvLoop.wp_proof hShapes hP (hPerm : isWatchPermitted.spec)
  (hHdr : newResponseHeader.spec) (hFil : FiltersFromRequest.spec) (hIs : errors.Is.spec)
  (hStart : traceutil.Tracer.Start.spec) (hWA : trace.WithAttributes.spec)
  (hAStr : attribute.String.spec) (hAI64 : attribute.Int64.spec) (hABool : attribute.Bool.spec)
  (hZErr : zap.Logger.Error.spec) (hZE : zap.Error.spec)`
- `serverWatchStream.sendLoop.wp_proof (hHdr : newResponseHeader.spec)
  (hGPI : GetProgressReportInterval.spec) (hICE : isClientCtxErr.spec) hShapes hP
  (hR : mvcc.api.wsChan_recv.law) (hRok : mvcc.api.wsRecv_ok.law)
  (hZero : mvcc.api.wsSentLb_zero.law) (hAssert : verify.Assert.spec) (hNT : time.NewTicker.spec)
  (hStop : time.Ticker.Stop.spec) (hSec : time.Duration.Seconds.spec)
  (hSecP : time.Duration.Seconds_ptr.spec) (hZD : zap.Logger.Debug.spec)
  (hZW : zap.Logger.Warn.spec) (hZE : zap.Error.spec) (hCV : prometheus.CounterVec.WithLabelValues.spec)
  (hRER : mvcc.ReportEventReceived.spec)`
- `watchServer.Watch.wp_proof hShapes hP (hRecv : recvLoop.spec) (hSend : sendLoop.spec)
  (hClose : close.spec) (hICE : isClientCtxErr.spec) (hIs : errors.IsCtxErr.spec)
  (hZD : zap.Logger.Debug.spec) (hZW : zap.Logger.Warn.spec) (hZE : zap.Error.spec)
  (hCV : prometheus.CounterVec.WithLabelValues.spec)`

- (fourth session) `raftKV_of_server hPut hDel hRange hTxn hKV (hsh : mvcc.api.shapes.law)
  (hP : mvcc.api.persistent.law) (hR : mvcc.api.mvccState_reachable.law) hCl hID hMID hTerm hLead`
  (was `… hKV hRev hCl …`, `hRev : mvcc.store.Rev.spec`); `kvGetOk_of_server` likewise;
  `raftKV_of_serverOn hPut hDel hRange hTxn hTxnR hKV hsh hP hR hCl hID hMID hTerm hLead`,
  `kvGetOk_of_serverOn` likewise.

## Left

- `Results.lean`, `Link.lean` (the coordinator's): the watch callees are now the API's laws
  (`shapes`, `persistent`, `wsChan_recv`, `wsRecv_ok`, `wsSentLb_zero`), taken as mvcc's results;
  `watch_registered_authorized` restated as `ctrlWatcher_authorized` (above). Their KV and model
  parts follow the fourth session's restatements (below): `raftKV_of_server(On)`'s new hypotheses,
  `etcdModelOfServer E γr on`, the bridges' new names (`read_keys` and the server's `srvKVCoreM_*`
  are the server's).
- The clients of `ClientModel`/`HistoryModel`/`ServerKV` (client/v3, the cache, the examples;
  other tracks): `etcdModelOfServer E` → `etcdModelOfServer E γr on`; `srvLog E` → `srvLog γr on`
  (now a prefix of a witnessed log); `etcdState_of_cert(_last)`/`_of_sealed(_last)` →
  `etcdState_of_nx(_last)` (premises `LogWf'`, `LogSmall`, the length, the keys' bound, in place of
  `storeSmall`); `etcdReached_of_certOk` → `etcdReached_of_nx`; `histLog_of_cert` →
  `histLog_of_srv` (pure, no `srvKVInvs`/mask); `histReached_of_cert` → `histReached_of_nx`;
  `histWL_of_sealed` → `histWL_of_srv`; `srvStep_of_watch E … : srvLog ∗ certOk ⊢ …` →
  `srvStep_of_watch γr on … : srvLog γr on log ⊢ …`; the answers' `E.Nx` (spatial: persistent
  under `envWitOk E`, `srvKVInvs`'), the `+ 3` room.

## Fourth session (2026-11-05/06): the KV path and the clients' model

All five build (`lake build` under the lock: `ServerKV`, `ServerKVOn`, `ClientModel`,
`HistoryModel`, `WatchStep`); `#print axioms` of `raftKV_of_server(On)`, `etcdModelOfServer`,
`etcdModelOfHistory`, `etcdState_of_nx_last`, `etcdReached_of_nx`, `srvLog_of_histLb`,
`histStep_of_srv`, `histWL_of_srv`, `histReached_of_nx`, `srvStep_of_watch`: no `sorryAx`.

- **`ServerKV`, `ServerKVOn` restated over the server's restated request and read path** (the
  answers `putApplied`, `deleteApplied`, `txnAppliedAns`: `srvApi.kvLogLb E.γs x'.log` and the
  witness `E.Nx x'.log` in place of `mvcc.idxCert E.γ.idx x'.log`/`mvcc.certOk E.γ x'.log`, the
  room `x.log.length + 3 ≤ 2 ^ 63` (`appliedHdr`'s, was `+ 4`); `rangeAnsOk`, `txnReadAns` and
  their `On` forms as `rangeReadOk(M)`: `kvLogLb E.γs log ∗ E.Nx log ∗ ⧖ (logCh log) ∗
  ⌜LogWf' log ∧ …⌝`, no longer persistent (`E.Nx` is persistent only under `envWitOk`); a call's
  floor `kvLogLb E.γs F`; `revR := threadTok` (was `mvcc.storeReader E.s E.γ`). The getters'
  `KV().Rev()` by `KV.Rev.contract` at the store handle's type (`shapes.law`, `txn.isMvcc_shape`),
  the update `srvApi.au_read` at the read side's floor `log₀` (`srvReadFieldsAt(M)`'s), the
  instances of `E.Nx`/`E.Cp` from `srvKVInvs(On)`'s `envWitOk`. No mvcc internal (the imports
  `storage.mvcc.ReaderSpecs`, `store__Rev` dropped).
- **`ClientModel` restated** (no mvcc internal): `srvLog γr on log := ∃ L', srvApi.kvNx γr on L' ∗
  ⌜log <+: L' ∧ LogWf' log ∧ log.length < 2 ^ 63 ∧ LogSmall log ∧ LogPutsLe etcdKeyMax log⌝` (a
  prefix of the KV model of a committed raft log); `srvEtcdState γr on`, `srvStep γr on` over it
  (`srvStep` without `certOk`: the witness is `srvLog`'s); `srvReachedAt γr on r :=
  srvApi.srvRevLbA γr on (sint.Z r)`; `srvReadAt E r := ∃ log, kvLogLb E.γs log ∗ ⌜r < len⌝`;
  **`etcdModelOfServer E γr on`** (was `etcdModelOfServer E`). `srvLog_two` by
  `srvRLogLb_prefix` and `kvModelM_prefix` (new, both modes; `kvEntryOn_extends`,
  `kvRaftOfOn_extends`), `logWf'_of_prefix` (new). Bridges: `etcdReached_of_nx` (was
  `_of_certOk`), `srvLog_of_nx`, `srvLog_of_histLb`, `etcdState_of_nx`, `etcdState_of_nx_last`
  (were `etcdState_of_sealed/cert(_last)`, with `storeSmall`).
- **`HistoryModel` restated**: `histLog` a prefix of `kvModel γk A` (was equal: the laws need only
  prefix order); the member bridges plain entailments at the mode off, no update, no short-log case:
  `histLog_of_srv`, `histStep_of_srv`, `histReached_of_srv`, `histReached_of_nx`, `histWL_of_srv`
  (were `histLog_of_cert`, `histStep_of_srv` over `srvKVInvs`, `histReached_of_cert`,
  `histWL_of_sealed`).
- **`WatchStep.srvStep_of_watch γr on`**: `srvLog γr on log ⊢ srvStep γr on …` (no `certOk`).

**F2 (a draft too weak, fixed locally; for the coordinator).** The server's draft restates the
clients' model "over `srvApi.srvLogA` (`histLb`)". `histLb` is a lower bound of the *notified*
log, and a read's log (`rangeReadOk`'s `kvLogLb E.γs log`, a lower bound of the *committed* log)
need not be one (the committed log runs ahead of the notified one between a write's `End` and its
notify). So `etcdState_of_cert` (a range's state is etcd's, client/v3's `Get`) is unprovable over
`srvLogA`. Fix, local to v3rpc: `srvLog` is "a prefix of the KV model of a committed raft log"
(`kvNx` of an extension), which both a read's log (`E.Nx log` itself) and `histLb` give
(`srvLog_of_nx`, `srvLog_of_histLb`); two are prefix-comparable through raft's committed log. No
frozen statement changes; `srvApi.srvLogA` is then unused by v3rpc.

**The server's watch-built restatements (`srvWatchBuilt`, `srvServeFacts`, "For v3rpc" in
`server.md`)**: nothing in v3rpc names them (nor `srvWatchReaders`); only `client/v3`'s
`ServeFromStart(On)` and the examples do. Nothing to follow here.

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

**F1 (the draft unprovable as written; minimal fix applied, local to v3rpc; accepted, decided by the
coordinator, 2026-11-05).** The draft's
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
