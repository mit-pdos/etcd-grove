# client/v3 and `examples/common` onto mvcc's API (strict M1): hand-off

Scope: `Proof/go_etcd_io/etcd/client/v3/**`, `Spec/go_etcd_io/etcd/client/v3/**`, and
`examples/common` (`Proof/github_com/mit_pdos/etcd_grove/examples/common/**`). `Results.lean` and
`Link.lean` are the coordinator's (below, "For the coordinator").

## Done (first session, 2026-11-06)

### The KV path's vocabulary (`KVService.lean`, built of record)

- **`srvLogCert E log`** (new, persistent): what a reply certifies of the log it read or wrote, in
  place of mvcc's `idxCert E.γ.idx log ∗ certOk E.γ log`:
  `srvApi.kvLogLb E.γs log ∗ □ E.Nx log ∗ ⧖ (mvcc.logCh log) ∗ ⌜LogWf' log ∧ log.length + 3 ≤ 2 ^ 63⌝`
  (the server's `rangeReadOkM`/`txnReadOkM` facts; `E.Nx` under `□` so the replies stay persistent:
  the server's `envWitOk E`, in `srvKVInvs`, makes `E.Nx` persistent). Mode-agnostic (`E.Nx` is
  `kvNxOff` off, `kvNxOn` on), so `KVServiceOn` can reuse the reply predicates.
- `srvLogCert_logOk` (proved, by `preceipt_lt`, as the server's `srvApi.logOk_of_receipt`) replaces
  `idxCert_logOk`; `putAns_st`, `rangeAns_st`, `delAns_st`, `txnAns_st` use it (same statements).
- The floors (`etcdPutSpec`, `etcdRangeSpec`, `etcdDeleteSpec`, `etcdTxnSpec`, `floorsAt`, `knownAt`,
  `srvStart`, `floorsAt_srvsAt`, `knownAt_srvsAt`) are `srvApi.kvLogLb E.γs F` (was `idxCert`);
  `srvStart_alloc` by `monoListLbOwn_nil`.
- `txnReplied`, `putReplyOk`, `rangeReplyOk`, `putReplied`, `deleteReplyOk`, `deleteReplied`: the
  log's `srvLogCert` in place of `idxCert ∗ certOk` (one conjunct fewer: patterns `#Hc, -, -, %Hk`).
- KVService no longer imports mvcc's internals (`InvIndex`, `InvStore`, `BucketLemmas`).
- Built with it (`lake build`): `KVMembers`, `kv__Get`, `kv__Put`, `kv__Delete`, `kv__Do`,
  `kv__Txn`, `txn__Commit`, `txn__If/Then/Else`.

### The KV path over the server (`InvServerKV`, `ServerKV{Get,Put,Txn}`: edited, **not checked**)

Not checkable yet: they import v3rpc's `ClientModel` (being restated by the v3rpc track, on disk
uncommitted: `etcdModelOfServer E γr on`, `srvReachedAt γr on := srvRevLbA`, `etcdReached_of_nx`,
`etcdState_of_nx(_last)` over `srvApi.kvNx γr on`), which imports the server's `InvApplier`/
`KVStoreApi` (red at the time), and `ServerKV*` import `LinkMembers` → `Link` (all of client/v3,
the watch path included, red).

- `InvServerKV` imports `KVService` (not `Results`: it used only docstring names of it).
- **`nxOrNil E l := ⌜l = []⌝ ∨ E.Nx l`** (new): a floor a client may take (until M1 `certOk`, whose
  first case was free). `kvAnyAu`, `kvRangeAu` quantify over it (`∀ op l, nxOrNil E l ={⊤}=∗ …`).
- `kv_client_floor` over `nxOrNil E l` (the `[]` case by `monoNatLbOwn_0`; else `srvKVInvs`'s tie
  `E.Nx = kvNxOff` and the server's restated `kv_cert_floor γ γk x hx1 hx3 l σ`).
- `certOk_of_reached` → **`nx_of_reached E γr lo : srvKVInvs E γr ∗ etcdReached (EM :=
  v3rpc.etcdModelOfServer E γr false) lo ⊢ ∃ l, nxOrNil E l ∗ ⌜sint.Z lo ≤ 0 ∨ sint.Z lo < l.length⌝`**
  (the floor's callers use the disjunction in `omega`).
- `floor0_of_read`: `∃ F, srvApi.kvLogLb E.γs F ∗ ⌜2 ≤ F.length ∧ LogPutsLe etcdKeyMax F⌝` (the
  restated `srvReadFieldsAt`'s floor).
- New: `srvLogCert_kvNx` (`srvLogCert E log ⊢ srvApi.kvNx γr false log` at the tie), `srvKVInvs_nx`.
- `ServerKV{Get,Put,Txn}`: at `v3rpc.etcdModelOfServer E γr false`; `storeSmall` gone (the read
  side's `storeSmall_of_read` is deleted): a reply's log is small by its receipt, so
  **`kv_get_server(_r)`, `isEtcdKVTodo_of_kv`, `isEtcdKVE_of_kv_r`, `kv_put_result`,
  `isEtcdPutKVTodo_of_kv`, `kv_delete_result`, `isEtcdDeleteKVTodo_of_kv`, `isEtcdTxnKVTodo_of_kv`
  take `(hrb : receiptBound GF ≤ 2 ^ 62)`** (last); `putResult_of_reply`, `deleteResult_of_reply`,
  `txnCommitResultTok_of_reply` take `hrb` and the tie `hNx : E.Nx = kvNxOff γ.raft γ.kv` in place
  of `storeSmall E.γ ∗`. `kvLeasedPutTodo api E γr` (new `γr`: the model needs it);
  `kvLeasedCommitTodo E _γw γr …` uses its `γr`; `etcdReached_zero E γr`.
  These are client/v3-internal (no exported result names them; `InvLease`/recipes mention them in
  docstrings only).

## Requests

1. **Server (the write path's posts): the log after a write carries its receipt and well-formedness.**
   `resultIsW`/`resultIsWOn` (`InvRequest.lean`, `ReqOn.lean`), hence `putAppliedOk`,
   `deleteAppliedOk`, `txnAppliedOk`, and v3rpc's `putApplied`/`deleteApplied`/`txnAppliedAns`
   (`ServerKV.lean`), give for `y'.log` only `kvLogLb ∗ revMinted ∗ appliedWit ∗ E.Nx`. The client's
   `putAns_st`/`delAns_st`/`txnAns_st` (the exported `isKv` calls' `putStOk`/`delStOk`/`txnStOk`:
   `kvLogOk` of the state after the write) need `LogWf' y'.log`, `y'.log.length < 2 ^ 63` and
   `LogSmall y'.log`, which until M1 came from `idxCert y'.log`. **Minimal fix:** add
   `⧖ (mvcc.logCh y'.log) ∗ ⌜mvcc.LogWf' y'.log ∧ y'.log.length + 3 ≤ 2 ^ 63⌝` to `resultIsW(On)`
   (the writer's facts at `y'.log`, `KVStoreCore.writer_facts`, give exactly these, and
   `MvccReachable → LogWf'` by the API's `reach_logWf.law`). The client's write replies
   (`putReplied`, …) take them as `srvLogCert E y'.log`. Without it the bridge from v3rpc's
   `put_end_to_end` to `putReplied` (client `Results.lean`) has no proof.
   (Also: v3rpc weakened `putApplied`'s `x.log.length + 4` to `+ 3`; the client's `putReplied` keeps
   `+ 4`, which follows from the requested `y'.log.length + 3 ≤ 2 ^ 63` for an applied put,
   `y'.log = x.log ++ [cs]`.)

## For the coordinator (`Results.lean`, `Link.lean`)

- The bridges from v3rpc's `*_end_to_end` to `putReplied`/`rangeReplyOk`/`deleteReplied`/
  `txnReplied`: `srvLogCert E log` from the server's `kvLogLb ∗ E.Nx ∗ ⧖ ∗ ⌜LogWf' ∧ …⌝` with
  `□ E.Nx` from `envWitOk E` (`srvKVInvs`); `LogPutsLe` as before (the server's keys lemma).
- `etcdModelOfServer E` → `etcdModelOfServer E γr false` in every statement (v3rpc's restatement;
  the exported results that name the model change by that argument only).
- New hypothesis orders (all the theorem's existing arguments first, then): `kv_get_server_r`,
  `kv_get_server`, `isEtcdKVTodo_of_kv (… hAs hrb)`, `isEtcdKVE_of_kv_r (… hpfx hrb)`,
  `kv_put_result (… h hrb)`, `isEtcdPutKVTodo_of_kv (… hAs hrb)`, `kv_delete_result (… h hrb)`,
  `isEtcdDeleteKVTodo_of_kv (… hAs hrb)`, `isEtcdTxnKVTodo_of_kv (… hAs hrb)`;
  `putResult_of_reply (… lf hlo hrb hNx)`, `deleteResult_of_reply (… lf hlo hrb hNx)`,
  `txnCommitResultTok_of_reply (… hx hlo hrb hNx)`.
- `lessor__Revoke.lean` (client's) builds as it is.

## Left (in order)

1. Check `InvServerKV`, `ServerKV{Get,Put,Txn}` once `ClientModel` (v3rpc) and the server build
   (`lake env lean` needs `LinkMembers`' olean, i.e. `Link`: the watch path first).
2. The watch path (`InvWatch`, `ServerWatcher`, `WatchFire`, `WatchCompl`, `WatchLawsHist`,
   `WatchContent`, `WatchRun`, `watchGRPCStream__run`, `watcher__Watch`, `WatchResumeSrv`,
   `WatchStateDefs`), over v3rpc's landed `WatchApi`/`InvWatch` (`WSrv` has no `γ`; `watchSpec R W
   tok` takes the server's `SrvW`; `WRun`, `mvccOk`, `rcvSnap`) and the draft's §8 bridges
   (`notes/mvcc-api-clients/WatchSpecs.lean`: `srvEventIdsAssigned2`, `recvEvents`, `progressCov`,
   `compactResp`, `srvWL2 W L := W.histLb L`): `WEnv` gains the member's `SrvW`; `srvWL`,
   `srvLogsSmall`, `srvNoDupKeys`, `watchMemberFacts` (no `watchTokPool`, `watchNoDup` →
   `srvOnce W`), `srvKVFacts` (no `idxSealed`, `srvKVCoreM` → the restated read facts),
   `watchLaws_srv` over `histLb_model.law`. Not started.
3. `ServedOn`, `ServeFromStart(On)` (import `Results`: after the coordinator's restatement);
   `ServeFromStart` uses `srvServeBuilt` without `mvcc.storeReader` slots.
4. `examples/common`: `Defs.lean` drops `srvWatchReaders s E 64` and the `mvcc.storeReader E.s E.γ`
   slots (now `threadTok`s), but its boot premises (`idKeyFactAt … E₀.γ.idx`, `mvcc.idxFresh
   E₀.γ.idx`) follow the server's `NewServer.spec`, not restated yet (the server's "Left", the boot).

## Placeholders (`M1-REPLACE`)

None. No axiom.

## Exported results

No statement of client/v3's exported results changed by this session's files except through the
definitions they name (`putReplied`, …: `srvLogCert` in place of `idxCert ∗ certOk`, the floors
`kvLogLb`). Their statements will change by v3rpc's `etcdModelOfServer E γr false` (an argument).
