# Track TX of the `origin/lean` → `mvcc-api` merge (2026-11-06): txn, v3rpc's KV path, client/v3

Resolved per `merge-brief.md`: mvcc-facing text ours, the rest lean's. No `lake build`, nothing
checked; all files staged, no markers.

## Per file

### txn

- `Spec/.../txn/{Txn,executeTxn,txn}.lean` (2 hunks each): **ours** (the restatement over the API,
  docstrings included), `mvcc.errorfIs err` → `mvcc.ctxErrorf err` in the done-context branch
  (lean's only change to these specs: verified by `git diff 5eea04e0d6 MERGE_HEAD`).
- `Proof/.../txn/txn.lean` (1): **ours'** structure (`hndro Hndf`), lean's
  `ihave ⟨%x, %Hx⟩ := mvcc.ctxErrorf_ok _ $$ He` in place of ours' `iunfold mvcc.errorfIs`.
- `Proof/.../txn/executeTxn.lean` (4): imports **both** (`txn.ApiLemmas`, `Spec.fmt.ErrorfWrap`);
  the header **ours** (`hsh : mvcc.api.shapes.law`, ours' intro/`mvccTxn_shape`) **plus lean's
  `(hWrap : fmt.ErrorfWrap.spec)`** as the last premise; the `wp_join` postcondition **ours**
  (`mvccTxn`, `Htrc`) with `ctxErrorf`; the error's construction **lean's** (`%w` wrap through
  `hWrap`, `ctxWrapErr_stringMethodSpec`/`ctxWrapErr_wrap2`, `e0`), followed by ours' frame.
- `Proof/.../txn/KeyObs.lean` (1): **ours** (the empty module importing `txn.ApiLemmas`).
- `Proof/.../txn/applyCompare.lean` (1): **combined**: ours' `iframe Htx Htrc` plus lean's
  `typedPointsto_not_null_dup` (the `kvIs` non-null conjunct, auto-merged further down).
- `Proof/.../txn/ApiLemmas.lean` (non-conflicted, adapted): ours' copy of mvcc's `Errorf.lean`
  (`txn.wp_New_errorString`, `txn.wp_Errorf_errorfIs`, the `errorf` section) **deleted**: its only
  user was `executeTxn`'s old error branch, now lean's `hWrap` wrap.

### v3rpc

- `ServerKV.lean` (3): hunks 1-2 **lean's** merged-mode rows `rangeAnsOkM on`/`txnReadAnsM on`
  (with lean's off abbrevs `rangeAnsOk`/`txnReadAns` = `…M false`), their log conjuncts **ours**
  (`srvApi.kvLogLb E.γs log ∗ E.Nx log ∗ ⧖ (mvcc.logCh log) ∗ ⌜mvcc.LogWf' log ∧ …⌝`; "persistent"
  dropped from the docstring, as ours). Hunk 3 **lean's** (the per-conjunct proofs
  `kv*Ok_of_server`, `raftKV_of_server` deleted: lean moved them to `ServerKVOn` as `…_of_serverM`
  over `E.authOn`). Ours' auto-merged changes kept (`srvKVAns`'s floor `kvLogLb E.γs F`,
  `revR := threadTok`, the `+ 3` rooms, the write answers' `kvLogLb`/`E.Nx`).
- `ServerKVOn.lean` (10): **lean's file** (stage 4/5's merged `srvKVAnsM`, `kv*Ok_of_serverM`,
  `raftKV_of_serverM`, the `_mono`/bridges), with ours' mvcc restatement re-applied by hand:
  `srvKVAnsOn`/`srvKVAnsM`'s floor `srvApi.kvLogLb E.γs F` and `revR := threadTok`; the write
  answers' `Hcok` spatial; `rangeReadOkM`/`txnReadOkM`'s patterns `⟨%log, #Hcert, Hcok, #Hrcp, …⟩`,
  `Hlen` reindexed, `isplitl [Hcok Hlin HQl]`; `hdr_of_own … threadTok`; the getter
  `kvGetOk_of_serverM` and `raftKV_of_serverM` take `hsh hP hR` (`mvcc.api.shapes.law`,
  `persistent.law`, `mvccState_reachable.law`) in place of `hRev : mvcc.store.Rev.spec`, the body
  ours' (`txn.isMvcc_shape`, `srvApi.au_read`, `KV.Rev.contract`).
  - `MERGE-TODO(v3rpc-getters)`: the store invariant `Hks` and `E.Nx`/`E.Cp`'s instances from
    `srvKVInvsM E.authOn`: ours had one text per mode (off/on); the on text is in place, a case on
    `E.authOn` is needed once the server's merged `srvKVInvsM` is settled.
- `serverWatchStream__isWatchPermitted.lean` (1): **combined**: ours' `ci cd` (swsIs's
  parameters), lean's extra `-` in `AuthInfoFromCtx`'s post pattern.

### client/v3

- `KVService.lean` (1): **combined**: ours' floor `srvApi.kvLogLb E.γs F`, lean's new
  `txnRevLb γw.kv t m -∗` (k8s-compactor U1; client-level ghost, no mvcc).
- `WatchFire.lean` (1): **combined**: lean's `⌜kvRoom σ⌝` in the AU, ours' `client.rawRespOk V.W`.
- `KVServiceOn.lean` (non-conflicted, adapted): lean's merged rows had 8 `mvcc.idxCert E.γ.idx F`
  floors (4 new); all → `srvApi.kvLogLb E.γs F` (matches `srvKVAnsM`'s call).

## Will break / to follow (not edited: other owners or next phase)

- `v3rpc/Results.lean` (coordinator's): `raftKV_serverM` calls `raftKV_of_serverM … EtcdServer.wp_KV
  mvcc.store.wp_Rev EtcdServer.wp_Cluster …`: replace `mvcc.store.wp_Rev` by
  `mvcc.api.mvccApi_shapes_law mvcc.api.mvccApi_persistent_law_holds
  mvcc.api.mvccApi_mvccState_reachable_law_holds` (ApiResults' names).
- `etc/link-lean-first-txn.txt` (merged as lean's): `executeTxn`'s line has
  `mvcc_metricsTxnWrite__Rev … mvcc_txnReadWrite__Changes … fmt_ErrorfWrap`; ours' proof takes
  `hsh : mvcc.api.shapes.law` first and `hWrap` last (after `hDel`); `txn`'s and `Txn`'s lines are
  likewise lean's (ours never regenerated txn's `Link.lean`). Regenerate in M3.
- `txn.KeyObs`'s former content (`kvWriter_keyObs`, `kvWriter_noCmp`, `mvcc.writerPin_*`) is used
  by lean's `etcdserver/SnapSendBranch.lean` (1068, 1072, 1077), `StopImage.lean` (60, 76, 80),
  `StopShutdown.lean` (289, 302: `mvcc.writerPin_noCmp`/`_keyObs` directly); `backend/InvStop.lean`
  (143, comment). They go to `mvcc.api.mvccImage_snapshot.law`.
- `client/v3/LeaseGrantServed.lean` (new on lean; 315, 319, 592, 596) and `AuthnServedOn.lean`
  (220, 234: one more than ours) name `mvcc.storeReader E.s E.γ` (`hA : A.revR = …`, the lease
  read's reader): `srvKVAnsM`'s `revR` is now `threadTok`, so `hA` fails; the lease path's reader
  (`v3rpc.raftLeaseRead`, `InvLeaseRead`, `ServerLeaseRead`) is unmigrated on ours too.
- Unchanged by the merge but still over mvcc internals on ours (already red before the merge):
  `txn/{Results,SoleWriterKV,Lemmas,Writer,Defs,KVWrite}`, `client/v3/{InvServerKV,Results,
  ResultsOn,ClientPutGet,kv__*,KVMembers,LeaseReadServed,ServeFromStart,WatchBridges,WatchRun,
  InvWatch}`, `v3rpc/{InvLeaseRead,ServerLeaseRead,Results}` (`idxCert`, `certOk`, `storeReader`,
  `isKV`, `watcherIs`, `idAssigned`, `kvWriter`).
- No user in these directories of lean's F2 names deleted with mvcc's F2 modules (checked).
- `mvcc.ctxErrorf`, `ctxErrorf_ok`, `ctxErrorf_ne_nil` (used by txn, `ServerKVOn`): track BK's port.

## Spec changes

- `txn.Txn.spec`, `txn.executeTxn.spec`, `txn.txn.spec`: the done-context disjunct
  `mvcc.errorfIs err` → `mvcc.ctxErrorf err` (lean's errorf-wrap, applied to ours' restatement;
  nothing else).
- `txn.executeTxn.wp_proof` gains `(hWrap : fmt.ErrorfWrap.spec)` (lean's; trust base: lean's
  `fmt.ErrorfWrap` axiom).
- v3rpc: `kvGetOk_of_serverM`/`raftKV_of_serverM`: `hRev : mvcc.store.Rev.spec` → `hsh hP hR` (ours'
  restatement of the getters, as ours' `raftKV_of_server(On)`); `srvKVAnsM`/`srvKVAnsOn`
  (`call`'s floor, `revR`), `rangeAnsOkM`/`txnReadAnsM` (the log's facts, no longer persistent):
  ours' restatement on lean's merged-mode rows.

## API weaknesses

None found in this area beyond what ours' hand-offs record (the lease read's reader, above, is
the plan's risk 1 territory: the store's readers are not client-held tokens).
