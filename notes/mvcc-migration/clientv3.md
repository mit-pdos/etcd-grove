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

### The KV path over the server (`InvServerKV` built; `ServerKV{Get,Put}` checked against a stub; `ServerKVTxn` not checked)

Over v3rpc's landed `ClientModel` (`8c419aa278`: `etcdModelOfServer E γr on`, `srvReachedAt γr on
:= srvRevLbA`, `etcdReached_of_nx`, `etcdState_of_nx(_last)` over `srvApi.kvNx γr on`).
`InvServerKV` builds of record (`lake build`). `ServerKV*` import `LinkMembers` → `Link` (all of
client/v3, the watch path included, red), so `ServerKVGet` and `ServerKVPut` were checked
(`lake env lean`) as one scratch file outside the repository with `LinkMembers`' three results
(`v3.kv.wp_GetM`, `wp_PutM`, `wp_DeleteM`) stubbed: no error but a scratch import
(`optsAt_res`, in `isEtcdKVE_of_kv_r`, whose remaining lines were therefore not checked).
`ServerKVTxn` (it imports `TxnPlain` → `Link`) is edited the same way, not checked.

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

### The watch path's foundation (built of record: `InvWatch`, `WatchLawsHist`, `InvClientNewResult`, `WatchCheck`, `ServerWatcher`, `Spec/…/watcher__Watch`)

Over v3rpc's landed watch path (`WatchApi`, `InvWatch`: `WSrv` without `γ`, `watchSpec R W tok`,
`watchDn γs R W tok`, `watchAuthed tag`, `watchUp` without token or store fact) and the draft's §8:
- `WEnv` gains `W : v3rpc.SrvW GF` (the current member's) and `memW : Nat → v3rpc.SrvW GF`
  (`atIdx` sets `W := memW i`; `memWOf`, `atIdx_W`, `atIdx_memWOf`); `WEnv.EM` deleted (unused).
- `srvWL W L := □ W.histLb L` (the draft's `srvWL2`, boxed: `histLb` is persistent only by
  `srvWOk`'s law); `srvWEnv R W γr addr ics conn wc pfx lg kv` (new `W γr`: the model
  `etcdModelOfServer R.E γr false`; `memW := fun _ => W`).
- `watchLaws`' fourth law: `□ ∀ L, V.W.histLb L ={⊤}=∗ □ V.WL L` (was mvcc's `evLog` with
  `LogSmall`).
- **`srvWLaws W`** (new, persistent): `srvWOk`'s laws but the handle and peek (histLb persistent,
  prefix-comparable, prefix-closed, its model facts; crevOk persistent); `srvWLaws_of_ok`,
  `srvWLaws_model`; `srvOnce_persistent` (an instance for v3rpc's `srvOnce`).
- `watchLaws_srv V on γr (hWM : V.WM = etcdModelOfServer V.R.E γr on) (hWL : V.WL = srvWL V.W)
  (hH : V.W.histLb = srvApi.histLb γr on V.R.E.γs) : srvWLaws V.W ⊢ watchLaws V` (over
  `srvLog_of_histLb`, `etcdReached_of_nx`; no `srvKVFacts`, no `R.γ.st` link).
- `watchLaws_hist V γ γk γr hWM hWL hm (hH : V.W.histLb = srvApi.histLb γr false V.R.E.γs) :
  srvWLaws V.W ⊢ watchLaws V` (over `histWL_of_srv`; was `srvKVInvs ∗ isWatchServer` with
  `hlog0`); `isWatchServer_start` deleted.
- `watchMemberFacts V := srvWLaws V.W ∗ v3rpc.srvOnce V.W ∗ watchLaws V ∗ srvKVFacts V`
  (`watchTokPool`, `srvLogsSmall`, `R.γ.st = R.E.γ`, `mvcc.watchNoDup` gone);
  `watchMemberFacts_once`, `_laws`, `_kv` (`_noDup`, `_st` deleted).
- `srvKVFacts` without `mvcc.idxSealed … [[], []]` (`srvKVFacts_intro`, `srvKVFacts_of_off` without
  it); `srvKVFacts_cperm` deleted (compaction permits: `W.crevOk`, the draft's `compactResp`).
- `watchUp_create V i c h : □ authPubLbM V.R.E.authMode c.bound ⊢ watchUp V.R i (.create c)`.
- `watchConnFacts`: `watchSpec (V.memOf a) (V.memWOf a) tok`; its pure part
  `∃ i, i < V.nm ∧ V.mem i = (V.addr, V.R) ∧ V.memW i = V.W`; `watchConnFacts_cur` gives
  `watchMemberFacts V ∗ ⌜V.pfx ≠ []⌝` (no `R.γ.st` link).
- S2 `srvProgressAllAnswers` deleted (the draft); **S3 `srvEventIdsAssigned R W`** restated as the
  draft's `srvEventIdsAssigned2` (a statement; `srvEventIdsAssigned_holds` not yet proved, so
  deleted: next step); `srvLogsSmall`, `srvNoDupKeys` deleted.
- `wsRow`, `respcE`, `watchCheckOk (tag : GName)` at the server's auth tag (`R.tag`); the spec
  `watcher.Watch.spec`'s post names `watchCheckOk (V.mem 0).2.tag …` (was `.γ`: the field v3rpc's
  `WSrv` lost; no other change to the spec).
- `watchAddrFacts V` (`InvClientNewResult`): `watchSpec V.R V.W`, `eofOk`, `⌜V.pfx ≠ []⌝`,
  `srvWLaws V.W`, `srvOnce V.W`, `watchLaws V`, `srvKVFacts V`; `watchConnFacts_of_addr`,
  `isNewClient_watcher`, `watcher_of_clientTokAt` take `(hw : V.memW = fun _ => V.W)` after `hm`.
- `ServerWatcher`: `srvLogsSmall_of_read`, `srvLogsSmall_of_receipts`, `watchTokPool_of_server`,
  `watchSrvLink_of_server` deleted.

## Done (second session, 2026-11-06): the watch path above the foundation, but `run`

Built of record (`lake build` under the lock), commit `879234f04c` and the next: `WatchBridges`
(new), `WatchStateDefs`, `WatchContent`, `WatchFire`, `WatchCompl`, `WatchResumeSrv`, `WatchEpoch`,
`WatchResume`, `WatchClientModel`, `watchGRPCStream__serveSubstream`, `WatchRun`, and again the
foundation (`InvWatch`, `InvClientNewResult`, `WatchLawsHist`, `WatchCheck`, `ServerWatcher`,
`watcher__Watch`'s spec); `WatchRecon` checked with `lake env lean` (its `lake build` then
failed in the server's `ModeSpecs`, another track's work in progress, which the client imports:
rebuild of record once it builds). No mvcc internal is left in these but the API's own
vocabulary (`evIs`, `kvPtrFixed`, `watchEvents`, `WatchRange`, the `api` names).

### The bridges (`WatchBridges.lean`, the draft's §8 over v3rpc's `mvccOk`/`rcvSnap`)

- `mvccOk_at r j m n x hsrc`: `mvccOk` unfolded at its source `(n, x)`: the pure facts, the down
  list `L` before it, `rcvLb r.γr (pre ++ [x])`, the snapshot's `histLb σ.notifiedLog`,
  `crevOk σ.crev` (spatial) and registry entries.
- **S3 `srvEventIdsAssigned_holds R W : ⊢ srvEventIdsAssigned R W`, proved** (`wsRecvOk`'s first
  conjunct and the snapshot's registry).
- `recvEvents r j m n x i hsrc hX : srvWLaws r.W ∗ srvOnce r.W ∗ mvccOk r j m ∗ regIs r.γreg x.id i
  ={⊤}=∗ ∃ pre Ls L hi, …` (the down list `Ls`, `rcvLb`, `□ histLb L`, `recvEvs (pre ++ [x]) x.id =
  watchEvents L i.rg i.lo hi`, and `mvccOk`'s `sentEvsOf` fact). **The draft's statement takes
  `srvOnce` alone; it is unprovable**: the snapshot's `histLb` is spatial (persistent only by
  `srvWOk`'s law) and `srvOnce` consumes it, while the conclusion gives it back. Fixed locally (a
  client lemma): `srvWLaws r.W` added (the client's member facts have it).
- `progCovd r Lj n x X rg lo` (persistent): a watcher covered by a progress response (its received
  events up to `x` the range's up to `x.rev`, `lo ≤ x.rev + 1`, `x.rev` within the log, `fwdEvs`).
  `progressCov r j m n x X i l Lc Lj … : srvWLaws ∗ srvOnce ∗ mvccOk ∗ regIs ∗ rcvLb l ∗ lb Lj ={⊤}=∗
  progCovd … ∨ (⌜x.id = -1⌝ ∗ cancelQ r.γs X)` (the draft's, with `srvWLaws`, over `createdAfter`'s
  facts: a `-1` received at `n` with `n < |l|` was sent before the created response, so is not `x`).
- `compactResp` (as drafted), `mvccOk_revLb`, `mvccOk_bcast`, `mvccOk_evs`, `mvccOk_dup`
  (`srvWLaws r.W ∗ mvccOk ⊢ □ mvccOk`), `progRev` (an earlier event-less response's revision at most
  `x`'s).

### Finding F-W1 (the frozen API too weak for client/v3's exported completeness contract)

`mvcc.api.wsRecvOk` (`Spec/.../mvcc/ApiState.lean`, frozen) does not say
1. that a watcher's progress notification (conjunct 3's response, its own id or `-1`) is at a
   revision at least its first revision less one: `(w.lo : Int) ≤ sint.Z r.rev + 1`;
2. that event-less responses' revisions do not decrease along the stream.

client/v3's exported contract (`watchStateRespOk`, the cache's completeness: a progress
notification at or past the cursor) needs both: the second cursor `c2` is the watch's start
(`rev - 1`, `lo = rev`) or an earlier progress notification's revision, and the new notification's
revision must be at least it (`cmpl_mono`, `cmpl_prog`'s `q ≤ p`, `cur2Ok`'s `lo ≤ q + 1`); with
`wsRecvOk` alone a later notification at a lower revision is consistent (the coverage facts of two
progress responses at `p < p'` are then equal, no contradiction). Until M1 mvcc's internal
`covFact` (`γw.lo ≤ rev + 1`) and `respRev` (`∀ y ∈ pre, y.evs = [] → y.rev ≤ x.rev`) gave them,
proved by the internals; the code does both (`progressIfSync`: progress only for synced watchers
with `rev ≥ w.startRev`, at `s.rev()` under `s.mu`, which only grows). **Minimal fix** (the API's
`wsRecvOk`, conjunct 3's conclusion and a new conjunct):
```
(∀ j r id w, rs[j]? = some r → r.evs = [] → r.compactRev = W64 0 → S.ws !! id = some w →
   (r.id = id ∨ (r.id = W64 (-1) ∧ w.live = true ∧ w.k ≤ j)) → (w.lo : Int) ≤ sint.Z r.rev + 1) ∧
(∀ i j y x, i < j → rs[i]? = some y → rs[j]? = some x → y.evs = [] → x.evs = [] →
   x.compactRev = W64 0 → sint.Z y.rev ≤ sint.Z x.rev)
```
Here they are the two listed placeholders `wsRecvOk_progLo`, `wsRecvOk_progMono` (exactly these
statements), each one `sorry -- M1-REPLACE`, used by `progressCov` and `progRev`; they go when the
API states them (the API's laws: mvcc track; the coordinator decides).

### The rest of the layer

- `rawRespOk W o c c' v r` at a member's `SrvW` (`□ W.histLb L`, was `mvcc.evLog γst L`);
  `recvCmpl`'s and `WatchResume`'s witness `∃ γst : v3rpc.SrvW GF` (was `mvcc.StoreNames`).
- **`srvKVFacts V`** gains `⌜V.W.histLb = srvApi.histLb γr on V.R.E.γs ∧ V.W.crevOk =
  srvApi.crevOk γr⌝` (in its `∃ on γr`): the member's watch facts are its server's, so a watched
  log extends to a witnessed one the read update fires at, and a compaction response's revision
  is the cluster's permit. `srvKVFacts_intro`/`_of_off` take `hH hC` (last). New:
  `srvKVFacts_cmp V c : srvKVFacts V ∗ V.W.crevOk c ⊢ ⌜c = -1⌝ ∨ kvCmpPermit V.kv c`.
- `WatchFire`: `srvKVCoreM_Nx` (`E.Nx = srvApi.kvNx γr on`), `srvKVCoreM_someNx` (some witnessed
  log, from the KV certificates' invariant), `srvKVFacts_fire`, `srvKVFacts_fire0`; `raw_to_state V
  γ hst o c c' v r Q : srvKVFacts V -∗ srvWLaws V.W -∗ □ AU -∗ posQ -∗ rawRespOk V.W … ={⊤}=∗ …`
  (was at `on E γr γ` with `idxSealed`); `sealed_logOk` deleted.
- `WatchContent`: `evsOf Dm X`, `evs_after` (by id, `recvEvs`), `dispatch_content` by id `X`
  over `recvEvents`' facts (`hfilt`, `hrecv`), `hlor : rr ≤ lo` (was `watcherIs`), the cut over
  `□ V.W.histLb`; `recv_unfiltered` deleted.
- `WatchClientModel`: `gOk`'s sources `ρ : Nat × WResp`, `sentEvsOf_snoc` by id,
  `flatten_evs_filter` over `WResp`.
- `WatchCompl`: `stepCert_of_watch`, `watchChain_of_watch` over `□ V.W.histLb L ∗ srvWLaws V.W`
  (no `hst`); `cLog W L` (`[]` or `□ histLb`), `rcvAt γs pre y` (a response's place in the run's
  received list), `progAt` and `cur2Ok … X rg lo c2` by id (no `w`); `cmpl_mono` over `progRev`
  (takes the run `r`, `mvccOk`, `fwdIdx`); `cmpl_cov` pure over `progCovd`'s facts;
  `recvEvs_snoc_nil`; `chanPos`, `lb_snoc_mem` deleted.
- `WatchResumeSrv`: `resumeF_evless`/`_delivered` take no server fact; `mvccOk_revLb` moved
  (restated) to `WatchBridges`.
- `WatchEpoch`: `respcE_at … (hi) (hw : V.memW i = V.W)` at `watchDn γs V.R V.W tok`.
- `WatchRun`: `ansH`, `idH` over the run (`∃ r, streamAuxIs γs (auxOf r) ∗ ansTok r.γa i` /
  `idTok r.γtok X`); `regSnap γs Dm X rg lo` (the run's registry entry `⟨rg, lo, k⟩` and the
  created response's received-list snapshot); `regFacts V γs Dm P B X rg lo` (no `w`, `fcs`;
  `rr ≤ lo`, `rr ≠ 0 → lo = rr`); `evsSoFar Dm X := evsOf Dm X`; `cursorOk`, `cur2St`, `wsRest`,
  `cur2Pend` by id; `respInfo` deleted from `runCore` (by id, a response of another id leaves a
  watcher's events alone: `wsRest_snoc_other`/`wsElem_recv_other` take no fact); `evsSoFar_fresh`
  pure; `idTok_excl`; `cpl_lo` pure; new `regCov` (`progressCov` at a substream's `regSnap`),
  `reg_events` (`recvEvents` at it), `regFacts_agree`; `prog_cmpl`, `cmpl_step` (takes
  `srvWLaws V.W`, no `hst`), `reg_pre`, `reg_pre_cmp`, `reg_pre_any`, `cmpOkOf_of_mvccOk` (over
  `compactResp` and `srvKVFacts_cmp`), `bcast_pre`, `bcastCov … r nx x X ws` (`progCovd` or
  stopped), `bcast_regPair` (per substream, an update), `cov_cancel` (generic), `bcast_covAll`,
  `bcast_elem`: each takes the run `r` with `hrW : r.W = V.W`, `hrs : r.γs = γs`,
  `streamAuxIs γs (auxOf r)`, `□ mvccOk r j m`, the source `(n, x)` and `srvWLaws V.W ∗ srvOnce
  V.W` (in place of `srvEventIdsAssigned V.R ∗ srvLogsSmall V.R`, `watchRecvOk`, `watcherIs`,
  `mvccCov`); `own_cov`, `bcast_regs`, `regs_collect` deleted.

## Requests

1. **(Landed, 2026-11-06)** Server: the log after a write carries its receipt and well-formedness.
   `resultIsW` now has `⧖ (mvcc.logCh y'.log) ∗ ⌜mvcc.LogWf' y'.log ∧ y'.log.length + 3 ≤ 2 ^ 63⌝`
   (`InvRequest.lean`). Not yet used: `putAns_st`/`delAns_st`/`txnAns_st`'s callers (`ServerKV*`)
   import `Link`, red until `watchGRPCStream.run` builds.
2. **mvcc's API (finding F-W1, above): `wsRecvOk` states a progress notification's lower bound and
   event-less responses' monotone revisions.** The two placeholders' statements are the fix.
3. **Whoever builds the client's member facts** (`ServeFromStart(On)`, `examples/common`,
   `linkv3p/WatchEnv`, the cache's `Results`): `srvKVFacts_intro`/`_of_off` take the ties
   `hH : V.W.histLb = srvApi.histLb γr on V.R.E.γs` and `hC : V.W.crevOk = srvApi.crevOk γr` (the
   server's `W` for v3rpc must be these: `watchLaws_srv` takes `hH` already).

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
  `txnCommitResultTok_of_reply (… hx hlo hrb hNx)`; (second session) `srvKVFacts_intro (… hrb hH
  hC)`, `srvKVFacts_of_off (… hrb hH hC)`.
- `lessor__Revoke.lean` (client's) builds as it is.

## Left (in order)

1. **`watchGRPCStream__run.lean`** (red; the only module of the watch path not restated): over
   `WatchRun`'s restated lemmas. **Edited, not yet checked** (the other tracks' rebuilds held the
   lock and deleted imported `.olean`s; first thing next session: `lake env lean` / `lean-check.py`
   it and fix): the member facts (`⟨#Hwl, #Honce, #Hlaws, #Hkvf⟩`, `Hpfx`), the token pool gone,
   `respInfo` gone, `respcE_at … hmi hmw`, `watchDn`'s run (`⟨%r, %Hrr, #Haux, %Hcm, Hcase⟩`,
   `hrR hrW hrs`), `ctrlOk`'s new shape, the registration (`Hidp` over `ctrlWatcher r`, `regSnap`
   from `createdAfter r`, `regFacts`, `evsSoFar_fresh` pure, `cpl_lo`, `cur2Ok_init` not an update),
   the mvcc branch (`mvccOk_dup`, `mvccOk`'s pure facts at `(nx, ρ)`, `compactResp`,
   `mvccOk_bcast`, `bcast_covAll`/`bcast_elem`/`reg_pre_any`/`reg_post` at the new arguments). The
   sites as they were (lines as of `879234f04c`): 207-215 (`watchMemberFacts`
   is `srvWLaws ∗ srvOnce ∗ watchLaws ∗ srvKVFacts`: no `Htoks`/`Hsmall`/`Hnoc`; drop
   `srvProgressAllAnswers_holds`, keep `srvEventIdsAssigned_holds V.R V.W` only if needed: `WatchRun`
   no longer takes it); 525, 1652, 2801 (`mvcc.watchTokPool_take`: gone, `watchUp_create` takes no
   token, `watchUp V.R i (.create c)` is `⌜watchReqOk⌝ ∗ □ authPubLbM`); 754 (`watchDn` is
   `∃ r, ⌜r.srv = V.R ∧ r.W = V.W ∧ r.γs = γs⌝ ∗ streamAuxIs γs (auxOf r) ∗ hdr ∗ (ctrl ∨ mvccOk)`:
   keep `r`, its `hrW`, `hrs`, `#Hax`, and `mvccOk_dup` with `srvWLaws V.W` to box `mvccOk`); 760-830
   (`ctrlOk r tok m`'s `upAtW ∗ ctrlAnswers ∗ ctrlWatcher r ∗ ansTok r.γa i`; `ans_fresh γs ansd i
   r`; `ctrlWatcher r tok (.create c) m` for not canceled: `∃ i, createRangeOk c m.watchId i.rg ∗
   regIs r.γreg m.watchId i ∗ idTok r.γtok m.watchId ∗ wsSentLb r.ι i.k ∗ (lo's fact) ∗
   watchAuthed r.srv.tag …`; `id_fresh γs regs X r`; the watcher's facts become `regFacts` once
   `createdAfter r p m` gives `regSnap`'s `rcvLb r.γr l`, `i.k ≤ |l|`, the `-1`s of `l` sent among
   `L`; `rr ≤ lo` and `rr ≠ 0 → lo = rr` from `ctrlWatcher`'s `if c.startRev = 0 then ∃ Lr, histLb Lr
   ∗ ⌜i.lo = |Lr|⌝ else ⌜i.lo = nat startRev⌝` and `ctrlAnswers`' `0 ≤ startRev`); 1065, 1335
   (`watcherIs` unfoldings: `regFacts`' pure part), 1103, 1424 (`createdAfter`, by id: no
   `idAssigned_agree`); 1622, 1779, 1845, 1937, 2135, 2212, 2302, 2427, 2477, 2581 (`respInfo`:
   gone from `runCore`, delete those blocks); 1942-2016 (`mvccOk` destructuring: use `mvccOk_at r j m
   n x hsrc` for the pure facts, the `-1` case `mvccOk_bcast`, the compaction facts `compactResp`; no
   `mvccCov`/`respCov`/`respCompl`/`respOk`); 2035 (`bcast_covAll V G n γs r hrW hrs j m n x hsrc hxe
   hxc hid hj hinj $$ [Hl Ho Hax Hmv HDw Hstok HelM]`); 2059 (`bcast_elem … X ws' r hrW hrs
   S.Dm.length m n x h sl hsrc …`); 2331-2345 (`reg_pre_any … r hrW hrs j m n x rg lo …`, the
   premises `srvWLaws V.W ∗ srvOnce V.W` in place of `HS3 Hsmall`); `recvMvcc_ok` takes `ρ : Nat ×
   WResp`; `wsElem_recv_other … m ρ hsrc rfl …` takes no `respOk`. Then `watcher__Watch` (the
   proof), `Link`'s members.
2. `ServerKVGet`'s `isEtcdKVE_of_kv_r` (the scratch import `optsAt_res`), `ServerKVPut`,
   `ServerKVTxn` (import `Link`; `putAns_st`/`delAns_st`/`txnAns_st` over `resultIsW`'s landed
   receipt): once `Link`'s members build.
3. `ServedOn`, `ServeFromStart(On)` (import `Results`: after the coordinator's restatement);
   `ServeFromStart` uses `srvServeBuilt` without `mvcc.storeReader` slots, and `srvKVFacts_intro`'s
   ties (request 3).
4. `examples/common`: `Defs.lean` drops `srvWatchReaders s E 64` and the `mvcc.storeReader E.s E.γ`
   slots (now `threadTok`s), but its boot premises (`idKeyFactAt … E₀.γ.idx`, `mvcc.idxFresh
   E₀.γ.idx`) follow the server's `NewServer.spec`, not restated yet (the server's "Left", the boot).

## Placeholders (`M1-REPLACE`)

- `WatchBridges.wsRecvOk_progLo`: `wsRecvOk` lacks a progress notification's lower bound (finding
  F-W1).
- `WatchBridges.wsRecvOk_progMono`: `wsRecvOk` lacks event-less responses' monotone revisions
  (finding F-W1).

No axiom.

## Exported results

No statement of client/v3's exported results changed by these sessions' files except through the
definitions they name: (first session) `putReplied`, …: `srvLogCert` in place of `idxCert ∗
certOk`, the floors `kvLogLb`; (second session) the member facts' `srvKVFacts` (the ties of the
member's `W` to its server's) and `recvCmpl`/`rawRespOk` (a member's `SrvW` in place of mvcc's
`StoreNames`), both inside `watchConnFacts`/`watchAddrFacts`, which `watcher.Watch.spec` and
`isNewClient_watcher` name. Their statements will change by v3rpc's `etcdModelOfServer E γr false`
(an argument). The watch contract's statements (`watchStateRespOk`, `watchStateElem`, `cmpOkOf`)
are unchanged; keeping them needs finding F-W1's fix.
