# The watch over etcd's KV state, and its clients (D46; 2026-10-26, branch `worktree-kv-stated-specs`)

The user's decisions (2026-10-26): the watch spec is `watcher.Watch.specσ` (`client/v3/WatchState.lean`:
each response one firing of the caller's persistent read update of `σ`, its events exactly
`σ.rangeEvents`); the applications **and** the libraries (the cache, recipes, concurrency,
leasing) use the new KV specs and `specσ`, and rebuild their own abstractions on top (an invariant
holding `etcdKV γ σ` with the authority of a ghost structure whose fragments they reason with);
the server-side contract (`EtcdModel` at `etcdModelOfServer`, `srvNoDupKeys`, `watchLaws`) goes.

## Stage 1: prove `specσ` (the client watcher's pipeline)

Today the pipeline (`run`, `serveSubstream`, `WatchRun`, `WatchCompl`, `WatchRecon`, the resume
files) carries two cursors: the dispatch cursor `γhi` with the weak per-event contract
(`rangeWatchRespOk`, whose put clause needs `srvNoDupKeys`: `ev_ok`, `WatchContent.lean`) and the
second cursor `γh2`/`cur2` with the cache's completeness contract (`recvCmpl`: `watchRespOk` at
`V.WM`, built by `cmpl_events`/`cmpl_prog` from mvcc-level facts through `watchChain_of_watch`).
`startOk` (the server reached `rev - 1`) is consumed only by `cmpl_prog`'s case of a progress
notification at the start revision minus one that the covered log does not reach.

Steps:
1. `recvElem`'s weak contract becomes its pure cursor part (`dispOk`: events sorted, above `c`,
   `c'` the last's revision or `c`); `dispatch_content` drops `ev_ok`'s state clause and
   `srvNoDupKeys` (out of `watchMemberFacts`).
2. A server-level completeness contract `rawRespOk` (no `EtcdModel`): an error; no events, not a
   progress notification; a progress notification at `p` (if `c < p`: a watched log `Lc` with
   `p < Lc.length` and no range event in `(c, p]`; if `p ≤ c`: the cursor kept); events
   `zipWith evModelOf (watchEvents Lc rg (c+1) (c'+1)) kvs` with the key-values fixed
   (`kvPtrFixed`), `c'` the last's revision, `c' < Lc.length`. `cmpl_events`/`cmpl_prog` (and
   `prog_cmpl`, `cmpl_step`, `own_cov`, `bcast_covAll`) produce it instead of `watchRespOk`;
   `startOk` is no longer needed (removed); `watchLaws`, `V.WM`, `V.WL` drop out of the pipeline.
3. The substream carries the caller's read update (`WsPrm`: `Q`, and `wsIs`: `□ AU` on
   `etcdKV`); each member's facts carry its KV invariants (`srvKVInvs`) at the cluster's KV state
   name (`WEnv`'s). Where a response is published to `outc` (`serveSubstream`, the canceled
   response of `sendCloseSubstream`, the closed channels of `WatchApiLemmas`/`Watch`), the update
   fires (`watch_fire`: `kvInv` open, `kv_cert_read`, `srvRLog_lb`; `σ = kvStateOf C` with the
   watched log a prefix of `C`) and `rawRespOk` becomes `watchStateRespOk` (`rangeEvents_kvStateOf`,
   the range `covers` ↔ `inRange`).
4. `outc`'s element is `watchStateElem` at the second cursor; `watcher.Watch.spec` is `specσ`
   (moved into `Spec/go_etcd_io/etcd/client/v3/watcher__Watch.lean`); `isKvWatcher`'s facts have
   no `srvNoDupKeys`. Candidate change to `specσ`: a progress notification at `p ≤ c` (cursor kept)
   promises nothing about `σ` (no `p ≤ σ.rev`).

## Stage 2: the libraries over `σ`

The cache, recipes, concurrency and leasing are stated over `EtcdModel` and the client contract
(`isEtcdClient`, `isEtcdKVE`, `isEtcdWatcher`, `isEtcdRangeWatcher`). Their instance becomes one
built from a client invariant over `etcdKV γ σ` (as `kvClientInv`): states, steps and reached
revisions as persistent fragments of a monotone record of `σ`, the revision tokens minted at the
writes the invariant's updates make; the contract proved from the KV specs and `specσ`. Laws that
need no duplicate keys per revision: dropped where the libraries do not use them, else kept as a
fact of the invariant (the libraries' writes are duplicate-free).

## Stage 3: the applications

watchkv, linkv3p's `MainWatch` on `specσ` with an invariant over `σ.changes` (every revision from
2 one plan put); cachekv over the cache's new instance.

## Stage 4

Full build, `etc/tcb-report.py --check` (and `--update` for the removed axioms/sorries), the
generated links, STATUS; merge into `lean`.
