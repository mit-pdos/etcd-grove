# J8a: `applyAll` with a snapshot (plan, 2026-11-01)

Stage J8a of `notes/snapshot-sj-plan.md`: the apply thread's job on a snapshot payload
(`rnApSnap`, the `sorry -- SNAPSHOT-SORRY` at `EtcdServer__run.lean` ~:873 and its auth-on twin
~:1412) runs `applyAll` over `applySnapshot.specSnap`, and `srvSnapApplied` gives back what the
next batch and the next snapshot take. Built on J1b (`snap-sorries` at `15ff878455`). J8b (the loop's
`applyRes` with `kvReach`, the link, `applyAll_model`) follows.

## The inventory (2026-11-01)

Every premise and resource of `specSnap`, against the apply thread's state at that `sorry`. Ready
(no work beyond glue): the apply thread's resources (`applyRes`), `srvSnapRO`'s fields and contracts,
`srvSnapRes` (stop channels, `bOpen ½`, the alarm store's `Get`, the KV's closer, `pathOwn` of the
backend path), the counter `γt` (`hnt`), J7's image facts (`SnapImageFacts`: `hmeta`, `hlease`,
`halarm`, `hauthb`, `hmemb`, `himg`, `hA'`, `hpre`, `hRok`, `hkI`, `certOk`), `hi`, `hle`, `hkb`,
`hstp`, `hlid`, `trLive`, the payload's snapshot (`ownSnapM … DFrac.discard`).

## Open problems, by risk

1. **R-loc lost: the snapshot file's `fileHolds`.** `snapDirInv` gives `fileHolds (snapDBPath ss i) D`
   from `snapSaved γd i`, which J2 got from raft's `snapLocal` in the snapshot `Ready`. Raft's
   internal `readySnapData` still has it (`InvNodeChan.lean:733`), but the node API's snapshot `Ready`
   (fdf2da3d6b, "snapshot paths unreachable") does not, and `rnApSnap` has `snapshotCert` in its place
   (its docstring still says `snapLocal`); `snapLocal_of_saved` was deleted (`Net.lean:294`). Fix: a
   raft API law giving `snapLocal` with the snapshot `Ready` (as `nodeDriver_hardStateCommitted`:
   an API change, `interface/` diff), then `rnApSnap` carries it again. **Approval: raft API.**
   *API part done (2026-11-01, the user approved):* `stepIn_intro` takes `snapLocalMsg`, `readySnap`
   gives `nodeSnapLocal` (decisions, "The raft API's `snapLocal` clause"); `rnApSnap` carries it
   (2026-11-01), and `rnApplyTok_recv`'s snapshot case gives it to the apply thread. Item 1 done; the
   apply thread turns it into `snapSaved γd i` with `nodeSnapLocal_elem` and `srvClusterOk`'s
   `snapLoc` (J8a-5). That case now also keeps `rnRtOk` at `A'` (item 4's merge).
2. **The `isMetaBackend` family is false as stated** (`specSnap`'s `□ ∀ π b, π.m0 = (i, tI) →
   isMetaBackend b … (readView (γ.withPh π))`, "D22 J1a"): any names `π`, any backend `b`. Restate:
   tie `π` to how `b` was opened (`isBackend` at `batchLockInv (γ.withPh π)`) and to the opened data's
   meta keys (`metaIs D π.m0`); or prove it from the backend's `ReadTx` (verified) and the protocol.
   **Approval: `specSnap` is a spec here, not trusted; but the premise is a named one to discharge.**
3. **`srvCfgAddr s ↦□ cfg` is false** (the struct copy in `OpenSnapshotBackend(s.Cfg, …)` races
   with `NewWatchServer`'s write of `WatchProgressNotifyInterval`,
   `issues/etcd-cfg-watch-progress-interval-race.md`). A field-wise restatement is not sound: the
   copy reads every field. Fix the fork (`NewWatchServer` not writing the server's config), pin bump.
   **Approval: fork change.**
4. **`applyAll` needs a snapshot spec.** `applyAll.spec` takes `taSnapshotAddr ap ↦□ null`, and its
   post's `ai'`, `ciEff`, `termAfter` and `entriesStep` clauses are false after a jump. A separate
   `applyAll.specSnap` (pre: the payload's facts, `srvSnapOwn`, …; post: the apply thread at the
   snapshot's index and backend, `srvSnapOwn` at `E'`), with:
   - no entries (`rnApSnap`), so `applyEntries` returns at once;
   - `<-notifyc` the second receive of `isNotify2` (and `specSnap`'s the first, in place of
     `isUnitBag`);
   - `snapshotIfNeededAndCompactRaftLog` a no-op (disk = mem = applied index): a spec of its
     no-op case, without `ai ≤ w`, `srvSnapStor`, `epCsCfg`, `srvFrozenTerm`;
   - the merge branch (`msgSnapC`) after the jump: `rnRtOk` (kept by `rnApplyTok_recv`, which drops it
     today), `lastTermIs A' Term` (payload amendment: raft's `plogLast` fact), `srvFrozenTerms` false
     after the compaction (to restate: the frozen terms from the snapshot's index);
   - J5's `uint.Z ai ≤ w`: not in `specSnap` (the jump passes `w`); `applyRes` keeps it only for
     the entries case (J8b).
   `applyAll_model` (an exported result) changes in J8b, not here.
5. **What `srvSnapApplied` does not give back**: `x'.chain` (needed by `kvApplied_of_jump`), the
   alarm store's `Get` after `Recover` (`alarmGetIs` at the new `Tal`), `isKV` at `E'`, `srvSnapRO`
   moved along `beSucc`. Strengthen the walk (`SnapApplyWalk`, `SnapApplyPost`).
   *Done 2026-11-01* (decisions, "`srvSnapApplied`'s missing post"): `srvSnapApplied` gives the
   chain (`zal = true → x'.chain = alarmChain E.authOn false false`) and the KV at `E'`
   (`txn.isKV`); `srvSnapRO_succ` moves the bundle along `beSucc`; the alarm store's `Get` needs
   nothing (`alarmGetIs` is persistent, `Tal` given back).
6. **The stocks** (the user's decision, 2026-11-01: thread pool, `threadBound ≤ 2^28`):
   - `E.RD`: `authIs`'s mutex holds `authInfoIdle p ∗ E.RD` (`Chain.lean:1270`); only the admin
     check (`IsAdminPermitted`) uses it, before the inner call. Restate: the mutex holds
     `authInfoIdle p`; `authApplierV3.Apply.spec`/`specL` and the chain's `Apply` triple take a
     lending law of their frame `A` (`A ⊢ E.RD ∗ (E.RD -∗ A)`, `kvOwn`'s: `Chain.lean:435`).
     Then `newAuthApplierV3`, `apply.NewUberApplier`, `EtcdServer.NewUberApplier` take no `RD`;
     `NewServer`'s `HRD` and `specSnap`'s second `E.RD` go. Apply package only.
     *Done 2026-11-01* (decisions, "The auth store's reader resource borrowed per `Apply`"): and
     `srvSnapStock`'s `E.RD` copies gone, the walk's post carrying the old KV's `E.RD`.
   - `lgMu`: the transport's `R` (8 copies per `AddPeer`, `startPeer`'s `HR1`-`HR8`, of which
     `RemoveAllPeers` returns 4) becomes a pool's: `threadPool.init` on J1b's 2^28 stock
     (`threadBound ≤ 2^28`, `NewServer.spec` and the closed theorems' `n + 2 ≤ 2^28`), each of the
     peer's goroutines forked with `wp_fork_tok` and borrowing with its thread token (`borrow`,
     `giveBack` at exit). The `rafthttp` specs (`startPeer`, `AddPeer`, `RemoveAllPeers`,
     `Transport.Start`, the stream readers') change from copies of `R` to the pool.
   - also: `c.R = srvLgReader s` (no tie today), `trPeersNoRem` after the `AddPeer`s (from the
     examples' `srvTrTok`).
7. **Environment facts not threaded** into `srvSnapRO` or `applyAll`: `E.cmp = false` (`hcm`),
   `storage.snapOpensOk` (`hsop`), `E.γ.watchQ` (`hwq`), `receiptBound ≤ wbInit - 6` (`hrbw`),
   `netDirOk`/`γn.dir = dir` (`hdok`, `hdir`), the backend parameters (`P.Wf`, `limit`, `ciKeys`,
   `hooksParams`, `bridgeParams`), `lessorInv`, `isWatchableStore` in the apply thread, `authMode =
   .off` (not only `authOn = false`), `hRO`'s fields tied to the stores'. Mechanical: each into
   `srvSnapRO` from `NewServer`/`bootOk`; some are `NewServer.spec` premises today (`hsop` is L3's).
   *Done 2026-11-01* (decisions, "`specSnap`'s environment facts in `srvSnapRO`") but for
   `hdir`/`hdok` (with J8a-6); `d.P.Wf ∧ d.P.limit = openLimit cfg` added to `bootOk` (approved);
   `hoff` from `authOn = false` (`authMode_off_of`).
8. **`specSnap` restated for the payload**: `isNotify2`'s first receive (item 4), `snapDirInv` at
   `srvSnapRm γt γr` (as `srvSnapRO` has it) in place of `snapTakenLb γt`, the image facts from
   `snapRecv_image` (`hch`, `|boot| ≤ i`: lemmas).
   *Done 2026-11-01* but for the image facts: `specSnap` takes the payload's `isNotify2 γnc nc True
   True ∗ notifyRcvN γnc 0` (its first receive, `wp_notify2_receive1`; the post gives back
   `notifyRcvN γnc 1` for `applyAll`'s second) and `snapDirInv` at `srvSnapRm γt γr`
   (`Release`'s obligation is its first disjunct). The image facts are `snapRecv_image`'s
   premises about the run (the start values, `hch`, `|boot| ≤ i`): lemmas for J8a-5, where
   `run`'s snapshot case calls it, not a restatement.

## Stages

- **J8a-1** (no approval): the stocks' `E.RD` half (item 6), the environment facts (item 7), `specSnap`
  over the payload's forms (item 8), the walk's missing post (item 5). Done 2026-11-01 (but for
  `hdir`/`hdok`, with J8a-6, and item 8's image lemmas, with J8a-5).
- **J8a-2** (raft API, approved 2026-11-01): `snapLocal` through the API (item 1); done.
- **J8a-3** (fork, approval): `NewWatchServer`'s config write (item 3).
- **J8a-4**: the `isMetaBackend` restatement (item 2).
- **J8a-5**: `applyAll.specSnap` and `run`'s two `sorry`s over it (item 4).
- **J8a-6** (with the peer?): the `lgMu` pool in `rafthttp` (item 6).
