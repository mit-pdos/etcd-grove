# Plan: the rest of D22 after S8d — S-j1, S-k, S-l (2026-10-26)

Drafted by a read-only planning agent for the orchestrator (the user away, decisions delegated:
`notes/decisions.md` entries marked "decided by the orchestrator while the user was away"). Goal:
the etcd KV adequacy examples (`putget_safe`, `putget3_safe`, `linkvtxn_safe`, `linkv3p_safe`,
`linkv3p_watch_safe`, `watch_safe`, `cache_safe`; `k8setcd3_safe` follows through
`examples/common`) proved with snapshots on at etcd's defaults. (`linkv`, `linkv3` were retired by
D34 for `linkvtxn`, `linkv3p`.)

## Seven gaps the notes did not record

1. **R-loc: the snapshot file's "saved" fact never reaches the `Ready`.** `applySnapshot` needs
   `fileHolds (snapDBPath ss i) D`, which comes out of `snapDirInv` only with `snapSaved γd i`; that
   fact reaches `Process` (`netSnapRecv`), but raft's `node.Step` precondition (`netP`,
   `raft/v3/InvNode.lean:472`) and `readySnapData` (`:632`) carry only cluster-level certificates
   (`isMessageC`, `snapDataOk`), nothing receiver-local.
2. **R-tok: the storage token is wanted by two goroutines.** `MemoryStorage.ApplySnapshot` takes
   `memSnapTok` (raft goroutine); the apply thread holds it in `srvSnapState` (`InvApplyAll.lean:122`)
   for `CreateSnapshot`/`Compact`. In Go they do overlap (the FIFO scheduler does not wait); Go
   tolerates it (`ErrSnapOutOfDate`, `ErrCompacted` handled). The proof needs the token shared.
3. **`EtcdServer.snapshot`'s axiom is silent about removals.** With `toDisk` it calls
   `s.r.storage.Release(snap)`, which deletes every `.snap.db` below `ep.appliedi`; the axiom
   mentions neither `snapDirInv` nor removals: false for frames that hold such a file (harmless only
   while no `MsgSnap` exists). `Rm := snapTakenLb γt` cannot justify these removals (a stale file
   below `appliedi` may never have been opened). Covering both callers: `Rm j := snapTakenLb γt j ∨
   appliedAtLeast γr (j+1)`; `applySnapshot(i)` still refutes `Rm i`.
4. **`applySnapshot` never updates `s.appliedIndex`** (only `applyEntries` calls `setAppliedIndex`;
   `applyAll` still triggers `applyWait` at `ep.appliedi`). `srvAppliedInv` (`InvRequest.lean:1955`)
   ties the atomic to `γr.applied`, so `applyAll`'s post and `applyRes`'s `srvAppliedOwn` cannot hold
   after a jump. Fix: atomic ≤ ghost. Possibly a small Go liveness issue (`waitAppliedIndex`, status
   calls see a stale index): check before filing.
5. **Repeated snapshots run out of resources.** `srvSnapApplied` does not give back what the next
   `specSnap` needs: `pathOwn (backendPathOf …)` (`os.Rename`'s axiom consumes `pathOwn dst`, returns
   `pathOwn src`), the second `E.RD` (a finite `replicate` in `NewServer.lean:605-621`), the
   `8·|ps|` reader slots of `lgMu` (`RemoveAllPeers.spec` returns none), the per-snapshot
   `□ isMetaBackend … m0 = (i,t)` and `certOk E.γ (…R)`.
6. **`applyRes` (`InvRun.lean:253`) excludes snapshots.** It requires `entriesStep C.c₀ A C.x₀ x` and
   `srvWTAt C.wt ai`; `rnApP` (`InvRaftNode.lean:837`) and `rnApplyTok_recv` fix `ap.snapshot' = null`
   and `cum[i+1] = F ++ ce`.
7. **NewServer still freezes the transport** (`trLive_freeze`, `NewServer.lean:940`; 17 files use
   `trFrozen`), while `specSnap` takes `trLive`. W8 and the hand-over are one job (T-M M5's rafthttp
   part). The proved `RemoveAllPeers` must also return the slots (gap 5). linkv3p's `CutPeer` premise
   ("no remote for the id") is at risk from window remotes.

## Sub-stages

Every Lean stage keeps the examples in the no-snapshot mode until L3, proving the snapshot code
parametric in `reNoSnap` (as M3 did for raft's mode), so each commit builds and keeps every closed
theorem.

- **J0. Design pass** (read-only; parallel with S8d): decide gaps 1-7. R-loc: a per-node family in
  `RaftNames` (`reSnapLoc : w64 → w64 → IProp`, keyed by receiver, `fun _ _ => True` for kv) or a
  `NodeNames` field set by `StartNode`. R-tok: logically atomic `ApplySnapshot`/`CreateSnapshot`/
  `Compact` over a server-held invariant (with `σ.ss` ≤ the delivered log's length, against
  `ApplySnapshot`'s out-of-date branch). Release: `Rm` as in gap 3, `storage.Release.spec` over any
  downward-closed `Rm`. Rename: keep `pathOwn dst`, drop `pathOwn src`. Audit `applyRes ⊢ specSnap
  pre` and `srvSnapApplied ⊢ applyRes` for a second snapshot. The auth premise's source
  (`srvAuthRecoverOk`: the auth E stage, or interim `NewAuthStore` off-mode restated with the Recover
  triple). A Go `-race` run with snapshot-heavy settings. Collection `etc/tcb-collections/snapshot.txt`.
- **J1a. Persistent threading and the bootstrap contract** (`InvBoot`, `NewServer`, `InvStart`,
  `InvRun`'s `isServerRun`, `InvNodeStart`, `NodeStart`, `InvRaftNode`'s `isRNWal`, the
  `start`/`run`/`Start` specs, `examples/common/{newServer,StartServer}`): a persistent bundle
  `srvSnapRO` (snapshotter, hooks, config, feature gate, `storageSnap`, `inv snapDirInv` with the new
  `Rm` and `γt`, the store contracts, `srvMembersDir` from `Hmembers`, `keySized`). `bootOk`'s
  `NewStorage` contract gains `SaveSnap`/`Sync` (contract clauses at the names-only WAL boundary).
- **J-T. The transport unfrozen, with W8** (T-M M5's rafthttp part; tell the membership owner):
  `trLive_freeze` removed, `trLive` to the apply thread; readers restated over `trState` + a reader
  token; `Stop_live`; `RemoveAllPeers.spec` returning the removed peers' slots (true if `peer.stop`
  joins its goroutines); W8: the HTTP protocol carries the sender's peer URLs as the directory's, the
  coverage invariant "every remote's URLs are the directory's". Risk: linkv3p's `CutPeer` premise.
- **J1b. Spatial threading into the apply thread** (`InvRun`'s `applyStart`/`applyRes`, `NewServer`,
  `run`/`applyAll`): `srvSnapOwn` = W7's `isStopChans d ∗ bOpen d ½`, `pathOwn`, `srvKVCloser`,
  `monoNatAuthOwn γt 1 0`, the second `E.RD`, the slots, `trLive`, `alarmGetIs`/`Tal`. After J1a, J-T.
- **J2. Raft: R-loc** (`raft/v3/Protocol/Ghost`, `Model`, `InvRawnode`, `InvNode`, `InvNodeRun`,
  `raft__Step`, the restore chain, the `Step` specs, `examples/kv` and `examples/common/Alloc*`,
  `EtcdServer__Process` passes `snapSaved`). No axioms.
- **J3. Raft: R-tok** (`raft/v3/InvMemstorage`, `MemoryStorage__{ApplySnapshot,CreateSnapshot,
  Compact}`): atomic variants, the existing specs kept as corollaries.
- **J4. The server's snapshot state shared** (`InvApplyAll`'s `srvSnapState` body, `EtcdServer.snapshot`,
  `compactRaftLog`, `snapshotIfNeededAndCompactRaftLog`, `storage.Release`): recommended to translate
  and prove `snapshot` and `compactRaftLog` (−2 axioms). After J3, J0.
- **J5. The applied index lags its ghost** (`InvRequest`'s `srvAppliedInv`/`srvAppliedPre`, `InvRead`,
  the read loop, `setAppliedIndex`): `applied_jump`; `appliedKeysOk` allows jumps.
- **J7. The image facts** (new `SnapRecvFacts.lean`, `InvImage`, `InvRest`): from `srvImage γ i D`,
  raft's `isCommitted l.dlv` and the workload, specSnap's pure premises (`hmeta`, `hkI`, `hRok`,
  `hpre`, `hlease`, `halarm`, `hauthb`, `hmemb`, `hA'`), `R` with `[[],[]] ++ R = kvModel γk A'`,
  `certOk`, `kvApplied_jump` (chain `alarmChain false false false`). `clusterImageOk`: +1 axiom or a
  definition proved over schema's codec.
- **J6a. The raft node's payload with a snapshot** (`InvRaftNode`'s `rnReadyData`/`rnApP`,
  `InvRaftLoop`'s `rnApplyTok_recv`, `updateCommittedIndex`, `newRaftNode`, `InvRun`). After J2.
- **J6b. `raftNode.start`'s snapshot branch** (its own module): `SaveSnap`, `Save`, `Sync`, the first
  `notifyc`, `ApplySnapshot` (J3/J4), `Append`, the second `notifyc`, `Advance`. After J1a, J3, J4, J6a.
- **J8a. `applyAll` with a snapshot**: one `applySnapshot` spec for both cases, `applyAll`'s post's
  snapshot case, `srvSnapApplied` giving back gap 5's resources. After J1b, J5, J6a, J7.
- **J8b. The loop and the link**: `applyRes` restated, `run`, `link-lean-first-server.txt`, `Link.lean`,
  `Results.lean`; `applyAll_model`, `server_run`, `server_start`, `server_Start` gain
  `[cache.v3.Assumptions] [ErrorStringLeaf]` (user-approved).
- **L1 (S-k). The quota after the swap** (`v3rpc/InvQuota`, `storage/NewBackendQuota`): any epoch's
  `isBackend`, `Size()` without a `bOpen` share. Any time after S8d.
- **L3 (S-l). Flip the mode**: `bootOk`'s `"%Hnosnap"` → `γ.reNoSnap = false ∧ 2^61 ≤ γs.cap`;
  `NewServer.spec` without `receiptBound ≤ SnapshotCatchUpEntries + 1`, `isServerApplyAll` without
  `scu`; `srvMsgSnapC_false`, `rnSnapMsg_false`, `certLink_noSnap` gone; the `msgSnapC` branch wired;
  `"%Hsop" ∷ ⌜storage.snapOpensOk⌝` in `NewServer.spec`.
- **L4a.** `examples/common/common.go` drops `SnapshotCatchUpEntries: 1 << 48`; re-translate; common,
  putget, putget3; closed theorems gain `(Hsop : storage.snapOpensOk)`.
- **L4b/L4c** (parallel after L4a): linkvtxn, linkv3p; watchkv, cachekv, k8setcd3.

Axioms, estimated net −2 to +1.

## Order

| Wave | Stages |
|---|---|
| 0 | S8d, J0, L1 |
| 1 | J2, J3, J7, J1a, J5 |
| 2 | J-T (after J1a), J4 (after J3), J6a (after J2) |
| 3 | J1b (after J-T), J6b (after J1a, J4, J6a) |
| 4 | J8a, then J8b |
| 5 | L3, then L4a, then L4b and L4c |

## Risks, and how to de-risk them

1. R-tok: a fork test delaying the apply job (as `TestSnapshotDBKeptUntilOpened`); a day on
   `CreateSnapshot`'s atomic form first.
2. R-loc: spike the field through `raft.Step`'s `MsgSnap` and `restore` only.
3. Gap 5: J0 writes the second-snapshot loop out; each missing item a named amendment before J8a.
4. Gap 3: a false trusted statement once files exist; translate `snapshot` (J4) or restate it.
5. J-T and W8: depend on M5 and 17 `trFrozen` files, may touch linkv3p's statement; check `CutPeer`
   first.
6. `srvAuthRecoverOk`'s source: decide early, else L3 is blocked.
7. `clusterImageOk`: axiom vs definition, early in J7.
8. Build cost: `raftNode__start.lean` runs at `maxHeartbeats 0`; the branch in separate lemma modules.
