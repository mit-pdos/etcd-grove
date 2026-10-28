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
  and prove `snapshot` and `compactRaftLog` (−2 axioms). After J3, J0. *Part a done (2026-10-26): the token
  shared, `compactRaftLog` over it, `Release` over any `Rm`; `snapshot` left an axiom: J4b after
  J1a (the registry authority from `bootOk`, J1a's bundle at the apply thread), and L3 gains
  `ep.confState`'s certificate; the ceiling `γsc` is J6b's (`notes/decisions.md`, "D22 J4").*
- **J5. The applied index lags its ghost** (`InvRequest`'s `srvAppliedInv`/`srvAppliedPre`, `InvRead`,
  the read loop, `setAppliedIndex`): `applied_jump`; `appliedKeysOk` allows jumps. *Done
  (2026-10-26; `notes/decisions.md`, "D22 J5").*
- **J7. The image facts** (new `SnapRecvFacts.lean`, `InvImage`, `InvRest`): from `srvImage γ i D`,
  raft's `isCommitted l.dlv` and the workload, specSnap's pure premises (`hmeta`, `hkI`, `hRok`,
  `hpre`, `hlease`, `halarm`, `hauthb`, `hmemb`, `hA'`), `R` with `[[],[]] ++ R = kvModel γk A'`,
  `certOk`, `kvApplied_jump` (chain `alarmChain false false false`). `clusterImageOk`: +1 axiom or a
  definition proved over schema's codec. **Done (2026-10-26)**, `SnapRecvFacts.lean`:
  `snapRecv_image` (premises: `γr.raft = ⟨γ, [], 0⟩`, `γr.kv`'s start values, `uint.Z ai =
  ai0 + |A|`, `ai < i`, `|reBoot| ≤ i`, `hRO`; it gives `SnapImageFacts` at
  `memI := (restModel … (pre ++ A')).mem`, `srvRLogLb γr.raft A'`), `snapRecv_kv_jump` (needs
  `|kvModel A'| < 2^63`: `kvModel_len_of_rok` from `hRok`), `kvApplied_of_jump`, `srvRLogLb_dlv`
  (`A'` is the `Ready`'s `l.dlv`). The axiom (`Spec/.../membership/clusterImageOk_restModel.lean`)
  takes `isRaftCluster`, `clusterMem` at `L`, `srvRLogLb γ L'`: not pure, see `notes/decisions.md`,
  "D22 J7". Left for J8a (not derivable from `srvImage`): `hmeta` at the snapshot's term and
  `hRok`; both need `imageAt`/`dbImage` strengthened at the sender (and raft's `Ready` to tie the
  snapshot's term to its last entry's). **J7b done (2026-10-26)**: `imageAt` carries
  `IdxWf (kvModel γk A) []` (`soleWriter_idxWf` at the sender), `SnapImageFacts.hRok`/`hlen`;
  `hmeta` by generalizing `specSnap` to the image's stored term `tI` (no term tracking, no `Ready`
  fact needed): `notes/decisions.md`, "D22 J7b".
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

## J0 decisions (2026-10-26; decided by the orchestrator while the user was away (J0))

Read-only design pass: what each later stage implements, true of the Go code at the etcd pin
(`bc9c3868c`) and adding the least to the trust base. Each item is recorded in
`notes/decisions.md`, "D22 J0". Amendments to the stages and the order are at the end.

### 1. R-loc: a per-receiver family in `RaftNames`, carried by the `RawNode`

- **Where.** `RaftNames` (`raft/v3/Protocol/Ghost.lean`) gains
  `reSnapLoc : w64 → Option GName := fun _ => none` (pure data, as `reSnapOkRaw`: neither
  `RaftNames` nor `NodeNames` is `GF`-parametric, so no `IProp` family can live in either), and
  `def snapLocal (γ : RaftNames) (id i : w64) : IProp GF := match γ.reSnapLoc id with | none => True
  | some γd => ghostMapElem γd i DFrac.discard ()` (persistent, timeless): the body of rafthttp's
  `snapSaved γd i`, so `snapLocal γ id i = snapSaved γd i` once `γ.reSnapLoc id = some γd` (lemma
  `snapLocal_of_saved`). `none` for raft's own results, `examples/kv` (its `snapIn` is on; its fact
  is `True`), putget, putget3.
- **Why not a `NodeNames` field.** The fact must survive from `node.Step`'s `MsgSnap` to the `Ready`
  that hands the snapshot out, and in between the pending snapshot lives inside
  `ownRawNode γ.raft rn id rs`, which sees only `RaftNames` and `id`; `RawNode.Step`'s post does not
  say which snapshot is pending (`RNState.psnap` is a flag). A `NodeNames` field would force
  `ownRawNode` to take `NodeNames`, or `RNState` to expose the pending snapshot's index through
  every `RawNode` spec.
- **Carried by.** `ownRawNode` (`InvRawnode.lean`) gains the persistent clause
  `□ (∀ p, ⌜s.logst.snap = some p⌝ → snapLocal γ id p.index')` over its raft state `s`. `raft.Step`'s
  spec is unchanged: its post already says how `s'.logst.snap` moves (`NetFrame`, `LocalFrame`:
  kept; `SnapLogStep`: kept, or `some (snapId sv)` of the message; `ackSnapLog`: `logStableSnap`,
  which J2 checks only clears it). What changes:
  - `RawNode.Step`'s `"#Hsnap"` and `netP`'s `MsgSnap` clause (`InvNode.lean:472`, so `node.Step`'s
    precondition) gain `snapLocal γ id sv.Metadata'.Index'`;
  - `RawNode.Ready`/`readyWithoutAccept`/`acceptReady`: the loan's
    `snapLocal γ id l.snap.Metadata'.Index'`;
  - `readySnapData` (`InvNode.lean:632`) gains `snapLocal γ.raft γ.id l.snap.Metadata'.Index'`;
  - `NewRawNode`/`newRaft` (no pending snapshot: vacuous); `StartNode`/`RestartNode` unchanged.
- **Allocation.** The receivers' directory names must exist when `RaftNames` is fixed:
  `examples/common/Alloc*.lean` allocate one empty ghost map per member (`ghost_map_alloc_empty`,
  `K := w64`, `V := Unit`) before raft's names, set `reSnapLoc := fun id => some (γd id)` for the
  members (`none` elsewhere), and give each member's start bundle `ghostMapAuth (γd id) 1 ∅`.
  `NewServer` takes it with `⌜γ.raft.reSnapLoc id = some γd⌝` instead of calling `snapDir_alloc`,
  which is split into `snapDir_init ss γd img Rm : ghostMapAuth γd 1 ∅ ={E}=∗ inv snapDirN
  (snapDirInv ss γd img Rm)`.
- **The server.** `EtcdServer.Process`'s proof turns `netRecv`'s `snapSaved γd i` into `snapLocal`;
  J6a passes the `Ready`'s `snapLocal` to the apply job, where `snapDirInv` gives
  `fileHolds (snapDBPath ss i) D` because `Rm i` is refuted (item 3).
- No axiom; no closed statement changes (`RaftNames` gains a field with a default).

### 2. R-tok: the storage token in a server invariant; the three methods logically atomic

- **Split the token.** `memSnapTok ms γs σ = memSnapRO ms γs ∗ memSnapTokG γs σ`: `memSnapRO` its
  persistent part (`isPkgInit`, the mutex, `inv memSnapN`), `memSnapTokG γs σ := memKey γs.ak ∗
  ghostVar γs.sn memQ (snapPart σ) ∗ ghostVar γs.cb ½ σ.prev` (`InvMemstorage.lean`, lemma
  `memSnapTok_split`).
- **The three specs become atomic in the token**, in the repository's AU form (as
  `consistentIndex.SetBackend.spec`), mask `⊤ \ ↑memSnapN`; the linearization point is inside the
  storage's mutex, which each method holds throughout. Shapes (exact binders as today):
  ```
  MemoryStorage.ApplySnapshot.spec :=
    ∀ ms γs σ sp sv dq eood, σ.pend = [] → sv.Index < 2^61 → σ.fl ≤ sv.Index → sv.Index ≤ γs.cap →
    ⊢ ∀ Φ, (isPkgInit ∗ ownMemoryStorage ms γs σ ∗ memSnapRO ms γs ∗ snapArg sp dq sv ∗
            □ memStorCert γs (snapTrip sv …) ∗ □ (ErrSnapOutOfDate ↦ eood)) -∗
      (|={⊤ \ ↑memSnapN, ∅}=> ∃ σt, memSnapTokG γs σt ∗
         ((⌜σt.ss.index ≠ 0 ∧ sv.Index ≤ σt.ss.index⌝ -∗ memSnapTokG γs σt ={∅, ⊤ \ ↑memSnapN}=∗
             ownSnapM sp dq sv -∗ ownMemoryStorage ms γs σ -∗ Φ #eood) ∧
          (⌜¬ (…)⌝ -∗ memSnapTokG γs (memStorApplied sv) ={∅, ⊤ \ ↑memSnapN}=∗
             ownSnapM sp dq sv -∗ ownMemoryStorage ms γs {memStorApplied sv with fl := σ.fl} -∗
             Φ #interface.nil))) -∗
      WP ms.ApplySnapshot(sp) {{ Φ }}
  MemoryStorage.CreateSnapshot.spec :=
    ∀ ms γs x i cs dq oc data bs eood,
    ⊢ ∀ Φ, (isPkgInit ∗ memSnapRO ms γs ∗ memFloorTok ms γs x ∗ Hcs oc ∗ data ↦* bs ∗ □ eood) -∗
      (|={⊤ \ ↑memSnapN, ∅}=> ∃ σt, memSnapTokG γs σt ∗
         ⌜σt.ss.index < i → σt.prev.index ≤ i ∧ i ≤ x⌝ ∗
         □ (∀ t, memStorCert γs (snapTrip (memSnapCreated σt i t oc bs) …)) ∗
         ((⌜i ≤ σt.ss.index⌝ -∗ memSnapTokG γs σt ={∅, ⊤ \ ↑memSnapN}=∗
             Hcs oc -∗ data ↦* bs -∗ Φ (null, eood)) ∧
          (∀ t, ⌜σt.ss.index < i⌝ -∗ memSnapTokG γs {σt with ss := (t, i), scs, sal, sdat := bs}
             ={∅, ⊤ \ ↑memSnapN}=∗ ∀ snap', ownSnapM snap' 1 (memSnapCreated σt i t oc bs) -∗
             Hcs oc -∗ Φ (snap', nil)))) -∗
      WP ms.CreateSnapshot(i, cs, data) {{ Φ }}
  MemoryStorage.Compact.spec: likewise; inside the AU the premise
    ⌜σt.prev.index < ci → ci ≤ x ∧ ci ≤ σt.ss.index ∧ ci ≤ γs.cap⌝; `ErrCompacted` at
    ci ≤ σt.prev.index with the token unchanged, else the token at {σt with prev := (t, ci)}.
  ```
  These replace the current `.spec`s (the link generator takes one spec per function); the current
  triples become corollaries `MemoryStorage.<M>.spec_tok` (the AU fired at once from the token in
  hand) in a new lemma module `Proof/go_etcd_io/raft/v3/MemstorageAU.lean`, which today's callers
  (`examples/kv`'s `KV__run`, the boot) use. No axiom.
- **The invariant** (J4, `InvApplyAll.lean`; namespace `srvStorTokN`, disjoint from `memSnapN`):
  ```
  srvStorTokInv ms γs γsc γss := ∃ σt, memSnapTokG γs σt ∗
      monoNatLbOwn γsc σt.ss.index ∗ monoNatAuthOwn γss 1 σt.ss.index ∗
      ⌜σt.prev.index ≤ σt.ss.index⌝
  ```
  - `γsc`, **the storage's snapshot ceiling** (new): its authority is raft's goroutine's
    (`raftNode.start`'s loop, `InvRaftNode`), at `|d|`, the committed log handed out before the
    current `Ready`; it raises it to `|d ++ ce|` before sending an entries `toApply` (whose payload
    carries the lower bound, which bounds the apply thread's `CreateSnapshot(appliedi)`), and to `i`
    right after a snapshot's `ApplySnapshot(i)` (the `notifyc` payload carries `monoNatLbOwn γsc i`
    and `γss`'s). At `ApplySnapshot(i)` its value `|d| < i` (`readySnapData`: `d.length <
    l.dlv.length = i`) refutes the out-of-date branch. Go ignores that error (`raft.go`); raft's
    `Advance` needs the storage at the snapshot (`snapReceipt`); the invariant shows the branch dead.
  - `γss`, **the storage's snapshot index**, monotone (both writers only raise it): the apply thread
    keeps `monoNatLbOwn γss sl` (from `CreateSnapshot`'s commit, or from its out-of-date branch,
    which shows `σt.ss.index ≥ i`), so `compactRaftLog(appliedi)`'s `ci ≤ σt.ss.index` holds also
    when `snapshot` returned early on `ErrSnapOutOfDate` (Go then still compacts).
  - `prev ≤ ss`: kept by all three (`Compact` needs `ci ≤ ss`; `ApplySnapshot` sets both).
- **`srvSnapState`** (`InvApplyAll.lean:122`) loses `memSnapTok` and `σ.prev.index ≤ ai` (false in
  the window after raft's `ApplySnapshot`; `CreateSnapshot`'s `prev ≤ i` now comes from
  `prev ≤ ss < i`) and gains `memSnapRO ms γs ∗ inv srvStorTokN (srvStorTokInv …) ∗
  monoNatLbOwn γss sl ∗ (∃ c, monoNatLbOwn γsc c ∗ ⌜ai ≤ c⌝)`. `NewServer` (J1a) moves the token
  into the invariant after `InitialState`, its last non-atomic user.
- **De-risking** (risk 1): J3 starts with `CreateSnapshot`'s AU proof. A fork test delaying the
  apply job is not needed for the design (the interleaving is the AU's).

### 3. `Rm`'s final form, `storage.Release`, and `snapshot`/`compactRaftLog` translated

- **`Rm j := snapTakenLb γt j ∨ appliedAtLeast γr (j + 1)`** (supersedes S8d's `snapTakenLb γt`):
  `snapshot(toDisk)`'s `Release(snap at ai)` removes the `.snap.db` files `j < ai`, including ones
  saved but never opened (a stale `MsgSnap` raft rejected, or one a later snapshot superseded), for
  which only `appliedAtLeast γr ai` (the apply thread's lower bound) holds; `applySnapshot(i)`'s own
  `Release` (after the open, the fork fix) has `snapTakenLb γt i`. `applySnapshot(i)` refutes `Rm i`
  with the apply thread's two authorities (`γt` at `nt ≤ ai < i`, `srvAppliedOwn γr ai`'s half with
  `ai < i`), so the file `i` is in the directory.
- **`storage.storage.Release.spec`** (axiom, restated with a weaker premise): over any `Rm`, the
  removal facts below the snapshot's index given:
  `inv snapDirN (snapDirInv ss γd img Rm) ∗ □ (∀ j : w64, ⌜uint.Z j < uint.Z md.Index'⌝ -∗ Rm j)`
  in place of `inv … (snapTakenLb γt) ∗ snapTakenLb γt md.Index'`. True: `ReleaseSnapDBs` removes
  only the files below the index (`storage.go:75-82`).
- **J4 translates and proves `EtcdServer.snapshot` and `compactRaftLog`** (−2 axioms; `snapshot`'s
  axiom is false once `.snap.db` files exist: its `Release` removes files that `snapDirInv`'s frame
  holds). Go: `server.go:2101-2153` and `:2155-2181` (in-memory snapshots:
  `CreateSnapshot(ep.appliedi, ep.confState, nil)`, no data). Callees:
  - specified: `s.Logger()`, `zap.String`/`Uint64`/`Bool`, `Logger.Info`/`Debug`/`Panic` (the
    panics refuted), `s.MemberID()`, `types.ID.String`, `s.KV()` and the store's `Commit`
    (`mvcc.store.Commit`, proved), `errors.Is`, `s.consistIndex.ConsistentIndex()` (`ci_get_au`),
    `raftpb`'s getters, `s.inflightSnapshots.Load()` (`srvInflight`), `storage.Release` (restated
    above), `MemoryStorage.CreateSnapshot`/`Compact` (J3's AU);
  - to translate: `verifyConsistentIndexIsLatest` (`server.go:1193`, over `verify.Verify`, which
    has a spec);
  - to state: `s.r.storage.SaveSnap(snap)`, a clause of `bootOk`'s storage contract (the WAL's
    `SaveSnapshot`, names-only; the plan's "`NewStorage` contract gains `SaveSnap`/`Sync`", J1a);
    J1a checks where `bootOk`'s storage comes from: restated there if that is an axiom, nothing new
    if it is a premise of the boot;
  - `KV().Commit()` spends one write-back token of the current backend per disk snapshot: J4 takes
    it from the write pool, counted by J5's write counter (item 4).

### 4. The applied index lag: a real Go issue; the invariant becomes `≤`

- **Filed:** `issues/etcd-applied-index-stale-after-snapshot.md` (reproduced by an integration test
  at the pin; a one-line fix passes it). `applySnapshot` never calls `setAppliedIndex` (nor
  `setTerm`); the request limit of `processInternalRaftRequestOnce` (`committed > applied + 5000`,
  `v3_server.go:1059-1064`) then refuses every proposal through that member with
  `ErrTooManyRequests` until another member's write commits (with the default
  `SnapshotCatchUpEntries`, 5000, the gap exceeds 5000 after every install). Not affected:
  `waitAppliedIndex` (it waits on `applyWait`, which `applyAll` triggers at `ep.appliedi`) and the
  linearizable read loop (an extra `ApplyWait` that returns at once). Stale: `Status`'s
  `RaftAppliedIndex` and `RaftTerm`. Upstream `main` has the same code.
- **The verified code stays as Go has it** (no fork fix: the proof tolerates the lag; the issue is
  one of liveness, outside the safety results). J5: `srvAppliedInv` (`InvRequest.lean:1955`)
  becomes `∃ v a, ownUint64 (srvAppliedIndexAddr s) v ∗ monoNatAuthOwn γr.applied ½ a ∗
  ⌜uint.nat v ≤ a⌝ ∗ …` with the logs map, `appliedKeysOk` and `appliedLogAt` keyed by the ghost
  `a`; a reader of the atomic gets `appliedAtLeast γr v` (still a lower bound); `setAppliedIndex(v')`
  sets both (`v' > a`); new `applied_jump` (the apply thread, with its half, raises `a` to `i` and
  publishes `appliedLogAt γr i L`, the atomic untouched); `appliedKeysOk` allows jumps.
- **J5 also decouples the write counter from the applied index** (found here): `srvWTAt γp ai` (one
  write token and one time receipt per entry: `srvWTPool`'s `⧗ a`, `receiptBound ≤ a + n + 1`)
  cannot follow a jump (raising `a` by `i - ai` needs receipts a snapshot does not bring). The
  counter becomes the tokens taken, `w`: `apply.spec`, `applyEntries.spec`, `applyAll.spec` and
  `snapshotIfNeededAndCompactRaftLog.spec` take `srvWTAt γp w` and return `srvWTAt γp (w + k)` (`k`
  the tokens they took; `snapshot`'s `Commit` one more), and `applyRes` keeps
  `∃ w, srvWTAt C.wt w ∗ ⌜γ.reNoSnap = true → w = ai⌝` (the only reader of `w = ai` is the
  no-snapshot mode's compaction argument, D21 M3, which L3 drops). The new backend's stock refills
  the pool at the swap (`srv_be_swap`), so the pool's bound holds after it.

### 5. The second-snapshot loop: what `srvSnapApplied` must give back

For each exclusive resource of `specSnap`'s precondition (the persistent ones are J1a's `srvSnapRO`):

| resource | after S8d | decision |
|---|---|---|
| `isServer`, `applyThread`, `applyBackend`, `srvApplyKV`, `srvRest`, `srvKVCloser`, `ep`'s fields, `epConfState`, `srvLgReader`, `srvBemuReaderAt`, `Tal` | given back at the new names | ✓ |
| `isStopChans d ∗ bOpen d ½` (W7) | given back at `d'` | ✓ |
| `monoNatAuthOwn γt 1 nt` | given back at `i` | ✓ |
| `fileHolds (snapDBPath ss i) D` | one per snapshot | from `snapDirInv` with R-loc (items 1, 3) |
| `certOk E.γ ([[], []] ++ R)` and the image's pure facts | one per snapshot | J7 |
| `pathOwn (backendPathOf cfg.DataDir')` | given back as `pathOwn (snapDBPath ss i)` | **`os.Rename.spec` restated** (axiom, J8a): success gives `fileHolds dst D ∗ pathOwn dst`, not `pathOwn src` (true: the program keeps its right to `dst`; `pathOwn src` was dubious, since the transport may create a file at the same index again); `OpenSnapshotBackend.spec` and `srvSnapApplied` follow |
| `trLive γn t c rs` and the coverage | given back as `trLive (rs.1, L)` | J-T's state (item 7) |
| `8·|ps|` of `lgMu`'s slots (`c.R`) | consumed by the `AddPeer`s | `RemoveAllPeers` returns 4 per peer (6 once `streamWriter.stop`'s spec says it waits on `cw.done`): 2 per peer leak per snapshot (`peer.stop` does not join the `Process` goroutines). See below |
| a second `E.RD` | consumed by `NewUberApplier` | from a stock threaded from `NewServer` (J1b keeps the `actualMaxReaders - 66` slots it drops today); one per snapshot. See below |
| `srvWTPool`, the stores' contracts, `srvAuthRecoverOk`, `srvMembersDir`, `alarmGetIs`, `lessorInv`, `isWatchableStore`, the `□ isMetaBackend` premise | persistent | J1a's `srvSnapRO`; the `isMetaBackend` premise stated for every `π`, `i`, `t` (`□ ∀ π b i t, π.m0 = (i, t) → …`), from `bootOk`'s `Hmeta` generalized (J1a: the same argument, any backend's `ReadTx` of its meta bucket) |
| the storage token | `srvSnapState` | the shared invariant (item 2) |

**The slots are a limit of the model, not of Go** (Go counts only the readers inside
`RLock`..`RUnlock`): any finite stock runs out after enough snapshots. Decided: the general fix is a
Perennial change (`notes/perennial-changes.md`, "An `RWMutex`'s reader slots are leaked by readers
that hold them for life": `RLock` paid by a thread token), proposed on its own; it gates J8b's loop
and L3, not J8a. J8a states `srvSnapApplied` with the stocks counted (the slots it gives back, what
remains), so it does not wait. If the change has not landed by J8b, the fallback is a named premise
bounding the snapshots a member applies in a run by the stocks (about `2^30 / (2·|ps|)`), an
environment premise for the user to approve. For `E.RD` alone, an alternative to try first in J8a:
the auth applier borrows the apply thread's `E.RD` (`kvOwn`'s) per call instead of holding one, so
`NewUberApplier` takes none.

### 6. `applyRes`'s restatement (J8b)

- `entriesStep C.c₀ A C.x₀ x` → `kvReach C.c₀ A C.x₀ x`, new in `InvRun`:
  `kvReach c₀ A x₀ x := entriesStep c₀ A x₀ x ∨ ∃ A₁ A₂ x₁, A = A₁ ++ A₂ ∧ A₁ ≠ [] ∧
  (∃ R, x₁.log = [[], []] ++ R) ∧ entriesStep c₀ A₂ x₁ x` (the KV at the last snapshot's image, then
  entries), with `kvReach_append` (a batch) and `kvReach_snap` (a jump). Nothing consumes the
  conjunct but `run`'s loop; the link of `x.log` to `A` stays `kvRun`'s `kvApplied`, whose chain fact
  `x.chain = γk.ch0` J7 gives after a jump (`ch0 = alarmChain false false false`, from `zal`).
- `uint.Z ai = uint.Z C.ai₀ + A.length` kept: `A` is the committed log through `ai` (after a jump,
  the image's entries `A'`, `|A'| = i - ai₀`).
- `srvWTAt C.wt ai` → `∃ w, srvWTAt C.wt w ∗ …` (item 4).
- `srvSnapState … ai (W64 0)` at item 2's body; `srvAppliedOwn`/`appliedLogAt` at the ghost index
  (item 4); `srvRest B.E C.γr A` unchanged (`hA'`).
- `applyAll.spec`'s post gains the snapshot case (the KV at the image, `kvReach_snap`): a change to
  the statement of the closed result `applyAll_model`, beside J8b's approved instances, stated so
  that its no-snapshot case reads as today.

### 7. The transport: J-T, W8, `CutPeer`

- **The carve-out: split the transport's records** (rather than restating every `trFrozen` user
  over one record): `γr` keeps the peers' ids and the stopped flag (half in the lock, half in
  `trLive`, which the apply thread holds; `AddPeer`, `RemoveAllPeers`, `RemovePeer`, `Stop_live`
  update it); the remotes' ids leave `γr` and are owned by the lock (`trLockP`), each remote with its
  persistent facts, so a handler adds a remote under the write lock without `trLive`, as Go does; a
  per-member remote budget in the lock (4 `R` for each other member not yet a remote: `AddRemote`
  returns at once for an existing remote, so at most one per member for the transport's life); a
  no-remote token `trNoRem γ f` per member (lock: `f ∈ dom RM →` the token consumed; `f ∉ dom RM →
  4R ∗ (token ∨ f ∈ dom PM)`). `NewServer` no longer freezes (`trLive_freeze` stays a lemma).
- **Files** (the review's list): `rafthttp/{TransportState, TransportInv, TransportAdd,
  TransportHandler, TransportCut, TransportStop, TransportFull, TransportSpecs}.lean`,
  `Transport__SendSnapshot` (trivial), the Spec files of `CutPeer`, `MendPeer`, `Handler`, `Start`,
  `SendSnapshot` and `ActiveSince` (an axiom: restated over `trState`, `--check --update`),
  `etcdserver/{InvRaftHandler (srvNetMember), NewServer, InvBoot (a comment)}`; `Net.lean`'s
  `netTransport` Stop clause and `InvRaftNode.lean`'s `isRNTransport` (`Stop` takes the live right:
  a `Stop` concurrent with the apply thread's `AddPeer` panics, `transport.go:300-301`; it reaches
  `raftNode.onStop` through the `stopped` channel's payload), `raftNode__start`/`onStop`,
  `EtcdServer__{CutPeer,MendPeer}`.
- **W8 is real.** In the window between `RemoveAllPeers` and the `AddPeer` loop
  (`server.go:1150-1160`) a peer whose stream our `writer.stop` closed redials, `Get(from)` is `nil`
  (`http.go:415-423`), and `AddRemote` adds a permanent remote (only `Stop` removes one; Go's
  `AddPeer` does not look at `t.remotes`). The fix is the plan's: the raft protocol states that
  `X-PeerURLs` is the sender's directory URLs (non-empty, plain peer URLs, each host the sender's,
  no commas), so the handler meets `AddRemote_core`'s premises (`TransportAdd.lean:217-220`) with
  the budget's 4 `R`. Untrusted definitions only (`fromOkAt`/`pipeReq` in `Pipe.lean`, `streamReq`
  and `snapReq` in `Stream.lean`); no D38c boundary axiom changes (they are generic over the
  registered protocol); on the sender's side, `setPeerURLsHeader.spec` states the header's value,
  `createPostRequest` and `streamReader.dial` pass it on, `trFixed`/`Start` tie `tr.URLs` to
  `γn.dir lid` (perhaps with `url.URL.String` facts). Rejected as false of Go: "no request in the
  window", "`AddPeer` stops the window's remote", "a non-peer's requests are rejected".
- **`CutPeer`: `linkv3p_safe`'s statement survives.** Its premise is internal and proved
  (`id ∉ rs.1`, from `srvNetMember`'s `rs.1 = []`); `CutPeer`/`MendPeer` take `trNoRem` for the id
  instead, which `NewServer` lends linkv3p's partitioner (`PeerPausable`), and `applySnapshot`'s
  `RemoveAllPeers` needs back: fine in the examples' mode, where the snapshot branch is dead. A
  future example with both snapshots and partitions cannot keep `PeerPausable` without a fork fix
  (an idempotent `remote.Pause`): a window remote cut twice panics (`remote.go:89-91`,
  `pipeline.go:81-82`). `issues/nonissues/etcd-rafthttp-cutpeer-twice-remote-panic.md` corrected.
- **What J-T takes from M5**: the state split, `trLive` to the apply thread, `RemoveAllPeers` proved
  (its `sorry` gone; the slots it really gives back), `Stop_live` with the Stop clause and the
  `stopped` payload, the readers restated, W8. M5 keeps `RemovePeer`, `applyConfChange` and the
  removed sender's `403`. Note in `notes/membership-plan.md`, M5.
- D40's note ("the window's remotes stopped by the re-add") is false of Go: corrected in
  `notes/decisions.md`, "D22 J0".

### 8. `srvAuthRecoverOk`: from `NewAuthStore`'s axiom, restated

The auth track's E stage (the authority at the server) is not close (left after E2a: S4's `Lock`
contract in mode `on`, D22's boundary, then the server). Decided: **`auth.NewAuthStore.spec` (an
axiom) is restated, its post gaining `authRecoverOk stl`**: the body of today's `srvAuthRecoverOk`
(`SnapApplyDefs.lean:80`), moved to the auth package's contracts beside `authApplyOk` (persistent:
for every later backend `dn` with its contract, an open share, a reader token and its tracked
buckets with the auth buckets at `authBoot`/empty, `Recover(ab)` moves `authBeOn stl oldbe` to
`authBeOn stl dn.be`, all else given back). True of the Go code in the mode the axiom is in (auth off
for the store's life; `Recover`, `auth/store.go:399-418`: `beMu`'s write lock to swap `as.be`, a
read transaction of the new backend reading `authEnabled` (absent: false) and the revision,
`refreshRangePermCache` over no users, `enabledMu`'s write lock to set `enabled = false`): S8c's
argument, which the docstring takes over. `srvAuthRecoverOk` becomes `authRecoverOk`; `specSnap`'s
premise is discharged at `NewServer` (J1a, into `srvSnapRO`). No axiom added; the named premise
goes. The auth E stage later proves the clause with the server's constructor (from the proved
`auth.authStore.Recover.spec`). Dated note in `notes/auth-plan.md`.

### 9. `clusterImageOk`: an axiom over the rest model

A definition over schema's codec would unseal `memberKey`/`memberEnc` (opaque,
`apply/RestModel.lean`) and model JSON decoding: far more than the fact is worth. Decided:
`membership.memBucketsOk` stays opaque and J7 adds **one pure trust-boundary axiom**,
`membership.clusterImageOk_restModel`, in
`Proof/go_etcd_io/etcd/server/v3/etcdserver/api/membership/RaftCluster__Recover.lean` (beside the
axiom it feeds): for the server's cluster `c` (its boot members, the local member among them) and
any log `L` the apply thread's rest model reaches under the server's conf-change policy
(`ccApplyOk`: no removal), `clusterImageOk c (restModel c0 boot L).bk (restModel c0 boot L).mem`.
Why true: the buckets hold exactly what the writers put (`memberEnc` of the members, the JSON
`MustSaveMemberToBackend` writes, which `MustReadMembersFromBackend` decodes back), the local member
is a boot member, nothing is removed, and the cluster version is the one binary's (every member runs
the same version, so `MustDetectDowngrade` accepts it). +1 axiom; J7 gets `himg` from `hA'` and it.

### 10. The collection

`etc/tcb-collections/snapshot.txt` exists (the snapshot path's linked roots). `specSnap`'s proof
(`EtcdServer.applySnapshot.wp_proof_snap`) is not a root (unlinked; roots are linked results), so no
pattern selects it until J8b links it; no root added. Its baseline was not refreshed in J0: no
stable build could be seeded (`s8d-int`'s `.lake/build` was being rebuilt by another session
during the copy) and a full build was too costly on the shared machine; J0 changed no Lean file,
so the baseline is S8d's. The first Lean stage to merge runs `--check --update` on it.

### Amendments to the stages and the order

- **J1a** also: `NewAuthStore.spec` restated (item 8); `srvSnapRO` with `authRecoverOk` and the
  `isMetaBackend` family; `bootOk`'s `SaveSnap` clause; the storage token into item 2's invariant at
  the end of `NewServer`; the stocks of `E.RD` and `lgMu` slots kept (not dropped) for J1b.
- **J2** also: `examples/common/Alloc*` allocate the receivers' directory maps; `NewServer`'s
  `snapDir_alloc` → `snapDir_init` (one binder: merge J2's `NewServer` edit before J1a's, or J1a
  rebases on it).
- **J3**: the specs become the AU forms (item 2), the old triples corollaries. *Done 2026-10-26,
  with one change to item 2: `memSnapTokG` holds no `memKey γs.ak` (`CreateSnapshot` needs the key
  for its whole critical section; its caller, the apply job, keeps it), so J4's `srvSnapState`
  keeps `memKey γs.ak` beside `memSnapRO`; `ApplySnapshot` takes no `memSnapRO`. `notes/decisions.md`,
  "D22 J3".*
- **J4** after J3 and **J5** (J5's write counter, which `snapshot`'s `Commit` advances); also
  `Release` restated and the new `Rm` in `snapDirInv`'s users (`NewServer`, `specSnap`,
  `SnapApplyWalk`).
- **J5** also decouples the write counter (item 4): the specs of `apply`, `applyEntries`,
  `applyAll`, `snapshotIfNeededAndCompactRaftLog`.
- **J7**: +1 axiom (item 9).
- **J8a**: `os.Rename` restated (item 5); `srvSnapApplied` with the counted stocks.
- **J8b and L3 are gated on the Perennial reader-slot change** (item 5) or the fallback premise.
- New issue: `issues/etcd-applied-index-stale-after-snapshot.md`.
- Axioms, revised: −2 (`snapshot`, `compactRaftLog`), +1 (`clusterImageOk_restModel`); restated:
  `os.Rename`, `storage.Release`, `NewAuthStore`, `Transport.ActiveSince`, and `bootOk`'s storage
  source if it is an axiom; `sorry`s: −1 (`RemoveAllPeers`). Net −1 axiom, −1 `sorry`.
- Order: wave 1 J2, J3, J7, J1a, J5; wave 2 J-T (after J1a), J4 (after J3 and J5), J6a (after J2);
  the rest unchanged; the Perennial change proposed in parallel from now.
- Not done in J0: the plan's Go `-race` run with snapshot-heavy settings (left for J3's
  de-risking, risk 1).

## Where J-T stopped (2026-10-27, branch `snapshot-jt`; paused by the user)

**Landed on `lean` (2026-10-27)**: finished on lean's head (with J4b): the full build, the
examples, `etc/gen-link.py` (only `--server` changed) and the trust base checked; the three
fixes are in `notes/STATUS.md`'s Snapshots item. What follows is the state at the pause.

Base: `origin/lean` at `ed462bf259` (M5's proved transport, the Perennial bump); the four J-T
commits rebased onto it cleanly (they were first written on `f6e5c001d6`, also M5-based, pushed as
`snapshot-jt-m5wip`; `snapshot-jt-old` is the abandoned J6a-based first attempt). Design and
statement changes: `notes/decisions.md`, "D22 J-T".

- **Done**: the stop invariant's no-remote tokens and opening flag (`TransportInv`,
  `TransportState`: `trNoRem`, `trUnopened`/`trOpened`, `trNoRemAcc`, `trPeersNoRem`);
  `AddPeer` gives the token out before opening; `AddRemote` needs `trOpened`; `CutPeer`/`MendPeer`
  over `trNoRemOr`; `RemovePeer`/`RemoveAllPeers` take the tokens back, `RemoveAllPeers` returns
  four `R`s per peer; `Handler` over the live transport; W8 (`peerURLsHdrOk` in `fromOkAt` and
  `streamReq`, `trURLsOk` in the transport's views, `setPeerURLsHeader`/`createPostRequest` state
  the header, `URLStringAny_ok` restated); `NewServer` unfrozen (pool of every other member,
  tokens in `srvTrTok`, live right in `srvApRes`, new premise `peerURLsDir`); `applyConfChange`'s
  static branch on `trLive`; `applySnapshot`'s walk takes `trPeersNoRem`; examples' `newServer`/
  `StartServer` premise `"http://" ++ peerAddr ∈ dir id`, the five `Main`s discharging it.
- **Builds**: on `f6e5c001d6` the rafthttp package, `Proof.go_etcd_io.etcd.server.v3.etcdserver.Link`
  (but `SnapApplyWalk`, fixed after, unchecked) and `NewServer` (lean-check, 0 errors) built. Not yet
  checked: `SnapApplyWalk` after its fix, the examples (common, linkv3p, putget3, the five Mains),
  the full `lake build` and `etc/tcb-report.py --check` on the rebased base (a full build was in
  progress, no error up to module 7398/9399 when paused).
- **Next step**: finish the full `lake build` on this branch, fix the examples' errors (expected:
  the `NewServer` call sites' new premise, `srvTrTok`'s new shape where examples unfold it,
  `EtcdServer.CutPeer`'s callers unchanged), run `etc/gen-link.py` for any mode whose callee lists
  changed (`--server` done), `etc/tcb-report.py --check` (expect no change but the restated
  `URLStringAny_ok`), then push and hand over to J1b/J8a ("D22 J-T", "For J1b/J8a").
