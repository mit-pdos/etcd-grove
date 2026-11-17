# WAL link: handoff

## START HERE (2026-11-17, L2: T1 and the ReleaseSnapDBs axiom done)

- **Branch** `wal-link` in `/shared/etcd-grove-wallink`; `.lake/package-overrides.json` = `/shared/tmp/manifest-c6b.json`.
  Coordinator: etcd-grove-03. Scope §7-§8, `questions.md` for the decisions. L1 (L1a, L1b) accepted by etcd-grove-03.
- **ReleaseSnapDBs:** round 1 REFUTED, round 2 SURVIVES (`notes/axiom-review/releasesnapdbs.md`; Go tests
  `examples/axiomcx/releasesnapdbs/`). **T1 done** (decided by etcd-grove-03): `storage/SnapHeld.lean` (`snapHeld`,
  sealed, gated in `etc/import-all.txt`), `snapDirInv` sealed with `snapDir_take` (generic, sealed token) and
  `snapDirInv_ss_congr` in `rafthttp/Net.lean`, `SnapRO.snapRmM_take`, `OpenSnapshotBackend.spec` over `snapHeld … R'`,
  `applySnapshot` takes `snapHeld … (monoNatAuthOwn γt 1 nt)`, `ApplyAllSnap`'s two takes. The axiom file
  `api/snap/Snapshotter__ReleaseSnapDBs.lean` added (no client until `storage.Release`'s proof).
- **Next, in order:** L2 proper: `storage.toml` (Scope §2), specs/proofs of `NewStorage`/`Save`/`SaveSnap`/`Sync`/
  `Close`/`Release` (Release from `ReleaseLockTo` + `ReleaseSnapDBs`; then `storage.storage.Release.wp_proof` axiom
  gone), `purgeFile` under `MaxWALFiles = 0`. Then L3 (with L4). `etc/tcb-report.py --check --update` once the new
  axiom is reached and the old one gone (hard stop: trust-base delta).
- **L3 obligations from L1b:** the server's `hardStateAt` becomes `hsOptC` (the Save law's premise; decided at the
  L3 statement stop); `walEntInW` needs `ufWire` and `0 < entrySize c`; `metaEnc` of `etcdserverpb.Metadata` in L3.
- **Pitfalls:** gen-link/gen-init compare only with Perennial linked at `.lake/packages/perennial` (gates.sh does it:
  `ln -s /shared/perennial-c6b39d4f8`, then remove). Lock + later credit and SaveSnapshot pitfalls: History.
- **Check:** `TMPDIR=/shared/tmp LAKE_OPTS=--packages=/shared/tmp/manifest-c6b.json etc/lean-check.py --max-open 2 FILE`.
  **Build:** `/shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-c6b.json build TARGET`.
  **Go:** `cd examples && GOWORK=off TMPDIR=/shared/tmp go test -count=1 -v ./axiomcx/releasesnapdbs/`.

## History

### START HERE (2026-11-17, after L1b)

- **Branch** `wal-link` in `/shared/etcd-grove-wallink`, lean `3cd4b72599` merged (5ab12b6538); `.lake/package-overrides.json`
  = `/shared/tmp/manifest-c6b.json`. Coordinator: etcd-grove-03. Scope §7-§8, `questions.md` for the decisions.
- **Done:** Scope (72997e9e36); L0 `St/WalLinkPure.lean`; L1a (shared handle, the five collapses; see History);
  **L1b** (decided by etcd-grove-03: entries by a model wrap, hard state by raft's canonical `Ready`):
  - raft: `hsROC`/`hsOptC` (`InvPb.lean`, `InvPbLog.lean`); `raft.hardState.spec` post `hsROC`; `readyWithoutAccept`,
    `RawNode.Ready` posts and `readyRest` carry `hsOptC` (internal `ownRawNodeReady`, `readyData`, `freshOk`,
    `staleOk` too); clients convert by `hsOptC_hsOpt`; RaftTla regenerated (+ its hand-written `makeTracingState`);
    ledger entry 2026-11-17.
  - `PW/RaftModel/Srv.lean`: `walEntW`/`walEntUnwrap`, `walEncEntW`/`walDecEntW` (injective: the bytes fix the model,
    `entryEncC_ok`), `walSrvMr`/`walSrvU`, `walEntInW`, `walSrvP` (hard states = `walHsIn`; `walHsIn_of_hsOptC`),
    `walSrvPb_laws` (all `WalPbLaws`; `MarshalHsLaw`/`CloneHsLaw`/`WalHsOwn` stay hypotheses as for WalTester).
  - `St/WalLinkPure.lean`: `walFoldChkFrom_map`, `walRead_map` (the fold commutes with `walOpMapE f`, `f` keeping
    indices: `walEntUnwrap_index`).
- **Next, in order:** L2: Go config (`storage.toml`), specs/proofs of `NewStorage`/`Save`/`SaveSnap`/`Sync`/`Close`/
  `Release`, `purgeFile` under `MaxWALFiles = 0`; HARD STOP at the `ReleaseSnapDBs` axiom text (proposal in the
  report of 2026-11-17). Then L3 (with L4).
- **L3 obligations from L1b:** the server's `hardStateAt` becomes `hsOptC` (the Save law's premise; raft's `Ready`
  gives it); `walEntInW` needs `ufWire` (from `entRoC`'s `pbMsg_ufWire`) and `0 < entrySize c` (index ≥ 1 sets
  `Index`); `metaEnc` of `etcdserverpb.Metadata` moved from L1b to L3 (needed only by `walMetaIs`).
- **Pitfalls:** gen-link/gen-init compare only with Perennial linked at `.lake/packages/perennial` (gates.sh does it:
  `ln -s /shared/perennial-c6b39d4f8`, then remove). Lock + later credit and SaveSnapshot pitfalls: History.
- **Check:** `TMPDIR=/shared/tmp LAKE_OPTS=--packages=/shared/tmp/manifest-c6b.json etc/lean-check.py --max-open 2 FILE`.
  **Build:** `/shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-c6b.json build TARGET`.

### START HERE (2026-11-17, after L1a)

- **Branch** `wal-link` in `/shared/etcd-grove-wallink`, off `lean` `9702d5707e`; `.lake/build` from a full c6b
  build at 9702d5707e; `.lake/package-overrides.json` = `/shared/tmp/manifest-c6b.json`. Coordinator: etcd-grove-03.
- **Decisions** (Scope §7, `questions.md`): plan approved by the user; Q1 L3 lands with L4; Q2 P2 (`--wal-dir` under
  per-member `fsExt` roots, examples' Go absolute); Q3 `NoIoErr` all inodes; Q4-Q6 as recommended (etcd-grove-03).
- **Done:** Scope + Go evidence (72997e9e36); **L0** `St/WalLinkPure.lean` (proved, no trust change): the read bridge
  `walRead_of_fold`, the eager steps `walFoldChkFrom_save_cons`/`_snoc_save`/`_snoc_snap` (`WalSaveOkC` = `WalSaveOk`
  unfolded, so the sealed `WalRecs` can import it), `walCommitLe_of_fold`, `walCommitLeFrom_snoc/_nil`, `walIdxLe_*`.
- **L1a done** (no-twin collapses, Scope §8; shapes accepted by etcd-grove-03): `PW/HandleShared.lean` (the shared
  handle `walOpenWS`, its laws, `ioNone`, `noErr_ioNone`); one spec + one proof each for `Sync` (7eba580698), `Save`,
  `Close` (over `WalCloseSt`), `ReleaseLockTo` (`spec`, corollary `spec_R`); `PW/CalleeCov.lean` chooses the
  callees' two specs by `walCov`; `etc/link_walfs.py` handles `(Sio := ioNone)` binders.
- **SaveSnapshot's room (A) done** (dcb795d4b3, then the SaveSnapshot commit after it): `HandleRoom.lean`
  `walSnapBudget`/`walSaveRoom`/`snapRoom`; `HandleShared.lean` `WalShN.γu`, `walUsed`, γ-indexed `walHdl`
  (`walHdlF` before sharing, `walOpenWS_alloc` also returns `walUsed γ 0`), `walShPers` holds the WAL's
  `isPkgInit` (`walShPers_pkgInit`), AU transformers `walAu_save`/`walAu_snap` (method) and
  `walAu_saveC`/`walAu_snapC` (client); `Save`'s AU carries `walUsed` (`walUsedAfterSave`), room premise
  `walSaveRoom`. **SaveSnapshot: one spec** over `WalSnapSt` (`shared γ q` | `pre …`, `HandleShared.lean`), one
  proof by cases (`wp_shared`, `wp_pre`); `WAL__SaveSnapshotNoErr` gone, `specPre` gone (its proof is `wp_pre`);
  `CalleeCov.walCov_encodeTail`; Create at `.pre` (`Sio := ioNone`, `walPbNone`); WalTester's `member__saveSnap`
  shares the handle. Links regenerated; both Links and the importers' leaves build.
- **Decided (etcd-grove-03, 2026-11-17):** the server SaveSnap law old → new APPROVED (with Save's matching
  `walUsed` update); the collapse's forms ACCEPTED; wire vs model: (i) if provable, else (iii); (ii) out.
- **Next, in order:** L1b by **(iii)** (the check below rules out (i) for entries), stop if a closed statement
  would change; merge lean (≥ 3cd4b72599, then `.lake/package-overrides.json` stays the c6b manifest); end-of-L1
  full build via the build slot (retry on 143); `etc/tcb-report.py --check` and `--collection` for
  `wal-fsext.txt` and `wal-tester.txt`; report the L1 boundary; then L2 (HARD STOP before `ReleaseSnapDBs`).
- **Pitfall (lock + later credit):** a method needing the handle before its first resolution after `Lock` takes
  `Lock` with `+noauto`, steps the deferred `Unlock`'s resolution by hand (`wp_go_step_receipt'`, its `£ 1`), then
  `wp_raise_receipt` at the next resolution (`WAL__Save.lean`, `WAL__SaveSnapshot.lean`). A spec whose pre/post is a
  `match` on a state: `dsimp only` in the call's side goal. Build the Links before committing (lean-check once hid
  an unknown identifier).
- **Pitfall (SaveSnapshot):** the receipt is raised at `encode`'s resolution: `simp only [SnapshotType]` first,
  or `wp_to_resolve` stops at the record's literal. A multi-line `{ h with … }` in a tactic term: fields of a
  continuation line must align with the first field's column.
- **Open (for L3/L5):** nothing produces `walOpenWFR` yet (Create's/ReadAll's posts give `walOpenWF`; room is an
  open layer-1 decision, `notes/wal-units/noioerr.md`): the server's shared handle needs the fresh room from
  bootstrap's slot (L3, trusted) and, in L5, from `Create` (headers < 2^43) and the restart's `ReadAll` (a tail bound).
- **Pitfalls:** WAL Go sources at the pin: `/shared/tmp/wallink/etcd` (shallow fetch of `8c28a4296`); `.lake/go-src/etcd`
  is older. `E/WalApi.lean`'s header "NOT YET IN USE" is stale (fix in L3). `WalViews.lean` is over the old `absDiskExt`.
- **Check:** `TMPDIR=/shared/tmp LAKE_OPTS=--packages=/shared/tmp/manifest-c6b.json etc/lean-check.py --max-open 2 FILE`
  (`--stop` before builds and at the end). **Build:** `/shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-c6b.json build TARGET`.

### L1b by (iii): cost stop (2026-11-17; reported to etcd-grove-03; no Lean changed)

- **Why (iii) is not internal to RaftModel/WalApi.** Layer 1 fixes `Mr : WalMarshal` (model -> bytes) as a
  parameter of `walInv` (`PW/Inv.lean:2128`), allocated before any entry exists, and every stream function
  (`opDs`, `cutHdrDs`, `segsDs`, `recsOfSegs`, `tailStream`, `tailRecs`, `allRecs`, `segStream`,
  `St/WalEncRecs.lean`, `St/WalEncSegs.lean`, `PW/Handle.lean`) computes the bytes from `H.map WalOpG.toM`.
  Per-record bytes need a new argument (an annotated history `X` with `strip X = H.map toM`, kept per directory
  in `walInv` and in the tail record, maintained by Save/SaveSnapshot/cut/Create/ReadAll/crash): 105 files,
  919 uses of the stream functions, 176 of `map WalOpG.toM` (57 files): est. 2-4k lines changed, about (ii)'s cost.
- **Entries alone are cheap (no layer-1 change):** the server's WAL-level model of content `c` keeps term/index/
  type and puts `entryEncC c` in `Data'` (`Mr.encEntry` := those bytes when the model is such a wrap of a `ufWire`
  content, else injective stand-in bytes as `walEntJunk`); round trip from `entryEncC`'s injectivity on `ufWire`
  (MsgAppV2.lean:567-570). The history then holds wrapped models; L0/L3 map them back (fold commutes with maps
  keeping Index/Term, ~100 lines). Est. 300-600 lines.
- **The hard state is the blocker:** `WalOpG.save (h : HardStateM)` (trusted `GooseLang/Ext/AbsDisk/Impl.lean:83`)
  has no room for content, and `cut` repeats the last state record (wal.go:931, `w.state = s`, :1098). Options:
  (a) raft's exported Ready results give the hard state canonical (`raft.hardState` builds all three cells, uf = []:
  `raft__hardState.lean:31-35`): a stronger post on `RawNode.wp_Ready`/`node.wp_Ready`/`isReadyChan_recvAu`
  (exported statements: user/coordinator stop); (b) layer 1 over per-record state bytes (the annotated history
  above, state part only; most of the 2-4k); (c) `walInv`'s `encState` a ghost map extended at first use, with a
  no-conflicting-repeat premise on Save (raft's hard-state monotonicity at `raftNode.start`: not exported today).
- Recommendation in the report: entries by the wrap; hard state by (a).

### L1b at the R5 stop (2026-11-17; HARD STOP (b), reported to etcd-grove-03; no Lean changed for L1b)

- **R5 (fraction vs frozen): no client change.** `storage.SaveSnap` (S/storage/storage.go:59-70) shares raft's
  `Index`/`Term` cells and `ConfState` object in its `walpb.Snapshot`; layer 1's `walSnapAt` needs them frozen.
  The law's `smPtsV mp dq' md` has the cells `cellRO` already; only the conf state is at `dq'`. Both callers pass
  a discarded metadata (`EtcdServer__snapshot.lean:366`, `raftNode__start.lean:616` via `srv_ownSnapS_meta`'s
  persistent facts): the law fixes `dq' := DFrac.discard`. Bridge (L1b lemma): `csPts … DFrac.discard` gives
  `csRoC` with `uf = []` (`PbContent.lean:704`) → `walCsRoC` at `walCsCanon`.
- **New finding (content vs model):** layer 1's `WalMarshal` encodes models; `walRaftP` (PW/RaftModel) needs the
  canonical wire content (`walEntIn`: `entRoC l (walEntCanon e)`; `walHsIn`: `walHsCanon h` unless empty). The
  server's entries are any content of the model (`walSaveEnts true`: `∃ c, entRoC l c`, `c.uf` and field presence
  free; MsgApp entries are unmarshalled) and `hardStateAt = hsRO` leaves `pbMsg … uf` free; protobuf-go writes
  presence and unknown fields, so the records' bytes are not a function of the model. Options: (i) a fact that the
  server's entries/hard states are canonical (needs `uf = []` and raft's presence pattern; likely false for
  received entries); (ii) layer 1 over contents (`WalOpG` over `EntryC`/`WalHsC`, `Mr` over contents, `ReadAll`
  returns contents): several k lines; (iii) `Mr` over contents with the per-record bytes in a ghost map read by the
  crash invariant. Recommendation in the report.
- **(i) vs (iii), checked 2026-11-17 (read-only):** entries cannot be shown canonical: `appendEntry`
  (raft.go:812-819) clones the proposer's entry and sets only Term/Index; proposals build `&pb.Entry{Data: data}`
  (node.go:472, rawnode.go:94; no `Type`, while `walEntCanon` needs `Type = some`); received MsgApp entries keep any
  `uf` within `ufWire` (`MsgAppV2.lean:87,108`, `msgAppV2Decoder__decode.lean:190`) and reach `Save` uncloned.
  Hard state: Go's `r.hardState()` sets all three cells with `uf = []` (raft.go:504-510; proof
  `raft__hardState.lean:31-35`), but `raft.hardState.spec` returns only `hsRO` (uf, nil cells free); making it
  canonical would restate raft library results (`Proof/go_etcd_io/raft/v3/Results.lean`: `RawNode.wp_Ready`,
  `node.wp_Ready`, `isReadyChan_recvAu`). So **(iii)** for both: `Mr` over contents (entry bytes `entryEncC c`, any
  `uf` with `ufWire`; the decoder's round trip from `entryEncC`'s injectivity on `ufWire` contents, as
  `MsgAppV2.lean:567-570` uses), each record's bytes in a ghost map the crash invariant reads, the history over
  models. Expected internal to the WAL model (`RaftModel/EntCodec.lean`, `Pb.lean`, `Marshal.lean`) and
  `WalApi.lean`; WalTester's canonical instance stays a special case.
- Server `SaveSnap` law, old → new: in the report (and `/shared/tmp/wallink/l1b-r5.md`).

### Older

### START HERE (2026-11-17, Scope)

- **Branch** `wal-link` in `/shared/etcd-grove-wallink`, off `lean` `9702d5707e`; no `.lake/build` (disk);
  `.lake/package-overrides.json` = `/shared/tmp/manifest-c6b.json`. Coordinator: etcd-grove-03.
- **Done:** the Scope, `notes/wal-link-scope.md` (HARD STOP: Scope ready for review); Go evidence
  `examples/wallink/link_test.go` (C1-C7), all pass at the etcd pin `8c28a4296`
  (`cd examples && GOWORK=off TMPDIR=/shared/tmp systemd-run --scope -q -p MemoryMax=32G go test -race -count=1 -v ./wallink/`,
  ~95 s, most of it C1's fsyncs; last run log `/shared/tmp/wallink/test-run.txt`). No Lean changed.
- **Next, in order, once the Scope is approved:** L0 (pure read bridge, `St/WalHistLemmas.lean` neighbours) ∥ L1a
  (layer 1's shared handle, `PW/Handle.lean`) ∥ L1b (the server's `WalPbIn`/`WalMarshal`; check R5 first: are
  `hardStateAt` and raft's snapshot conf state frozen?); then L2 (`storage.toml`, `serverstorage` proofs,
  `ReleaseSnapDBs` axiom: HARD STOP), then L3 with L4 (Q1). Scope §5.
- **Open decisions (Scope §5):** Q1 land L3 with L4 (recommended); Q2 placement P2, `DedicatedWALDir` under
  per-member `fsExt` roots (recommended; changes the examples' Go); Q3 `NoIoErr` on all inodes now; Q4 the
  received snapshot's bounds from the cluster's room invariant; Q5 take `walFiles`' exclusivity and the `walSnapRec`
  witness; Q6 drop the `sized = false` law.
- **Pitfalls:** the WAL's Go sources at the pin are not in any local checkout (`.lake/go-src/etcd` is at
  `6e8f0c004c`); a shallow fetch is in `/shared/tmp/wallink/etcd` (`git fetch --depth 1 https://github.com/upamanyus/etcd 8c28a4296f…`),
  and the module cache has `server/v3@v3.0.0-20261115085855-8c28a4296f16`. `E/WalApi.lean`'s header still says
  "NOT YET IN USE" (stale since R2b-1; fix it in L3, not in a Scope commit). `WalViews.lean` is over the old
  `absDiskExt`, not `WalFs`: L0 states its lemmas over `WalHist` only.
- **Build (L1+):** `/shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-c6b.json build TARGET`; a `.lake/build`
  must be seeded or moved here first (the coordinator; `df -h /shared` ≥ 40 GB before any `cp -a`).
