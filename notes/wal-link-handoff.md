# WAL link: handoff

## START HERE (2026-11-17, after L1a)

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
- **Next, in order:** L1b, L2 (HARD STOP before `ReleaseSnapDBs`).
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

## History

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
