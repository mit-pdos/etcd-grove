# WAL link: handoff

## START HERE (2026-11-17, after L0)

- **Branch** `wal-link` in `/shared/etcd-grove-wallink`, off `lean` `9702d5707e`; `.lake/build` from a full c6b
  build at 9702d5707e; `.lake/package-overrides.json` = `/shared/tmp/manifest-c6b.json`. Coordinator: etcd-grove-03.
- **Decisions** (Scope §7, `questions.md`): plan approved by the user; Q1 L3 lands with L4; Q2 P2 (`--wal-dir` under
  per-member `fsExt` roots, examples' Go absolute); Q3 `NoIoErr` all inodes; Q4-Q6 as recommended (etcd-grove-03).
- **Done:** Scope + Go evidence (72997e9e36); **L0** `St/WalLinkPure.lean` (proved, no trust change): the read bridge
  `walRead_of_fold`, the eager steps `walFoldChkFrom_save_cons`/`_snoc_save`/`_snoc_snap` (`WalSaveOkC` = `WalSaveOk`
  unfolded, so the sealed `WalRecs` can import it), `walCommitLe_of_fold`, `walCommitLeFrom_snoc/_nil`, `walIdxLe_*`.
- **L1a in progress (no-twin collapses decided by etcd-grove-03, Scope §8).** Done: `PW/HandleShared.lean` (the shared
  handle `walOpenWS Sio P Mr w dir γ q`, invariant `walShInv` = handle+`γl ↦ none` ∨ `ownMutex`+½`γl ↦ some q`+the
  holder's share ∨ whole token; laws `walOpenWS_alloc/_split/_pers/_acquire/_release/_finish/_reclaim`, `walHdl`
  (handle when `¬ walCov Sio`, else fresh room), `ioNone` + its `FsStepSat` instance); **`Sync` merged** (one spec,
  one proof; `WAL__SyncNoErr.lean` spec+proof deleted); WalTester's `member__sync` shares the handle for the call and
  reclaims it; `etc/link_walfs.py` accepts `(Sio := ioNone)` at a binder; both Links regenerated, targeted build OK.
  **Checkpoint: Sync's text reported, waiting for review** before Save, SaveSnapshot, ReleaseLockTo, Close.
- **Next, in order:** Save (two proofs → one; the callees `saveEntry`/`saveState`/`cut` keep their twin families, so
  the merged proof chooses the callee spec by `walCov Sio`, like Sync's `sync`/`sync.specNoErr`), SaveSnapshot
  (`specPre` as a precondition disjunct), ReleaseLockTo (rename), Close (disjunction of handle states); WalTester's
  members move like `member__sync` (share for the call, reclaim). Then L1b, L2 (HARD STOP before `ReleaseSnapDBs`).
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
