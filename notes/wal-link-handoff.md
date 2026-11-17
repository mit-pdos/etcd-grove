# WAL link: handoff

## START HERE (2026-11-17, after L0)

- **Branch** `wal-link` in `/shared/etcd-grove-wallink`, off `lean` `9702d5707e`; `.lake/build` from a full c6b
  build at 9702d5707e; `.lake/package-overrides.json` = `/shared/tmp/manifest-c6b.json`. Coordinator: etcd-grove-03.
- **Decisions** (Scope §7, `questions.md`): plan approved by the user; Q1 L3 lands with L4; Q2 P2 (`--wal-dir` under
  per-member `fsExt` roots, examples' Go absolute); Q3 `NoIoErr` all inodes; Q4-Q6 as recommended (etcd-grove-03).
- **Done:** Scope + Go evidence (72997e9e36); **L0** `St/WalLinkPure.lean` (proved, no trust change): the read bridge
  `walRead_of_fold`, the eager steps `walFoldChkFrom_save_cons`/`_snoc_save`/`_snoc_snap` (`WalSaveOkC` = `WalSaveOk`
  unfolded, so the sealed `WalRecs` can import it), `walCommitLe_of_fold`, `walCommitLeFrom_snoc/_nil`, `walIdxLe_*`.
- **STOPPED (2026-11-17) on the no-twin rule's cost:** Scope §8 (design over `inv (walOpenWF ∨ ownMutex ∨ tok 1)`,
  the spec families classified: Save/SaveSnapshot/Sync/Close are twin families, ReleaseLockTo a corollary; delta
  +2.5-5k lines if the collapses are in L1a). Waiting for etcd-grove-03's decision; no L1a Lean written yet.
- **Next, in order (after the decision):** L1a (`PW/Handle.lean`: shared handle `walOpenWS`, the five `NoErr` specs' shared variants,
  history-prefix fragment + `walSnapRec` from `SaveSnapshot`) ∥ L1b (server `WalPbIn`/`WalMarshal`; R5 checked:
  `hardStateAt` = `hsOpt` is frozen (`hsRO`), `entRoC` frozen, but `smPtsV mp dq md` is fractional: the `SaveSnap`
  law's conf state must become discarded or layer 1 take a fraction); then L2 (HARD STOP: `ReleaseSnapDBs` axiom),
  L3+L4 (HARD STOPs (a)-(c) of the brief before any trusted text / server statement / closed theorem change).
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
