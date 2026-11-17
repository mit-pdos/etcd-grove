# WAL link: handoff

## START HERE (2026-11-17)

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
