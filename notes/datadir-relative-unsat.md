---
title: the examples' relative data directories make the bootstrap contract's file claims unsatisfiable
found: 2026-11-19
by: the snapdir re-attack (wal-link, fresh read-only agent, axiom skill), notes/axiom-review/snapdir.md §2
blocks-proof: no
status: fixed on wal-link (2026-11-19, approved by the user via etcd-grove-03); lands with wal-link
---
# Relative data directories against absolute file claims

A bug in this repository's trust base (the closed theorems' bootstrap premise), not in etcd. Pre-existing on
`lean` since S5 (2026-11-18), when the backend's and the snapshots' paths became claims in the Linux file
extension's shared mode (`backend.bPath`, `fileFree`, `fileHolds`).

**The chain.** `bootOk`'s `Hpath` is `backend.bPath γ (config.backendPathOf cfg.DataDir)` and `Hsfree` is made of
`backend.fileFree`; `srvFiles` (restart) of `fileHolds` (`storage/backend/InvBbolt.lean`). Each needs `path = d ++
"/" ++ b` with `osPathS R d …`, which needs `RootsOk R ∧ (r, j0) ∈ R ∧ d = joinPath r cs`
(`GooseLang/Ext/Fs/TreeSharedRes.lean`); `RootsOk` makes every root a `RootForm`, absolute
(`GooseLang/Ext/Fs/Tree.lean`). Under the examples' extensions `onFs` is its body. The examples fix `DataDir = name
++ ".etcd"` (`examples/lib/etcdstart/Defs.lean`'s `cfgOk`; Go `common.go:81`), relative; the trusted
`config.ServerConfig.BackendPath.wp_proof` says Go's `BackendPath()` is `config.snapDirOf dd ++ "/db"`, and Go
returns `"m1.etcd/member/snap/db"`, so (in the intended reading of the opaque `snapDirOf`) `snapDirOf "m1.etcd" =
"m1.etcd/member/snap"`, relative. No `osPathS` names it: `Hpath` and every conjunct of `Hsfree` are false, while Go's
`bootstrap` returns, so `bootstrapContract` is false of Go **for every member, k ≥ 1**, and every closed theorem
taking it holds vacuously. Not derivable as `False` in Lean (`snapDirOf` is opaque). Known in a weaker form
(`notes/bbolt-integration-plan.md`, Open, Left 1; `notes/wal-link-scope.md`, F-c: "cannot be derived",
"may be undischargeable"): it is unsatisfiable.

**Absolute data directories alone do not fix it:** `walAreaOf dd = "/tmp/etcd-grove-wal/" ++ dd`
(`storage/WalLayout.lean`, wal-link P2) gives `//` for an absolute `dd`, not a `RootForm`, so `HWal`
(`etcdWalAreasInit`: `walAreaOf d` is a root) becomes false.

**Fix (wal-link, 2026-11-19, approved by the user via etcd-grove-03).** Each member's data directory is
absolute and a root of its own: `memberDataDir n = /tmp/etcd-grove-data/<n>.etcd` (`storage/WalLayout.lean`;
Go `etcdstart.DataBase + "/" + name + ".etcd"` in `common.go`, `auth.go`, `auth3.go`, `authkv.go`; the tests'
`walarea.Reset`/`ResetFamily` reset it with the WAL area); `cfgOk` and every example's data-directory list
over it; `walAreaOf dd := walBase ++ dd.drop dataBase.length`, the member's `<n>.etcd` under
`/tmp/etcd-grove-wal` (the Go WAL paths unchanged). The closed theorems' premise `etcdWalAreasInit` also
says each data directory is `memberDataDir n` and an empty root; the allocation at adequacy
(`lib/etcdstart/WalAreas.lean`) hands each member `dataAreaFresh d` (its spine, its root's whole call
permission and its whole name claim, no entry), which `wal.bootRes` (the bootstrap contract's pre) now takes
in `memberAreasFresh`: what the contract's `Hpath`/`Hsfree` claims are made of.
