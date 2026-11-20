# Re-attack: the snapshotter's directory per execution (wal-link, 2026-11-19)

**Reviewed:** the uncommitted wal-link restatement on 559395f5ee (committed after the review with this
report): `snap.isSnapshotter ss sd` (the `dir` field's cell `snapDirAddr ss ↦□ sd`, `⌜∃ dd, sd = snapDirOf dd⌝`),
`snapDBPath sd i` (a definition), `snapDirInv sd`, the axioms `DBFilePath`/`SaveDBFrom`/`ReleaseSnapDBs` over
`sd`, `bootOk`/`bootOkR` (`Hss` at `config.snapDirOf cfg.DataDir`, `Hssp` gone), `srvDiskImageAt`, and the proved
specs restated with them. **By:** a fresh read-only agent (axiom skill), brief `/shared/tmp/wallink/attack-sd-brief.md`.
Go: etcd at the pin (`server/etcdserver/api/snap/{snapshotter,db}.go`, `bootstrap.go`, `config/config.go`); scratch
test `/shared/tmp/wallink-attack2/ex/sdrel/sd_test.go` (real `config.ServerConfig`, PASS).

| task | verdict |
|---|---|
| 1. Cross-world | **ok**: no pure fact of a run-allocated location is pinned per run any more |
| 2. Multi-member boot premise | the k-member collision is **fixed** (assignment below, over absolute data directories); but **refuted for the closed theorems as stated, for every k ≥ 1**, on another account (pre-existing since S5): `notes/datadir-relative-unsat.md` |
| 3. The axioms over `sd` | **ok** |
| 4. Other | documentation only |

## 1. Cross-world (ok)

`snapDBPath : Loc → …`, `snapDBPathOf`, `snapDirInv_ss_congr` are gone. `isSnapshotter`'s directory is a heap
cell's content (two worlds may hold different `sd` at one location); its pure part is about the string only (a
fresh world satisfies it with any `snapDirOf d`, so the crossWorld construction gives nothing); `snapshotterRO`
(opaque) has no producer but the two bootstrap contracts. `snapDirInv sd`, `snapDir_init`, `snapDir_take` conclude
no pure fact about a location. `dirReadOk (ss : Loc)` stays over the location but is sound: it occurs only as
`¬ dirReadOk ss` in error branches, positively only in `snapOpensOk`'s `∀ ss, dirReadOk ss` (`storage/InvOpen.lean`),
which no trusted text pins per run (restating it over `sd`, or without argument, would be cleaner).

## 2. The boot premise

**k members, fixed (over an absolute layout).** Roots `/srv` (inode `r0`) and WAL roots `A_i`, pairwise not nested;
`d_i = /srv/m_i.etcd`, absent at the start; `sd_i = d_i/member/snap` (inode `s_i`), `sd_i/db` (inode `f_i`),
`n_x = hex16 x ++ ".snap.db"`. Member `i`'s post: `Hss` a fresh `ss_i` with `snapDirAddr ss_i ↦□ sd_i`
(`snapshotterRO := emp`, `dd := d_i`) and its logger cell; `Hsdo` (`snapDirIsRO := emp`); `Hsfree`: for each `x`,
`fileFree (sd_i/n_x)` = fractions of the spine claims `m_i.etcd`/`member`/`snap` below `/srv`, a share of `/srv`'s
call permission (the k shares sum to ≤ 1), the whole `osNames s_i (.only [n_x]) (own 1)`, `n_x` absent; `Hpath`:
`boltIno f_i` and the whole claim on `(s_i, "db")`; `Hbfile` persistent; `Hwal` under `A_i`. The exclusive claims
are pairwise distinct: across members the `s_i` differ (the spines part at `m_i.etcd`; `TreeWf` names each
directory once), within one the `n_x` differ (16 fixed hex digits) and differ from `db` (24 bytes against 2). Nothing
in Lean makes `snapDirOf d_1 ≠ snapDirOf d_2`, and nothing needs it: each member's claims come from its own contract
instance; semantically, for clean absolute `d`, `SnapDir` is `d ++ "/member/snap"`, injective (string distinctness
alone is not: `a`/`a/`, `a`/`./a` alias; only `dataDirsApart`/`dataDirsAbsent` exclude aliases). Restart
(`bootOkR`): a fresh `ss'_i` with a cell holding the same `sd_i`; `srvDiskImageAt`'s `snapDirInv sd_i γd_i` reused;
`Hpath` the claim `srvFiles` hands back.

**But no assignment exists for the examples** (pre-existing since S5): their data directories are relative
(`cfgOk`: `DataDir = name ++ ".etcd"`), the claims need absolute paths (`osPathS` needs `RootsOk`, whose roots are
`RootForm`, absolute), and the trusted `config.ServerConfig.BackendPath.wp_proof` makes `snapDirOf "m1.etcd"` the
relative `"m1.etcd/member/snap"` (Go's `BackendPath()`); so `Hpath` and `Hsfree` are false, the contract false of
Go for every member. Absolute data directories do not help with the current WAL layout (`walAreaOf dd =
"/tmp/etcd-grove-wal/" ++ dd` has `//`, not a `RootForm`, so `HWal` fails). `notes/datadir-relative-unsat.md`.

## 3. The axioms over `sd` (ok)

`DBFilePath` (`db.go:102-123`): every admitted `sd` is some `cfg.SnapDir()` (clean, non-empty, ending in `snap`),
so `Join(sd, name) = snapDBPath sd id` for every `DataDir` string (B1's randomized test and the relative cases);
with the file held the only error is a failed `ReadDir`/`stat`, the `¬ dirReadOk` branch. `SaveDBFrom`
(`db.go:39-98`, `os.Link`) and `ReleaseSnapDBs` (`snapshotter.go:45-72`): meaning unchanged. Two incarnations
sharing one `snapDirInv sd` is sound and more faithful (one ghost map per directory): `os.Link` puts one save's file
in place; a stopped incarnation's release needs `Rm j = monoNatLb γm (j+1)`, which `snapDir_take` of `j` refutes
(the same counter authority); a second invariant would need a second `snapDirOwn` with the exclusive `snapFreeAll`.
`os.Rename`'s same-parent premise holds (both names in `sd`).

## 4. Other

`snapDirOwn` is duplicable with `snapDirIsRO := emp` (pre-existing); only the exclusive `snapFreeAll` that
`snapDir_init` also takes prevents a second invariant. The restated proved specs only add `isSnapshotter ss sd`
beside `snapDirInv sd`.
