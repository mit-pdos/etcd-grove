# Unit `lean-integration`: the WAL over `fsExt` into the main tree (branch `wal-lean`)

Plan: `notes/wal-lean-integration.md`. Branch `wal-lean` = `origin/wal-int` (`87db1a9cf3`) + the
relocation + `origin/lean` merged. Log of the session(s); the plan says what and why.

## Session 1 (2026-11-15)

### Done

1. **Plan** (`21ec9e8636`): inventory of `LinuxFs/` (1126 files) by class, the mapping, the trusted
   text differences, what retires, the scripts, the stages.
2. **Relocation** (`stage 2`): `LinuxFs/X` -> `X` (the tester's and `lib/durable`'s files ->
   `WalTester/X`), git renames; the module prefix dropped from imports and paths (`.scr/relocate.py`,
   not committed); the 55 part copies deleted (their imports name the originals, at the same paths;
   `WalDisk.lean` takes the copy's form); the part's raft root translation and its generated copies
   of main package inits deleted; the absDisk tester deleted.
3. **Merge of `origin/lean`** (`stage 3`, `26cfac15a7`): 47 conflicts. The `os` layer's files (in
   `LinuxFs/` at the merge base, moved on both sides) were re-merged with the right base (the base's
   `LinuxFs/X`, prefix dropped): all 218 clean, 17 of them git's conflicts with the wrong base. 10
   rename/delete conflicts were git pairing unrelated small files (kept ours). `os/Rename.lean`: the
   main tree's backend axiom spec stays `os.Rename.spec` (Spec/Proof `os/Rename.lean`); the part's
   fsExt specs are now `os/RenameS.lean` (13 importers rewritten). Notes: both sides; STATUS's Last
   updated line the ten newest. `GooseLang/Ext/Fs/Write.lean`: lean's pwrite-anywhere (`wp_osPWriteFinishKG`)
   with wal-int's `maxBytes` cut and `pwCz`; repaired (`631d660dd2`): the cache condition is lean's
   `min off m.size ≤ b ∧ 0 < k ∧ ...`, `pwFinish_cz_raise` takes any `lo ≤ off`; lean's
   `mcells_congr` (⊢) kept, wal-int's (⊣⊢) duplicate dropped (its users `iapply` it).
4. **Scripts** (`stage 4a`): `etc/goose.py` (etcd pin `3df9b265f`, roots `bufio=`, `path/filepath=`,
   `internal/filepathlite=`, `syscall=`, `golang.org/x/sys=`, `internal/poll=`, `internal/syscall=`;
   the WAL packages with bodies in the main etcd project; the parts of raft and etcd gone; durable's
   part and etcd-wal in `WalTester/`); `examples/go.mod` (+ `k8s/etcd3`, `k8s/compactor`): the fork's
   `v3.0.0-20261114215450-3df9b265f7e7`; regenerated: no change but import order in `fileutil`
   (the moved part translations were already the main configuration's output). `etc/gen-init.py`:
   `LFS_SPECIAL` into `SPECIAL` (os's and io/fs's facts with `ErrExist` non-nil etc.; ioutil, walpb,
   fileutil, the WAL), `LFS_MODE` and the part generation gone, `wt_inits` for `WalTester/`, the
   tester's Perennial imports in `PkgInitExt`. `etc/link_walfs.py`: main-tree paths, `PROOF_DIRS`
   (the proof directories whose theorems are candidates), `WalTester` for `--durable`; both links
   regenerated (no change but the header and import order). `etc/gen-part-copies.py` deleted (and its
   `gates.sh` step); `lakefile.toml`: lib `WalTester`; `etc/tcb-collections/wal-fsext.txt` roots.
5. **One home per package-init instance** (`stage 4a`): new `PkgInit.lean` for zap/zapcore, semver,
   prometheus, pbutil (out of the cache's, lease's, backend's, apply's `Base.lean` and the WAL's
   `DepsPkgInit`); verify's, ioutil's, the WAL's, walpb's, fileutil's are the WAL's `PkgInit.lean`s
   (out of the backend's `Base` and `BaseApply`; the names-only `fileutil/Base.lean`, `walpb/Base.lean`
   deleted); `proto`'s and raft's root are raft's `Base.lean` (the part's `proto/PkgInit`,
   `raft/v3/{PkgInit,InitPb}` deleted; `RaftModel/Pb.lean`'s `rootInit_hsGet` over raft's
   `isInitialized`, whose `#emptyState` conjunct is the part's `rootInit` word for word).
6. Retired: `WalBodies.lean` (no importer left), the 11 WAL axioms and `TouchDirAll`'s (their files are
   the part's proofs now), the absDisk tester with `purgeRound`'s axiom. Kept: `GooseLang/Ext/AbsDisk`
   (the proofs are stated in its `AbsDiskState`/`WalDur`/`walImg`), `WalDisk`/`WalViews`, `durableExt`.

### Decisions for the user / coordinator

- **`lib/durable`: two translations** (plan §1): done provisionally as D2 (the part `WalTester/` holds
  the bodied `durable` and the tester). Alternatives D1 (bodied `durable` alone in a part) and D3 (port
  kvdurable/kvfile/etcdstart onto the bodied `durable`, retiring `durableExt`).
- **`purgeRound`'s approved axiom retired** with the absDisk tester (w4c plan §6.2): the new tester
  translates `purgeRound` with its body; nothing needs the axiom.
- Trusted text: no conflict with `lean` (lean changed none of the layer's semantics); `wal-int`'s
  pending-review changes taken as they are (plan §3).

### Build status / next

(see the end of the session's report; updated below)
