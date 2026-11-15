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

7. **Build repairs** (`631d660dd2`, `adf063c95f`, `68969d455e`, `fc16855e12`): `GooseLang/Ext/Fs/Write.lean`
   builds (checked); `os.WaCut` carries `PwCut`'s `maxBytes` part (`waCut_step` with `nn ≤ j`); the WAL's
   `snapRoC`/`snapSize` renamed `walSnapRoC`/`walSnapSize` (raft's `PbContent` declares both); wal-int's
   `mcells_congr` (⊣⊢) is `mcells_congr_iff`; `os.File.WriteAt.specExt`'s proof split to
   `Proof/os/File__WriteAtExt.lean` (see Open); the part's extracts are main modules `<Source>Core.lean`
   (`NodeApiVocabCore`, `CommitWitCore`, `WalRecsCore`, `InvPbCore`, `PbContentCore`, `PbContentOwnCore`,
   `PbEntryTypeCore`), their sources import them, the WAL imports them (the whole sources brought clashing
   names: `NodeApiVocab`'s `LogEntry` shadows `Fs.LogEntry` under `open Fs`); the Whole copies' drops applied
   to the main specs (`time.Duration.Seconds{,_ptr}` without the server's `BaseApply`, zap's specs over zap's
   `PkgInit` instead of the cache's `Base`, whose closure reached `cache`'s `chainEnd`).
8. **Re-merge of `origin/wal-int`** `b46dd78a5d` (`403a7e7e88`): Create's cleanup (`cleanupWAL`), specgap;
   `etc/wal-lean-remerge.py` carries `LinuxFs/` changes to the main tree (plan §7, "Procedure").

### Build status (end of session 1)

- `lake build GooseLang.Ext.Fs.Write`: OK (after the merge repair).
- `lake build Proof.go_etcd_io.etcd.server.v3.storage.wal.Link`: **not reached**. Runs 3-5 found the errors
  repaired above (each run builds ~3500 modules from the copied, older build); run 6 (after the extract
  splits and the re-merge) failed only on **"no space left on device"** (the machine's disk: 482 of 484 GB
  used; this worktree's `.lake` is 33 GB). The last real errors before the splits (`Cut`, `CreateNamedPure`:
  `LogEntry`; `TailCrashPure`, `ReadAllDecode`: `chainEnd`) are what the splits/drops address; unverified.
- Known not to build: `Proof/os/WriteChunks.lean` (`pwPost_chunk`'s `cz`/`rz` goals) and so
  `Proof/os/File__WriteAtExt.lean` and the bbolt port's users of `specExt` (Open below).
- Not attempted: the server (`etcdserver/Init.lean`'s regenerated call of the WAL's `wp_initialize'_lb`,
  `BaseApply`), the bbolt port (`Proof/go_etcd_io/bbolt/`, over wal-int's `MetaOk`/`OsMeta` changes),
  `WalTester/`, the main users of the dropped zap/time imports, a full build, `etc/gates.sh`,
  `etc/tcb-report.py --check --update`, interfaces.

### Open

- **`os.File.WriteAt.specExt` under `cz`** (ledger 2026-11-15): lean's chunked `WriteAt` spec (bbolt port)
  states the post `OsMeta` as `pwPost m off a j`, false once wal-int's `OsMeta.cz` (P1, pending the user's
  review) remembers a chunk that landed whole; wal-int's own chunked spec (`specLong`) uses `os.pwPostE`.
  Proposed: `specExt`'s post over `pwPostE` with an `E`, `WriteChunks`' chunk lemma as
  `WriteLongStep.pwPostE_step` for `pwrite` anywhere, the six bbolt users re-proved. Coordinator's call.

### Next steps

1. Free disk (or build elsewhere), then `nice lake build Proof.go_etcd_io.etcd.server.v3.storage.wal.Link`
   and fix what remains (expect more name clashes from main modules the part never imported: `.scr`-style
   scan of top-level names; rename the WAL's).
2. `WalTester/`: `lake build` its links (`--durable`; the tester has no Link yet on wal-int).
3. The server: `Proof.go_etcd_io.etcd.server.v3.etcdserver.Init`, `BaseApply` and their importers (the WAL's
   package fact is now the part's, with deps fileutil/crc/bufio/filepath).
4. `specExt` (Open), then the bbolt port's `Link`, `osfs` (minibolt/crashlog/walfs over wal-int's `MetaOk`).
5. The full niced `lake build`, `etc/gates.sh`, `etc/tcb-report.py --check --update` (−12 WAL axioms,
   −`purgeRound`, the WAL's copied axioms now the originals), `etc/tcb-collections` (`wal-fsext`, a
   `wal-tester`), `etc/gen-interface.py` for the changed APIs.
6. Re-merge `origin/wal-int` again before landing (`etc/wal-lean-remerge.py b46dd78a5d`).
