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

## Session 2 (2026-11-15)

Setup: a fresh worktree (local branch `wal-lean2`, pushing to `origin/wal-lean`: the old worktree
still holds `wal-lean`), the previous session's `.lake` copied.

### Coordinator decisions applied

- **`os.File.WriteAt.specExt` restated as `specLong`'s post** (ledger entry updated): `∃ j a E ys`,
  `E ≤ j ∧ (j = a → E = a)`, `osMeta (os.pwPostE m off a j E)`; `WriteChunks.pwPost_chunk` (false under
  `cz`) deleted, `File__WriteAtExt.pwPostE_chunk` (with `pwCzE_stepG`, `pwCzE_step` for a write
  anywhere) in its place; the proof carries the last whole chunk's end `E` through the Löb loop
  (generalized to a variable before the context's `omega`s: with its `if`, and with the loop invariant
  in context, `omega` timed out). bbolt: `Tx__write`, `Commit/WriteExtRun`, `Commit/PwMeta`
  (`pwPostE_inside`) take the `E`.
- **`lib/durable` D2** recorded as decided (plan, `CLAUDE.md`); **`purgeRound`'s retirement** approved
  (plan).

### Done

1. `Proof.go_etcd_io.etcd.server.v3.storage.wal.Link` builds (no repair needed past session 1's).
2. `WalTester/`: its generated `Init.lean`s imported wrong paths (`etc/gen-init.py`'s `wt_inits`: the
   part's instance paths lacked `Proof/`, the part's inventory shadowed the main tree's `os` with
   Perennial's); fixed and regenerated; builds.
3. Re-merge of `origin/wal-int` `8d6f3670d8` (`0542339226`): the tester's Go changes and proofs
   (`purgeRound` gone), `Create`'s cleanup proved (`CleanupAu`, `CleanupMoved`). `etc/wal-lean-remerge.py`
   fixed: "ours" is HEAD's file (git's own merge may have left markers in the working file), and the
   tester's imports get the `WalTester.` prefix. WalTester's translation regenerated (`--project
   etcd-wal`; the main tree's absDisk tester `wal.toml`/`wal.lean`, which wal-int changed, stay deleted).
4. Etcd pin `e115818f5` (fork 0006: `WAL.Sync` takes `w.mu`, issues/etcd-wal-sync-releaselockto-race.md):
   `etc/goose.py`, the examples' `go.mod`/`go.sum` (the replaces' pseudo-version; sums from `go mod
   download -json`, no `tidy`: it rewrote unrelated requirements). Regenerated: `WAL.Sync`'s body only
   (and `ioutil`, below). `WAL.Sync.wp_proof` takes the handle's mutex (`walHandleIn_lockFacts`,
   Perennial's `sync.Mutex.wp_Lock`/`wp_Unlock`, invariant `True`) around `sync`, the invariant opened
   right after the lock; **its spec is unchanged** (no ledger entry needed); no new hypothesis.
5. Full-build repairs (`187e7d78ce`):
   - `ioutil.toml`: the merge kept only the WAL's entries; lean's (rafthttp's readers, `ReaderAndCloser`)
     restored beside them (regenerated: `Code/.../ioutil.lean` gains the WAL's page writer only).
   - The WAL's specs are named in `EtcdGrove.go_etcd_io.etcd.pkg.v3.{crc,ioutil}`, so `open
     go_etcd_io.etcd.pkg.v3` inside `namespace EtcdGrove` resolved to it in every module that reaches
     the WAL (the server's): those opens (116 files) now name `_root_.Perennial.go_etcd_io.etcd.pkg.v3`.
   - k8s `PrepareKey`'s `argWf_string` is `storage.argWf_string` (the WAL's `Spec/fmt/ErrorfErrs` has it).
   - bbolt over wal-int's `os` changes: `File.Stat`'s error is an `errnoPathErr` (`PageSize.stat_err_ptr`
     gives the pointer-error fact the port used); `ftruncate` announces to the page end (`rsPost true`,
     `rsHi true`; `DB__grow.grow_rsHi`: for a page-aligned size at least the file's, the size).
   - raft's and RaftWitness's `Init`: `os`'s fact has more conjuncts (`sep_elim_left`); mvcc `Results`
     imports raft's `Code` (no longer reached through the backend's `Base`); `RaftModel/LawsHs`: raft's
     `isInitialized` is not persistent (the part's `rootInit` was); WalTester's new files use
     `walSnapRoC`/`walSnapSize`; `EntryType.Enum`'s spec imports raft's `Base`; SpecPlan's PkgInit
     regenerated (`etc/gen-specs-pkginit.py`).
   - `etc/api/raft.txt`: the seven `<Source>Core` extracts importable (each a piece of a listed module).

### Build status (end of session 2)

Full niced `lake build` (18355 jobs): everything builds **but 13 adequacy theorems**, all with one error,
`failed to synthesize HasExt Fs.fsExt`: `examples/etcd/{compacted,putget,putget3,restart1,lease,leasegrant,
leaseexpiry,leasecatchup,compactwatch,txnlin,partition}/Adequacy.lean`, `examples/k8s/{compactor,etcd3}/
Adequacy.lean`. Cause: with bodies, `fileutil`'s package initializer runs its `init` (lock_linux.go: the
`F_OFD_GETLK` probe, `syscall.FcntlFlock` over `fsExt`), and the server imports `fileutil`, so every
etcd program's `wp_initialize'` now needs the file extension (`[ExtSemantics fsExt] [FsSemOk] [HasExt
fsExt]`), where these adequacy theorems run over `trivialExts` (no extension). True of real etcd (every
etcd process makes that `fcntl` at startup), but closing them means changing the closed theorems'
semantics: **for the coordinator/user**. Options: (A) the etcd adequacy theorems over `fsExts`
(`fsExtsSemanticsWithS`, the osfs programs' setup; their start allocates the file extension's ghost state)
-- a change to 13 closed statements; (B) the server's `fileutil` initializer kept a trust-boundary fact
for the server's chain (an axiom that the probe's outcome is one of the two lock pairs, with no extension
step), which would be a trusted-text change; (C) etcd's main programs import the names-only `fileutil`
(a second translation, as `lib/durable`) -- against one translation per package. Not attempted.
Because the build fails there, `etc/gates.sh` and `etc/tcb-report.py --check --update` (and the
collections) cannot run yet (both need an up-to-date build).

### Checks run

- `etc/gen-init.py --check`: up to date. `etc/gen-specs-pkginit.py --check`: up to date.
- `etc/api-check.py --check` for every `etc/api/*.txt`: no errors (after the raft list's additions).
- `etc/goose.py --check`: passes (every project at its pin, the examples' replaces at the etcd pin).
- Interfaces regenerated (`etc/gen-interface.py`): `backend` (the package instances moved to their
  `PkgInit.lean`s), `etcdstart` (`wp_initialize'_res` takes `[ExtSemantics fsExt] [FsSemOk] [HasExt
  fsExt]`: the cause above, visible in the API), `raft` (the `<Source>Core` modules); `bbolt` could not
  be regenerated (its check needs the failing adequacy modules built), its only change was
  `DB__grow.grow_rsHi`, now `private`. `--layout`: no new violation in the three regenerated.
- Not run: `etc/gates.sh`, `etc/tcb-report.py --check --update` and the collections (`wal-fsext`, a
  `wal-tester`): they need the full build.

### Next steps

1. The coordinator's decision on the etcd adequacy theorems and `fsExt` (A/B/C above); then the 13
   adequacy files.
2. The full niced `lake build`; `etc/gates.sh`; `etc/tcb-report.py --check --update` (expected: −12
   names-only WAL axioms, −`purgeRound`, −`TouchDirAll`'s, the WAL's `sorry`s gone) and the collections;
   the `bbolt` interface.
3. Re-merge `origin/wal-int` (`etc/wal-lean-remerge.py 8d6f3670d8`; `23c56c7a32` added only notes and
   the fork patch since). A new wal-int file may name `snapRoC`/`snapSize` (here `walSnapRoC`/
   `walSnapSize`) or open `go_etcd_io.etcd.pkg.v3` inside `EtcdGrove` (here `_root_.Perennial....`).

## Session 3 (2026-11-15)

Setup: a fresh worktree (local branch `wal-lean`, from `origin/wal-lean` `227d715e95`), session 2's `.lake`
copied from its worktree.

### The user's decision (A): the etcd examples' closed theorems over the file extension

`fileutil` (with bodies) runs its `init` (the `F_OFD_GETLK` probe through `syscall.FcntlFlock`, over `fsExt`) in
every etcd program's initialization, so the examples' closed theorems run over the file extension now:

- `Proof/.../examples/lib/etcdstart/FsExts.lean` (new): `etcdFsExts = [idIssueExt, fsExt]`, its semantics
  `(idIssue_semantics, Fs.fs_semantics)` (the file extension's own: every `FsStep`, no premise on the
  environment) and ghost state `(idIssue_interp, Fs.fs_interp)`, `HasExt` of both by computation. As the osfs
  programs' results (`fsExts`), with `idIssueExt` kept (the request ids' record the server needs).
- Each theorem: the local instances are `etcdFsExts`'s, the ghost-state bundle's `goosePreGExts` gains the
  file extension's (the universal camera), and the **one new premise** is
  `Hfs : Fs.FsInit (extLocal Fs.fsExt σ.world)` (the file extension's initial state: no process state, nothing
  logged, every file named and on disk with its size bounded, the roots well formed, `RootsOk`), passed as
  `extsInitP`'s file-extension component (`⟨trivial, Hfs, trivial⟩`). The conclusion is unchanged. The proofs
  use none of the extension's start resources (the probe takes no extension step, `wp_getlk`), so no roots
  premise beyond `FsInit`'s is needed.
- Ledger entry (2026-11-15, "the etcd examples' closed theorems"); `TrivialExt.lean`'s header says who uses which.

**For the user's review: the restated closed theorems** (each in `Adequacy*.lean`, restated in the same
directory's `Results.lean` as `..._safe` with the same new premise; old premises otherwise unchanged; old
extensions `[idIssueExt]`, new `[idIssueExt, fsExt]` with `Hfs : FsInit ...`):

| theorem (and its `Results.lean` restatement) | new premise |
|---|---|
| `etcd_putget_adequate` / `etcd_putget_safe` | `Hfs` |
| `etcd_putget3_adequate` / `etcd_putget3_safe` | `Hfs` |
| `etcd_compacted_adequate` / `etcd_compacted_safe` | `Hfs` |
| `etcd_restart1_adequate` / `etcd_restart1_safe` | `Hfs` |
| `etcd_lease_adequate` / `etcd_lease_safe` | `Hfs` |
| `etcd_leasegrant_adequate` / `etcd_leasegrant_safe` | `Hfs` |
| `etcd_leaseexpiry_adequate` / `etcd_leaseexpiry_safe` | `Hfs` |
| `etcd_leasecatchup_adequate` / `etcd_leasecatchup_safe` | `Hfs` |
| `etcd_compactwatch_adequate` / `etcd_compactwatch_safe` | `Hfs` |
| `etcd_txnlin_adequate` / `etcd_txnlin_safe` | `Hfs` |
| `etcd_partition_adequate` / `etcd_partition_safe` | `Hfs` |
| `k8s_compactor_adequate` / `k8s_compactor_safe`, `k8s_compactor_partition_adequate` / `_safe` | `Hfs` |
| `k8s_etcd3_adequate` / `k8s_etcd3_safe`, `k8s_etcd3_cluster_adequate` / `_safe`, `k8s_etcd3_partition_adequate` / `_safe` | `Hfs` |
| (beyond the 13 files named, same cause, not reached by session 2's build because they import `putget`'s or `partition`'s) `etcd_partition_watch_adequate` / `etcd_partition_watch_safe`, `etcd_auth_adequate` / `etcd_auth_safe`, `etcd_auth3_adequate` / `etcd_auth3_safe`, `etcd_watch_adequate` / `etcd_watch_safe`, `etcd_cache_adequate` / `etcd_cache_safe` | `Hfs` |

All build (the full build below).

### Re-merges of `origin/wal-int`

1. `ba70ab7e55` (`b68210672e`): the tester's `Boot`/`Main`, `Create.specFresh`, the tester `Link` (`gen-link
   --wal-tester`), the `NoIoErr` premise, notes. `etc/link_walfs.py`'s conflict resolved: `TESTER` over the part
   `WalTester/` (`OUT`, `ROOT_DIRS`) and the main tree's WAL `Link` (`EXT_LINKS`); the `--durable`/`--wal-tester`
   modes walk `WalTester/`'s specs first; a `Link.lean` under `PROOF_PFX` is skipped unless it is an `EXT_LINKS`
   one. The three WAL links regenerated; collection `wal-tester`'s roots under `WalTester/`.
2. `7fe119fb19` (`b7091da704`), at the coordinator's request: the file-lock semantics (trusted, **pending the
   user's review**: `Impl.lean`'s `OsFd` lock fields, the `FcntlFlock`/`Flock` models, `os.File.Close.spec`'s
   `lockToks`, `fileutil`'s lock tokens), the no-error WAL specs, `link_walfs`'s implicit section variables.
   `Impl.lean`'s one conflict (the `OsFd` docstring) taken from `wal-int`; git paired `LinuxFs/Proof/syscall/
   Flock.lean` with `Proof/os/File__CloseNil.lean` (ours kept; `Flock`'s proof is at `Proof/syscall/Flock.lean`
   via the remerge script). `gen-init` up to date after it (the `fileutil` fact's `Pid' = 0`).

### Repairs

- `Proof/go_etcd_io/etcd/pkg/v3/ioutil/PageWriter__flush.lean`: `word`'s `bv_normalize` fallback realized
  `Iris.HasLC.enumToBitVec` in this module; `k8s/etcd3/parseRV`'s `bv_decide` realizes it too, and the TCB report's
  import of both failed ("environment already contains"). The four bounds now by `rw [h00]; decide`.
- `etc/gen-link.py`: `--server`, `--apply`, `--v3rpc` open `_root_.Perennial.go_etcd_io.etcd.pkg.v3` (session 2
  edited the generated Links, not the generator; `--check` now passes for all 55 modes).
- `WAL.Sync.wp_proofNoErr` (from `wal-int`, written before fork 0006): takes `w.mu` around `sync` as
  `WAL.Sync.wp_proof` does; its spec unchanged.
- **Real bbolt over the lock semantics** (the coordinator's instruction; ledger entry 2026-11-15, "real bbolt's
  `flock.spec` ..."): `flock.spec` (internal) takes `d.flk = none` and returns the locked descriptor with its
  token on `nil`, `d` on an error; `DB.close.spec_owned` (internal) takes `lockToks fd d`, its `funlock` passes the
  `flock` token on and `File.Close` gets both; after `Open`'s `flock` the descriptor is `dbFd i` (`⟨i, true, true,
  none, some true⟩`, `Inv/Locks.lean`) and the token rides with the `path` field in the writer's core
  (`dbPathLk db p fd`); `Open`'s failure paths give it back to `close`. No exported bbolt statement changed.

### Build and checks (end of session 3)

- Full niced `lake build`: **OK** (18398 jobs), after both re-merges and the repairs.
- `etc/goose.py --check`, `etc/gen-init.py --check`, `etc/gen-specs-pkginit.py --check`: up to date.
- `etc/gen-link.py` for every mode (55, the btree's, `--walfs`, `--durable`, `--wal-tester`): no difference.
- TCB: see "TCB" below.
- Interfaces: see below.

### TCB

`etc/tcb-report.py --check --update` (`ef33ef5a5e`; unchanged by the second re-merge and the bbolt repair: the
check after them matches, 895 axioms, 4 sorries -- the 4 `sorry`s are `lean`'s axiomatized-type instances of
bbolt's `Options` and `reflect.Type'`). Against `origin/lean`'s baseline: **removed** `axiom ...storage.wal.opaqueInitsOk`
(the names-only WAL's); against this branch's base also `sorry WAL.ReadAll.wp_proof`. **Added** (all from the
WAL's code on `wal-int`, now in the main trust base): the package-init trust boundaries of the bodied WAL and its
imports (`bufio.opaqueInitsOk`, `hash.crc32.opaqueInitsOk`, `path.filepath.opaqueInitsOk`,
`wal.walFsyncSec_init`/`walWriteBytes_init`/`walWriteSec_init`, `walpb.initFuncsOk`/`opaqueInitsOk`), which now
reach every etcd example's closed theorem (the server's initialization runs the WAL's); the WAL's and tester's
trust-boundary specs (`binary.ReadInt64LE`, `fmt.SprintfWalName`/`SscanfWalName`, `io.ReadFull`,
`proto.MarshalAppendCachedRecord`, `pbRecordC_reg`, `pbSnapC_reg`, `recEncC_ok`, `snapEncC_ok`); and nine
`etcd_wal.*._native.bv_decide.ax_*` (the tester's `bv_decide` calls, `tSaltOf_tEntData` and `u64Acc_step`:
`Lean.ofReduceBool`, the native evaluator trusted -- worth a look: elsewhere this repository avoids it).
Collections: the 16 etcd/k8s example collections gain the WAL's init axioms (updated); `wal-tester`'s baseline
written (its roots under `WalTester/`); `wal-fsext`, `osfs` unchanged; all 60 pass.

### Interfaces

`etc/gen-interface.py` for every `etc/api/*.txt` (absdisk, backend, bbolt, etcdstart, mvcc, raft): only bbolt's
changed (six proof files' interfaces: `DB.Close`, `fdatasync`, `Tx.write` ext over `dbFd`; `dbPathLk`'s
auto-generated congr lemmas in place of `osFd`'s), layout baseline updated (`--layout --update`: no new
violation kind, three `osFd.congr_simp` entries replaced by `dbPathLk.congr_simp`). `etc/api-check.py --check`:
no errors.

### `etc/gates.sh` (after the bbolt repair)

Passes: build, links, tcb (895 axioms, 4 sorries), collections (59 match), goose, gen-init, reader-slot, entsize,
joint-landing, issues, errorf-wrap, errdesc-check, bgcancel, bounds, mode, api, import-all, interfaces,
premisefix, the k8s attack checks. Fixed here: **featuregate** (the allow list's `pkg/v3` pseudo-version was
`lean`'s pin `2eaeb872bce9`; now the branch's `e115818f501d`, same lines) and **mode** (ratchet decrease 316 ->
315 recorded, `--check --update`).

**Still failing (decisions for the coordinator/user: each is a trust-base declaration about `wal-int`'s
trusted WAL specs, which `wal-int` never ran `lean`'s gates on; not papered over here):**
- **axiom-tok** (`--check`): `io.ReadFull.wp_proof` (`Proof/io/ReadFull.lean:28`) produces an `E` atom it does not
  consume (rule 3: needs an `entry` in `etc/axiom-tok-allow.txt` with a reason, or a spec change); the walk of
  `proto.MarshalAppendCachedRecord.wp_proof` truncates at `ownSlice` (needs a `trunc` line, or the checker
  taught `ownSlice`). The selftest fails with it.
- **model-param** (6): `pbRecordC_reg`, `pbSnapC_reg` (the WAL's protobuf model registrations) "not a constant at
  bound variables"; `proto.MarshalAppendCachedRecord.wp_proof`'s model binders `C`/`M` lack a registry premise
  (rule 1); `pbEntryC_reg` has no `Sat` theorem in `PbEntryTypeCore` (rule 7: the extract dropped it, or it must
  move there).
- **pbschema**: `pbRecordC_reg` reaches `WalEnc.recSchema`, not one of `pbSchemaOf`'s (the checker compares
  the trusted schemas with Go's descriptors; walpb's are not in its table).

### What is left before `etc/land.sh`

1. The user's review of the trusted changes pending on this branch: the file-lock semantics (`Impl.lean`,
   the `FcntlFlock`/`Flock` models, `wal-c-locks`), `wal-int`'s earlier pending ones (plan §3), the restated
   closed theorems above, and the `bv_decide` native axioms of the tester.
2. The three failing gates above (entries/registrations, or spec changes, by whoever owns the WAL's trusted
   protobuf specs).
3. A re-merge of `origin/wal-int` if it moves again (`etc/wal-lean-remerge.py 7fe119fb19`).
4. `notes/STATUS.md` (the coordinator integrates), the session registry.

## Session 4 (2026-11-15)

Setup: a fresh worktree (local branch `wal-lean-s4`, pushing to `origin/wal-lean`: session 3's worktree still
holds `wal-lean`), session 3's `.lake` copied from its worktree.

### The three failing gates

- **pbschema.** The WAL's two schemas join `pbSchemaOf`'s table (`PbSchema.lean`, which now imports walpb's
  `Code`): `walpb.Record ↦ WalEnc.recSchema`, `walpb.Snapshot ↦ WalEnc.walSnapSchema`, both moved there from
  `WalPbWire`/`WalPbSnapWire` (same names and lists; `record.proto:8-12`, `:15-20` at the pin `e115818f5`), and
  the WAL's `walCsSchema` (raft's `csSchema` word for word) replaced by `csSchema`. `examples/pbschema`'s
  descriptor test knows the two roots (`known`); it walks `Snapshot.conf_state` to `raftpb.ConfState`.
  `etc/pbschema-check.py` step 6 runs `examples/stdlib/walpb`'s encoder, schema and `MarshalAppend` tests (6).
  Result: `pbschema: ok (10 schemas, roots raftpb.Entry, raftpb.Message, walpb.Record, walpb.Snapshot ...)`.
  `pbMsg` of a walpb type (none exists) reads the real schema instead of `[]`: trusted text, for review.
- **model-param** (the 6 findings):
  - "not a constant at bound variables" (`pbRecordC_reg`, `pbSnapC_reg`): the WAL's instances are defined over
    `{hlc : HasLC}` (their specs, `UnmarshalWalRecord`, `Record.Reset`, ..., are stated at a generic `hlc`), so
    the registration applies them to `HasLC.hasLC`. `etc/ModelParamCheck.lean`'s `closedApp` now accepts
    `Iris.HasLC.hasLC` as a key/value argument, as `regShape` already did for the registry's arguments (the
    heap's later-credit flag, fixed). Restating the instances at `hasLC` would have changed seven spec
    statements; the checker change admits nothing a user can choose.
  - rule 1 (`MarshalAppendCachedRecord`'s `C`/`M`): the premise is now keyed by `I.data.ty`
    (`pbModelOf GF I.data.ty = some I → I.data.ty = walpb.Record.ty → ...`, the same statement; ledger).
  - rule 7: `pbEntryC_sat` (with `optCell_freeze`, `bytesC_freeze`, `treeWp_entryTree`) moved from
    `PbEntryType` into `PbEntryTypeCore`, the registration's module; and new `pbRecordM_sat`, `pbSnapM_sat`
    (with `recCell_freeze`, `recBytesOwn_of`, `treeWp_walCs`), proved (axioms: Lean's three only).
  - `MIN_REGS` 36 -> 38.
- **axiom-tok**: one `entry` (`io.ReadFull.wp_proof`, `3:E:produced1/consumed0`) and one `trunc`
  (`proto.MarshalAppendCachedRecord.wp_proof`, stuck at `ownSlice` as `MarshalAppendPb`'s listed walk), each
  with its reason in `etc/axiom-tok-allow.txt` (**for the user's review**; the `trunc` is an exception to the
  ratchet's "none may be added"). The `io.ReadFull` spec was not changed: `E` is persistent evidence the
  caller's reader gave, passed through; consuming it would be meaningless. Selftest: 0 failures.

### The native axioms

`u64Acc` and its lemmas moved to `WalTester/.../wal/U64Acc.lean` (shared by `DecRep` and `FromRaft`), proved bit
by bit (`BitVec.getLsbD`, `omega`), the masks by `decide +kernel`; `tSaltOf_tEntData` by a fold lemma
(`tSalt_fold`) over `u64Acc_step'`. No `bv_decide` left in the tester: the nine `etcd_wal.*._native.bv_decide`
axioms are gone (tcb baseline and `wal-tester` collection updated).

### Re-merges of `origin/wal-int`

`dbd4495eb5` (`adeabfb2e4`), `32d1f57a80` (`8613a6b7e3`), `95c0f4e3f0` (`685ff8d336`): `etc/wal-lean-remerge.py`
clean for every file but the links (regenerated: `--walfs`, `--durable`, `--wal-tester`) and the ledger (both
sides' entries kept). Next base: `95c0f4e3f0`.

### Build and gates

Full niced `lake build` after the last re-merge: OK (18424 jobs). `etc/gates.sh`: everything passed but tcb,
collections (the nine native axioms gone: updated), axiom-tok (entries above), model-param (`MIN_REGS`) and the
raft interface (regenerated: `PbEntryType`/`PbEntryTypeCore`); all fixed after, gates re-run below.

TCB against `origin/lean`: removed `wal.opaqueInitsOk` (the names-only WAL's); added the bodied WAL's package
inits (`bufio`, `hash.crc32`, `path.filepath` `opaqueInitsOk`, `walFsyncSec_init`, `walWriteBytes_init`,
`walWriteSec_init`, `walpb.initFuncsOk`/`opaqueInitsOk`) and its trust-boundary specs (`binary.ReadInt64LE`,
`fmt.SprintfWalName`/`SscanfWalName`, `io.ReadFull`, `proto.MarshalAppendCachedRecord`, `pbRecordC_reg`,
`pbSnapC_reg`, `recEncC_ok`, `snapEncC_ok`); no native axiom; 4 sorries (lean's).

### What is left before `etc/land.sh`

1. The user's review: the trusted changes pending on this branch (session 3's list), the two `pbSchemaOf`
   entries, and the two axiom-tok allow lines above.
2. A re-merge if `wal-int` moves again (`etc/wal-lean-remerge.py 95c0f4e3f0`).
3. `notes/STATUS.md` (the coordinator), the session registry.
