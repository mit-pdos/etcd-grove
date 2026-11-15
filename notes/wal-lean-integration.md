# Plan: the WAL over `fsExt` into the main tree (branch `wal-lean`)

**Date:** 2026-11-15. **Branch:** `wal-lean`, from `origin/wal-int` `87db1a9cf3`, merging `origin/lean`
(merge base `5fa596b038`; `lean` 322 commits past it, `wal-int` 1413). Unit `lean-integration`; log in
`notes/wal-units/lean-integration.md`.

Goal: `wal-int` with `lean` merged and the part `LinuxFs/` dissolved into the main tree's layout, so that
`etc/gates.sh` passes and `etc/land.sh` could land it. `lean` already dissolved the part's `os` layer and
minibolt/crashlog/walfs into the main tree (`003d52e8ff`, "bbolt port, step 0") and put real bbolt on
`fsExt`; what is left is the WAL and what `wal-int` added to the `os` layer since the merge base.

## 1. Inventory (`LinuxFs/` on `wal-int` `87db1a9cf3`: 1126 files)

Classified by `.scr`-scripts over `git ls-tree` of the three commits (base `5fa596b038`, `wal-int`, `lean`).
"Main X" is the path without `LinuxFs/`.

| class | files | on `lean` | resolution |
|---|---|---|---|
| A. the `os` layer and minibolt/crashlog/walfs, hand-written (existed in `LinuxFs/` at the base) | 164 | moved to main X by `003d52e8ff` (lean changed 9 since: `Proof/os/{Base,File__WriteAt}`, `Proof/runtime/PkgInitExt` and 6 others; `wal-int` changed 43) | 3-way merge with base = the base's `LinuxFs/X` with `LinuxFs.` removed; only 3 files changed on both sides (`Proof/os/Base.lean`, `Proof/os/File__WriteAt.lean`, `Proof/runtime/PkgInitExt.lean`, the last generated) |
| B. the WAL's, `walpb`'s, `fileutil`'s, `ioutil`'s, `crc`'s, `bufio`'s, `filepath`'s, `filepathlite`'s, `crc32`'s, the new `os`/`syscall`/`errors`/`fmt`/`proto`/`zap` specs and proofs, the tester's and `lib/durable`'s new files, hand-written, new on `wal-int`, no main X | 692 | absent | plain move to main X |
| C. hand-written, new on `wal-int`, main X exists (the absDisk tester `T/` 29+29 files, `lib/durable/{Read,Write}`, the 11 WAL specs/axioms, `TouchDirAll`'s, `os.Rename`'s spec/proof) | 84 | the main tree's old versions (names-only/absDisk axioms, durableExt) | the part's version replaces main X (U8); `os.Rename`: the part's (lean's main one is the v1 `osFsExt` leftover? checked at stage 2) |
| D. part copies (`etc/gen-part-copies.py`: `PbModel`, extracts of raft's `NodeApiVocab`/`CommitWit`/`InvPb`/`PbContent*`/`PbEntryType`, `WalRecs`, the `Wal*` vocabulary, `AbsDisk/{Impl,Specs}`, `proto` Size/Marshal/Unmarshal/Clone, `time.Duration.Seconds`, zap's specs, the copied axioms) | 55 | main X | deleted; imports `LinuxFs.X` become `X` (the copies sit at main paths, so dropping the prefix redirects them). Where a `Whole` copy differs from its main original by `omit`/`add` (`WalDisk` omits the absDisk `walSnapAt` family that `walpb/PbSnapshot.lean` declares over `walpb.Snapshot`), the main module takes the copy's form; `drop`s and extracts need nothing (the main module is a superset) |
| E. generated: `LinuxFs/{Code,GeneratedProof}` (119 files) and the part's `Init.lean`/`PkgInit.lean` written by `etc/gen-init.py` | ~150 | main tree's (os layer: lean's; WAL: names-only) | deleted, regenerated in the main tree (`etc/goose.py`, `etc/gen-init.py`) after the scripts move |
| F. trusted text: `LinuxFs/TrustedCode/{os,syscall,golang_org/x/sys/unix,hash/crc32,.../walpb}.lean`, `LinuxFs/ManualProof/*`, `LinuxFs/Code/**.toml` | 25 | `os`/`syscall`/`unix`'s at main X, equal to the base's part versions (lean changed no trusted text of the layer but comments of `GooseLang/Ext/Fs/Impl.lean`) | moved; `wal-int`'s changes kept as they are (§3) |

The hand-written part files that redeclare main names at other paths (clash candidates once there is one
tree): `wal/DepsPkgInit.lean` (`True` instances of zap, zapcore, semver, prometheus, pbutil, `hash`, which
the main tree gives in the cache's/lease's/backend's/apply's `Base.lean` and `Proof/hash/PkgInit.lean`),
`proto/PkgInit.lean` (the part's `proto` instance), the part's raft-root init (`raft/v3/{Init,InitPb,PkgInit}`),
`verify/PkgInit.lean`, `Proof/runtime/PkgInitExt.lean`, and the server's `BaseApply.lean:79-86` (`True`
instance of the WAL package, which with bodies has the part's fact). Each: one instance, kept where the
generated init chain wants it (stage 4).

### `lib/durable`: two translations of one package [decision, provisional]

The tester's oracle goes through `examples/lib/durable`; the part translates it **with bodies** over `fsExt`
(W4c U2), the main tree **trusted** over `durableExt`, which kvdurable (20+ files), kvfile and
`etcdstart/DurableExt.lean` use. One module path cannot hold both. Options:
- D1. the bodied `durable` alone in a part, the tester in the main tree (the tester would import a part:
  against the parts' rule "nothing outside imports it");
- **D2 (recommended, done provisionally)**: a small part **`WalTester/`** (modules `WalTester.*`) holding
  `examples/lib/durable` with bodies and the tester `examples/etcd/wal`: their `Code`, `GeneratedProof`,
  `Spec`, `Proof` (goose projects `durable`'s and `etcd-wal`'s parts, root `WalTester`). Nothing in the
  main tree reaches the main `durable` from the WAL side, so the part needs no copies; it imports the main
  tree's `os`, WAL, `fileutil`, raftpb;
- D3. port kvdurable/kvfile/etcdstart onto the bodied `durable`'s specs and retire `durableExt` (several
  sessions; the w4c plan's "later `durableExt` retirement").

D2 until D3. The old absDisk tester (`T/`, `Spec/.../examples/etcd/wal/`, the main `Code/.../examples/etcd/wal`)
goes (U8): it is stated over the WAL axioms the part's proofs replace. **Its `purgeRound` axiom goes with it**
(the w4c plan §6.2 makes retiring that approved axiom a user-review item; the new tester translates
`purgeRound` with its body, so nothing needs the axiom): flagged for the user.

## 2. Mapping (git renames, mirroring `003d52e8ff`)

`LinuxFs/X` → `X` for classes A, B, C, F (and the tester/durable → `WalTester/X`); `LinuxFs.` dropped from
imports and from paths in comments (`LinuxFs/X` → `X`); D and E deleted. Done as one relocation commit on
top of `wal-int` (`git mv`), so that `git merge origin/lean` sees renames on both sides for class A and a
later `git merge origin/wal-int` carries the other agents' edits to `LinuxFs/X` onto `X` (rename detection;
`merge.renameLimit` raised).

## 3. Trusted text: semantic differences

`lean` changed **no trusted text** of the layer since the merge base (its `TrustedCode/{os,syscall,
golang_org/x/sys/unix}.lean`, `Code/{os,syscall,io/fs,internal/poll,internal/syscall/unix,golang_org/x/sys/unix}.toml`
equal the base's `LinuxFs/` versions; `GooseLang/Ext/Fs/Impl.lean`: two comments, the `LinuxFs/` paths).
So there is **no conflict**; the differences are `wal-int`'s, all documented there as pending the user's
review (`notes/wal-fsext-plan.md` §4.3, "io.Copy log", §6 "Missing trusted models"), taken as they are:
- `TrustedCode/os.lean` (+855 lines): models `Stat`/`Lstat` (`model.stat`, `statAbove`, `fileStat`'s
  `name`), `MkdirAll` (`mkdirAllAbove`/`mkdirAllParent`, Go's body with no extension step), `RemoveAll`
  (`removeAllFrom`, unlink/rmdir/open loops over paths instead of `*at` calls), `File.copyFileRange`/
  `File.spliceToFile`/`File.readFrom` (copy_file_range(2) rounds, `pollCopyFileRange`), `rawConn.{Control,
  Read,Write}` (a panic); `os.toml`: those trusted, and Go's bodies translated for `fileStat.{Name,Mode,
  IsDir}`, `WriteFile`, `IsPathSeparator`, `endsWithDot`, `splitPath`, `PathSeparator`, `LinkError.Error`,
  the zero-copy dispatch (`File.ReadFrom`, `WriteTo`, `genericReadFrom`, ..., `SyscallError.*`);
- `TrustedCode/syscall.lean` (+92), `syscall.toml`: `Fallocate`, `FcntlFlock` (F_OFD_GETLK) trusted;
- `io/fs.toml`: `FileMode.IsDir`, `FileMode.Perm`, `ModeDir`, `ModePerm` translated; `internal/poll.toml`:
  `handleCopyFileRangeErr`, `maxCopyFileRangeRound` translated;
- new trusted files: `TrustedCode/hash/crc32.lean` (crc32's table/update), `TrustedCode/.../wal/walpb.lean`
  (walpb's protobuf plumbing), their tomls; `TrustedCode/.../lib/durable.lean` (main, durableExt: docstring
  only, the Go now opens with `os.Open`/`ReadAt`);
- `GooseLang/Ext/Fs/Impl.lean` (+283, main tree on both branches): `wal-int`'s fsExt changes (the names
  ghost, `Zeros`, truncate tails, `SectorAtomic`...), merged with lean's two comment edits.
Each also has its Go example in `examples/osfs/semantics/` (wal-int added 25 `model_*`/`data_*` files).

## 4. What retires (U8, where nothing still needs it)

- the 11 WAL axioms `Proof/go_etcd_io/etcd/server/v3/storage/wal/*.lean` and `fileutil.TouchDirAll`'s: replaced
  by the part's proofs at the same paths (their specs replaced by the part's at the same paths);
- the absDisk tester (`Proof/`/`Spec/.../examples/etcd/wal/`, with `purgeRound`'s axiom) and its
  `Code`/`GeneratedProof` (the tester is `WalTester/`'s);
- `WalBodies.lean` (only the old tester and axioms use it); `WalDisk.lean` takes the part copy's form;
- `etc/gen-part-copies.py`, `etc/tcb-collections/linuxfs.txt` (lean already has `osfs.txt`);
- kept: `GooseLang/Ext/AbsDisk` (the new proofs are stated in `AbsDiskState`/`WalDur`/`walImg`; moving
  them to a pure `WalAbs.lean` and deleting `AbsDiskStep`/`absDiskExt` is a follow-up), `durableExt`,
  the server's use of the WAL (only its package-init instance and `wp_initialize'_lb`; checked at stage 4).

## 5. Scripts

- `etc/goose.py`: projects `etcd`, `durable`, `etcd-wal`, `bboltfs`/`crashlog`/`walfs` lose their `LinuxFs`
  parts. Project etcd translates `wal`, `walpb`, `fileutil`, `ioutil`, `crc` with bodies (the part's tomls
  become the main ones) and `hash/crc32`, `bufio`, `path/filepath`, `internal/filepathlite` into the main
  tree (`lean_roots` `bufio=`, `path/filepath=`, `internal/filepathlite=`; `hash=` covers crc32); raft's
  root package is project raft's (its part copy goes). The etcd pin → `3df9b265f` (fork branch
  `goose-lean-walfs`), the examples' `go.mod`/`go.sum` replaces → its pseudo-version. `durable` and
  `etcd-wal` get a `WalTester` part. Regenerate with the pinned translator; `--check`.
- `etc/gen-init.py`: `LFS_PKGS`/`LFS_SPECIAL`/`LFS_MAIN_CODE` merged into the main configuration (`SPECIAL`)
  replacing the names-only WAL/ioutil/fileutil configurations; `PART_INITS` for `WalTester`.
- `etc/gen-part-copies.py`: deleted (its copies are the originals); `etc/gates.sh`'s call removed.
- `etc/gen-link.py --walfs` (and `etc/link_walfs.py`): paths `LinuxFs/Proof/...` → `Proof/...`; the tester's
  link → `WalTester/`.
- `etc/proof_roots.py`: the `LinuxFs` root goes, `WalTester` comes (as `RaftWitness`).
- `lakefile.toml`: lib `LinuxFs` → lib `WalTester`.
- tcb collections: `wal-fsext.txt` roots → `^Proof/go_etcd_io/etcd/server/v3/storage/wal/`; a `wal-tester.txt`
  for `WalTester/`; `osfs.txt` re-checked; `etc/tcb-baseline.txt` `--check --update` once it builds (−12 WAL
  axioms, −1 `purgeRound`, the part copies' axiom copies are the originals: no change).
- `etc/api/absdisk.txt`, the interfaces: regenerated after the build.

## 6. Stages (each builds its affected leaves, then a commit)

1. **This plan** (commit, push).
2. **Relocation** on `wal-int`: `git mv` by the mapping (§2), prefix removal, part copies and part
   generated files deleted, the old main versions of class C removed. Does not build alone (the main `os`
   on `wal-int` is still the v1 extension's).
3. **Merge `origin/lean`**: generated files take lean's for now; class A by the 3-way rule (§1); the rest by
   hand (`GooseLang/Ext/Fs/Write.lean`: both added pwrite lemmas; notes; `etc/` scripts).
4. **Scripts and regeneration**: `goose.py` (pin, roots, parts), go.mod/go.sum, `--project etcd`, `durable`,
   `etcd-wal`, `bboltfs`, ...; `gen-init.py` (main-tree WAL inits, the instance clash candidates of §1);
   `gen-link.py --walfs`. Build: `Proof.go_etcd_io.etcd.server.v3.storage.wal.Link` and the server's
   `Init`/`BaseApply` leaves.
5. **`WalTester/`**: the tester and `durable` part, its links.
6. **Retire** (§4), `lakefile`, `proof_roots`, tcb collections and baseline, api/interfaces, `CLAUDE.md`,
   `notes/STATUS.md`.
7. **Re-merge `origin/wal-int`** (other agents' later `LinuxFs/` commits arrive as renames), one niced full
   `lake build`, `etc/gates.sh`.

## 7. Carrying `wal-int`'s later commits

Other agents keep committing to `wal-int`'s `LinuxFs/` (the WAL's `Create` cleanup, the tester). `wal-lean`
merges `origin/wal-int` again (stage 7 and any time after): since the relocation is a commit of git
renames, git applies their edits of `LinuxFs/X` to `X` (`git merge -X find-renames=40%` if needed,
`merge.renameLimit=20000`). A file they **add** under `LinuxFs/` lands there and is moved by hand (the
merge's summary lists them); a generated file they change is regenerated. Once `wal-lean` lands, new WAL
work branches off `lean`.

**Procedure (used for `b46dd78a5d`, 2026-11-15).** `git -c merge.renameLimit=30000 merge --no-commit
origin/wal-int`, then `python3 etc/wal-lean-remerge.py <the wal-int commit merged before>` (last: `b46dd78a5d`):
each file `wal-int` changed under `LinuxFs/` is merged 3-way into its main-tree place (base: the previous
`wal-int`'s, prefix dropped) and each new one written there; then regenerate the links (`etc/gen-link.py
--walfs`, `--durable`) and resolve the notes. A new or changed `wal-int` file may need the renames this branch
made: `Spec/Proof os/Rename` -> `os/RenameS` (the fsExt specs), the extracts' sources -> `<Source>Core`
(`NodeApiVocabCore`, `CommitWitCore`, `WalRecsCore`, `InvPbCore`, `PbContentCore`, `PbContentOwnCore`,
`PbEntryTypeCore`), `snapRoC` -> `walSnapRoC`, `snapSize` -> `walSnapSize` (the WAL's walpb snapshot), the part's
`proto/PkgInit`, `raft/v3/{PkgInit,InitPb}` -> raft's `Base`/`Init`, `rootInit` -> raft's `isInitialized`.

## 8. Risks

- **Name clashes** between hand-written part files and main modules that declare the same names
  (package-init instances, §1): show up only at build; each gets one home.
- **The server** (`etcdserver/Init.lean:291`, `BaseApply.lean`) over the bodied WAL's generated init: the
  WAL's `isPkgInit` gains a fact and new dependencies (fileutil, crc, bufio, filepath); its
  `wp_initialize'_lb` position in the server's chain moves (`Hinit.2.2...`). Repair in the server's
  generated/hand-written init.
- **Every etcd package's translation** is regenerated under the new pin (`3df9b265f` touches only `wal`,
  `fileutil`, the tests): expected no diff outside them; checked by `goose.py --check`.
- **Build cost**: the main `Code.go_etcd_io.etcd.server.v3.storage.wal` changes, so the whole server rebuilds
  (`etc/importers.py --count`); one niced full build at the end.
- **Main modules heavier than their part extracts** (`InvPb`, `PbContent`, `NodeApiVocab`, `WalRecs`): the
  WAL's modules now import all of them; build time only.
- `git merge` of lean's 1063 regenerated `Code/` files: resolved by regenerating, never by hand.
