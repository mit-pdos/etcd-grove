# Plan: the WAL over `fsExt`, the 12 WAL axioms proved against the real code

**Date:** 2026-11-13. **Status:** in progress (coordinator: the session of branch `wal-fsext`; the user
away, decisions delegated). Survey of `lean` at `5fa596b038`. Go source: the pin `0b50f0426` from the
module cache (`~/go/pkg/mod/.../upamanyus/etcd/{server/v3,client/pkg/v3}@v3.0.0-20261112123031-0b50f04262d9`).
**`.lake/go-src/etcd` is stale (at `ce3dbc097`): do not read it.** Abbreviations: S/ =
`server/storage/wal/`, FU/ = `client/pkg/fileutil/`, AD/ = `GooseLang/Ext/AbsDisk/`, FS/ =
`GooseLang/Ext/Fs/`, ST/ = `Proof/go_etcd_io/etcd/server/v3/storage/`, SW/ =
`Spec/go_etcd_io/etcd/server/v3/storage/wal/`.

## 0. Summary

The 12 axioms can be proved over `fsExt` power losses with the client vocabulary unchanged
(`walDiskAt`, `walDirIs`, `walSyncedLb`, `walLenLb`, `walNamed`, `walOpenW`, `walPurgeW`,
`walUnlockedTok`, `walReadCut`, `walImg`). `walDur` stays the ghost state, now held by a WAL-layer
invariant over the real files. The extension, its steps, `WalBodies.lean` and `durableResvD` go.
Six things block this. Four are in the infrastructure, below the WAL; two are code findings.

1. **The tree ghost has no durability.** `TreeCrashed` (FS/CrashFiles.lean:35) lets a crash keep
   *any* prefix of the metadata log, but the semantics' `DirSync` commits everything
   (FS/Impl.lean:727). Without that fact, `walNamed`, `dirDurable`, Create's commit, and the
   survival of synced records past a cut cannot be proved.
2. **Metadata steps need the whole tree history** (`wp_metaStep`, FS/TreeSpecsMeta.lean:245;
   header lines 7-9). So no directory fd may be open and no other path call may be in flight. The
   WAL breaks both rules. It keeps `w.dirFile` open across a cut's rename (S/wal.go:936-940). Its
   file pipeline goroutine creates `N.tmp` files at the same time as the main thread's calls
   (S/file_pipeline.go:75-106, started at S/wal.go:340 and :429).
3. **Locks are not modelled.** `Flock` and `OfdLock` return any errno (FS/Impl.lean:682-685,
   835-838). `unl`, `walPurgeW` and `purgeRound` get their meaning from OFD locks. Without a lock
   model, the `unl` raises in Open and ReleaseLockTo are provable only vacuously, and `purgeRound`
   and the server's purge are unprovable.
4. **The opaque error arms cannot be proved.** The arms `⌜¬ storage.walSaveOk/walCloseOk/walCreateOk⌝`
   (ST/InvOpen.lean:79, 84, 115) say that an I/O error does not happen. A proof that gets an errno
   from `fsExt` cannot produce them.
5. **Reachable panics** in the code at the pin, under `fsExt`'s "any syscall may fail" rule:
   - `NewFileBufReader` panics when `fstat` fails (FU/filereader.go:53; reached by every
     `Open`/VSE/`Repair` through `NewDecoder`).
   - `cleanupWAL` calls `lg.Panic` (S/wal.go:297, :301) after a failed parent fsync in `Create`.
6. **Missing trusted models and specs** (§4.3). Among them, `(*os.File).Close` on a nil receiver
   gets stuck (`model.inner`, LinuxFs/TrustedCode/os.lean:123). `Open`'s error path reaches it
   (S/wal.go:383-386: `w.Close()` → `w.dirFile.Close()` with a nil `dirFile`).

`SectorWhole` is not needed for safety (§2.5). One new premise is needed: **W1**, no CRC32-C
collision on torn data. It is stated over crash candidates, like minibolt's P1.

## 1. Inventory of the 12 axioms

The **steps** column lists the `AbsDiskStep`s the axiom's body performs (AD/Impl.lean:253;
bodies in ST/WalBodies.lean). Under **kill-only** are the parts that only matter for a kill or a
kill followed by a power loss.

| # | Axiom (file) | Pre → post, in one sentence | Steps | Kill-only parts |
|---|---|---|---|---|
| 1 | `wal.Create` (SW/Create.lean:49) | `walAbsent dir` (AU), area `r` durable, token → commit at the rename to `walDurFresh md` (`named=false`); success: `walOpenW`, `walNamed`, `walLenLb 0`, `walSyncedLb 0`, `walPurgeW`; an error before the rename returns the token and the uncommitted AU; after the rename, `¬walCreateOk` | `WalCreate`, `WalNamed` | F-N1 (sync of `dir.tmp` before the rename): under ext4's ordered journal (`TreeCrashed` keeps a prefix) it is not needed, but harmless |
| 2 | `wal.Exist` (SW/Exist.lean:107) | AU over `walDirIs dir o`, unchanged; `false → o = none` | none | none |
| 3 | `wal.Open` (SW/Open.lean:184) | token, AU raising `unl` to `walOpenPos`; success `walOpening w dir s`, error gives the token back | `WalUnlock` | none (the lock reasoning is power-loss neutral) |
| 4 | `wal.Repair` (SW/Repair.lean:240) | AU over `walDirIs`, unchanged; returns some bool | none | "a synced record is never torn" relied on the sector assumption, which is no longer needed (§2.5) |
| 5 | `ValidSnapshotEntries` (SW/ValidSnapshotEntries.lean:306) | token (framed), AU unchanged; success: `walValidSnaps H cut` | none | the docstring's kill-image test only |
| 6 | `Close` (SW/WAL__Close.lean:364) | (a) `walOpenW`+`walPurgeW`, AU syncs `|H|`, success gives the token back, else `¬walCloseOk`; (b) of an opening or failed handle | `WalSync`, close-handle | none |
| 7 | `ReadAll` (SW/WAL__ReadAll.lean:446) | `walOpening`, AU with `s = walNewestPair(walValidSnaps H cut)`; success: `walReadCut H cut = σ`, `walOpenW`, `walNamed`, `walSyncedLb |H|`, `walLenLb`, `walPurgeW`; error `walReadFailed` | `WalNamed`(open), `WalSync` | **F-N4** (fsync of the WAL directory and its parent, S/wal.go:633-639) is kill-then-power-loss; **F-Z** (fdatasync of the zeroing, :626) is **needed under power loss** (§2.4) |
| 8 | `ReleaseLockTo` (SW/WAL__ReleaseLockTo.lean:513) | `walOpenW`, a synced snapshot record of index `a`, AU raising `unl` to `walReleasePos` | `WalUnlock` | none |
| 9 | `Save` (SW/WAL__Save.lean:582) | `walOpenW`, indices < 2^64-1, AU appends `save hs es` before any write; success `walLenLb (|H|+1)`, `walMustSync → walSyncedLb`; else `¬walSaveOk` | `WalAppend`, `WalSync` | none |
| 10 | `SaveSnapshot` (SW/WAL__SaveSnapshot.lean:638) | the same for `snap md`, always synced | `WalAppend`, `WalSync` | none |
| 11 | `Sync` (SW/WAL__Sync.lean:691) | `walLenLb n` → `err = nil -∗ walSyncedLb n` | `WalSync` | none |
| 12 | `fileutil.TouchDirAll` (Spec/.../fileutil/TouchDirAll.lean) | `dirDurable parent`, `d ∉ area`, `walAreaOk r` → success `dirDurable d` | `DirDurable` | none; F-N2's parent fsync is power-loss relevant |

Also kill-only: `walImg`'s kill reading and `walCrash`'s "named kept after a kill" comment
(AD/Impl.lean:141, :223-235). They may stay, since they are more general than needed. The tester's
`purgeRound` axiom (Spec/.../examples/etcd/wal/purgeRound.lean) is not one of the 12, but it sits
on the same layer. Its "unlinks durable out of order" clause is moot under `fsExt`, whose crash
keeps a log prefix, so the unlinks become durable in order.

## 2. The abstraction

### 2.1 Ghost state replacing the extension

There is a per-generation **WAL layer**, `WalGS` (ghost names, given as a typeclass instance the
way `gooseAbsDiskGS` is today, so that the spellings `walDiskAt dir d` stay the same). It owns an
invariant `walInv r` for the area `r`. Inside the invariant:

- `ghostVar γs ½ M` with `M : GMap GoString WalDur`. The program's half is `walOwn M`, with its
  token, as today (AD/Specs.lean:343, :621). The relation `walMapLe` between the program's copy
  and the real map is kept, so the mark and `named` stay lower bounds.
- The past-state authority (`absPastAuth`), so `walSyncedLb`, `walNamed`, `dirDurable` and
  `walLenLb` keep their "fact about a past state" reading. Handle authorities, purge rights and
  the generation's lock token `γu` carry over unchanged from AD/Specs.lean:318-340. They were
  always proof-level ghost state.
- The area's share of the tree: the history `V` restricted to `r` (needs gap 2's region
  resource), with the facts `lookupH R V r = dir`, plus one inode per WAL directory and per segment.
- For each segment inode `i` of each WAL, a record `SegG`: its name `(seq, idx)` (or `N.tmp`), its
  start position `b` in `H`, its intended content `cont = frames(recsOf H [b, e)) ++ zeros`, its
  synced offset `so`, and **half** of its `osMeta i` and of its `osBytes i 0 …`. The other half
  belongs to the handle (the tail) or is also in the invariant (non-tail files).
- Optionally, after gap 3: the lock table share, with the fact that every file holding a position
  `≥ unl` is OFD-locked by one of the handle's fds.

The **static relation** `WalAbs M V FS` says, for each `dir`:
- `M dir = none` iff the current tree has no `.wal` entry under `dir`, or `dir` is absent.
- The `.wal` entries are consecutive by seq. File 0 starts at 0. File `f+1` starts at a
  `walCutPos` (ST/WalDisk.lean:91) and is named `idx ≥ walLastIdx (H.take b) + 1`. This
  name-bound invariant comes from W4a.2. It is now *proved* from `cut`'s naming
  (S/wal.go:891-896) and `w.enti`/`w.snapi`, where it used to be argued in docstrings.
- The bytes of each segment are `cont` below the handle's flushed offset. Above it: zeros, the
  junk left by the last crash, or at most a PageWriter-buffered prefix.
- `d.cut` is the start of the first present file. Every file deleted ends at or before `d.pur`.
- `d.metadata` is the metadata record of every header.

### 2.2 The crash invariant

`CrashOk` is the condition the invariant keeps true, so that every crash decodes into an image of
the history. For every `V'` with `TreeCrashed⁺ V V'`, and every image `f'` of each segment with
`FileCrashedR` (FS/CrashFiles.lean:116) against the invariant's halves, under W1, for each `dir`
with `M dir = some d`, one of these holds:

- `d.named = false` and `dir` is absent in `V'`; or
- the files `V'` names under `dir` are a suffix of the segment list, by seq. **`walDecode`** (a
  pure Lean model of `decoder.decodeRecord`, S/decoder.go:88-155, over the files in name order, the
  CRC chain included) accepts a record prefix `ρ` of the stream, then stops at EOF or an error.
  The ops boundary of `ρ` gives `I` (below) with `walImg d.H d.m I`, and the start of the first
  file gives `k ≤ min d.pur |I|`.

`TreeCrashed⁺` is `TreeCrashed` with the durability lower bound from gap 1.

The map from `ρ` to `I` is not a parse of `ρ`. Record streams are ambiguous at Save boundaries
when the state is empty, so `I` is cut from `H` at `ρ`'s length. Let `|ρ| = |recsOf (H.take j)| + t`
with `t` less than op `j`'s record count. Then:
- `t = 0` gives `H.take j`;
- `t > 0` inside a `save h es` gives `H.take j ++ [.save hsZero (es.take t)]`. A cut never falls in
  the middle of a Save: `walCutPos`.

This is exactly `walImg`'s second disjunct. Both cases need `|ρ| ≥ |recsOf (H.take m)|`, which
holds because every byte of the first `m` ops is durable and the names are committed (gap 1). So
`walImg` is unchanged, and `walCrash` (AD/Impl.lean:223) becomes the *conclusion* of the crash
lemma instead of a trusted relation.

The crash lemma `walInv_crash` replaces `walDiskAt_crash*_keep`. From `walInv` (opened at ⊤ by the
client's crash step) and `crashRest` (FS/CrashTok.lean header: `crashRest_take_runs_keep` per
file, `crashRest_tree`), it builds the next generation's `walInv'` at `M' = crash(M)`. The new
`SegG`s have `cont' = frames(recsOf I) ++ junk`, where junk is the durable bytes after `ρ` (the
first rejected frame, or a zero length field). It gives back `walOwn M'`, a fresh token, and the
old copy unchanged (the W4c Q1 `_keep` form). Determinism of `walDecode` on the now-durable image
is the fact the next generation's `Open`, `ReadAll`, `VSE` and `Repair` rest on. The decoder
returns the same `ρ`, then the same stop.

### 2.3 Encoding facts needed (pure, ST/WalEnc*.lean)

- **Framing** (S/encoder.go:100-108, decoder.go:157-168): `decodeFrameSize ∘ encodeFrameSize =
  id` for lengths `< 2^56`. Padding is 0-7 zero bytes and the pad flag is `0x80|pad` in the top
  byte. An 8-byte zero length field means EOF (decoder.go:95).
- **Record bytes**: `proto.Size`/`MarshalAppend` of `walpb.Record{Type, Crc, Data}` and
  `proto.Unmarshal` round trip (Spec/google_golang_org/protobuf/proto/{SizePb, MarshalAppendPb,
  UnmarshalPb}.lean, D2). New registered models for `walpb.Record` and `walpb.Snapshot`. Entry and
  HardState are already registered for raft.
- **CRC chain**: `pkg/crc` is `crc32.Update` over Castagnoli. `encode` sets `rec.Crc :=
  Sum32()` after `Write(rec.Data)` (encoder.go:73-74), the CRC record included (its Data is nil,
  so Crc = prevCrc). The decoder skips `Write` for CRC records and ReadAll checks `crc == 0 ∨ Crc
  = LastCRC()` (S/wal.go:556-564). So the chain is `crcChain p datas`, a Lean definition of
  CRC32-C. It is trusted as the model of `crc32.Update`; the Go code uses SSE4.2 assembly that
  Goose cannot translate.
- **Stream**: `ioutil.PageWriter` writes the concatenation of its inputs in order through
  `File.Write` at the file offset. Its spec has a ghost pending buffer.
- **Segments**: the records of a file are its headers, `Crc(prev)`, `Metadata md` and
  `State(w.state)` (S/wal.go:909-921; Create: :173-182 with `SaveSnapshot(0,0)`), then the ops'
  records. `w.state = walLastHS (H.take b)` (saveState, ReadAll :645). The tail past the last
  record is preallocated zeros (fallocate: "an extension reads zeros past the old size",
  FS/Impl.lean:122). A cut is: truncate the old tail at the offset and fdatasync (S/wal.go:882-888);
  the headers go into `N.tmp`; fdatasync; rename; fsync `dirFile`.
- **Purge**: unlink of whole files, oldest first. `TreeCrashed` keeps a prefix, so the remaining
  files are a suffix and `nonissues/etcd-wal-purge-unlink-gap.md`'s gap cannot occur.
- `isTornEntry` (decoder.go:170-203) only classifies errors (`ErrUnexpectedEOF` versus a CRC
  error). No safety clause needs it.

### 2.4 Where a power-loss image could make the real code return success with wrong data

1. **A torn frame that passes the CRC** (crc32-C collision), including a torn CRC-typed frame at a
   point where the running CRC is 0 (S/wal.go:558, the unchecked case). **W1** rules it out.
2. **Stale frames brought back.** After a zero length field, ReadAll stops (EOF) and the bytes
   after it may be stale records. If new records overwrite the zero field but the zeroing is lost,
   the stale records pass the chain again. **F-Z's `Fdatasync`** (S/wal.go:626) makes the
   candidates collapse to zeros before any append (`OsFile.synced`). The proof uses it directly,
   which is why F-Z is not kill-only.
3. **A non-suffix file set.** Excluded by `TreeCrashed`'s prefix property; no premise is needed.
4. **A synced record lost behind a rename that did not survive** (a cut's `N.tmp` → `.wal`, or
   Create's `dir.tmp` → `dir`). `cut`'s `dirFile` fsync before any later append, with gap 1, rules
   it out. Create: `walNamed` from the parent fsync.
5. **A wrapped name** (index `2^64-1`): kept as `Save`/`SaveSnapshot`'s premise.
6. **A stale reused `N.tmp`.** `alloc` opens `N.tmp` without `O_TRUNC` (S/file_pipeline.go:78;
   upstream does the same). A crash during a cut leaves `0.tmp` with headers in it. The next
   generation's cut writes new, possibly shorter, headers over it, so *durable stale bytes* follow
   the new headers. A frame of only stale bytes is "durable" and no candidate-based premise can
   tell it apart from a synced one, so W1 does not cover it. Either the proof tracks the stale
   remnant (its first frame is the middle of an old record, accepted only by collision, so W1
   needs a "durable but never synced as this file's stream" clause, which `OsState` cannot
   express), or the fork opens with `O_TRUNC`. See Q3.

Past the synced offset each byte's candidates are `[(0,0)]` or `[(0,0),(x,s)]`, `x` the intended
byte (each offset written once per epoch). This needs no write after a failed write (§3).

### 2.5 `SectorWhole` is not needed

Write-mode `ReadAll` succeeds only at `io.EOF` (S/wal.go:605-608). A torn tail gives
`ErrUnexpectedEOF` or a CRC error, so the read fails, and every read spec allows that.
`Repair`'s spec claims nothing about its boolean. VSE tolerates `ErrUnexpectedEOF`
(S/wal.go:771), but it reads only the accepted prefix `ρ`, and `I` is defined from `ρ`.
`SectorWhole` only affects liveness (whether Repair fixes a torn tail). Do not assume it; update
`notes/STATUS.md`'s "Known limitations".

**W1, stated like P1** (`LinuxFs/Proof/.../bboltfs/BootP1.lean`). At a crash `st → st'`, for each
file under the area and each frame `walDecode` accepts in the image at offset `o`, one of these:
- every byte of the frame has a single candidate (durable); or
- there is a stamp `n > 0` such that, for every byte `j` of the frame, `f'.cache j = valAt
  (f.cand j) n` and `cand j` has a candidate stamped in `(0, n]`. That is, as of one change, every
  byte was written since the last sync.

The second disjunct with the per-byte invariant gives "the accepted frame is the intended frame".
Like P1 it needs a satisfiability lemma (`W1Sat`: a crash keeping everything as synced satisfies
it) and a docstring with its evidence (the W3 decision, the CP1 runs).

## 3. Changes to the statements

Binder changes for all 12:
- `[HasExt absDiskExt]` becomes `[HasExt fsExt] [ExtSemantics fsExt] [FsSemOk]`, plus `os`,
  `syscall` and `unix` `Assumptions`/`FieldAssumptions`, plus `[WalGS GF]`.
- The specs move to `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/` (the part's namespaces;
  the main tree's copies go when `os` is promoted).
- Each `Proof/.../wal/*.lean` axiom becomes a `theorem … .wp_proof` over the callees' specs, and
  `Link.lean` links them.

**Kept verbatim** apart from the binders: `Exist`, `Open`, `VSE`, `ReleaseLockTo`, `Sync`, and
the success arms of all the others. `walReadCut`, `walValidSnaps`, `walOpenPos`, `walReleasePos`,
`walImg` and `WalDur` stay. `walRead` loses its "[trusted meaning]" status, since it becomes plain
vocabulary.

**Must change:**
- **`walAreaOk r`** (ST/WalDisk.lean:194). Today it is `walArea r ∗ durableResvD r`; it becomes
  `walInv r` (persistent) plus ownership of the area's tree region (gap 2). `durableResvD` goes:
  `lib/durable` over `fsExt` uses a disjoint region. `dirDurable d` and `walNamed` are redefined
  over the tree's commit bound (gap 1), with the same reading.
- **The error arms `⌜¬ walSaveOk⌝`, `⌜¬ walCloseOk⌝`, `⌜¬ walCreateOk⌝`** become honest failure
  posts:
  - Save and SaveSnapshot: `∃ d, Q d`. The AU commits before the first write, and the handle,
    its purge right and the token are lost (no `Close`). Writing after a failed write would break
    the per-byte invariant of §2.4, and both the tester (run ends) and etcd (`Fatal`) stop there.
  - Close (a): token lost, as today.
  - Create after the rename: see Q4.

  The opaque premises stay as the *server's* environment premises at C6, used where it calls
  `Fatal`.
- **`Repair`** takes `walUnlockedTok` (framed). With trivial locks its blocking `LockFile`
  (S/repair.go:30-38, FU/lock_linux.go:85-92) waits for nothing, and a concurrent appender would
  race its truncation. Both callers already hold the token: the tester calls Repair after a
  successful `Close` (examples/etcd/wal/wal.go:192-198), and so does `openWALFromSnapshot`. The
  docstring's "blocks until Close" scenario is dropped. Once the lock model (gap 3) exists, the
  token could be made optional again.
- **`Create`** needs a "no other path call in flight" resource for its directory rename
  (S/wal.go:333; `fsExt` gets stuck otherwise, FS/Impl.lean:83-86). It also loses the
  `durableExt`-reservation reasoning in `walCreateRegion`'s docstring.
- **`ReadAll`**: fix I9 of `restart-wal-interface.md` (return `walSaveEnts d.sized`, not `false`;
  SW/WAL__ReadAll.lean:456), since the proof sees the sizes.
- **`TouchDirAll`**: its probe argument (`d/.touch` is never a durable name) now rests on region
  disjointness instead of durable's reservation.
- **`Exist`**: changes only if Q4 picks option (b): `b = false → o = none ∨ o = some d with
  d.H = [] ∧ ¬d.named` (the cleaned-up fresh WAL).

**Clients.**
- **The tester** (`Proof/.../examples/etcd/wal/`, paused W4c):
  - `TInvBody` (Defs.lean:376) keeps `walDirIs`, `walSyncedLb` and `walNamed`. It replaces
    `durableOwnM` by `lib/durable`'s `fsExt` predicate, and `walArea`/`dirDurable` by the new
    definitions, and drops durable's reservation.
  - `tester_crash` (Crash.lean) calls `walInv_crash` in place of the `walDiskAt_crash*_keep`
    family.
  - `purgeRound` becomes a proved spec only with gap 3; until then it cannot be stated without
    absDisk steps.
  - The closed theorem gains W1 and drops `absDiskInitOk` in favour of `FsInit` with the area absent.
- **C6** (`notes/wal-crash-handoff/restart-wal-interface.md`): I1-I11 are unaffected. Gate 2 (a
  WAL present at the start) gets better: `walInv` is established from the initial disk by a
  checkable premise (`WalAbs` of the on-disk bytes and names) instead of `s.wal = ∅`. Gate 8
  (the server's purge) needs gap 3. Gate 9 (the area) becomes region ownership.

## 4. Proof units, hardest first

Effort is in agent-weeks, at the walfs rate (5.5k lines for seglog and dirswap).

### 4.1 Infrastructure (in FS/ and LinuxFs/Proof/os; untrusted unless marked)

| Unit | What | Risk | Effort |
|---|---|---|---|
| I1 | **Tree durability**: a persistent `osTreeCommitLb V n` from `DirSync` success. `TreeCrashed` keeps at least `n` log entries. Updates the crashRest lemmas and walfs/crashlog. | high: it touches the crash interpretation shared with bbolt's port | 1 |
| I2 | **Concurrent path calls and sync-only dir fds**: the tree history in an invariant, with per-call tokens in place of history fractions. Directory renames still exclusive. A dir fd that never reads (`DirPh.blind`) holds no view. Region ownership (subtree of a path) so the WAL, `lib/durable` and bbolt compose. Re-proves FS/TreeSpecs*, LinuxFs/Proof/os/Ns.lean and walfs. | **highest**: a redesign of an API another agent uses | 3-4 |
| I3 | **Multi-file crash invariant**: a map of files' halves, `crashRest` taken for all of them, and files created, renamed and unlinked under the invariant. Generalizes `cfInv`/`csInv` (LinuxFs/Proof/os/CrashFile.lean, CrashSt.lean). | high | 2 |
| I4 | **Large zero runs**: a symbolic `osBytes` over `replicate n (0, [(0,0)])`, or a zero-run resource, for 64 MB segments (CLAUDE.md "Large contexts"). | medium | 0.5 |
| I5 | [trusted] **OFD lock state** in `ProcState`: `SETLK` succeeds only if no other open description holds the inode; close and crash release. `examples/osfs/walfs/linux_test.go` already tests the conflict within one process. | medium; needs the user | 1 + review |

### 4.2 The WAL itself (LinuxFs/Proof/go_etcd_io/etcd/server/v3/storage/wal/)

| # | Unit (Go) | Needs | Risk | Effort |
|---|---|---|---|---|
| W1 | **`walInv`, `WalAbs`, `CrashOk`, `walInv_crash`**, and the pure `walDecode`/`recsOf`/frames lemmas (decode∘encode, the decode of {0,new} images under W1 is a prefix, the prefix gives `walImg`, determinism) | I1-I4, W1's definition | **highest** (the shared invariant) | 3 |
| W2 | **`cut`** (S/wal.go:875-965) with `filePipeline` (open, alloc, run, Close) | Truncate (exists), `File.Seek`/`Write` (Off.lean), `Fdatasync` (exists), Rename of a file (`wp_osRenameFileG`, an `os` spec to write), `dirFile` DirSync (I1), `LockFile` (Open O_WRONLY + FcntlFlock), `Preallocate` (needs a `syscall.Fallocate` model), channels, `fmt.Sprintf("%016x-%016x.wal")` and `"%d.tmp"`; the name bound | high | 2 |
| W3 | **`ReadAll`** (:505-676): decoder loop (`decodeRecord`, `readInt64`/`binary.Read`, `bufio`, `io.ReadFull`, proto Unmarshal, `MustUnmarshal*` panics excluded by W1 + D2), the Go fold ≡ `walReadCut` (W4b's `walReadFrom_eq`/`walReadR_eq_openPos`, WalHistLemmas.lean:1685, :1834), ZeroToEnd (walfs `SegLog.lean` has a prototype), F-Z, F-N4 dir syncs, encoder hand-off | the decoder model of W1, the proto registrations, `binary.Read`/`bufio` specs | high | 3 |
| W4 | **`Create`** (:103-262): `Exist`, `os.RemoveAll` (no model), `CreateDirAll` (TouchDirAll + ReadDir), the first segment, the dir rename (`wp_osRenameDirG`), the parent fsync, `renameWALUnlock` (Open + ReadAll inside), `cleanupWAL` | Q4, Q5 fork fix, I2's exclusive rename | high | 2 |
| W5 | **`Open`/`openAtIndex`/`selectWALFiles`/`openWALFiles`** (:378-490): `readWALNames` (ReadDir, `sort.Strings`, `Sscanf` of `%016x-%016x.wal`: a new shape of Spec/fmt/Sscanf.lean), `searchIndex`'s/`isValidSeq`'s `lg.Panic` shown unreachable, TryLockFile loop, `NewDecoder` (Q5 fstat panic), pipeline start, `walOpenPos` (meaningful only with I5) | | medium-high | 1.5 |
| W6 | `Save`/`saveEntry`/`saveState`/`sync`/encoder/`PageWriter` (:1072-1135, :967-992) | MarshalAppend/Size, crc, `PageWriter` spec | medium | 1.5 |
| W7 | `Repair` (S/repair.go) | decoder (W3), `f.Truncate`, `Fsync`, the `.broken` copy (`io.Copy` → `File.WriteTo`/`ReadFrom`: no models) | medium | 1 |
| W8 | VSE (:698-791) | decoder in read mode, retry loop (dead with the token) | medium | 0.7 |
| W9 | `ReleaseLockTo` (:1002-1044) | trivial without I5; with I5, the name bound over `parseWALName` | low / medium-high | 0.3 / 1 |
| W10 | `Close` (:1046-1070) | `fp.Close`, sync, closing the locks, `dirFile.Close` (the nil model fix) | low-medium | 0.5 |
| W11 | `SaveSnapshot` (:1137-1162), `Sync` (:994) | W6 | low | 0.5 |
| W12 | `Exist` (S/util.go:30-36) | ReadDir with `WithExt`, `filepath.Ext`, readdir's semantics with concurrent changes | low-medium | 0.5 |
| W13 | `fileutil.TouchDirAll` (FU/fileutil.go:49-85) | `os.Stat` of a path (no model: `Exist`, `CheckDirPermission`'s `Mode()`), `os.MkdirAll` (translate the stdlib body), `syncDir` (I1), `IsDirWriteable` (`filepath.Abs`, `os.WriteFile`, Remove) | medium | 1 |

Order: I1 → I2 → I3/I4 (in parallel) → W1 → W2 (cut) → W3 (ReadAll) → W4 (Create) → W5 → W6 →
the rest. W1's pure lemmas (decoder model, decode∘encode, prefix → `walImg`) can start at once,
in parallel with I1-I2, because they need no ghost state. I5 is decided early (Q1). If it is
approved, W5 and W9 are proved with it from the start, not re-proved later.

### 4.3 Missing models and specs (the translating agent will meet these)

**Trusted models** (each with a Go example in `examples/osfs/semantics/`): `syscall.Fallocate`
(only `unix.Fallocate` exists); `syscall.FcntlFlock`, which must return any errno on an unknown
fd, since fileutil's `init` calls it on fd 0 with `F_OFD_GETLK` (FU/lock_linux.go:46-52) and is
stuck today; `os.Stat` of a path; `os.RemoveAll`; `File.WriteTo`/`ReadFrom` (for `io.Copy`);
`fileStat.Mode`; the nil-receiver `File.Close`. **`LinuxFs/Spec/os` specs**: Rename (file, dir),
Remove, Mkdir/MkdirAll, Readdirnames (lemmas in `Ns.lean`), Seek/Read/Write (lemmas in
`Off.lean`), FcntlFlock, Fallocate. **Library specs**: `hash/crc32` (Castagnoli) and `pkg/crc`;
`binary.Read` of `*int64`; `bufio.Reader`, `io.ReadFull`; `fmt.Sscanf`/`Sprintf` hex shapes;
`path/filepath`; `time.Now().Format`; `errors.As` of `*os.LinkError`; `proto.Clone`; prometheus
`Observe`/`Add`; `verify.Assert`.

## 5. Open design questions, with recommendations

- **Q1 (locks).** Should OFD lock state go into `fsExt` (a trusted change, I5)? **Yes; ask the
  user.** Without it `unl` and `walPurgeW` have no content and `purgeRound`/C6's purge cannot be
  proved. The 12 specs themselves do not need it once Repair takes the token. Until the user
  decides, prove the 12 with `unl` as bookkeeping only, and record that the Open and
  ReleaseLockTo raises are vacuous.
- **Q2 (W1's text).** Take §2.5's two-disjunct form (P1-style, stated over `walDecode`), with a
  satisfiability lemma. It is a new world premise, so it goes to the user. It is the formal
  version of the W3-approved "no CRC32-C collision on torn data".
- **Q3 (stale `N.tmp`).** First write a Go test: crash during a cut, restart, a shorter header in
  the reused `0.tmp`, a crash, a restart. If the restart fails (`Repair` gives up on a non-torn
  CRC error over the stale remnant), it is a bug: fix it in the fork (`forceNew = true` in
  `alloc`, S/file_pipeline.go:78) and record an issue. If not, record a nonissue and add a
  "stale durable" clause to W1 (arbitrary data, still within W3's wording). Recommendation: the
  fork fix, which keeps W1 simple.
- **Q4 (Create's failure after the rename).** `cleanupWAL` moves the WAL to `dir.broken.*` after
  the AU has committed. Options:
  - (a) Create takes a second, cleanup AU (`walDiskAt dir fresh → walAbsent dir`) and its arm
    returns that AU's `Q'`.
  - (b) A fresh, unnamed WAL may be absent from the tree, with Exist's `false` arm weakened (§3).

  **Recommend (a)**: it is honest and local, and both clients stop on a Create error anyway.
- **Q5 (the reachable panics).** `NewFileBufReader`'s `panic(err)` on fstat failure, and
  `cleanupWAL`'s `lg.Panic` on a failed Close or rename. **Fork fixes** (return the error; the
  decoder stores the Stat error and returns it from `Decode`), recorded as issues/nonissues
  first. "Failing-Go-test bugs get fork fixes": a test can inject the fstat failure with a
  `FileReader` whose `FileInfo` fails. The alternative is an `fsExt` assumption that `fstat`
  never fails, which goes against the model's "any syscall may fail" rule.
- **Q6 (the error arms).** Replace the opaque `¬walXOk` arms by honest posts (§3). The server
  keeps `walSaveOk` and the rest as its own premises at C6. Not escalated: the posts get weaker
  only on error paths, and every client stops there.
- **Q7 (`Repair` takes the token).** Adopt it. It is minor, both callers comply, and the ledger
  entry goes to `notes/specs-only/ledger.md`.
- **Q8 (where the specs live).** In `LinuxFs/` until the `os` promotion. Keep `ST/WalHist*.lean`
  and `WalViews.lean` in the main tree (pure, importable by both). Delete `WalBodies.lean`, AD/
  and `durableResvD` only when the tester and the server stop importing them.
- **Q9 (sharing I2 with bbolt's port).** I2 changes FS/TreeSpecs*'s statements, which walfs and
  `LinuxFs/Proof/os/Ns.lean` use and bbolt's port may use. Recommend: design I2 as an addition
  (atomic, invariant-friendly variants next to the existing whole-history specs, which are
  derived from them), so the bbolt agent's code keeps building. Tell that agent before landing.
- **Q10 (F-N1, F-N4, F-Z).** Stay, per the decision; the proof uses F-Z (essential) and F-N4
  (for `walNamed`).

## 6. Decisions on §5 (the coordinator, 2026-11-13; the user away, "make decisions autonomously")

Each marked **[user]** is in the user's category (trusted semantics, world premises, fork changes) and
is taken provisionally: it is kept off `lean`'s trust base and off the fork's remote until the user
reviews it.

- **Q1 locks: deferred [user].** No lock state in `fsExt` now. The 12 specs are proved with `unl` as
  bookkeeping (the Open/ReleaseLockTo raises vacuous, said in their docstrings); `purgeRound` and C6's
  purge wait for the user's decision on I5.
- **Q2 W1: adopted provisionally [user]**, in §2.5's two-disjunct form with `W1Sat`. It formalizes the
  approved "no CRC32-C collision on torn data" (W3); the user reviews the text.
- **Q3 stale `N.tmp`: Go test first.** If it fails: a local fork fix (`O_TRUNC` in `alloc`) and an
  `issues/` file **[user: the fork push]**. Otherwise: a nonissue and W1's stale clause.
- **Q4 Create after the rename: (a)**, the cleanup AU.
- **Q5 panics: Go tests, then local fork fixes [user: the push]**, issues/nonissues recorded first.
- **Q6 honest error posts: adopted** (intermediate specs; every client stops on these errors).
- **Q7 `Repair` takes the token: adopted** (ledger entry).
- **Q8 placement: adopted.** The WAL specs and proofs in `LinuxFs/`; the pure vocabulary (`WalHist*`,
  `WalViews`, the new `WalEnc*`) in the main tree.
- **Q9 I2 additive: adopted.** New invariant-friendly specs beside the whole-history ones, which become
  corollaries; nothing the bbolt port uses changes statement.
- **Q10 F-Z/F-N1/F-N4: kept.**
- **Missing trusted models** (§4.3: `syscall.Fallocate`, `syscall.FcntlFlock` including the
  `F_OFD_GETLK` query on any fd, `os.Stat`, `os.RemoveAll`, `File.WriteTo`/`ReadFrom`, `fileStat.Mode`,
  nil-receiver `File.Close`): **drafted provisionally [user]**, each mirroring an existing model where
  one exists (`unix.Fallocate`, `unix.FcntlFlock`) and with its Go example in `examples/osfs/semantics/`;
  on a branch, landed only after review.

## 7. Waves

- **Wave 1** (started 2026-11-13): I1 (tree durability); the pure encoding/decoding layer of W1
  (`walDecode`, frames, decode∘encode, prefix → `walImg`); the Go tests of Q3/Q5 with the local fork
  fixes; the design of I2 (concurrent path calls, blind directory fds, region ownership) as a written,
  reviewed design before code.
- **Wave 2**: I2, I3, I4; the trusted-model drafts; W1's ghost part (`walInv`, `CrashOk`,
  `walInv_crash`).
- **Wave 3**: W2 (`cut`), W3 (`ReadAll`), W4 (`Create`); then W5-W13.

Branches: `wal-fsext-translate` (the with-bodies translation, `5bd96e306a`) is every wave's base until
it lands with the first proofs.

## 8. Wave 1 results (2026-11-13)

- **Translation** (`wal-fsext-translate`, `5bd96e306a`): the WAL, `walpb`, `fileutil` (Linux files),
  `pkg/v3/ioutil` (PageWriter), `pkg/v3/crc` with bodies in `LinuxFs/` (parts of projects `etcd` and
  `raft`: the raft root package's `IsEmptyHardState`/`MustSync` with bodies in a part copy, since the main
  raft root imports the main `os`); `hash/crc32`, `bufio`, `path/filepath` names-only in the part. Gaps:
  §4.3, plus `fileutil` calls `syscall.Fallocate`/`syscall.FcntlFlock` (not `unix`'s) and its package
  init issues `F_OFD_GETLK` on fd 0.
- **I1** (`wal-i1`, `497080aa57`): `osCommitLb n` (persistent) from a successful `DirSync`
  (`wp_osDirSync_lb`; the semantics commits the whole log), `TreeCrashedLb`, `osTreeCrash_take_lb`,
  `lookupH_crashLb`. Statements unchanged, but definitions extended: `OsGS.γcm`, `treeCtx ∗ commitRes`,
  `crashRest ∗ crashCommit` (`Ghost.lean`, `World.lean`, `CrashTok.lean`): **the bbolt port will meet
  merge conflicts there** (repair: the proofs inside `GooseLang/Ext/Fs` that unfold them).
- **Go tests** (`wal-gotests`): three nonissues, `etcd-wal-cut-reuses-stale-tmp` (safe because a cut
  appends nothing before its rename and directory fsync: W1 needs a stale-bytes clause),
  `etcd-fileutil-filebufreader-stat-panic` and `etcd-wal-create-cleanup-panic` (blocks-proof: both).
  **Local fork fixes** on `goose-lean-walfs` (`0fa9710dc` the decoder returns the stat error, `f15d88841`
  `cleanupWAL` returns an error), in `/home/ubuntu/.claude-E/jobs/af0ee947/tmp/etcd-fork` (scratch: copy
  the commits to a durable clone before the job ends). **Not pushed [user].** Until the user pushes them,
  the WAL is translated from that checkout (`etc/goose.py --src etcd=...`) on the WAL branches, and they
  cannot land on `lean` (CI's `goose.py --check` needs the pin on GitHub).
- **Encoding layer** (`wal-enc`, `d607fbfb92`, continuing): `WalEncFrame`, `WalEncDecode`, `WalEncRecs`,
  `WalEncFiles` (main tree, pure, no `sorry`): frame round trip, `walDecode` (the Go decoder and
  `ReadAll`'s CRC check, stop reasons), decode∘encode, the prefix lemma under `NoCollision`,
  `walDecode_walImg`. Next: multi-file stream with cut headers, reads from a later file, the stale clause.
- **I2 design**: `notes/wal-fsext-i2-design.md` (no semantics change; a shared mode entered at a
  `CallBegin`; region ownership; a new per-name ordering premise; ~4 agent-weeks), under independent review.
- Integration branch `wal-int` (notes + translation + I1 + nonissues): wave 2's base.
- **Encoding layer, part 2** (`wal-enc`, `6a3c72dd5e`, merged): `WalEncSegs` (cut headers, decode∘encode
  across files, `walDecodeFiles_streamFiles`), `WalEncSegsImg` (`walDecodeFiles_walImg`: intact earlier
  files and an image of the last give `walImg`), `WalEncSuffix` (`walDecodeFiles_suffix`: the read from a
  later file, CRC 0 start). Open: `(segsOf H cuts).flatten = H`; the fold of `ReadAll` over decoded
  records ≡ `walReadCut` (next unit). **Decision (stale `N.tmp`)**: no fork change (the code is correct,
  `nonissues/etcd-wal-cut-reuses-stale-tmp.md`); the stale clause is proved in W3 from concrete wire
  facts of `walpb.Record`/`HardState`'s marshalling model, which W3 registers anyway.
- **ReadAll's fold** (`wal-fold`, `WalEncFold.lean`, no `sorry`): `readAllFold` (the loop, S/wal.go:505-676,
  over decoded records, abstract `WalUnmarshal` with round-trip laws). From a cut file it is exactly
  `walReadFrom` (`readAllFold_from`, `_complete`: success iff, but for `ErrSnapshotMismatch`); from the first
  file it is the fold at the fixed base `s` (`walReadAt`), equal to `walRead` when `walRead` succeeds under
  `walCommitLe` (`readAllFold_zero_eq`). **Spec deviation** (`readAllFold_zero_dev`): `Save({Term 1, Commit 5},
  [entry 6])`, `SaveSnapshot({5, 1})`, restart at `(5, 1)`: `ReadAll` succeeds with `[entry 6]`, `walRead` is
  `none` (its base is 0 at the entry), so `WAL__ReadAll.spec`'s success post (`walReadCut … = some σ`) is false
  at `cut = 0` without a history premise (`walCommitLe` holds vacuously). `segsOf_flatten` (WalEncSegs).
- **ReadAll's restated post** (`wal-fold`, `WalReadAllPost.lean`, no `sorry`): `walReadAllOk I cut s σ` (∃ k ∈
  [cut, walOpenPos], `s` newest valid from k, `walReadAt I k s = some σ`) in place of `walReadCut … = some σ`.
  Condition `walReadsBack I := walCommitLe I ∧ ∃ σ, walRead I = some σ` (its second half is necessary at k = 0);
  `walReadAt_cut` (k > 0 unconditional), `walReadAllOk_walRead` (clients get `walRead`'s hs/ents under W4b's
  premises). Preserved by `SaveSnapshot` (any) and by `Save` that unfilters no pending snapshot record and
  whose entries apply to the read with commit ≤ last; the received-snapshot `Save` (the one raising the commit
  to the snapshot just saved) is not covered yet. The tester's generator (opEntries/opResend/opRecvSnap) only
  saves entries contiguous with its log, so it never produces the deviating order (CP1 saw none).

## W1 implementation log (branch `wal-inv`, 2026-11-13)

Modules (`LinuxFs/Proof/go_etcd_io/etcd/server/v3/storage/wal/`, namespace `Perennial.EtcdGrove.WalFs`):
`W1` (the premise), `Ghost` (names and vocabulary), `Abs` (layout, `WalAbsD`, `CrashTo`, `CrashOk`),
`Inv` (`walInv`), `Crash` (`walInv_crash`, `walInv_alloc`, the `_keep` lemmas).

**Proved:** every law of the vocabulary (`Ghost`: `walDiskAt_weaken`, `walOwn_excl`, `walDirIs_excl`,
`_mono`, `walOwn_agree`, `walGhost_upd`/`_upd_lag`, `walGhost_init`, ...); `W1Sat`; the frame bounds;
`w1G_of_W1` (W1 over the state gives it over the invariant's ghost candidates); **`walInv_crash`'s Iris
proof** (open with the crash token, `crashRest_region`, the segments, the new generation), over two
pure/FS lemmas; the six `_keep` lemmas with `AbsDisk`'s statements, over `walCrashWal`.
**`sorry`:** `walCrash_pure` (the crash's pure core: `CrashOk` per WAL → `CrashTo` → the crashed
state `s'` with `walStCrash s s'` and the new layouts; the plan is in its docstring and below),
`crashRest_take_files` (I3), `walAbs_crashOk_start` (the new generation's `CrashOk`), `walInv_alloc`.

**Design changes against §2.1-§2.5:**
- *Reuse, not copy*: the generic parts of `AbsDisk/Specs.lean` (`AbsDiskState`, `absLe`, `walMapLe`,
  `walDurLe`, `WalMode`, `walOwnAt`, `absPastAt`/`absPastAuth` and their lemmas, `absDisk_local_init`)
  are imported; `WalGS` wraps an `AbsDiskGS` plus this layer's handle maps and crash token. When `AD/`
  goes, these move into `Ghost.lean`. `walStCrash := absDisk_semantics.crash` (the relation, now a
  conclusion).
- *Crash token*: `walInv` is `inv (body ∨ walCrashTok)`. The crash obligation cannot keep the old
  authorities and close the invariant with them; `walInv_crash` takes the token, closes the invariant
  with it, and hands the old authorities out in `walCrashWal` (the analog of `absDiskCrashWal`), from
  which the `_keep` lemmas convert old facts.
- *Two-phase restart*: the new generation starts in legacy mode (I2), so `walInv_crash` cannot build the
  next `walInv` (it needs claims, which exist only after `wp_osShare`). It returns `walStart` (the ghost
  authorities, every segment's `osFileStartO`, the layouts' static relation over the crashed tree); the
  boot program builds `walInv` with `walInv_alloc` after the switch and `osNames_split`.
- *`CrashTo` is literal*, not only a decode outcome: the kept non-last segments' images are exactly the
  image history's frames, the last one starts with them and the reader stops there. The new
  generation's `WalAbsD` needs literal bytes; the decode outcome follows by the encoding layer
  (`walDecodeFiles_walImg`/`_suffix`). This rests on W1 plus "the byte under a frame of this generation
  is a zero" (`WalAbsD.last`'s `old` clause), which also covers the padding.
- *Fields the crash forced into `WalAbsD`*: `lastSynced` (every segment but the last synced, so the cuts
  survive every crash image), `fit` (`RecsFit`), `tailStop`, and `metas` with `lo = hi = size` (else an
  image byte past the ghost bytes has no ghost candidates and W1 cannot be transported).
- *W1's text* (`W1.lean`): over every directory's `.wal` files in name order, every fresh reader from
  any of them; each accepted frame's **core** (length word and record bytes, not the padding) as of
  the last sync, or as of a change `n > 0` by which each byte was written. **For the review:** the CRC
  covers `Data` only, so a tear confined to the `Type` field passes with no collision; W1 excludes such
  crashes and the CRC evidence does not justify that (the file header says when it matters).
- **I2/I3 API gaps:** (1) `crashRest_take_runs_keep` gives each file its own existential crashed state;
  W1 is a premise over several files at once, so `walInv_crash` needs one state for all segments
  (`crashRest_take_files`, stated here, belongs in `FS/CrashTok.lean`, I3). (2) `crashRest` does not
  relate `st'.fs.treeDur` to `V'` (needed to read W1's directory listing as the crashed tree):
  `crashRest_take_files` states it. I2's statements otherwise fit (`crashRest_region`, `osClaims`).
- *Not yet in `walInv`*: a write in flight (its token, as `cfInv`'s `invRes`), the pipeline's `N.tmp`
  claims, `Create`'s `dir.tmp`; W2-W6 add them.

**`walCrash_pure`'s plan:** per WAL, `w1G_of_W1` (sizes from `FileCrashedR` and `metas`) and `CrashOk`
give `CrashTo`; `s'.wal dir` is `none` (left) or `{d with H := I, cut := segStart (first+q), unl/pur
clamped}` (right), so `walStCrash s s'`; the new layout keeps the cuts, `segs.drop q` with `initMeta` and
`contents.map durB` of each kept file (named in `m'`, so `isSome`), `old` the last image, `wr = so = z0 =
|S'|`. Lemmas needed: `walCutPos` and `walLastIdx` under a prefix of the history, the last segment's
records of `I.take m` a prefix of `I`'s, `RecsFit` of a prefix.

**Third session (branch `wal-int-w1c`, 2026-11-13): `walInv_alloc` proved; the W1 layer has no `sorry`.**
The integration build of `wal-int` needed two fixes: `crashRestAt` (CrashTakeFiles) over I2's
`crashMode` in place of `crashCommit`, and `wp_osPathKind` (models branch) taking `osTree` as its
`LegacyWit`. Statement changes (the five points the coordinator adopted):
- `walInv_alloc`: premises `hV : V.2 = []`, `hcl` (each claim as the boot history has it), `harea : ∃ N h,
  (jr, N, h) ∈ cl ∧ ∀ nm, walNameOk nm → N.Mem nm` (one claim on all the area's WAL names), `hdirs : ∀ nm J,
  walNameOk nm → V.now.entry jr nm = some (.dir J) → ∃ h, (J, .except [], h) ∈ cl` (every directory at a
  WAL name, WAL or not, wholly: `AbsentOk` needs the non-WAL ones too), `hdok : DirsOk R s cl 0`. No
  `osSharedInv` (unused). The commit bound is 0 (`osCommitLb 0`, for free). Returns, beside `walInv` and the
  claims' halves, `∃ Ls, ⌜WalsStart … Ls V.now⌝ ∗ laysRes Ls` (the program's halves of the segments). The
  start's files that are no segment are dropped.
- `walAbs_crashOk_start`: `hj : ∃ h, (lay.j, .except [], h) ∈ cl ∧ h.boot = ents`, `hr : ∃ N h, (lay.jr, N, h)
  ∈ cl ∧ N.Mem lay.nm ∧ h.boot !! lay.nm = some (.dir lay.j)` (any claim on the name, the area's whole one
  included).
- `walStart` records `((segsAll Ls).map (·.ino)).Nodup`; `walCrash_pure` proves it (`crashTo_start` and
  `CrashGood` record each new layout's inodes a sublist of the old one's; `segsAll_nodup_iff`/`_sub`).


## 9. The trusted-model drafts (2026-11-13, branch `wal-models`; pending the user's review [user])

The WAL and fileutil retranslated from the fork's `goose-lean-walfs` (`f15d88841`, the two local fixes
of §8; the pin stays `0b50f0426` until the user pushes them, so `goose.py --check` of project etcd
fails on this branch). Drafted in `LinuxFs/` (each with its Go example in `examples/osfs/semantics/`,
`model_*.go`, indexed in `doc.go`; measurements in `models_test.go`, run on this machine):

- `syscall.Fallocate`: `unix.Fallocate`'s model (`FallocStart`/`FallocFinish`, `FallocKeep`).
- `syscall.FcntlFlock`: `unix.FcntlFlock`'s (`OfdLock`), plus `F_OFD_GETLK` (36) on any fd: no
  extension step, `nil` or any errno, on success arbitrary values in `Type`/`Whence`/`Start`/`Len`/
  `Pid`. Lock state still not modelled (Q1).
- `os.Stat`/`os.Lstat`: an `Open(O_RDONLY|O_CLOEXEC)` + `FdKind` + `Fstat` + close (the extension has
  no path `stat`); mode = type with arbitrary permission/setuid/setgid/sticky bits. `fileStat` gained a
  `mode` field (`File.Stat` stores a regular file's arbitrary mode); `fileStat.Mode`/`IsDir` and
  `FileMode.IsDir`/`Perm` translated.
- `os.MkdirAll`: Go's body over the models, `VolumeName` as 0 (`internal/filepathlite` is translated
  nowhere).
- `os.RemoveAll`: Go's `removeall_at.go` body over paths, a `CallBegin` held for the call (directory
  renames by other threads stuck), passes nondeterministic.
- `(*File).Close` on a nil receiver: `ErrInvalid`. An empty `File.Write`: `(0, nil)` or any errno, no
  step (was a panic). `os.WriteFile` translated.
- Not modelled: `File.WriteTo`/`ReadFrom` (and `io.Copy`, names-only in Perennial's `io`): Go's path
  for `*File`→`*File` is `copy_file_range` (`zero_copy_linux.go`, with fallbacks on ENOSYS/EXDEV/...),
  whose errors are `*os.SyscallError`s; a model needs `io.Copy` translated first (a Perennial change).

Proofs repaired: `LinuxFs/Proof/os/{Base,File__Stat,File__Close,fileStat__Size}.lean` (`ownFileStat`
holds some mode). Nothing proves the new models yet.

## 10. Leaf specs (2026-11-13) and the trust-base additions pending the user's review

- **Encoding leaves** (`wal-leaf-enc`, continuing): CRC-32C as a trusted GooseLang model of `hash/crc32`'s
  `Update`/`MakeTable(Castagnoli)` (`LinuxFs/TrustedCode/hash/crc32.lean`, a Lean `crc32c` checked by
  `decide` on the check vector; Go evidence `examples/stdlib/crc32/`, 20,000 random inputs against
  SSE4.2); `pkg/crc` proved over it. Decided: `walpb.Record`/`Snapshot` registered as raft's messages
  are (`enc_ok` + `pbModelOf`, two axioms each), with a transparent encoder and a Go round-trip test.
- **Standard-library leaves** (`wal-leaf-std`, merged): `bufio` and `path/filepath` (over a part
  `internal/filepathlite`) translated with bodies; `bufio.NewReader` and `Sprintf("%d.tmp")` proved;
  axioms (temporary trust boundary, to be replaced): `io.ReadFull`, `binary.ReadInt64LE`,
  `fmt.SscanfWalName`, `fmt.SprintfWalName` (beyond Perennial's `Sprintf` model, which does not format
  `%0Nx`: a Perennial change to propose), `time.Time.Format`; generated init axioms for bufio's
  `errorRune` and filepath's `SkipDir`/`SkipAll`/`lstat`. Open: `bufio.Reader.Read`'s proof,
  `filepath`'s specs.
- **Per the closed-theorem rule** (no Iris axioms in the end state), the axioms above are to be
  replaced: `io.ReadFull`/`binary.Read` by translations of their Go bodies (Perennial: `io` is
  names-only there), the `fmt` ones by a Perennial `Sprintf`/`Sscanf` model of `%0Nx`, `Time.Format` by
  a model returning any string.

**Pending the user's review (trusted or axiomatic), all off `lean`:** the fork fixes (§8,
`notes/wal-fsext-fork/`); W1 (the crash premise, `LinuxFs/.../wal/W1.lean`; the open question of torn
non-`Data` bytes, under investigation on `wal-bytemix`); the new `os`/`syscall` models and the
`PathKind` query in `GooseLang/Ext/Fs/Impl.lean` (§9, `notes/wal-fsext-models-review.md`); the
crc32 model; the `walpb` registrations; the leaf axioms above; the restated `ReadAll` post
(`notes/specs-only/ledger.md`, 2026-11-13).
**Second session (2026-11-13, branch `wal-inv`).** Proved: `walCrash_pure` (`CrashPure.lean`, with
`WalsStart` moved there; statement unchanged), `crashRest_take_files` (`Crash.lean`, over the new
FS module `GooseLang/Ext/Fs/CrashTakeFiles.lean`), `walAbs_crashOk_start` (`CrashStart.lean`, moved
out of `Abs.lean`; statement unchanged). Left: `walInv_alloc` (`sorry`).
- *Modules*: `SegPre` (pure: the segments of a history agreeing with another up to the last cut,
  `segs_pre`; `walImg_segPre`, `take_segPre`; `walCutPos`/`walLastIdx` under such a prefix);
  `CrashPure` (`crashTo_start`: one WAL's `CrashTo` → `walCrash d (some d')` and the new layout
  `crashLay`; `crashGood_exists`, `walCrash_pure`: the choice per WAL, the maps by `gmapBind`);
  `CrashStart`.
- *Where W1 enters*: only `w1G_of_W1` (called in `crashGood_exists`), feeding `CrashOk`'s `W1G`
  premise. `crashTo_start` and `walAbs_crashOk_start` do not use W1. The "accepted frames are the
  intended frames" step lives in the proofs that each operation keeps `CrashOk` (W2-W6): a narrowed
  W1 changes `W1G`/`w1G_of_W1` and those proofs, nothing here.
- *Definition changes*: `WalAbsD.nonempty` (a WAL has a segment; else `CrashTo` is unprovable);
  `CrashOk` takes "a segment the crashed tree names is there" (`FileCrashedR` allows a missing file);
  `crashRest` (`CrashTok.lean`) records `st'.fs.treeDur = V'.now` (true at `os_local_crash`, kept by
  every take; the three destructurings in `CrashTok.lean` gained a name; no theorem statement moved;
  **the bbolt port may meet a merge conflict there**). `crashRestAt` (`crashRest` with `st`, `st'`
  fixed, `crashRest_at`) gives one crash for several files (`crashRest_take_list`, `FileCrashAt`).
- *`walInv_alloc`'s statement needs rework* (its `hcov` is a placeholder): (1) the claims must cover,
  wholly and with empty histories, each WAL directory (`(lay.j, except [], namesOf V lay.j _)`, whose
  `cur` must be shown `entsOf V.now lay.j`) and the area directory's WAL names (generalize
  `walAbs_crashOk_start`'s `hr` to any claim on `jr` holding `nm` with an empty history: a whole-area
  claim then serves `AbsentOk` too); (2) `DirsOk R s cl 0` is a path-walking fact over the claims, best
  a premise; (3) `walStart` must also record `((segsAll Ls).map (·.ino)).Nodup` (provable in
  `walCrash_pure` from the old one: per-key nodup and cross-key disjointness of `segsAll`, each new
  layout's inodes among its old one's); (4) `osCommitLb 0`; (5) the program's halves of the segments
  are dropped (or returned, once W2 needs them).
- **Leaf units, encoding** (`wal-leaf-enc`, 2026-11-13): `encodeFrameSize` proved (no `sorry`).
  `WalPbWire.lean` (main tree, pure): `walpb.Record`'s wire format as a transparent function (`RecC`,
  `recEnc`, `recSize`, `recEnc_length`), the WAL's record content `recOf` (`Data` nil exactly for a CRC
  record without data: Create/cut build it without `Data`; every other record's data is a `Marshal`
  result, never nil, or the caller's metadata, which the WAL's specs must take non-nil, since a nil
  metadata encodes without field 3), and the two stale-`N.tmp` wire facts: `recEnc_blk` (a record with
  data empty or a block has no two adjacent zeros and a non-zero first byte) and `window_len_or_zeros`
  (a length word read inside such bytes followed by zeros has byte 3 or 4 non-zero, i.e. a length
  `≥ 2^24`, or everything from its byte 3 on is zero). Go check `examples/stdlib/walpb` (encoder, size,
  `MarshalAppend` with `UseCachedSize`, round trip, descriptor). In the part: `walpb.Record` registered
  (`PbRecord.lean`; axioms `recEncC_ok`, `pbRecordC_reg`, **pending review**), the new
  `proto.MarshalAppendCachedRecord.spec` (axiom, **pending review**; stated at `walpb.Record` only: a
  stale size cache changes nested messages' length prefixes), part copies of `InvProto` and of the
  `SizePb`/`MarshalPb`/`UnmarshalPb` axioms, the proto package instance; `walCodec`, `walCodec_ok`
  (`WalCodec.Ok.dec_enc` now only for records under `2^56` bytes, which `decStep_frame` has).
- **Blocker found (import clash)**: the part cannot import anything over the main raft root package
  (`Code.go_etcd_io.raft.v3`), whose names its own raft root copy declares: raft's `Base` (hence the main
  `InvProto`, every main proto spec, `pbMsg`), `PbModel` (`EntryM`, `HardStateM`), so also `WalRecs`,
  `WalHist`, `WalEncRecs`, `WalEncFold`, `WalReadAllPost` and the WAL's specs (`SW/`). The real WAL's
  proofs live in the part, so they cannot state their posts over that layer today, and `WalMarshal`/
  `WalUnmarshal` cannot be instantiated there (Entry's encoder `entryEncC` is in raft's `PbEntryType`).
  Options: (a) give the part no raft root copy (the main raft root's only reason was the main `os`
  import: translate raft's root with the part's `os` mapped, or split `IsEmptyHardState`/`MustSync`
  out); (b) make `PbModel`/`Base`-free cores of the WAL layer (`PbModel` imports the raft root only for
  types: move `EntryM`/`HardStateM`/`SnapshotMetadataM` to a module over `raftpb`); (c) part copies (as
  done here for `InvProto`, cheap only for leaves). (b) for `PbModel` and dropping `InvProto`'s
  `raft.v3.Base` import (it compiles without it: the part copy) are the cheapest, but each rebuilds
  ~1400 main-tree modules. **Decided (coordinator): (b), "raft-free cores"** (branch `wal-rfc`):
  the cores moved to raft-root-free modules re-exported by the old ones, no statement changes.
- **(b) cannot reach the WAL vocabulary** (`wal-rfc`, 2026-11-13, before any edit): `StorContents.base`
  (`NodeApiVocab`) is `entryID`, a Goose struct of the raft root package itself
  (`Code/go_etcd_io/raft/v3.lean:14735`), which the part's raft root copy declares too
  (`LinuxFs/Code/go_etcd_io/raft/v3.lean:2230`, `translate_types = true`); `walFresh`, `walRead`,
  `walReadFrom` (`entryID.mk`), hence `WalRecs`, `WalHist`, `WalEncRecs`, `WalEncFold`, mention it. No
  raft-root-free core of them exists without a statement change. Measured: a module importing
  `LinuxFs.Code.go_etcd_io.raft.v3` and `Code.go_etcd_io.raft.v3.raftpb` builds (raftpb is shared);
  with `Code.go_etcd_io.raft.v3` it fails (`Code.io.fs` vs `LinuxFs.Code.io.fs`). The other edges
  from the WAL vocabulary into the main tree (all would need cores too): `WalRecs` → `InvOpen` (the
  server, backend, bbolt: main `golang.org/x/sys/unix`), `NodeApiVocab`, `Protocol.CommitWit`
  (`phsNext`, `hsZero`), `Protocol.RaftState` (`appendEnts`, over `Plog`); `GooseLang.Ext.AbsDisk.Impl`
  → `PbModel`; `WalHistLemmas` → `WalDisk` → main `walpb` translation (only its `pure` section is
  needed). What does work without statement changes: `PbModel` (raftpb only), and the proto specs
  (`InvProto` drops raft's `Base`; the `proto` package instances move out of `Base`), which would
  retire the part's copies of `InvProto` and the `SizePb`/`MarshalPb`/`UnmarshalPb` axioms. The WAL
  vocabulary needs (a): one raft root for both trees, i.e. a main raft root without the main `os`
  (its only `os` uses are the logger's `os.Stderr`/`os.Exit`: a translation change of the main raft,
  trusted logger models), or the part's `os` becoming the main tree's. **Decided (coordinator, 2026-11-13): part copies** (the
  `RaftWitness` pattern): the pure WAL vocabulary the WAL's code proofs need is copied into `LinuxFs/`
  over the part's raft root, generated by a script with `--check` (no hand-kept duplicates), main modules
  split (re-exported, no statement changes) only where a copy would drag too much; the copies go when
  the `os` promotion dissolves the part. Rejected: (a), a raft trust-base and `Assumptions` change that
  rebuilds everything under other sessions' raft work, with the user away; waiting for the promotion
  (weeks).
- **Part copies carried out** (branch `wal-copies`, 2026-11-13): `etc/gen-part-copies.py` (`--check`:
  a copy differs, or a copy's main-tree import reaches a module the part declares again) writes
  `LinuxFs/<path>` copies, each headed "GENERATED ... from `<path>`". *Whole copies* (imports of copied
  modules and of the part's own translations, `LinuxFs/{Code,GeneratedProof,...}`, pointed at the
  part's): `PbModel`, `AbsDisk/{Impl,Specs}`, `WalHist`, `WalDisk`, `WalHistLemmas`, `WalViews`,
  `WalEnc{Recs,Segs,SegsImg,Suffix,Fold}`, `WalReadAllPost`, and the `proto` vocabulary (`InvProto`
  without raft's `Base`, the `Size`/`Marshal`/`Unmarshal` specs and axioms; the hand-kept copies before).
  *Extracts* (named top-level declarations, verbatim with their docstrings, in a frame of given imports,
  `open`s and `variable`s): `NodeApiVocab`'s `StorContents` (and `.b`/`.last`/`.commit`), `CommitWit`'s
  `hardStateM_countable`/`hsZero`/`phsNext` (+ lemmas), `WalRecs`'s `walFresh`/`walSaveSnap`/
  `walSaveSnap_base_ge` (not the server's ghost state, not the `walFiles` axiom). **No main-tree split**:
  a split of `NodeApiVocab`/`CommitWit`/`RaftState`/`WalRecs` changes their public `.olean` and rebuilds
  2202/2733/4750/1253 modules (`etc/importers.py --count`); an extract rebuilds none. Not copied:
  `walSave` (needs `appendEnts`, `RaftState` over `Protocol.Model`; no WAL module uses it), the
  `StorContents` countable instance (needs raft's `entryID`/`EntryM`/`SnapshotM` instances; unused). The
  modules that do not reach the clash (`WalEncFrame`/`Decode`/`Files`, `WalPbWire`, `AbsDisk/Paths`)
  are imported from the main tree. The W1 layer imports the copies; `wal/ImportCheck.lean` (the WAL
  translation with the vocabulary, the fold, the W1 layer and the `proto` copies) builds. Adding a
  module: append it to `COPIES` (an extract when its imports are heavy). The copies go with the `os`
  promotion.
- **W6, the page writer** (`wal-enc3`, 2026-11-13, no `sorry`): `pkg/v3/ioutil`'s package init in the
  part (`etc/gen-init.py`: `LFS_PKGS` gains `ioutil` and `client/pkg/v3/verify`, the latter generated
  from the main translation, `LFS_MAIN_CODE`, over a part instance, since the main one is in the
  backend's `Base` over the main `os`; `LFS_SPECIAL` for a part package whose main namesake differs;
  fact `ioutilInit`: `defaultBufferBytes ↦□ 131072`). `io.writerStream wi W` (`Proof/io/WriterStream.lean`,
  persistent, the `io.Writer` contract: accepts a prefix of `p`, all unless it errs) and
  `ioutil.ownPageWriter pw wi pend` (ghost buffer `pend`; `pwOk`: the next page boundary fits in the
  buffer, so a full last page of `watermark + pageBytes` bytes is allowed, which `Write` reaches before
  flushing). Proved: `NewPageWriter` (`0 < pageBytes ≤ 128 KiB`, `0 ≤ pageOffset < 2^62`), `flush`,
  `Flush`, `Write` (success: writer's new bytes ++ new buffer = old buffer ++ `xs`; error: buffer empty,
  the writer has a prefix of old buffer ++ `xs`; premise `len(p) < 2^62`, else `len(p) + bufferedBytes`
  overflows). `Write`'s self-call is the fitting case (`ioutil.wp_Write_fits`), so no recursion. Not
  linked yet (no `Link` covers `ioutil`/`crc`). Gotcha: `etc/lean-check.py` reported a kernel
  "application type mismatch" in auxiliary `_proof_` terms of these proofs that `lake build` does not.
- **W6, the encoder: blocked on the `MarshalAppend` axiom's ownership** (open). `encode` passes
  `e.buf[:0]` (1 MiB, reused across calls) to `MarshalAppendCachedRecord`, whose spec consumes the
  buffer's capacity and returns only `b'` (may or may not alias it). The encoder then cannot own
  `e.buf` for the next `encode`. Proposed amendment of that pending axiom (trusted, for the user):
  add to its post `⌜b'.ptr = b.ptr ∧ b'.cap = b.cap⌝ ∨ ∃ ys, b ↦* ys ∗ ownSliceCap w8 b 1` (the old
  array comes back, contents arbitrary, when the result was reallocated; protobuf-go only `append`s,
  so the old array is referenced by nobody else). With it the encoder's invariant owns `e.buf` whole
  and the padding `append` (fits or grows) keeps it. Also needed: `recSize < 2^47` (data below
  `2^46` bytes) for `MarshalAppend`/`Marshal`'s premises.
