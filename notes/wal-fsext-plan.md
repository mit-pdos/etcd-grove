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
