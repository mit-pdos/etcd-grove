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
   express), or the fork opens with `O_TRUNC`. See Q3. **Resolved (2026-11-13):** the fork opens
   `N.tmp` with `O_TRUNC` (item 7; `notes/decisions.md`, "WAL over fsExt: `N.tmp` opened with
   `O_TRUNC`"): no stale bytes, no stale clause.

7. **A torn Type byte** (2026-11-13, `nonissues/etcd-wal-record-type-outside-crc.md`). The CRC
   covers `Data` only; a crash keeping a frame but its Type byte (frame byte 9) gives a record of the
   type under it, CRC valid. Over zeros: type 0, a `ReadAll` error (allowed). Over a stale byte (only
   a reused `N.tmp`'s remnant in the fork; `TestWALTypeTearStaleTmp` builds one): an entry read as a
   hard state or snapshot record, **wrong content with no collision**. W1 as stated excludes it; the
   narrowest justified premise is "an accepted frame carries the intended `Data`" plus `O_TRUNC` in
   `alloc` (or "frame bytes 8-15 come back whole"). Byte-mix enumeration over zero old bytes: no other
   wrong acceptance (3.5 M images). **Decided (2026-11-13):** `O_TRUNC` in `alloc` (fork commit,
   `notes/wal-fsext-fork/0004-*.patch`); the 8-byte-word premise is rejected (it contradicts
   `fsExt`'s per-byte model).

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

**W1's target (2026-11-13, with the fork's `O_TRUNC` in `alloc`):** plain *no CRC-32C collision on the
`Data` of a frame whose bytes under it were zero*. Every byte under a fresh frame is zero (a truncated,
preallocated `N.tmp`, or F-Z's synced zeroing), so a torn non-`Data` byte is the intended byte or 0, and
the byte-mix argument (`nonissues/etcd-wal-record-type-outside-crc.md`, "Why zero old bytes are safe")
turns any acceptance with wrong content into a collision on `Data`. The form above (every byte of an
accepted frame written since the last sync) excludes more than this justifies (a torn Type over 0); its
Lean restatement in `W1.lean` to the narrower target is a later proof unit.

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
  **Revised 2026-11-13:** the test passed (a nonissue), but the torn Type byte over the remnant
  (§2.4 item 7) makes the restart accept wrong content with no collision, so the fork fix is taken
  anyway: `O_TRUNC` in `alloc` **[user: the fork push]**, no stale clause (`notes/decisions.md`, "WAL
  over fsExt: `N.tmp` opened with `O_TRUNC`").
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
  records ≡ `walReadCut` (next unit). **Decision (stale `N.tmp`), superseded 2026-11-13 by the fork's `O_TRUNC` (below, "Fork fix: `O_TRUNC`")**: no fork change (the code is correct,
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
- **Fork fix: `O_TRUNC`** (`wal-otrunc`, 2026-11-13): after the torn-Type finding
  (`nonissues/etcd-wal-record-type-outside-crc.md`, §2.4 item 7), a third local fork commit on
  `goose-lean-walfs`: `alloc` opens `N.tmp` with `O_TRUNC`, with `TestFilePipelineTruncatesStaleTmp` and
  `TestWALTypeTearStaleTmp` rewritten as a regression test (both fail before, pass after). Patches
  `notes/wal-fsext-fork/0003` (the byte-mix tests, which the regression test builds on) and `0004` (the
  fix). **Not pushed [user].** The part's WAL is retranslated from the fork checkout (`--src`); the pin
  stays `0b50f0426`. Supersedes the "no fork change" decision above; W1's target narrows (§2.5).

### Status (2026-11-13, branch `wal-owner`, after `wal-int` `e4df0f9fae` merged)

Everything under `LinuxFs/` and `GooseLang/Ext/Fs/` builds (3019 jobs); `etc/gen-part-copies.py --check` and
`etc/gen-init.py --check` pass. The W1 layer (`Ghost`, `Inv`, `Crash`, `CrashPure`, ...), `CreateAu`'s update
(both arms) and the pipeline have no `sorry`. The remaining `sorry`s of the track (declarations using one, by
module; the bboltfs/crashlog/walfs examples and the generated translations not listed):
- `wal/`: `Create.wp_proof` (`Create.lean`), `Open.wp_proof`, `OpenForRead.wp_proof`, `openAtIndex.wp_proof`,
  `openWALFiles.wp_proof`, `WAL.ReadAll.wp_proof`, `WAL.Save.wp_proof`, `WAL.SaveSnapshot.wp_proof`,
  `WAL.saveEntry.wp_proof`, `WAL.saveState.wp_proof`,
  `WAL.sync.wp_proof`, `wal.tailWriter` (`TailWriter.lean`);
- `fileutil/`: `ReadDir.wp_proof` (`TouchDirAll`/`CreateDirAll` proved, `wal-create7`, over the above-root hypotheses);
- `os/`: `File.Truncate.wp_proofAu` (`File__TruncateAu.lean`), `File.WriteAt.wp_proof_long` (`WriteLong.lean`,
  past 1 GiB).
Not yet stated (no `sorry`, no statement): `Close`, `ReleaseLockTo`, `Repair`, `ValidSnapshotEntries`, `Exist`
(§4.2's W7-W12), the WAL-level resize updates (I3b's open items). `Create`'s ghost steps (drop, mint, unmint, merges) are proved (`wal-create10`; W4 log, tenth session). The record of what is out of the parked state and the changes in flight only on segments out (W3/W5's gaps A and B) are in the invariant, with the pin's and the put-back's moves (`Parked.lean`, `wal-read9`; W1 log, tenth session). A change in flight only on a registered tail (`TailsOnly`), the tails' authority halved with the lock holder (`walTailsFrag`), and `openAtIndex`'s pin (`walInvBody_pin`, `OpenPinTake.lean`) are proved (`wal-read10`; W1 log, eleventh session; W3/W5 log, tenth session). Gap C (every WAL's directory claim once and exclusive, `DirClaimsOk` in `DirKeysOk`), the pin keying its WAL, the put-back (`walInvBody_unpin`), the commit's `unl` raise (`walInvBody_unl`) and the tail's registration (`walTailsRes_register`) are proved (`wal-read11`; W1 log, twelfth session; W3/W5 log, eleventh session).
`Exist` proved over hypotheses (`wal-small12`, W7-W12 log; no `sorry`). Not yet stated (no `sorry`, no statement): `Close`, `ReleaseLockTo`, `Repair`, `ValidSnapshotEntries`
(§4.2's W7-W11), the WAL-level resize updates (I3b's open items). `Create`'s ghost steps (drop, mint, unmint, merges) are proved (`wal-create10`; W4 log, tenth session). The record of what is out of the parked state and the changes in flight only on segments out (W3/W5's gaps A and B) are in the invariant, with the pin's and the put-back's moves (`Parked.lean`, `wal-read9`; W1 log, tenth session). A change in flight only on a registered tail (`TailsOnly`), the tails' authority halved with the lock holder (`walTailsFrag`), and `openAtIndex`'s pin (`walInvBody_pin`, `OpenPinTake.lean`) are proved (`wal-read10`; W1 log, eleventh session; W3/W5 log, tenth session).

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


**Fourth session (branch `wal-nc`, 2026-11-13): `walInv` with Perennial's crash token (§11).** Perennial's
Lean port has no fractional `NC q`/`C`: its crash token is `notCrashed` (whole, owned by the state
interpretation, `gooseBstateInterp`) and the persistent `crashed` (`Perennial/GooseLang/CrashToken.lean`;
`goose_crash_adequacy` hands the old generation's `crashed` to the crash obligation). `crashed` alone cannot
replace the WAL's token in the invariant (it is persistent, so it would not stop `walInv_crash` from finding
the crash branch), so the invariant's second branch holds both:
`walInv := inv walN ((∃ s, walInvBody s) ∨ (crashed (hC := L.goose_crashGS) ∗ walCrashTok))`.
- `walInv_open` (new, `Inv.lean`): `walInv -∗ notCrashed ={E, E \ ↑walN}=∗ (∃ s, walInvBody s) ∗ notCrashed
  ∗ ((∃ s, walInvBody s) ={E \ ↑walN, E}=∗ True)` (`notCrashed_crashed` excludes the crash branch).
- `walInv_crash` takes `crashed` (old generation) beside `walCrashTok`, and closes the invariant with both;
  `walInv_alloc` allocates the new shape; the `_keep` lemmas and `walInvBody_named` are unchanged (not over
  `walInv`).
- **Open (for every W-unit that opens `walInv`):** an operation has `notCrashed` only inside a step (the
  state interpretation), and the `os` specs' atomic updates (`osAU`, `wp_au_step`) are opened by
  `wp_atomic` before the step, without it. Needed: a lifting lemma giving a step's pre-update access to
  `notCrashed` (for a non-value `e`: `(notCrashed -∗ |={E}=> notCrashed ∗ WP e @ E {{Φ}}) ⊢ WP e @ E {{Φ}}`,
  from the WP's unfolding; Perennial) and an `osAU` whose opening receives it (`notCrashed -∗ |={osAuMask,
  ∅}=> α ∗ notCrashed ∗ …`, `LinuxFs/Proof/os/SharedAu.lean`), so that the WAL's update, opened inside the
  `os` update, can call `walInv_open`. Not done here.

**Fifth session (branch `wal-ncau`, 2026-11-13): the open point closed (proved, no axiom).**
- *Lifting* (`GooseLang/Ext/Fs/NotCrashedAcc.lean`): `wp_notCrashed_acc` (non-value `e`, mask kept)
  and `wp_atomic_nc : (notCrashed -∗ |={E1,E2}=> notCrashed ∗ WP e @ s; E2 {{v, |={E2,E1}=> Φ v}}) ⊢
  WP e @ s; E1 {{Φ}}` (`Atomic ↑s e`, `toVal e = none`): iris's `wp_atomic` with the token taken from
  the first step's state interpretation. Proposed upstream (`notes/perennial-changes.md`).
- *`osAUnc`* (`LinuxFs/Proof/os/SharedAu.lean`): a greatest fixpoint whose accessor is `notCrashed -∗
  |={osAuMask, ∅}=> α ∗ notCrashed ∗ ((α ={∅,osAuMask}=∗ osAUnc …) ∧ (∀ o, β o ={∅,osAuMask}=∗ Q o))`;
  `osAU_osAUnc` (every `osAU` is one), `osAUnc_coiter` (how a client builds one), `wp_aunc_step`
  (`wp_au_step` for it, over `wp_atomic_nc`). The token is needed only at the opening: `walInv_open`
  returns it at once, and the invariant stays open across the step until the abort or the commit.
- *`os.Rename.specFileSnc`* (`Spec/os/Rename.lean`): `specFileS` with `osAUnc`; its proof is the old
  one (`wp_au_step` → `wp_aunc_step`), and `specFileS` is now derived from it (statement unchanged).
  The other shared `os` specs (`specDirS`, `Remove`, `Mkdir`, `OpenFile*S`) get the same treatment
  when a W-unit needs them: rename the proof to the `nc` variant and derive the old spec.
- *Test* (`wal/InvOpenTest.lean`): `walN_sub_au` (`↑walN ⊆ osAuMask`); `walInv_osAUnc`, a client update
  that opens `walInv` with `walInv_open` at its opening, reads the area's name from the contents and
  closes it at the abort or the commit; `walToy_rename`, `specFileSnc` with it. **Convention for the
  W-units:** a WAL client update `AU <{…}> @ walAuMask, ∅` is turned into an `osAUnc` by opening
  `walInv` (`osAuMask → walAuMask`) and then the client's update (`walAuMask → ∅`) in `osAUnc`'s
  accessor.

**Sixth session (branch `wal-read3`, 2026-11-13): two `walInvBody` conjuncts for the read path (W3/W5's
gaps 1 and 2), appended last: `⌜WalsNamed Ls cl n⌝ ∗ walParked Ls cl` (`Inv.lean`).**
- *`WalsNamed`*: per layout, in every claim of its directory (`WalDirClaim`) each segment's name is a `.wal`
  name holding the segment's file and every `.wal` entry is a file (`SegsNamed`); after every crash the
  claims allow, the same for the segments the crash kept (`SegsNamedC`, conditional on the inode being among
  `walInos`). `WalsStart` gains `SegsNamed` over the start tree (5th conjunct); `walCrash_pure` takes
  `WalsNamed` and gives it (`crashTo_start`/`CrashGood` now record `lay'.j = lay.j` and each kept segment's
  old name and inode); `walsNamed_start` establishes it at `walInv_alloc`; `walsNamed_mono` (commit bound).
- *`walParked`*: the parking flag `walParkAuth b` (new `WalGS.γpk`, a ghost `Bool`, half the invariant's);
  the program's halves of every segment but the inodes `O` (`segRes`) and of every WAL directory's claim
  (`WalDirClaimOf`) but the claims `D` (`ParkedClaim`, classical `if`); `b = true → O = D = []`. **The lock
  token carries the other half**: `walUnlockedTok := token γu ∗ walParkFrag true`; new `walLockedTok :=
  token γu ∗ walParkFrag false`, which `walHandleP` (so `walOpening`, `walReadFailed`), `walOpenW` and
  `walReadOnlyF` now carry; `walUnlockedTok_lock` (flag to `false`, gives `b = true`: nothing is out, so
  `Open` can take its WAL's halves), `walLockedTok_unlock`. Why the token: `Open`'s only exclusive resource
  is the lock token, so "nothing is out" must be read off it. `walGhost_init` allocates the flag (`walStart`
  gains `walParkAuth true`); `walInv_alloc` deposits the segments' program halves and the WAL directory
  claims' halves; **its statement changed**: it returns `∃ Ls, ⌜WalsStart⌝ ∗ [∗list] c ∈ cl, if
  WalDirClaimOf Ls c then emp else osNames c ½` (no `laysRes`, no WAL-directory claim halves).
- **Obligations for the other units** (their agents merge them):
  - `cut` (W2): the rename keeps `WalsNamed` (the new segment at its name in the new claim history; a crash
    dropping the rename leaves its inode out of `walInos`) and `walParked` (the handle holds the flag
    `false`: it may add the new tail's inode to `O`, take the directory claim out by adding it to `D`, and
    deposits the old tail's halves by dropping its inode from `O`).
  - `Create` (W4): `walOpenW`'s body is now `walHandleSt ∗ walLockedTok`, so `Create` flips the flag
    (`walUnlockedTok_lock`) at an invariant opening. `CreateAu`'s commit keeps both conjuncts in its abort
    arms; **its commit arm has a `sorry`** for them (the new WAL's segment and directory claim out: `g.ino`
    and the claims on `J` into `O`/`D` with the flag `false`, which `walCreateP` must then carry; the area
    claim's new history is no WAL directory's, a third half contradicts).
  - `Close` (W10): parks what the handle holds and returns `walUnlockedTok` (`walLockedTok_unlock`).

**Seventh session (branch `wal-owner`, 2026-11-13; the invariant's owner): `wal-int` as merged built.**
Three modules failed at `497f88bb04` (`wal-save5` merged); fixed:
- `filePipeline__alloc` (136), `checkWALNames` (119): `zap.Logger.{Error,Warn}.spec` take `zapLoggerOk l`
  (premise fixes 6, from `lean`) in place of `⌜l ≠ null⌝`; `wp_apply` frames the `□ zap.loggerRaw` part
  from the persistent `zapLoggerOk lg` and leaves `⌜lg ≠ null⌝`: `iapply zapLoggerOk_ne_null`.
- `TailAcc` (`walInvBody_tail`, W6) did not carry `wal-read3`'s `WalsNamed`/`walParked`. Carried
  (`walsNamed_tail`, `walParked_tail`); the continuation's premise gains `g.name = g0.name` (its two callers in
  `TailWriter`: `rfl`). **`walParked`'s segment entry changed** to `segResP g` (the program's halves of the
  inode's `OsMeta` and of bytes as many as `g.bs`, any contents; `segRes_segResP`): an open handle changes
  its tail's contents in the layout with its halves out, and the parked entry of the tail (out, but not known
  to be out inside the lemma: the program's half that would contradict a parked one is not the lemma's)
  must survive that. Open recovers the exact halves by agreement with the invariant's (`segResF`, idle).

**Seventh session, task 2: the directory-claim map (W2's proposal, as decided).** `Ghost.lean`: `WalGS.γdk`
(ghost map `dir ↦ (j, X)`, persistent elements: `walDirKeysAuth K`, `walDirKey dir j X`, `walDirKey_lookup`,
`walDirKey_insert`) and `WalGS.γcp` (the pending cut: a ghost `Option GoString`, `walCutAuth c` the invariant's
half, `walCutFrag c` the program's; `walCut_agree`, `walCut_set`). **The lock tokens carry `walCutFrag none`**
(`walUnlockedTok`, `walLockedTok`: at most one handle per generation, so one flag; a cut sets it to its directory
at the rename, back at the directory's sync). `walGhost_init` allocates both; `walStart` carries `walDirKeysAuth ∅
∗ walCutAuth none`. `Inv.lean`: `walInvBody`'s new last conjunct `∃ K c, walDirKeysAuth K ∗ walCutAuth c ∗
⌜DirKeysOk C Mr jr s Ls cl n K c⌝`:
```
DirKeysOk … K c :=
  (∀ dir j X, K !! dir = some (j, X) → ∃ lay hj, Ls !! dir = some lay ∧ lay.j = j ∧ j ≠ jr ∧
    (∀ b ∈ X, walNameP b = false) ∧ ClaimOnce (j, .except X, hj) cl ∧ ClaimCoh hj j (.except X) ∧
    ∀ c' ∈ cl, c' ≠ (j, .except X, hj) → c'.1 = j → ∀ b, walNameP b = true → ¬ c'.2.1.Mem b) ∧
  (∀ dir d lay, s.wal !! dir = some d → Ls !! dir = some lay → c ≠ some dir → CrashOkA … d lay none cl n)
```
(the crash clause is over every WAL, keyed or not, so `ReadAll`'s insertion of a key needs no crash argument).
**`CreatingOk`**: the creating map's values are `(N, h, J)` (`walCreating dir N h J`), and each entry carries
`CreatingNew jr cl CR dir N J`: `J ≠ jr`, no claim of `J` among `cl` holds a `.wal` name, no other entry's
directory is `J`, and the area claim leaves out some `.wal` name. All four are facts of the shared invariant at
the token's minting (W4's step at `⊤`: the program holds `J`'s claim and the creating claim `.only [nm, nm.tmp]`
whole); they give the commit `J ≠ j` for every key (a keyed claim holds every `.wal` name) and that the area
claim is no WAL directory's (`walParked`). Established: `walInv_alloc` (`K = ∅`, `c = none`; the crash clause by
`crashOk_start`), carried by `walInvBody_tail` (`dirKeysOk_tail`), `walInvBody_named` (`dirKeysOk_named`,
`crashOkA_none_named`, `crashOkA_mono`), `CreateAu`'s abort arms; `walInv_crash` drops them (a generation's keys
are its own). **For the units**: `cut` (W2) matches its handle's claim half by `walDirKey_lookup` and `DirKeysOk`'s
`ClaimOnce`; at the rename `walCut_set` to `some dir` (the lock token's flag, from `walOpenW`), at the
directory's sync back to `none` with `CrashOkA … none` (`crashOk_dirSync`). `ReadAll` (W3) inserts its WAL's key
(`walDirKey_insert`; its facts from `NamesCoh` at a step at `⊤`, as `Create`'s minting). The handle
(`walHandleIn`) holding `walDirKey dir j X ∗ osNames j (.except X) ½ hj` is left to the units that produce it
(`Create`'s body, `ReadAll`): no proof destructures `walHandleIn` yet.

**Seventh session, task 3: `CreateAu`'s commit arm proved** (no `sorry` left in `CreateAu.lean`). New module
`CreateKeys.lean` (pure, and `walParked_create`): `dirKeysOk_create` (the new WAL keyed `(J, X)`; the others'
claims kept once and exclusive; `crashOkA_none_create_other`), `walsNamed_create`, `parkedClaim_create`,
`walParked_create` (the new segment's inode into `O`, `J`'s claim into `D`; the area claim is no WAL directory's
before or after, since it leaves out a `.wal` name), `walInos_mem`, `segsNamedC_congr_ents`,
`mem_createClaims_cases`. **`walCreate_osAUnc`'s statement changed** (for `wal-create6`):
- `walCreateP` also holds `walLockedTok` (its parking flag `false`: the new WAL's segment and claim stay out,
  the handle's); `walCreateQ` gives it back in both arms, and after the commit also `walDirKey dir J X`;
- two new premises: `hsn : SegsNamed lay.segs hJ.cur` (the segment at its `.wal` name in `J`, every `.wal`
  entry a file) and `hJC : ∀ K E, (∀ b, walNameP b = true → E !! b = hJ.valAfter J K b) → SegsNamedC lay.segs E`
  (the same after any crash of `J`'s claim: every `.wal` value along `hJ`'s history a file, the segment's inode
  only at its name), both of `J`'s history as `Create` made it (`CreateDirAll`, then the one segment).

**The part's WAL package init (branch `wal-nc`, 2026-11-13).** `etc/gen-init.py` generates the
`wp_initialize'` of the WAL's whole import closure in the part (`LFS_PKGS`): the part's `wal`, `walpb`,
`fileutil`, `crc`, `hash/crc32` and raft root package (names-only); the main-tree translations below them
(`LFS_MAIN_CODE`: zap, zapcore, semver, prometheus, pbutil, `hash`, protobuf's pragma/protoreflect/impl/
protoimpl), over the part's own instances (their main instances sit in modules reaching the main raft);
raftpb/quorum/tracker/confchange/proto from `InitPb.lean`, a generated copy of the main raft
`Init.lean`'s theorems (`lfs_raft_initpb`). Facts (`PkgInit.lean`s):
- `wal.walInit`: `walCrcTable` (MakeTable's spec), `wal.metricsInit` (new trust-boundary axioms
  `walFsyncSec_init`/`walWriteSec_init`/`walWriteBytes_init`, as the backend's), `SegmentSizeBytes ↦□
  64000000`, and `wal.errVar X` (an `errOk` error, read-only) for the eight error variables
  (`ErrCRCMismatch` from `walpbInit`). Not `openWALFilesFn`; no distinctness of the errors.
- `walpb.walpbInit`: `ErrCRCMismatch` an `errOk` error.
- `fileutil.fileutilInit`: `∃ ofd, linuxLockFile ↦□ lockFn ofd ∗ linuxTryLockFile ↦□ tryLockFn ofd`
  (**both** outcomes: the `F_OFD_GETLK` probe's errno is arbitrary, `wp_getlk`; `ofd` the same for the
  two), `wrlck` (`Type = F_WRLCK`, `Whence = Start = Len = 0`), `ErrLocked` an `errOk` error.
- The others `True` (the part's raft root too: `emptyState`, which `IsEmptyHardState` reads, would join
  when `Save` needs it). `Create`'s spec can now take `isPkgInit wal`.

**`wal-int` integration fixes (branch `wal-fix`, 2026-11-13).** Proofs only, no statement changed; after them
every module of `LinuxFs` and `GooseLang/Ext/Fs` builds (3052 jobs).
- `checkWALNames`: `wp_apply HWarn` leaves the goal `⌜lg ≠ null⌝` (not `zapLoggerOk lg`): from `zapLoggerOk_ne_null`.
- `ReadDefs`: `walPipeH` takes the directory inode (`walPipeH fp dir j k`): `walReadH`'s write mode holds
  `∃ j, walPipeH fp dir j 0`, the `∃ j` the predicate used to hold (tying it to `walReadTie`'s `j` is left to `ReadAll`).
- `newEncoder`: `e ≠ null` is now last in the post, so `isplitl` (the encoder's resources to the left), not `isplitr`.
**Eighth session (branch `wal-read7`, 2026-11-13): W3/W5's gaps 1 and 3 in the invariant** (the
coordinator's decisions). Both separate; every lemma below builds, no `sorry`.
- *Gap 1, `WalsAt`* (`Inv.lean`, pure, `walInvBody`'s new **last** conjunct `⌜WalsAt jr Ls cl⌝`, after the
  `∃ K c, …` one):
  ```
  WalsAt jr Ls cl := ∀ dir lay, Ls !! dir = some lay → ∀ N h, (jr, N, h) ∈ cl → N.Mem lay.nm →
    h.cur !! lay.nm = some (.dir lay.j)
  ```
  Established by `walInv_alloc` (`walsAt_start`, from `WalsStart`); carried by `walInvBody_tail`
  (`walsAt_insert hl rfl rfl`), `walInvBody_named` (unchanged `Ls`, `cl`), `CreateAu`'s abort arms
  (unchanged) and commit (`walsAt_create`, `CreateKeys.lean`), `cut`'s rename (`CutAu`: `walsAt_repl`,
  `CreateKeys.lean`; the new claim's directory `j ≠ jr` from `DirKeysOk`) and its directory sync
  (`CutSync`: `walsAt_mid hjjr`), `Create`'s drop step (`CreateDropStep`: `walsAt_drop`, the area claim
  losing a non-WAL name). Generic: `walsAt_congr`. **Obligations for `wal-cut7`/`wal-create9`**:
  a proof destructuring `walInvBody` adds `, %HAt` after `⟨%K, %cp, Hdk, Hcp, %Hdko⟩`; one rebuilding it
  wraps the last part as `isplitl [Hdk Hcp]; · iexists K, cp …; ipureintro; exact <WalsAt>`, with
  - `walsAt_insert (hl : Ls !! dir = some lay) (hnm : lay'.nm = lay.nm) (hj : lay'.j = lay.j) : WalsAt jr Ls cl →
    WalsAt jr (<[dir := lay']> Ls) cl`;
  - `walsAt_repl (hA : WalsAt jr Ls cl) (hl) (hnm) (hj) (hc1 : c1.1 ≠ jr) : WalsAt jr (<[dir := lay']> Ls)
    (replClaim c0 c1 cl)`;
  - `walsAt_mid (hne : c'.1 ≠ jr) : WalsAt jr Ls (l1 ++ c :: l2) → WalsAt jr Ls (l1 ++ c' :: l2)`;
  - `walsAt_create (hA) (hok : WalsOk …) (hnew : CreatingNew jr cl CR dir N J) (hin : InArea s.area dir nm)
    (htmp : ¬ walNameOk tmp) (hc : (jr, N, h) ∈ cl) (hothers) (hlay : lay.jr = jr ∧ lay.nm = nm ∧ lay.j = J) :
    WalsAt jr (<[dir := lay]> Ls) (createClaims cl jr N h x (renDirEnt jr tmp nm J st) (renCur N h tmp nm J) J X hJ)`.
- *Gap 3, the pipeline names parked*: `tmpEnt`/`tmpClaim` moved from `Pipe.lean` to `TmpClaim.lean` (over any
  `HeapGS hlc GF`; `walTmpsRes j := [∗list] b ∈ walTmps, tmpClaim j b`). `walParked` gains a **last** sep
  conjunct `walTmpParked Ls b` (`b` its flag):
  ```
  walTmpParked Ls b := ∃ (Jt : GMap GoString Ino) (T : List GoString),
    ⌜(b = true → T = []) ∧ ∀ dir lay, Ls !! dir = some lay → Jt !! dir = some lay.j⌝ ∗
    [∗map] dir ↦ J ∈ Jt, if dir ∈ T then emp else walTmpsRes (hG := ⟨G, L⟩) J
  ```
  Lemmas (`Inv.lean`): `walTmpParked_congr`, `walTmpParked_insert Ls b dir lay lay' hl (hj : lay'.j = lay.j)`
  (tail, cut: `walParked_tail`/`walParked_cut` use it), `walTmpParked_create Ls dir lay` (flag `false`: the new
  WAL's names out, `walParked_create` uses it), `walTmpParked_take Ls dir lay hl : walTmpParked Ls true ⊢
  walTmpParked Ls false ∗ walTmpsRes lay.j` (`Open`, write mode). **Not provided: `Close`'s put-back** —
  turning the flag back to `true` needs `T ⊆ [dir]`, which the invariant does not record (nor `O`, `D` for
  `walParked`'s other parts): `Close`'s design (W10) must track what the handle took. **Obligation for the
  units destructuring `walParked`**: the pattern gains `, Ht` (`⟨%b, %O, %D, Ha, %hb, Hs, Hc, Ht⟩`) and the
  rebuilt one an `isplitl [Hc]` before the tmp part.
- *`walInv_alloc`'s statement changed*: `hdirs` gives each directory at a WAL name the claim `(J, .except
  walTmps, h)` (was `.except []`: the pipeline names are claimed apart, whole); new arguments `Jm : GMap GoString
  Ino`, `hJm : ∀ dir nm J, InArea r dir nm → V.now.entry jr nm = some (.dir J) → Jm !! dir = some J`, and the
  Iris premise `[∗map] _dir ↦ J ∈ Jm, walTmpsRes (hG := ⟨G, L⟩) J` (the boot program's whole claims on each
  WAL directory's `0.tmp`/`1.tmp`, a leftover file whole), deposited. `walAbs_crashOk_start`'s `hj` is now
  `∀ m', RegionCrashed cl n m' → walInos (entsOf m' lay.j) = walInos ents` (`start_walEnt`, `walInos_congr`;
  `Crash.lean` imports `CutSynced`).

**Ninth session (branch `wal-zte2`, 2026-11-13): `WalAbsD` relaxed for the tail's resize window** (the
coordinator's decision of the I3b entry's open item 1; pure, every repaired module builds).
- *The window* is read off the last segment's `OsMeta` half: **`SegExact g := g.om.lo = |g.bs| ∧ g.om.hi =
  |g.bs|`** (a crash leaves the file at its size); a resize opens it (truncate in flight: `lo = tg`; landed:
  `hi` the old size; a growth: `hi` the target, then `lo` the size before), the fdatasync after it closes it
  (`OsMeta.synced`); writes inside the file keep it. No new layout field, no ghost flag.
- *`WalAbsD`* (`Abs.lean`; same twelve fields, so positional patterns still match):
  - `metas`: `size = |bs| ∧ cut = none ∧ lo ≤ |bs| ∧ |bs| ≤ hi ∧ (segs.getLast? = some g ∨ SegExact g)`
    (every segment but the last exact);
  - `last g`: `(SegExact g → TailLast …) ∧ (¬ SegExact g → TailWin …)`. `TailLast` is the old 8-tuple
    unchanged; **`TailWin`** (the window) = `so ≤ wr ∧ wr ≤ |S| ∧ |bs| ≤ |old| ∧ wr ≤ |bs| ∧ ByteOk below wr only
    ∧` the three `z0` facts. Bytes from `wr` on are unconstrained in the window (the coordinator's "zero
    candidates past the stream" is subsumed: a growth's bytes carry the file's candidates past its size, not
    `(y, 0)`, and its page cache is 0, not `old`; `ByteOk` itself unchanged, so `Save`'s `ByteOk.snoc` stands).
  - Accessors: `WalAbsD.lastEx (hex : TailExact lay)` (the old `last`), `WalAbsD.lastWin` (`TailWin`, window
    or not), `WalAbsD.metasEx hex` (the old `metas`); `TailExact lay := ∀ g, getLast? = some g → SegExact g`.
- *`W1G`* takes `(img i).length ≤ bs.length →` (frames of an image longer than the bytes the ghost knows are
  a window crash; `w1G_of_W1` no longer needs a size bound, so `crashGood_exists` holds in a window).
- *Exactness supplied where the crash proofs need it* (statement changes):
  - pure: `crashTo_synced`, `crashOkA_rename`, `cutLay_abs`, `crashOkA_cut` (`hex : TailExact lay`;
    `crashOkA_cut` also `hexg : SegExact g`, the new segment), `crashTo_tail` and `tailCands_of_abs`
    (`hex : SegExact g`), `walAbsD_tail`/`walAbsD_announce`/`walAbsD_finish` (`hex0 : SegExact g0`),
    `crashOk_create_new`/`walsOk_create` (`CreateCommit`) and `dirKeysOk_create` (`hex`/`hexL`);
  - the tail steps' `hzf` (`crashOkA_tail`, `crashOkW_tail`, `walsOk_tail`, `TailAcc`'s two lemmas and
    `walInvBody_tail`'s continuation) is now `(∀ z, …) ∧ SegExact g0 ∧ SegExact g`;
  - `WalsStart`'s, `CrashGood`'s and `crashTo_start`'s last-segment clause, and `walAbs_crashOk_start`'s
    `hlast`: `g.bs = old.map durB ∧ SegExact g` (a crash's files are `initMeta`: exact);
  - **`TailMeta`** (`Handle.lean`, the program's knowledge in `walTailW`) gains `m.lo = m.size ∧ m.hi = m.size`
    (the program writes only outside a window): `TailWriter` derives `SegExact` from it at both steps and keeps
    it (`pwPost` of a write inside the file).
  - **`walCreate_osAUnc`** (`CreateAu`) takes `hgx : SegExact g` (the fresh segment's `OsMeta`, `initMeta`-like);
    **`walCut_osAUnc`** (`CutAu`) takes `hm0x : m0.lo = m0.size ∧ m0.hi = m0.size` (the old tail's `OsMeta` after
    the truncate's fdatasync), `cutCommit_pure` `hex0 : SegExact g0`.
- *Build*: `lake build LinuxFs` at `wal-int` `1ac7232c86` plus this: every module builds but four that fail
  without importing anything changed here (`bufio/Reader__Read` 217/259 "No goals", `wal/DecLemmas` 67,
  `wal/ReadBridge` 79 `iintro` of a non-existential, `wal/checkWALNames` 120 `zapLoggerOk lg` not pure).
- **Obligations**: `Create` (wal-create9): `hgx` for `walCreate_osAUnc`; `TailMeta`'s two new conjuncts where
  `walTailW` is built (`Create`, `ReadAll`: after `ZeroToEnd` and its fdatasync, `OsMeta.synced` has `lo = hi =
  size`). `cut` (wal-cut8): `crashOkA_cut`'s `hex` (the old tail after `cut`'s truncate and sync: exact again
  once the sync's commit sets the invariant's `om` to the synced meta) and `hexg`; `cutLay_abs`'s `hex`.
  Every resize step (`cut`'s truncate, `ZeroToEnd`) commits a layout in the window: `last`'s `TailWin` half
  (`wr ≤ |bs|`: `cut` truncates to `wr`, `ZeroToEnd` to `z0 = wr`), and the sync's commit closing it must
  give `TailLast` again (`|bs| = |old|`: `ReadAll`'s sync re-sets `old` to the zeroed bytes, `cut`'s to the
  truncated ones).

**Ninth session (branch `wal-create10`, 2026-11-13; W4's tenth session): two invariant changes (the
coordinator's decision for the first, mine for the second).**
- *No WAL's directory is the area directory*: folded into **`WalsAt`** (`Inv.lean`), whose per-layout clause is
  now `lay.j ≠ jr ∧ ∀ N h, …` (accessors `WalsAt.ne`, `WalsAt.at`, `WalsAt.not_walDirClaimOf`: a claim of `jr` is
  no WAL directory's claim). Carried: every layout change keeps `lay.j` (`walsAt_congr` checks it); `Create`'s
  commit has `CreatingNew`'s `J ≠ jr` (`walsAt_create`); through the crash, **`WalsStart` gains a last clause**
  `∀ dir lay, Ls !! dir = some lay → lay.j ≠ jr` (so `hst.2.2.2.2` is now `hst.2.2.2.2.1`), which `walCrash_pure`
  proves from a new premise `hjne` (the old invariant's `WalsAt.ne`, passed by `walInv_crash`) and `CrashGood`'s
  `lay'.j = lay.j`; `walsAt_start` reads it. **For the concurrent units**: a use `hA dir lay hl N h hm hN` becomes
  `hA.at hl hm hN`; a new proof of `WalsAt` gives `lay.j ≠ jr` first (`refine ⟨hA.ne hl, fun N h hm hN => ?_⟩`).
- *The creating map holds the free lock token* (`walCreatingAuth`'s non-empty case: `walUnlockedTok`, was
  `walLockedTok`): the parking flag stays `true` while `Create` is between the minting and the rename, so an
  abort (`walInvBody_unmint`) gets the free token back with everything parked (with the flag `false`, nothing
  recorded that `O`, `D`, `T` stayed empty). `walCreating_mint` no longer takes `walParkAuth`;
  `walCreating_delete` gives `walUnlockedTok`; `Create`'s commit takes the lock after the deletion
  (`walParked_lock`, `CreateKeys.lean`: flag to `false`, nothing out, `walTmpParked_unpark`). The drop's
  exclusion is `walUnlockedTok_excl`. `Close`'s exclusion of a non-empty map is `walLockedTok_unlocked_excl`.

**Integration fixes (branch `wal-int2`, 2026-11-13):**
- Merge `wal-zte2` into `wal-int` (with `wal-save8`): `crashTo_tailM` keeps the mark `m0` and takes `hex : SegExact g`;
  `walAbsD_sync` (and `crashOk_sync`, `walsOk_sync`, `dirKeysOk_sync`, `walInvBody_sync`'s success wand) takes
  `hex : SegExact g0` (the synced tail is exact, so its `TailLast` needs the tail exact before the sync; a sync closing
  a resize window is still the obligation above), discharged in `wp_tailFsync` from `TailMeta`'s `lo = hi = size`;
  `TailMeta.synced` gives the two new conjuncts; `wp_tailFsync`'s `hzf` reads `TailMeta`'s third conjunct.
- `checkWALNames` (120): `zap.Logger.Warn`'s precondition is now `zapLoggerOk` (premise-fixes-6): `iexact Hlg`.
- `bufio/Reader__Read` (217, 259), `wal/DecLemmas` (67), `wal/ReadBridge` (79): not merge breakage; a stale
  `Proof/io/ReaderStream` `.olean` in the seeded `.lake` (without `io.readerStream`'s `2 ^ 62` bound). Deleting its
  artifacts and rebuilding fixes all three, with no source change.
- Merge `wal-create10`: notes conflict only; everything builds.

**Tenth session (branch `wal-read9`, 2026-11-13; the invariant's owner): W3/W5's gaps A and B (the
coordinator adopted both logged proposals).** Every module of the WAL directory builds; no `sorry` added.
- *Gap A, the record of what is out* (`Ghost.lean`): **`WalOut`** `{O : List Ino, D : List (Ino × NameSet),
  T : List GoString}` (segment inodes, WAL-directory claims **by key** `(j, N)`, directories whose pipeline
  names are out; `WalOut.empty`, `addSeg`/`delSeg`, `addClaim`/`delClaim`, `addTmp`/`delTmp`), a new ghost
  variable `WalGS.γpo`: `walOutAuth o` (the invariant's half, in `walParked`), `walOutFrag o` (the program's);
  `walOut_agree`, `walOut_set`. **`walUnlockedTok` holds `walOutFrag WalOut.empty`** (4th conjunct);
  `walLockedTok` unchanged (the holder of what is out carries the frag beside it, in its sealed body).
  `walUnlockedTok_lock` also gives `walOutFrag WalOut.empty`; `walLockedTok_unlock` takes it.
  `walGhost_init` allocates it (`walStart` gains `walOutAuth WalOut.empty`). With `wal-create10`'s design
  (the creating map holds `walUnlockedTok`), the record needs nothing in `walCreatingAuth`.
- *`walParked Ls cl F`* (`Inv.lean`; **now takes `F`**): `∃ b o, walParkAuth b ∗ walOutAuth o ∗ ⌜∀ i, F !! i ≠
  none → i ∈ o.O⌝ ∗ segs (but `o.O`) ∗ claims (`ParkedClaim Ls o.D c`: `WalDirClaimOf Ls c ∧ (c.1, c.2.1) ∉ o.D`) ∗
  walTmpParked Ls o.T`. The flag's clause `b = true → …` is gone (the record does its work: the free token's
  empty frag). **Gap B** is the pure clause (a change in flight only on a segment out). `walTmpParked Ls T` takes
  the record's `T` (no flag, no inner `∃ T`); `walTmpParked_take` (`dir ∉ T`, to `dir :: T`), `_create` (to
  `dir :: T`), new `_put` (to `T.filter (· ≠ dir)`).
- *The moves* (new `Parked.lean`, all proved): `walParked_lock` (`walParked Ls cl F -∗ walUnlockedTok ==∗
  walParked Ls cl F ∗ walLockedTok ∗ walOutFrag ∅ ∗ ⌜∀ i, F !! i = none⌝`; replaces `CreateKeys`'s);
  `walParked_unlock` (with `walLockedTok` and `walOutFrag ∅`); `walParked_takeSeg`/`_takeSegs` (segments of
  `segsAll Ls` not in `o.O`, distinct: their `segResP`, `⌜F !! g.ino = none⌝`, frag `⟨S.map ino ++ o.O, …⟩`);
  `walParked_putSeg` (premises `g ∈ segsAll Ls`, the inodes distinct, `F !! g.ino = none`; frag `o.delSeg`);
  `walParked_takeClaim` (`c ∈ cl`, `WalDirClaimOf Ls c`, key `∉ o.D`; its half, `o.addClaim`);
  `walParked_putClaim` (`l1 ++ c :: l2`, no other claim of its key: `DirKeysOk`'s exclusivity; `o.delClaim`);
  `walParked_takeTmps`/`_putTmps`; `walParkedIn` (walParked with `i ∈ o.O`), `walParkedIn_of_fl`,
  `walParkedIn_of_halves` (two halves of `i`'s `OsMeta` outside: a parked one would be a third,
  `osMeta_three_halves`).
- **Obligations for the concurrent units** (statements changed here; their callers in this branch repaired):
  - *the tail's steps (`wal-save*`, `wal-zte*`)*: **`walInvBody_tail … tg m`** takes `(m : OsMeta)` and the premise
    `tailHeld tg m` (`TailAcc.lean`: the caller's half `osMeta tg.i ½ m` while `tg`'s change is `none`, `emp`
    otherwise), given back after the second `tailVar`. Callers: idle `… _ m $$ Hb Hk Hv [Hm1] with ⟨…, Hv', Hm1,
    Hclose⟩` then `· dsimp only [tailHeld]; iexact Hm1` (and `dsimp only [tailHeld]` after); in flight
    `… _ fl.m $$ Hb Hk Hv [] with ⟨…, Hv', -, Hclose⟩` then `· dsimp only [tailHeld]; iempintro`
    (`TailWriter.lean`'s two). A resize supply (`truncSup`/`fallocSup`) passes the `½ m0` it receives.
    `walParked_tail` takes `F F'`, `hF : ∀ i, i ≠ g0.ino → F' !! i = F !! i` and `walParkedIn Ls cl F g0.ino`;
    `walParked_relay` (`TailSync`) and `walParked_cover` (`CreateMergeStep`) take an implicit `{F}`.
  - *`cut` (`wal-cut9`)*: **`walCut_osAUnc`** takes `(o : WalOut)` after `g` and `hoD : (j, NameSet.except X) ∈
    o.D`; `walCutP … g o` holds `walOutFrag o` (after `walParkFrag false`); `walCutQ … g o bt wr`'s commit gives
    `walOutFrag ((o.delSeg i0).addSeg g.ino)`. `walParked_cut … wr F o hl hg0 hnd hino (hkey : c'.1 = c.1 ∧
    c'.2.1 = c.2.1) (hD : (c.1, c.2.1) ∈ o.D) (hF0 : F !! g0.ino = none) : ⊢ walParked Ls (l1 ++ c :: l2) F -∗
    walOutFrag o -∗ segResP g0 ==∗ walParked (<[dir := cutLay …]> Ls) (l1 ++ c' :: l2) (GMap.delete g.ino F) ∗
    walOutFrag ((o.delSeg g0.ino).addSeg g.ino)` (no `walParkFrag`, no `hc'`; `CutAu` passes `⟨rfl, rfl⟩ hoD
    hF0.symm`). `WAL.cut`'s proof gets `o` and `hoD` from the write handle's body (below).
  - *`Create` (`wal-create*`)*: `walCreateQ`'s commit holds **`walOutFrag (WalOut.empty.create g.ino J X dir)`**
    (`WalOut.create o i J X dir := ⟨i :: o.O, (J, .except X) :: o.D, dir :: o.T⟩`, `CreateKeys.lean`), which
    `Create`'s post must put into the new handle's body. `walParked_create Ls cl F o CR … : ⊢ walParked Ls cl F -∗
    walOutFrag o ==∗ walParked … (GMap.delete g.ino F) ∗ walOutFrag (o.create g.ino J X dir)` (no
    `walParkFrag`); `CreateAu`'s commit: `imod walParked_lock (W := W) Ls _ F $$ Hpk HLk with ⟨Hpk, HLk, Ho, -⟩`.
    `CreateDropStep`'s `walUnlocked_park` became `walUnlocked_out` (`o = WalOut.empty` from the free token).
  - *the write handle (`walOpenWF`/`walHandleIn`, `ReadAll`, `Close`)*: its sealed body holds `walOutFrag o` with
    `⌜o = ⟨[tail ino], [(lay.j, .except X)], [dir]⟩⌝` (what it keeps after `ReadAll`'s put-back); `Close` puts
    back with `_putSeg`/`_putClaim`/`_putTmps` and `walParked_unlock`.
- **Open**: putting back the **tail** without a tail record (`openAtIndex`'s error arms, a failed `ReadAll`)
  needs `F !! tail = none`, which no resource of the holder shows (a change starts only through
  `walInvBody_tail`, i.e. on a registered tail, but nothing records that). Proposed: `walTailsRes`'s pure part
  gains `∀ i, F !! i ≠ none → ∃ dir γ, T !! dir = some γ ∧ <dir's last segment>.ino = i` (it has `T`, `Ls`, `F`):
  kept by `walInvBody_tail` (the tail stays last), `cut` (`delete g.ino`, the old tail idle), `Create`.
  The non-tail segments have the same need; the same clause gives them (a change only on a last segment).

**Eleventh session (branch `wal-read10`, 2026-11-14; the coordinator's decision of the tenth session's "Open"):
a change in flight only on a registered tail.** Every importer of `Ghost.lean` builds (93 modules); no `sorry` added.
- *The decided clause* (`Inv.lean`): **`TailsOnly T Ls F := ∀ i, F !! i ≠ none → ∃ dir γ lay g, T !! dir = some γ ∧
  Ls !! dir = some lay ∧ lay.segs.getLast? = some g ∧ g.ino = i`**, `walTailsRes`'s new **second** conjunct:
  `∃ T, walTailsAuth T ∗ ⌜TailsOnly T Ls F⌝ ∗ [∗map] …`. Lemmas: `TailsOnly.none_of_empty`, `.mono_F`, `.insert` (a
  registered WAL's layout replaced: `hF : ∀ i, F' !! i ≠ none → i = g.ino ∨ (F !! i ≠ none ∧ i ≠ g0.ino)`, `g0`/`g`
  the old/new last segments), `.insert_new` (`Create`: `Ls !! dir = none`, `F' ⊆ F`).
- **Deviation (needed to use it): the tails' authority is halved with the lock holder.** The clause alone does not
  let a holder with no tail record conclude `F !! tail = none`: it would need `T !! dir = none`, which no resource
  of the holder shows (the key `dir ↪[γt] γ` is exclusive, its absence is not ownable). So **`walTailsAuth T`** is
  now half of `γt`'s authority (`(1 : Qp).half`), and **`walTailsFrag T`** (new, `Ghost.lean`) the other half: the
  lock token's, empty (**`walUnlockedTok` gains a fifth conjunct `walTailsFrag ∅`**), or the lock holder's, with
  the tails it registered. `walTails_agree`; **`walTailsRes_none`** (`Inv.lean`): `walTailsRes s Ls F -∗
  walTailsFrag ∅ -∗ ⌜∀ i, F !! i = none⌝ ∗ …` (so a holder with the empty half puts back any segment). The
  statement of `walGhost_init` is unchanged (its `walTailsAuth ∅` is the half; the other is in `walUnlockedTok`).
- **Statement changes** (callers in this branch repaired):
  - `walUnlockedTok_lock` gives `walTailsFrag ∅` (fifth); `walLockedTok_unlock` takes it (after `walOutFrag ∅`);
    `walParked_lock … ==∗ walParked … ∗ walLockedTok ∗ walOutFrag ∅ ∗ walTailsFrag ∅ ∗ ⌜∀ i, F !! i = none⌝`;
    `walParked_unlock` takes `walTailsFrag ∅` after `walOutFrag ∅`.
  - `walTailsRes_cut`'s continuation premise gains a fifth conjunct `∀ i, F' !! i ≠ none → i = g.ino ∨ (F !! i ≠
    none ∧ i ≠ g0.ino)` (`CutAu`: from `F' = delete g.ino F` and the old tail idle; `TailSync`'s two: `F' = F`,
    `g.ino = g0.ino`: `fun i hi => if e : i = g0.ino then Or.inl e else Or.inr ⟨hi, e⟩`).
  - `walTailsRes_create` takes `hLd : Ls !! dir = none` and `hF : ∀ i, F' !! i ≠ none → F !! i ≠ none`.
  - `walCreateQ`'s commit (`CreateAu.lean`) holds **`walTailsFrag ∅`** after `walOutFrag (WalOut.empty.create …)`.
- **Obligations for the concurrent units**:
  - *`Create` (`wal-create*`)*: `walCreateQ`'s commit now holds `walTailsFrag ∅` (pattern `⟨HQ, Hm, Hb, HLk, Ho,
    Htf, Hkey, Hp⟩`); `Create`'s post must keep it in the new handle (registering its tail turns it into
    `walTailsFrag {dir ↦ γ}`, below). A proof destructuring `walUnlockedTok` gains a fifth name.
  - *registering a tail* (`ReadAll`, `Create`; no lemma yet): `walTailsAuth T ∗ walTailsFrag T` combine to the
    whole authority (`ghostMapAuth_halves`), `ghost_map_insert` gives the key, split back; `TailsOnly` is kept
    with `T` larger. The handle's body (`walOpenWF`) then holds `walTailsFrag {dir ↦ γ}` beside `walOutFrag`.
    `Close` (W10) deletes the key the same way (the record's `F !! tail = none` from the tail record's idle half:
    `TailsOnly` with `T` back to `∅` needs every change in flight on that tail finished) and unlocks with
    `walTailsFrag ∅`.
  - *a proof destructuring `walTailsRes`*: `⟨%T, HTa, %HTo, HTm⟩`; rebuilding: `iexists T; iframe HTa; isplitr;
    · ipureintro; exact HTo…`.
- **Gap C, found (for the put-back; the invariant's owner)**: the error arms (and `Close`) put the WAL directory's
  claim back at a later step, so they must find it among the invariant's claims `cl'` then, once
  (`walParked_putClaim`'s `l1 ++ c :: l2`, no other of its key). `DirKeysOk` says it only of a WAL with a key
  (`walDirKey`), and the WALs of a new generation have none (`K = ∅` at `walInv_alloc`, the keys made by
  `Create`'s commit and `ReadAll`). Two ways: (a) by fractions, no invariant change — the holder's half and the
  invariant's halves of `cl'` (`osClaims`): a second entry of the same key would be a third half
  (`osNames`' validity), and an entry of that key agrees on the history; if no entry has the key, the half is
  dropped (the record entry goes); (b) the pin makes the key (`walDirKey_insert`), which needs `DirKeysOk`'s
  facts (`ClaimOnce`, no other claim of `j` with a `.wal` name) for a keyless WAL: an invariant clause over every
  present WAL, established by `walInv_alloc` (its claims are the boot program's, distinct). `ReadAll` needs (b)'s
  facts anyway to make its key. Recommended: (b). The segments' put-back has the same shape at a later `Ls'`
  (`walParked_putSeg`'s `g ∈ segsAll Ls'`): by inode and length (`segResP` depends on nothing else), the sizes
  from `WalAbsD.metas` at both ends and the `OsMeta` agreement, or dropped if no segment has the inode.

**Twelfth session (branch `wal-read11`, 2026-11-14; gap C as decided, option (b)).** Every importer of `Ghost.lean`
builds; no `sorry` added.
- *The clause* (`Inv.lean`): **`DirClaimOk jr cl j X hj`** (`j ≠ jr`, `X` no `.wal` name, `ClaimOnce (j, .except X,
  hj) cl`, coherent, no other claim of `j` on a `.wal` name: the keyed clause's facts) and **`DirClaimsOk jr Ls cl :=
  ∀ dir lay, Ls !! dir = some lay → ∃ X hj, DirClaimOk jr cl lay.j X hj`**, **`DirKeysOk`'s third conjunct** (so
  `walInvBody`'s shape is unchanged). Lemmas: `DirClaimOk.eq_of_mem` (a `WalDirClaim` of `j` is that claim),
  `.key_once` (`walParked_putClaim`'s `l1 ++ c :: l2` and no other of its key), `DirClaimsOk.insert`, `.mono_cl`.
  Kept by every `DirKeysOk` step lemma (`_drop`, `_cover`, `_create` (new WAL: the key's facts; others: `j ≠ J`),
  `_named`, `_cut` (cut WAL: the replaced claim; others: `walsOk_dir_ne`), `_cutSynced`, `_sync`, `_tail`).
- **`walInv_alloc` takes `hdirs1`** (new premise; no caller yet): each WAL directory's boot claim `(J, .except
  walTmps, h)` occurs once in `cl` and no other claim of `J` holds a `.wal` name (`dirClaimsOk_start`).
- **The key authority keeps a copy of each key** (`Ghost.lean`): `walDirKeysAuth K := ghostMapAuth γdk 1 K ∗ [∗map]
  dir ↦ x ∈ K, dir ↪□ x`; new `walDirKeysAuth_get` (a holder of the lock finds a key made earlier in the
  generation, e.g. by a `Create` or a `ReadAll` whose handle was closed). `walDirKey_lookup`/`_insert` unchanged.
- **Statement changes** (callers repaired): a proof projecting `DirKeysOk`'s crash clause writes `h.2.1` (was
  `h.2`; `CreateKeys`, `CreateNamed`, `CutSync`, `CutCommit`, `CutCommitLemmas`, `TailSync`); a proof building it
  gives a third component (`h.2.2`, `h3.insert hl rfl` for a layout replaced at the same directory).
- **Obligations**: `Create` (`wal-create*`) none beyond the above (its commit lemma `dirKeysOk_create` is repaired
  here); a unit proving a new `DirKeysOk` step: the third conjunct; the adequacy theorem (`walInv_alloc`'s caller):
  `hdirs1` from the boot split of the claims.

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
- **`wal-leaf-std2`** (2026-11-13): `(*bufio.Reader).Read` proved over its translated body (every
  branch: an empty `p`, a pending error, the large read straight into `p`, the one-read refill, the
  copy out of the buffer; `LinuxFs/Proof/bufio/Reader__Read.lean`). `io.ReadFull`/`binary.Read`: not
  translatable in the part (a part-local `io` would clash with Perennial's `io`, which the part's other
  standard-library imports reach), so the two axioms stay until Perennial translates the bodies
  (`notes/perennial-changes.md`, "`io.ReadFull`/`ReadAtLeast` and `binary.Read`'s fast path without
  bodies"); the `fmt`/`time` ones likewise ("`Sprintf`'s `%0Nx`, ..."), with Go evidence for all three
  in `examples/stdlib/{fmtwalname,timeformat}/`.
- **`wal-read5`** (2026-11-13): `io.readerStream` takes `len(r) + len(p) < 2^62` of each `Read` (decided
  option (a) of the `wal-read4` finding: the `*os.File` model does not model reads ending past
  `model.offMax`). So the `io.ReadFull` axiom's statement is **weakened** by the premise `len(r0) +
  len(buf) < 2^62` (a stronger precondition: what the axiom claims is less); `binary.ReadInt64LE`'s is
  stated over `ReadFull`'s triple and does not change. `bufio.ownReader` records the buffer at most 4 KiB
  and `bufio.Reader.Read.spec` asks that the underlying stream's states stay 4 KiB below `2^62` (a
  refill reads a whole buffer at the position); `decFile`'s bound is now `|F.bs| + 2^12 < 2^62`;
  `readInt64` takes `len(r0) + 8 < 2^62`. The decoder discharges both reads: the length word inside
  `|F.bs| + 8`, the frame at most 8 bytes past the file (Go's size check counts from `lastValidOff`).

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
  (`PbRecord.lean`; axioms `recEncC_ok`, `pbRecordC_reg`, **pending review**), and `walpb.Snapshot`
  (`PbSnapshot.lean`, W6 tenth session; axioms `snapEncC_ok`, `pbSnapC_reg`, **pending review**; Go check
  `examples/stdlib/walpb/snapshot_test.go`), the new
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

## W3a: the decoder (branch `wal-dec`, 2026-11-13)

- **Pure** (`Proof/.../storage/WalEncDecoder.lean`, no `sorry`): the Go decoder's own step
  (`decRecStep`, `goDecode` over the state `(files left, lastValidOff, crc)`), `decStep_eq` (the
  reader's step = the decoder's step + the CRC-record check), and the **loop lemma**: `ReaderRun`
  (the readers' `Decode` loop with the CRC-record check and `UpdateCRC`) computes `walDecodeFiles`
  (`readerRun_start`: same records, same stop, same `LastOffset`/`LastCRC` at `io.EOF`).
- **Deviations Go vs `decStep`** (all accounted for in `decStep_eq`/`rdRest_*`): (1) the decoder accepts a
  CRC record unchecked and leaves its CRC; the reader checks and calls `UpdateCRC` (modelled in
  `decStep` as one step); (2) after a CRC mismatch Go's CRC has the bad data written in
  (`walDecodeFrom` keeps the old CRC; `DecOut.crc` differs only then); (3) after the reader's
  `crcRec` stop Go's `lastValidOff` is past the record, `walDecodeFrom`'s `off` before it (off/crc agree
  at every stop but `crcErr`/`crcRec`); (4) the end of the last file leaves `lastValidOff` (no reset).
  (5) Not in `WalStop`: a failed `FileInfo` (the fork fix) or a failed read returns that error (`IoE`
  outcome of `decPost`, the decoder no longer live).
- **Iris** (`LinuxFs/{Spec,Proof}/go_etcd_io/etcd/server/v3/storage/wal/`; vocabulary `DecDefs.lean`:
  `decFile`, `ownFbr`, `ownDecoder`, `decEnv`, `decPost`, `stopErr`; walpb `ownRec`): proved
  `decodeFrameSize`, `readInt64`, `LastOffset`, `LastCRC`, `UpdateCRC`, `Decode` (over decodeRecord's
  spec), walpb `GetType`/`GetCrc`/`Validate`, fileutil `NewFileBufReader`/`FileInfo`/`Err`/`Read`.
  `NewDecoder` proved (`wal-dec3`: the range loop builds `ownFbrs` by `ownFbrs_snoc`, each reader's `*FileBufReader` cell persisted; `sync.init_Mutex` for `d.mu`; the readers' slice persisted). `isTornEntry` proved (`wal-read`, 2026-11-13: the chunks as bounds `[a, b)` into `data`, `chunkBnds`; each chunk's points-to split out of `data` with `ownSlice_slice` around the inner loop and put back; premise now `off + 8 + len(data) < 2^62`, since `fileOff` is an `int64`: `decodeRecord` passes it). `decodeRecord` proved (branch
  `wal-dec2`, by induction on the files for its recursive call), over its lemmas in `DecLemmas.lean`
  (`fbr_readerStream`: a `*FileBufReader` as `io.Reader` is a stream reader of its file; the
  `decRecStep_*` equations by what the reads returned; `decPost_{stop,accept,ioe,cons_eof}`).
  `isEofOk` gained `nil` and `⌜eof ≠ ueof ∧ ¬ IoE eof⌝` (ledger, 2026-11-13).
- **A failed `proto.Unmarshal`: the weaker model** (2026-11-13, `wal-dec3`; supersedes the finding of
  `wal-dec2` that `proto.UnmarshalWalRecord.spec` was not derivable). `proto.UnmarshalPb.spec` says
  that a success is the canonical decoding (D1) and that an encoding of a valid content succeeds
  (D2), nothing more: `Unmarshal` may fail on any other bytes, including bytes `recDecode` decodes
  (a non-canonical encoding). So the pure decoder keeps `decStep`/`walDecodeFrom`/`walDecodeFiles`
  as the canonical reader (`C.decRec` = `recDecode`, Unmarshal's result *when it succeeds*; no
  downstream lemma changed, no part copy changed), and the Go decoder may in addition stop with
  `badRec` where `Unmarshal` is handed bytes that are no record's encoding (`UFail C u := ∀ r, u ≠
  C.encRec r`): `WalEncDecoder.lean`'s `decFrame` (the frame handed to `Unmarshal`), `RecFail`,
  `GoFail` (the decoder state's version, dropping files at their end first), `ReaderRun.fail`; the
  loop lemma `readerRun_eq`/`readerRun_start` is now "the canonical reader's result, or the
  canonical records up to a decoder state where `GoFail` holds" (`recs = rs ++ (rdRest …).recs`).
  A frame the encoder wrote never fails (`UFail` excludes it), so with `NoCollision` a failure can
  only be where the canonical reader stops too; turning that into the read specs' terms is left
  to their proofs. `decPost` gained a third disjunct (`GoFail` with `stopErr`, the decoder not live,
  **the record not given back**: `UnmarshalPb`'s error post drops it; every reader stops at an
  error, so nothing needs it).
- **`proto.UnmarshalWalRecord.spec` derived** (`LinuxFs/Proof/google_golang_org/protobuf/proto/UnmarshalWalRecord.lean`,
  from `proto.UnmarshalPb.spec` and `pbRecordC_reg`): stated over `walCodec` (no codec parameter),
  pre `isPkgInit proto ∗ b ↦*{dq} bs ∗ pbRecordC.data.blank l`, post `nil` and `ownRec l r` with
  `recDecode bs = some r`, or an error with `UFail walCodec bs` (D2 at `recOf r`, valid: no unknown
  fields). Consequently `decoder.decodeRecord.spec`/`Decode.spec` take `C = walCodec` (was
  `C.crc32c = crc32c`), `decodeRecord`'s precondition is `pbRecordC.data.blank rp`, and `decEnv`
  gained `isPkgInit proto` (a client obligation, like its other `isPkgInit`s: the part has no
  `Init.lean` for the WAL's packages, `etc/gen-init.py`'s `LFS_PKGS` stops at `ioutil`; adding `wal`,
  `walpb`, `fileutil`, `crc` there, with their `SPECIAL` facts, is what derives them).
- **The registered `walpb.Record`'s decoded object is owned whole** (`PbRecord.lean`, `recOwnC`, the
  instance's `decC`/`dec`; **trusted, pending the user's review** with the registration): every field
  at `1`, the hidden ones included, `Data`'s bytes owned. Raft's types put the hidden fields of a
  decoded object in an invariant (`pbMsg`); that cannot work here: the decoder reuses `rec`
  (`Reset`, then `Unmarshal` into it), `Reset` writes the whole struct, and a `Reset` spec taking a
  decoded record to `blank` would duplicate the invariant's points-tos (`False` derivable), nor could
  the invariant (at the old unknown fields) survive `*x = Record{}`. Faithful: the decoded message is
  fresh and protobuf-go keeps no reference to it. The frozen form (`recRoC`, what `Marshal` reads)
  keeps the invariant. `PbRecord`'s definitions are now generic in `HasLC` (the registration axiom
  stays at `hasLC`).
- **`walpb.Record.Reset` stays names-only** (2026-11-13): its body (`*x = Record{}`, then
  `protoimpl.X.MessageStateOf(x).StoreMessageInfo(&file_record_proto_msgTypes[0])`) is the protobuf
  runtime plumbing the configuration excludes on purpose (`walpb.toml`). Its spec (a hypothesis) is
  now `{{ ownRecAny l }} Reset {{ pbRecordC.data.blank l }}`: blank as the registered instance says
  (what `Unmarshal` takes), whatever the message state then holds.
- **Hypotheses** (theorem parameters, not axioms): `proto.UnmarshalWalRecord.spec` (derived, above;
  a parameter of `decodeRecord`'s proof until a `Link` covers the decoder), `walpb.Record.Reset.spec` (names-only),
  `fmt.ErrorfErrs.spec` (Perennial's `Errorf` spec refuses error arguments, `ArgsWf`; Perennial
  change to propose), and in `decEnv` the client's `isEofOk` (`errors.Is(e, io.EOF)` on the readers'
  errors). **Gap**: Perennial's `Errorf` model does not wrap, so `errors.Is(err, io.ErrUnexpectedEOF)`
  of the `tooLarge`/`crcErr` errors is false in the model (Go: true); `stopErr` says only `≠ nil` for
  them. ReadAll's read-mode branch tests exactly that.
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

## W2 implementation log (branch `wal-cut`, 2026-11-13)

Modules (`LinuxFs/Proof/go_etcd_io/etcd/server/v3/storage/wal/`), all pure, **no `sorry`**: `Cut` (the
invariant's new definitions), `CutCrash` (the rename and the directory sync keep the crash condition),
`CutSynced` (a synced WAL's crash; `walInos_congr`), `CutLay` (the layout after a cut: its static relation,
the composed rename lemma).

**Invariant changes** (`Inv.lean`'s `WalsOk`, per WAL; the W1 lemmas re-proved, statements unchanged):
- `(lay.j, NameSet.except [], hj) ∈ cl` became `WalDirClaim lay.j hj cl` := `∃ X, (∀ b ∈ X, walNameP b =
  false) ∧ (lay.j, .except X, hj) ∈ cl ∧ ClaimCoh hj lay.j (.except X)`: the WAL's claim leaves out
  non-`.wal` names (the pipeline's `walTmps = ["0.tmp", "1.tmp"]`, whose claims the pipeline holds), and is
  coherent: `ClaimCoh h j N` := entries below `next`, and a crash keeping all of them leaves every name as
  `h.cur` (preserved by `claimCoh_log` for an entry at `x ≥ next` that changes only the names it writes;
  `claimCoh_init` at boot). Producers (`walsOk_start`) give `X = []`.
- `CrashOk C Mr d lay cl n` became `CrashOkW` := `∃ alt, (∀ lay0, alt = some lay0 → AltOk d lay lay0) ∧
  CrashOkA d lay alt cl n`. `CrashOkA`: every crash gives `CrashTo lay` or `CrashTo lay0` (`alt = some
  lay0`). `AltOk`: `lay0` has its own static relation (over some entries), the same `jr`/`nm`/`j`, its
  segments a prefix of `lay`'s. `alt = none` is `CrashOk` (`crashOkA_none_iff`). `crashGood_exists` takes
  whichever `CrashTo` holds (`crashTo_start` over that layout; the sublist and inode facts through the
  prefix).

**Which intermediate states the invariant allows during a cut** (S/wal.go:875-965):
1. old tail truncated at the file offset, not yet synced: W6's tail step (the reader stops at the
   stream's end with or without the zeros past it); `CrashOk` unchanged.
2. old tail flushed and fdatasync'd (`w.sync()`): `d.m = |H|` (the invariant's `s` raised, the
   program's copy lagging, `walGhost_upd_lag`), every byte of every segment `durB`, the last one's
   `bs = S.map durB` and its `OsMeta` sized `|S|`.
3. `N.tmp` (from the pipeline: `O_TRUNC`, preallocated) holding zeros, then the headers, then
   fdatasync'd: not a `.wal` name, owned wholly by `cut` (its `OsMeta`/`osBytes`, its claim `.only
   [N.tmp]` from the pipeline): no invariant fact.
4. renamed (`os.Rename.specFileS`, two claims: `N.tmp`'s and the WAL's; the AU commits in the
   invariant): layout `cutLay lay |H| g wr` (cut `|H|` and segment `g` appended; `old` zeros; `wr = so =`
   the headers' frames; `z0 = 0`), `alt = some lay`, the claim `h.log x e c`. `cut` hands the
   invariant the halves of `g`'s `OsMeta`/bytes (`segRes`). Proved: `crashOkA_cut` (from `CrashOk lay`,
   `cutLay_abs`, the bytes durable, the rename's entry writing only the new `.wal` name among the
   claim's names, no other claim holding it).
5. after `Fsync(w.dirFile)` (`os.File.Sync.specDirS`: `osCommitLb n`, `n > x`): `alt = none`
   (`crashOk_dirSync`: every crash keeps the rename, so the new segment is named, which `CrashTo lay`
   excludes).
The re-lock (`newTail.Close()`, `LockFile(fpath, O_WRONLY)`, `Seek(off)`) changes no invariant fact
(locks are bookkeeping, plan §6 Q1).

**Pure lemmas** (proved): `regionCrashedK_unlog` (a crash dropping the logged entry is one of the
claims before it), `regionCrashedK_kept` (keeping it keeps every earlier entry of the coherent claim,
and without the new name is a crash of the claims before it: `treeDel`), `w1G_durable` (W1 over
all-durable segments holds by itself), `w1G_prefix`, `crashOkA_rename`, `crashOk_of_alt`,
`crashOk_dirSync`, `crashTo_synced` (all bytes durable, `d.m = |H|`, the names kept: `CrashTo` with
`I = H`, `q = 0`; zeros after the last stream read as EOF), `walInos_congr` (directories agreeing on
`.wal` names), `segRecs_snoc`/`segStream_snoc`/`segStart_snoc` (an extra cut at `|H|`),
`cutLay_abs` (the static relation after the rename: premises the old tail synced and truncated, the
new name above the old ones and above `walLastIdx H`, the new bytes `(S' ++ zeros).map durB`, the zero
tail `0` or `≥ 8` bytes, `RecsFit` of the new segmentation, the directory's `.wal` files the old ones
then `g`).

**Not done: the Iris specs** of `filePipeline.alloc`/`run`/`Open`/`Close` and `(*WAL).cut`. Their
statements need vocabulary not yet on `wal-int`, so they were not stubbed (a stub over a guessed
vocabulary would fix the wrong statement):
- the WAL handle predicate (fields `dir`, `dirFile`, `locks`, `encoder`, `fp`, `enti`, `snapi`,
  `state`, `metadata`) and the specs of `(*WAL).sync`, `saveCrc`, `saveState`, `encoder.encode`,
  `newFileEncoder` on a tail that is (a) the last segment, its bytes crash-tracked, or (b) the cut's
  `N.tmp`, owned wholly: W6;
- `fileutil.LockedFile` ownership and the specs of `fileutil.LockFile`, `Preallocate`, `Fsync`,
  `createNewWALFile` (over `os.OpenFile` and `syscall.FcntlFlock.wp_lock`/`Fallocate.wp_grow`);
- **an `O_CREAT|O_TRUNC` shared-mode open** (`alloc` now opens `N.tmp` with `O_TRUNC`, decision of
  2026-11-13; `os.OpenFile.specCreateS`/`wp_osOpenCreateS` exclude `O_TRUNC`): an `os`/I2 unit;
- a zero-run byte resource (I4) for the 64 MB preallocation (CLAUDE.md, "Large contexts").
**I4 and fileutil (branch `wal-zr`, 2026-11-13).** I4 done: `GooseLang/Ext/Fs/Zeros.lean`, `osZeros i lo
n dq cs` (sealed `osBytes` of `List.replicate n (0, cs)`) and `osZerosA i lo n dq` (zeros, each with
its own candidates), laws over a symbolic length only: `_add` (split/merge), `_take` (a prefix as
`osBytes`, for a write), `_frac`, `zrun_synced`/`zcands_synced` (a sync gives durable zeros),
`rsDone_zeros` (a growth with `m.zf` known, candidates `zcs n`), `rsDone_zerosA`, `zcs_crash`/
`zrun_crash`. fileutil (no `sorry`): `Fsync`, `Fdatasync`, `preallocExtendTrunc`, `preallocExtend`,
`preallocFixed`, `Preallocate` (extending: `preGrown`, the growth as an `osZerosA` run; premise the
file at most `sizeInBytes`, `nonissues/etcd-fileutil-prealloc-fallback-shrinks.md`; `os.File.Seek.
wp_endOff` added). Not done: `LockFile`/`TryLockFile` (need a `fileutil` package fact for
`linuxLockFile`, set by `init`: no `PkgInit.lean`/`Init.lean` for the part's `fileutil` yet),
`LockedFile`, `ZeroToEnd`, `ReadDir`, `Exist`, `createNewWALFile`.
Planned shape: the pipeline's predicate `isFilePipeline fp dir j γ` (persistent: the fields, `filec` a
rendezvous handshake (Perennial `Chan/Idioms/Handshake`, `P` the handed file, `Q` the claim on the
name received before, via a ghost count), `errc`/`donec` invariants); `alloc`: the claim on
`walTmps[count%2]` whole → a fresh file there (zeros, `OsMeta` whole) or an error with the claim back;
`Open`: the main thread's token `pipeMain γ c` → `pipeMain γ (c+1)` and the file with its claim, or an
error; `Close`: the token → the pipeline's claims (and the file in flight removed). `cut`: within
`Save`'s proof, the handle and `walInv`, `walSyncedLb |H|` preserved, the layout `cutLay`, `alt` back to
`none` on success; on an error the handle is lost (§3's honest error posts), `CrashOkW` held throughout.

**Second session (branch `wal-cut2`, 2026-11-13): the pipeline.**
- *`HandshakeN.lean`* (generic, to propose to Perennial): an **indexed handshake** on an unbuffered
  channel, `isHsn γ ch P Q` with `P : Nat → V → _`, `Q : Nat → _`, the sides' counts `hsnSnd γ n`/
  `hsnRcv γ n` (ghost-variable halves, the other halves in the invariant; the side completing an
  exchange finds the other's resource at its own index). `hsn_send_au`/`hsn_receive_au` (for
  `select`), `wp_hsn_send`/`wp_hsn_receive`, `start_hsn`. Needed because the plain handshake's `Q` is
  one proposition: `run` cannot know which claim it gets back, and no ghost token exchanged through
  the plain idiom fixes that (each round both sides' tokens cross without meeting).
- *`Pipe.lean`*, the predicate (replaces `walPipeH`'s placeholder): `filec` an indexed handshake
  (`P n lf = pipeFile j dir n lf`: `N.tmp` locked, offset 0, `OsMeta`/zero bytes whole, no mappings,
  its whole claim holding it; `Q n = pipeQ j n`: the claim on `pipeTmp (n+1)`, the name of file
  `n-1`, and `n + 1 < 2^63`); `errc` Perennial's SPSC (its value: an error with `pipeLeft`, the
  pipeline's half call permission, path fraction and claim; its close without a value: `pipeLeft`
  and `pipeClosedW`); `donec` a broadcast carrying `pipeClosedW` (`dghostVar γ.a discard true`, from
  the caller's alive flag `dghostVar γ.a (own 1) false`: an `Open` meeting `errc` closed and empty
  is a contradiction). Tokens: `pipeMain γ n`, `pipeDead γ e`, `pipeRun fp γ … n`. `walPipeH fp dir k`
  (`Handle.lean`): `isFilePipe`, `pipeMain γ n`, the claim on `pipeTmp (n+1)`, `n ≤ k`, with
  `walHandleIn` passing `h.cuts.length`.
- **Proved:** `filePipeline.Open`, `filePipeline.Close`. **Stated, `sorry`:** `alloc`, `run`,
  `newFilePipeline` (plans in their proof files), `WAL.cut` (the steps and their needs in
  `WAL__cut.lean`'s header).
- **Statement change:** `WAL.cut.spec` takes `h.cuts.length + 2 < 2^63` (`count` is a Go `int` and
  `count % 2` a signed remainder: after `2^63` files the name would be `-1.tmp`). Save's proof must
  supply it (e.g. from a bound on the history; logged for W6).
- **Gaps found (for the coordinator):** (1) the open specs' posts (`fileutil.openPost`, hence
  `lockPost`, `crTr`) give no `os.ownOff f 0`, which `Preallocate`, `Seek` and `newFileEncoder` need
  of a fresh file; (2) `m.maps = ∅` of a truncated file is not in `trFile`; (3) `filepath.Join` has no
  spec; (4) `sync`/`saveState` are stated over `walHandleIn` whose tail is the crash-tracked last
  segment, but `cut` runs them on the owned `N.tmp` (a second tail mode, or inline them in `cut`);
  (5) `walHandleIn`'s non-tail locks hold an exclusive `LockedFile.File` field, `LockFile` gives the
  persistent `lockedFile`; (6) task 2's `nc` variants: `specCreateTruncSnc` landed on `wal-int`
  (`wal-osau4`); `os.File.Sync.specDirS` has no atomic update, so it needs none: `crashOk_dirSync`
  is applied after the step, opening `walInv` with `wp_notCrashed_acc` before the next one.
**Gaps session (branch `wal-gaps`, 2026-11-13).** Gaps (1)-(3) closed, no `sorry` added:
- (1) `os.ownOff f (W64 0)` (the model's `file.off` starts at 0) in the success posts of
  `os.OpenFile.specCreateS`/`specCreateSnc`/`specCreateTruncS`/`specCreateTruncSnc`, `wp_fileS`,
  `wp_truncS`, and of `fileutil.openPost`/`lockPost` (`LockFile`'s proof passes it on; the spec
  modules import `LinuxFs.Proof.os.Off`). `os.OpenFile.wp_dirS` unchanged.
- (2) `trFile i P` has `m.maps = ∅` (third pure conjunct): a new file has no mappings, a truncation
  keeps them (`announce_maps`); `trFile_of_rsDone` takes it. True of the WAL's `N.tmp` (never mapped).
- Found and fixed: the `nc` open specs had lost `fmtErrorOkOrNil err` in their error posts (the merge
  of `wal-osau4` into `wal-int`, 9bc9e5356e), so `OpenFileS`/`OpenFileTruncS` did not build on `wal-int`.
- (3) `filepathlite.Clean` proved (`LinuxFs/Proof/internal/filepathlite/Clean.lean`, the main tree's
  `path.Clean` proof adapted: `IsPathSeparator` calls, the empty output appended through the buffer,
  `postClean`, `FromSlash`); `filepath.join` specified (`LinuxFs/Spec/path/filepath/join.lean`, the
  same post as `Join`, no premise) and proved over Perennial's `strings.wp_Join` and `filepath.Clean`
  (pure: `filepath.joinModel_drop`, `joinModel_empties`); `filepath.Join` proved over `join`. `join`
  takes `[UntypedRuneSemantics]` (`string(Separator)`, `notes/perennial-changes.md`), to be listed in
  `etc/gen-link.py`'s `SEM_PREMISES` when filepath is linked.
- Not done: `fileutil.ReadDir` (still wholly `sorry`), `filepathlite.Dir`/`IsAbs`.

**Third session (branch `wal-cut3`, 2026-11-13): the pipeline proved.**
- **Proved (no `sorry`):** `filePipeline.alloc`, `filePipeline.run`, `newFilePipeline` (with `Open`/`Close`
  from the second session, the whole pipeline). Helpers in `PipeLemmas.lean`: `pipeTmp_sprintf`
  (`Sprintf("%d.tmp", count % 2)` of `count < 2^63`), `osPathS_cleanAbs`/`join_child` (a directory with a
  shared-mode path is a clean absolute path, so `filepath.Join(dir, b) = child dir b`), `osAUnc_triv` (the
  trivial update of a caller holding the whole claim), `wp_createTmp` (`createNewWALFile(dir/b, true)` over
  `os.OpenFile.specCreateTruncSnc` for an absent name, `os.OpenFile.wp_truncS` for a leftover file),
  `wp_removeTmp`, `zerosA_trFile`. `CutPipe.lean`: `wp_walPipeH_open` (cut's step 4 from the handle),
  `walPipeH_next` (the handle's pipeline after the rename), `tmpClaim_absent`. `CutLay.lean`: `altOk_cut`.
- **Statement changes:** `tmpClaim j b` now owns what the name holds (`tmpEnt`: nothing, or a leftover
  file whole, `trFile i False`; a directory excluded), since `alloc`'s `O_TRUNC` open of a leftover `N.tmp`
  (`wp_truncS`) takes the file whole: the producer of the first claims (W5's `Open` after a crash) must hand
  over a leftover tmp file's `OsMeta`/bytes with its claim. `isFilePipe` and `newFilePipeline.spec` carry
  `dir.length < 2^61` (`filepath.Join`'s premise). `run.wp_proof` takes `os.Remove.specFileSnc` (was
  `specFileS`); `alloc.wp_proof` takes `[os.file.FieldAssumptions]` (`wp_truncS`) and the open/Join/zap/
  Close specs; both take `[fileutil.Assumptions]` (the promoted `LockedFile` methods).
- **`AltOk`** gains `lay0.segs.length < lay.segs.length` (W6's decision); `crashOk_of_alt`,
  `crashOk_dirSync`, `crashOkA_rename` unchanged; `CrashPure`'s `crashGood_exists` takes the prefix part.
- **`cut` not started** (still `sorry`). What it needs beyond the pipeline: a crash-aware truncate of the
  tail (step 1; no spec on `wal-int`); the header phase over the owned `N.tmp` (step 5): `walPreIn`
  (W4's pre-rename `sync.specPre`) fixes `locks = [lt]` and lacks `dirFile`/`fp`/`state`, so `cut` needs
  a generalized pre-rename handle (the old segments' locks and the WAL's other fields framed) and a
  pre-rename `saveState`; the rename's client update `walCut_osAUnc` (as `walCreate_osAUnc`: opens
  `walInv`, layout to `cutLay` with `alt = some lay` by `crashOkA_cut`/`altOk_cut`, deposits `N.tmp`'s
  halves, and moves the tail record of `walTailsRes` to the new segment, establishing `TailBound`); the
  dir sync then `crashOk_dirSync`; the re-lock (`LockFile` of an existing `.wal`, `os.OpenFile.wp_fileS`).

**Fourth session (branch `wal-cut4`, 2026-11-13): the pre-rename header phase; the rename's update blocked
on three facts the invariant does not record.**
- *Done (no `sorry`):* `walPreInL w lg dir mds md e ls lt f snapi enti` (`Spec/.../wal/WAL__cutPre.lean`): W4's
  `walPreIn` with the locks `ls ++ [lt]` (cut's `w`: the old segments' locks, then `N.tmp`'s); `dirFile`,
  `fp`, `state` are the caller's frame (`sync` does not read them). `walPreIn ⊣⊢ walPreInL … [] …`
  (`walPreIn_L`, definitional). **`WAL.sync.wp_proofPreL`** (W4's fifth-session proof generalized, in
  `WAL__SaveSnapshotPre.lean`; `wp_tail` at `ls`), and W4's `sync.wp_proofPre` now its corollary
  (`sync.specPre_of_L`): one proof, both statements unchanged. **`WAL.saveState.specPre P Mr`** (only the
  `state`/`encoder` fields, any guarded writer `io.writerStreamP`, post as `encode.specG`'s with the state
  frame `stateFrame Mr c hs`) **proved** (`saveState.wp_proofPre`) over `encode.specG` and two laws over the
  client's `P.hsIn`, hypotheses like `pbutil.MustMarshalMessage.specWalSnap`: `WalPbIn.IsEmptyLaw` (result a
  `Bool` `b` with `b = true ↔ hsEmptyP hs`: `wp_if_destruct` does not take `#(decide _)` from a hypothesis
  triple) and `WalPbIn.MarshalHsLaw` (a non-empty state marshals to a non-nil slice of `Mr.encState hs`).
  `CutTail.lean` (pure): `tailZeros_cut`, `tailBound_cut` (the new segment's `TailBound`: `jE` all its
  records, `max so z0 = wr`), `cutLay_last`, `tailG_cut` (the tail record's value after the cut).
- **Blocked: `walCut_osAUnc`** (the update for `os.Rename.specFileSnc`). Like `Create`'s, its opening cannot
  open `osSharedInv` (`osShN ∉ osAuMask`), so it can only use facts `walInv` records, and three it needs are
  not recorded anywhere:
  1. *The WAL directory claim's key.* `specFileSnc` takes the program's fraction `osNames j' N' q2 h'` and
     the update must hand out the rest *of the same key and history*. `walHandleIn` holds no fraction of its
     directory's claim at all (`walReadTie`, `ReadDefs.lean`, does: the read handle's half), and the
     invariant's `WalDirClaim lay.j hj cl` is `∃ X`: from the handle nothing ties `(j', N')` to
     `(lay.j, .except X)` (fragments of different keys do not contradict; the tail record has no `j`/`X`).
  2. *Exclusivity on the new name* (`crashOkA_cut`'s `hothers`: no other claim of `lay.j` in `cl` holds
     `bt`): a fact of `NamesCoh.disj` only, as `CreatingOk`'s for `Create`.
  3. *`alt = none` at the cut* (`crashOkA_cut` needs `CrashOk lay`, i.e. no earlier cut's rename still
     pending): `CrashOkW` is `∃ alt`; the previous cut's `crashOk_dirSync` step makes it `none` but nothing
     keeps it so.
  **Proposed (for the coordinator; internal ghost state, the W4 `walCreating` pattern):** a `WalGS` field
  `γdk` and a framed `walInvBody` conjunct `∃ K, walDirKeysAuth K ∗ ⌜DirKeysOk Ls cl n K⌝`, `K : dir ↦ (j, X)`
  with persistent elements `walDirKey dir j X` (in `walHandleIn`, with the handle's half `osNames j
  (.except X) ½ hj` and `hj` in `WalHS`): `DirKeysOk`: each entry's WAL has a layout with `lay.j = j`, its
  claim `(j, .except X, hj)` once in `cl`, coherent, `X` without `.wal` names, no other claim of `j` holding
  a `.wal` name, and `CrashOkW` at `alt = none` unless the handle's tail record says a rename is pending
  (or: record the pending flag in the tail record, `TailG`). Producers: `Create`'s commit and `ReadAll`;
  preservation by `Create`'s commit needs `J ≠ j` for every entry, which `CreatingOk` could carry from the
  token-making step (W4's unwritten step at `⊤`: the program holds `J`'s claim whole, so no claim of `J` in
  the invariant holds a `.wal` name, by `NamesCoh.disj`). Not implemented: it changes `Ghost.lean`,
  `walInvBody` and every unit destructuring it, under five concurrent branches.
- *With them, the update's commit* (designed): open `walInv`, look the tail record up (`walTailKey`,
  agreement with the program's half: `H`, `cuts`, `wr`, the old tail inode), the old tail's halves against
  the program's (its bytes all `durB` and sized after step 1's truncate and the fdatasync: `hdur`, `hm`),
  `cutLay_abs`/`crashOkA_cut`/`altOk_cut` for the WAL, a `walsOk_cut` for the rest (the other WALs, `AbsentOk`,
  `DirsOk`, `AbsentNone`, `DirsAvoid`, `WalsCreateOk`, `CreatingOk` under the `replClaim` of the directory's
  claim, as `walsOk_create`'s pieces: not written), `laysResF_insert` of `g`'s halves (its inode new by
  `laysResF_ino_ne`), the tail record moved (`tailG_cut`, `tailBound_cut`, `tailZeros_cut`); `Q` the
  program's new record half and `g`'s other halves.
- *`(*WAL).cut`* (still `sorry`): beyond the update it needs `wal-i3b`'s crash-aware truncate (step 1, not
  landed), `w.seq()` (`filepath.Base`, `parseWALName` of the tail's `Name()`: no `Name`/`Base` spec over the
  part), `fileutil.LockFile` of an existing `.wal` (`wp_fileS`), `newFileEncoder`, the encoder over
  `os.File.writerStream` for `saveCrc`/`encode(Metadata)`/`saveState.specPre`/`sync.specPreL`, and the cuts
  budget (W6). The order the proof must take: the header phase over `walPreInL` with the old segments'
  locks in `ls`, `encode.specG`/`saveCrc.spec` (both still unproved over `writerStreamP`).

**Fifth session (branch `wal-cut5`, 2026-11-13): the rename's update proved, over one pure lemma.**
- *`walCut_osAUnc`* (`CutAu.lean`, **proved**): the update for `os.Rename.specFileSnc` of the pipeline's
  `tmp` (claim `(j, .only [tmp], ht)`, the program's half in the update, the call's half) onto the free
  `.wal` name `bt` of the WAL claim `(j, .except X, hj)`. The program splits its half of the WAL claim:
  a quarter in the update (`walCutP`, to agree with the invariant's half at the opening; the key
  `walDirKey dir j X` finds the claim by `DirKeysOk`'s `ClaimOnce`), a quarter to the call; `α` is
  the tmp claim's half and the WAL claim's `½ + ¼`. Commit: `walCut_agree`/`walCut_set` (`none` →
  `some dir`); `walTailsRes_cut` (the tail record gives `d`, `lay`, `g0`; the program's `H`, metadata,
  cuts, old tail inode are substituted); the old tail's halves agree with the program's (`hlast0`:
  synced, truncated); `laysResF_ino_ne` (the new segment's inode fresh); the invariant takes half of the
  new claim (`cutClaim`), the new segment's halves (`laysResF_cut`), the tail record moved
  (`tailG_cut`), the old tail's program halves deposited (`walParked_cut`: `O' = g.ino :: O.filter (·
  ≠ g0.ino)`, `D' = cutClaim :: D`; if the old tail was already parked, the program's halves are
  dropped). `walCutQ` gives back the claims' new histories (½ tmp, ¼ WAL), the keys, the tail record at
  the new segment, the flags (`walCutFrag (some dir)`), the new segment's other halves.
  Program premises (over its copy `H`, `md`, `cuts`): `tmp ∈ X`; the cuts below `|H|`; the old tail at
  the `.wal` name `nm0` of `hj.cur`; `bt` free, a `.wal` name, `walFileName sq ix` past `nm0` with `ix`
  past the history's last index; the old tail's bytes the stream's, durable, `|bs0| = m0.size`; the new
  segment's bytes the headers' frames (`wr`) then zeros, durable, `OsMeta` sized, named `bt`, nonempty;
  `RecsFit` of the new segmentation; `walSyncedLb dir |H|`, `walNamed dir` (in `walCutP`).
- *`CutAuLemmas.lean`* (proved): `walGhost_synced`, `walGhost_named` (past states → `d.m`, `d.named`),
  `walTailsRes_cut`, `laysResF_cut`, `walParked_cut`, `walDirClaimOf_insert`.
- **`sorry`: `cutCommit_pure`** (`CutCommit.lean`): every pure conjunct after the commit (`WalsOk`,
  `WalsCreateOk`, `CreatingOk`, `AbsentNone`, `WalsNamed`, `DirKeysOk … (some dir)`), its plan in the
  file header. The two non-obvious parts: `cutLay_abs`'s `hents` (`bt` is the largest `.wal` name of
  `hj.cur`: `nm0` is the last segment's name, since `walInos` of the sorted names are the segments'
  inodes, `Nodup`), and `WalsNamed`'s crash dropping the rename (`g.ino` in no `.wal` entry of `j`: the
  old crash condition, the WAL named, puts only the old segments' inodes there; hence `walNamed` in
  `walCutP`); `DirsOk` needs "a lookup succeeding in `treeDel m' j bt` reads no `(j, bt)`".
- **`walHandleIn` change** (`Handle.lean`): a new conjunct `walDirH dir h.ino name` (the key
  `walDirKey dir j X`, the program's half of `(j, .except X, hj)`, `osPathS R dir dq j ∗ osSharedInv
  R`, `osCallPerm ½`, the tail at `.wal` name `nm0` of `hj.cur` with `name = child dir nm0`). Producers
  (`Create`'s body, `ReadAll`) must provide it; nothing destructured `walHandleIn` before. Its pipeline
  (`walPipeH`) still has its own `∃ j`: `cut` ties it to `walDirH`'s by path agreement.
- **`Ghost.lean`**: `walOpenWC` (sealed: `walOpenW` without its two flags) and `walOpenW_cut :
  walOpenW ⊣⊢ walOpenWC ∗ walParkFrag false ∗ walCutFrag none` (the update needs the parking flag to know
  the handle's halves are out, and sets the cut flag).
- **For W6 / `cut.spec`**: the update needs the cuts strictly below `|H|` (`cutLay_abs`'s increasing
  cuts), so `cut.spec` needs `∀ b ∈ h.cuts, b < h.H.length` (Save's op is committed before its cut; a
  second cut at the same length would break `WalAbsD.cuts`): not yet added to the statement.
- *`(*WAL).cut`*: still `sorry`. Its rename step is now `os.Rename.specFileSnc` with
  `walCut_osAUnc` (q1 = ½, q2 = ¼); the dir sync then `crashOk_dirSync` with `walCut_set` back to
  `none` (a lemma opening `walInv` via `wp_notCrashed_acc`, the analog of this one, not written).

**Sixth session (branch `wal-cut6`, 2026-11-13): `cutCommit_pure` proved.**
- *`cutCommit_pure`* (`CutCommit.lean`, **no `sorry`**), over `CutCommitPure.lean` (the rename's writes,
  `replClaim` membership and `ClaimOnce`, `walClaim_eq` (the keyed claim is `j`'s only claim on `.wal`
  names), `walName_unique` (distinct files, one `.wal` name each), `walInos_insert_last` (`bt` above every
  name: its file last), `regionCrashed_cut` (a crash of the new claims is one of the old, on the tree or
  on `treeDel m' j bt`), `lookupH_treeDel`, `crashOkA_cut_other`) and `CutCommitLemmas.lean`
  (`walsOk_dir_ne`: another WAL's directory is not `j`; `creatingOk_cut`, `absentNone_cut`, `dirsOk_cut`,
  `walsNamed_cut`, `dirKeysOk_cut`). `nm0` is the last segment's name by `walName_unique`; `bt` the
  largest by the segments' names sorted.
- **Invariant change: `SegsNamedC` gains a third clause** (`Inv.lean`): every file at a `.wal` name after
  a crash is a segment's (`∀ i ∈ walInos ents, i ∈ segs.map (·.ino)`). `WalsNamed`'s crash clause for a
  crash dropping the cut's rename must say the new segment is at no `.wal` name; the old crash condition
  says so only for crashes whose files `FileCrashedR` allows, and no such files can be produced purely
  (an old segment's `zf` is not recorded: a durable nonzero byte past a `zf` below the size would admit
  none). Re-proved: `SegsNamed.crash` (takes the clause), `walsNamed_start` (`WalAbsD.names`),
  `walsNamed_tail`/`segsNamedC_congr` (the inodes kept), `segsNamedC_congr_ents`, `walCrash_pure`.
  **For W4 (`wal-create7`)**: `walCreate_osAUnc`'s `hJC` now asks the clause too (after any crash of `J`'s
  claim, its `.wal` files are the new segment's: the claim's boot holds no `.wal` file, its entries are
  the segment's create).
- **Statement change**: `cutCommit_pure` and `walCut_osAUnc` take `walCutPos (H.map toM) |H|` (`cutLay_abs`'s
  `hcut`: the new segment starts at a cut position, i.e. after a `Save` that wrote a record), so `cut.spec`
  needs it from `Save` (with the cuts below `|H|`).
- **`cut.spec` premises added** (`wal-save6` had not added the handle bound): `∀ b ∈ h.cuts, b < h.H.length`
  and `walCutPos (h.H.map WalOpG.toM) h.H.length`. `Save`'s proof (W6) supplies them: the cut follows the
  `Save` that wrote a record, after every earlier cut.
- *`CutSync.lean`* (proved): `walInvBody_cutSynced`, step 7's update (after `os.File.Sync.specDirS`'s
  `osCommitLb n`, `x < n`, the program opening `walInv` with `wp_notCrashed_acc`): the program's fraction
  of the WAL claim agrees with the invariant's (history ending with the rename), the tail record names
  the layout's last segment `i` (`walTailsRes_lookup`), so the alternative's segments, a strict prefix,
  miss `i` and `crashOk_dirSync` drops it; the flag back to `none` (`dirKeysOk_cutSynced`, at `max n0 n`).
- *`(*WAL).cut`*: still `sorry`. Done of its steps: 4 (`wp_walPipeH_open`), 6 (`walCut_osAUnc`), 7
  (`walInvBody_cutSynced`). Left: 1 (split-form `os.File.Truncate.specAu`, its proof `sorry`, on the
  tail's `walTailW`), 2 (`sync.spec` on the truncated tail, then the `walSyncedLb |H|` and the durable
  bytes `walCut_osAUnc` needs), 3 (`w.seq()`: `filepath.Base`/`parseWALName` of `Name()`; the
  `max(enti, snapi) + 1` naming and `walLastIdx` bound from the handle), 5 (the header phase over the
  owned `N.tmp`: `newFileEncoder`, `saveCrc`, `encode(Metadata)`, `saveState.specPre`, `sync.specPreL`
  over `walPreInL` with the old locks in `ls`), 8 (`Close`, `LockFile` of the renamed `.wal`
  (`os.OpenFile.wp_fileS`), `Seek`, `newFileEncoder`), and rebuilding `walHandleIn` (with `walDirH` at
  the new claim history, `walPipeH_next`).

**Seventh session (branch `wal-cut7`, 2026-11-13): `cut`'s statements settled for its body; steps 1-2 as
hypotheses; step 3's pure part.**
- **`walHandleIn` changes** (`Handle.lean`; no producer was proved, nothing destructured it): `walDirH dir j dfd ino
  name` takes the directory's inode `j` (shared with the pipeline: `walPipeH fp dir j k`, so the rename's two
  claims are of one directory) and holds `w.dirFile`'s fd as `osDirFdS dfd j ph` (was `osFd dfd (own 1) dd`, which
  `os.File.Sync.specDirS` cannot take); `walTmps ⊆ X` (the rename's `tmp ∈ X`); the tail's name `walFileName sq
  ix` with `sq + 1 < 2^64` (the next sequence does not wrap); `nm0` the largest `.wal` name of `hj.cur` (so the
  new name is free: `walCut_osAUnc`'s `hcur`; producers know it from `WalAbsD.names`). The handle's pure part:
  `o0 + |out| ≤ sz ≤ 0xffffffff000`, `o0 + |out| + |pend| ≤ 0xffffffff000` (`Seek`'s bounds),
  `walLastIdx H ≤ max(enti, snapi)` and `max(enti, snapi) + 1 < 2^64` (the new name above `walLastIdx`, no
  wrap). **For W5/W6** (producers: `ReadAll`, `Create`, `Save`'s preservation): the index bound needs `snapi`
  the largest snapshot index saved (`SaveSnapshot` sets `w.snapi = e.Index`, not a max: true while snapshots
  are saved in increasing order; else a premise).
- **`cut.spec`** takes `h.st = walLastHS (H.map toM)` (the new segment's headers hold `w.state`, `cutHdrDs`;
  `Save` has it: `WalHS.Done`).
- **`walCut_osAUnc`'s premise weakened**: the old tail's bytes only sized to its stream (`bs0.length =
  |tailStream|`), not durable: durability is the invariant's (`CutTail.lastSeg_synced_durable`: a synced WAL's
  last segment, sized to its stream, is its stream durable, from `WalAbsD.synced`/`last`).
- **Steps 1-2 as hypotheses** (`Spec/.../wal/WAL__cutTail.lean`, not axioms): `os.File.Truncate.specWalTail Mr`
  (the tail truncated at its write position: `walTailW` at `sz := o0 + |out|`; from `Truncate.specAu` and the
  `walInv` supply of branch `wal-zte`, the coordinator's decision) and `WAL.sync.specCut P Mr` (`sync` of the
  truncated handle: the pending bytes written past the size, the tail sized to its stream, `cutSynced h`,
  `walSyncedLb |H|`; to prove with W6's `sync`, whose writer then accepts writes past the size).
- *`CutName.lean`* (pure, proved): `walFileName_lt` (a larger sequence sorts after: `hexPad_lt`, fixed-width
  hexadecimal byte-wise), `cleanSeg_walFileName`, `baseModel_child_walFileName` (`filepath.Base` of the tail's
  path), `scanWalName_walFileName` (`parseWALName` reads it back). `walName` is `fmt.Sprintf("%016x-%016x.wal")`:
  `fmt.SprintfWalName.spec` (the main tree's trust-boundary axiom) as a hypothesis.
- *`cut.wp_proof`*: steps 1-2 written (the handle opened, `Seek` by `os.File.Seek.wp_cur`, the truncate, the
  handle refolded at `sz := o0 + |out|` for `sync.specCut`, the error exits); `sorry` from step 3 on. The
  theorem takes `[os.file.FieldAssumptions]`, `[fileutil.Assumptions]` (`Seek`, the promoted methods).
  Order for the next session: step 3 (above), 4 (`wp_walPipeH_open` at the handle's `j`), 5 (the header phase:
  `os.File.writerStream` over the first bytes of `N.tmp` split off its `osZerosA` run; a `walPreSyncOk` for
  a preallocated owned file, the zeros synced by `zrun_synced`, shareable with W4's `Create`), 6
  (`walCut_osAUnc`: split the handle's ½ of the WAL claim into ¼ + ¼, the path fraction in halves,
  `osPathS_frac`), 7 (`walInvBody_cutSynced` under `wp_notCrashed_acc`; the rename's `logOut` for the
  `osLogLb`), 8 (re-lock, `walHandleIn` at the new claim history, `walOpenW_cut` back).

**Eighth session (branch `wal-cut8`, 2026-11-13): steps 3-4 proved; step 5's lemmas; what step 5 still needs.**
- **Statement change (the coordinator's decision): the pipeline's count in the handle.** `WalHS` gains `pc`
  (the files the handle's pipeline has handed over since this `Open`/`Create`; the pipeline's `count`
  restarts at 0 with each, while `cuts` counts the WAL read back too); `walHandleIn` holds `walPipeH fp dir j
  h.pc` (was `h.cuts.length`; `ReadDefs`' `walPipeH fp dir 0` is `pc = 0`). `cut.spec` takes `h.pc + 2 <
  2^63` (was `h.cuts.length + 2 < 2^63`) and gives `h'.pc = h.pc + 1`. W6 supplies the bound (per-lifetime
  receipts, `notes/bounds-plan.md`).
- *`cut.wp_proof`, steps 3-4* (proved, `sorry` from step 5 on): `w.seq()` inline (`os.File.Name.spec`,
  `filepath.Base.spec`, `parseWALName.spec`; the `lg.Fatal` arm unreachable), `next` joined with `wp_join`
  (`uint.nat nx = max(enti, snapi)`), `walName` over `fmt.SprintfWalName.spec` (`cutName_str`: the name is
  `walFileName (sq + 1) (max(enti, snapi) + 1)`, no wrap from the handle's bounds), `filepath.Join` (`dir`'s
  length from `isFilePipe`, `join_child`, `walFileName_nameOk`); `wp_walPipeH_open` with its error exit.
  New hypotheses of the theorem: `os.File.Name.spec`, `filepath.Base.spec`, `parseWALName.spec`,
  `fmt.SprintfWalName.spec`, `filepath.Join.spec`.
- *`PreSync.lean`* (proved, shareable with W4's `Create`): `io.writerStream_frame` (a persistent frame in a
  stream's states), `os.fileWI`/`os.fileBI` (`os.fileW`/`fileB` from offset 0 with `osInv`: `walPreSyncOk`'s
  hypothesis triple has no other place for it), `os.File.writerStreamI`, `os.fileS` (the state after a
  successful fdatasync: `OsMeta` synced, bytes durable), **`os.fileWI_preSyncOk`** (`walPreSyncOk f (fileWI
  …) (fileS …)` over `fileutil.Fdatasync.spec`).
- *`CutHdr.lean`* (pure, proved): `metaChain_cut` (writes keep `OsMeta.cut`), `metaChain_size` (the size
  grows to `max m0.size (o0 + a)`), `streamOk_vals` (over zeros: the bytes are the stream's then zeros).
  *`CutName.lean`*: `walFileName_nameOk`, `cutName_str`.
- **Step 5 needs three facts `pipeFile` does not record** (found writing it; a cascade through `os`/`fileutil`
  specs, not done): `walCut_osAUnc` asks `g.om.cut = none` and the zero tail `0` or `≥ 8` bytes, and
  `os.fileW_start` asks `m0.lo ≤ m0.size`. Proposed: `pipeFile` gains `m.cut = none ∧ m.lo ≤ m.size ∧ m.size %
  8 = 0` (`walCut_osAUnc`'s `hz` then follows: the headers' frames are 8-aligned, so `max(size, wr) - wr` is a
  multiple of 8); `isFilePipe` gains `sz.toInt % 8 = 0` (`newFilePipeline.spec`'s premise; etcd's
  `SegmentSizeBytes` is 64·10^6); `trFile` (`Spec/os/OpenFileTruncS.lean`) gains `m.cut = none ∧ m.lo ≤
  m.size` (a new file's `newMeta`, a truncation's `rsPost` keeps `cut` and sets `lo` to 0; a leftover tmp
  file's producer, W5's `Open`, must give them); `preGrown` (`fileutil/Defs.lean`) gains `m'.cut = m.cut ∧
  m'.lo ≤ m'.size` (the growth's `rsPost`: `lo := min m.lo tg`). Then `alloc` proves the new `pipeFile`.
- *Step 5's plan* (with the above): unfold `pipeFile`; `append(w.locks, newTail)` (`wp_slice_append`);
  `prevCrc` (unfold `ownEncoder`/`ownDecCrc`, `digest.Sum32.spec`, as `decoder.LastCRC`); `w.tail()` at the
  locks `ls ++ [lt] ++ [newTail]`; `newFileEncoder(newTail.File, prevCrc)` (offset 0); the stream
  `os.File.writerStreamI` at `lim` the headers' length, `os.fileW_start` over the zeros (`osZerosA_unfold`);
  `saveCrc.spec`, `encode.specG` (metadata, through `io.writerStream_P`), `saveState.specPre`,
  `sync.specPreL` over `walPreInL … (ls ++ [lt]) newTail …` with `os.fileWI_preSyncOk`; then `Seek` and
  `os.fileS` → the new segment `g` (`om := m.synced`, `bs := ys.map durB`) for `walCut_osAUnc`
  (`streamOk_vals`, `metaChain_*`; the headers' frames = `tailStream Mr H md (cuts ++ [|H|])` from
  `cutHdrDs` and `h.st = walLastHS`).

**Ninth session (branch `wal-cut9`, 2026-11-13): the `pipeFile` facts; steps 5-6 of `cut` proved up to the
rename's return; `sorry` from the rename's outcome on.**
- **`pipeFile` facts (the coordinator's decision, done)**: `pipeFile` carries `m.cut = none ∧ m.lo ≤ m.size ∧
  m.size % 8 = 0`; `isFilePipe` and `newFilePipeline.spec` take `sz.toInt % 8 = 0`; `trFile` (`Spec/os/
  OpenFileTruncS.lean`) gains `m.cut = none ∧ m.lo ≤ m.size` (**for W5's `Open`**: a leftover `N.tmp` handed
  to the pipeline must satisfy them); `preGrown`/`preGrownH` gain `GrowMeta m m'` (`fileutil/Defs.lean`: the cut
  kept, and `m.lo ≤ m.size → m'.lo ≤ m'.size`: the implication form spares `Preallocate`'s specs a premise);
  `rsDone_preGrown`, `fallocDoneH_preGrownH` take `m.size ≤ sz' ∨ sz' = tg`, `preGrown(H)_trans` takes
  `GrowMeta m m1`, `trFile_of_rsDone`/`zerosA_trFile` take the cut and the bound. Repaired: `OpenFileTruncS`,
  `preallocExtend(Trunc)(Au)`, `ZeroToEnd(Au)`, `alloc`, `run`, `newFilePipeline`.
- **Statement changes**: `cut.spec` takes `h.cuts.Pairwise (· < ·)` (the headers' state is `walLastHS` of the
  segments' concatenation, `segsOf_flatten`) and `h.md.length + (Mr.encState h.st).length < 2^42` (the headers'
  frames within ext4's maximum offset, `Seek`'s bound, each record within the encoder's `2^47`): **for W6, `Save`
  supplies both** (or the handle carries them). `walHandleIn`: the metadata slice as `recBytes mds (some h.md)`
  (non-nil: the record's data is present, `recOf`; `Create` takes it non-nil). `walDirH` holds `walNamed dir`,
  `walOutFrag ⟨[ino], [(j, .except X)], [dir]⟩` (the out-record, W1 log tenth session), and `∀ b ∈ X, walNameP b =
  false` (the rename's `N'.Mem bt`): producers (`Create`, `ReadAll`) supply them. `walCut_osAUnc` takes only the
  headers' fit (`hfitH`), the old records' from `WalAbsD.fit` (`allRecs_cut`). `CutCommitPure`'s `walName_unique`
  renamed `walName_unique_nd` (clash with `OpenNames`').
- *New pure files*: `CutHdrStream.lean` (`tailRecs_cut`/`allRecs_cut`/`tailCrc_cut`: the new segment's records are
  `cutHdrDs` chained from `tailCrc`; `cutHdrRecs_frames`, `crcAfter_cutHdrs`, `WalHS.crc_done`, `cutHdrs_fit`,
  `recSize_hdr`), `CutRen.lean` (`walNameP_walFileName`, `cutName_free`, `recFrames_mod8`, `recsFit_of_frames`,
  `tailStream_len_split`, `cutHdrZeros`).
- *`cut.wp_proof`*: the synced handle generalized to a variable `h1` after step 2; step 5 proved (append, `prevCrc`
  by `Sum32`, `newFileEncoder`, the stream `os.File.writerStreamI` over the zeros (`os.fileW_start`), `saveCrc`,
  `encode(Metadata)`, `saveState.specPre` (both arms unified), `sync.specPreL` with `os.fileWI_preSyncOk`, `Seek`),
  every error exit; step 6: the new segment `g = ⟨bt, i2, mS.synced, ysS.map durB⟩` and all `walCut_osAUnc`
  premises, the update built, `os.Rename.specFileSnc` applied (½ tmp claim, ¼ WAL claim, path halves). New
  hypotheses: `Sum32`, `newFileEncoder`, `WriteAt.specLong`, `Fdatasync`, `sync.specPreL`, `saveState.specPre`.
- *Next* (`sorry` at the rename's return): the outcome `ro` (`hro`: success → `some`; `HQ : walCutQ … ro`,
  `Hro : renFileOut … ¼ ½ ro`; an error with `none` returns, with `some` the handle is lost too: return the error);
  step 7 `fileutil.Fsync(w.dirFile)` (`os.File.Sync.specDirS`, `walInvBody_cutSynced` under
  `wp_notCrashed_acc`, the claim's ¼ from `Hro`); step 8 (`Close` of `f2`, `LockFile` of `child dir bt`
  (`os.OpenFile.wp_fileS`), `Seek(L)`, `w.locks[last]`, `newFileEncoder`, the log) and the new handle: `h'` with
  `ino := g.ino`, `o0 := L`, `out = pend = []`, `cuts ++ [|H|]`, `pc + 1` (`walPipeH_next`), `walDirH` at the claim's
  new history (`walOutFrag` from `walCutQ`), the old tail into `walLockH` (`Hf`, `Hfdo`), `crc := crcAfter …`
  (`tailCrc_cut`). The goal is heavy (≈330 hypotheses): `iclear` what step 8 does not need before going on.

**Tenth session (branch `wal-cut10`, 2026-11-14): `WAL.cut.wp_proof` proved (no `sorry`).**
- *Steps 6-8* (`WAL__cut.lean`): the rename's outcome (an error returns; success gives `some (x, s0)`, `walCutQ`'s
  commit arm, `renFileOut`'s claims, the log bound `osLogLb (x + 1)` from `osLogged`); step 7 `fileutil.Fsync`
  (`Fsync.specDirS`, `osCommitLb (x + 1)`), then `CutFin.lean`'s `walInv_cutSynced` (`walInv_step` around
  `walInvBody_cutSynced`) at the next step through `wp_notCrashed_acc`; the metrics (`time.Since`,
  `Duration.Seconds`, the histogram); step 8 `Close` of `N.tmp`, `LockFile(fpath, O_WRONLY)` over
  `openWALFiles.lean`'s `walOpen_triple` (the WAL claim's ½ at its new history, lent and given back), `Seek`,
  `w.locks[last]` (`wp_store_slice_index`), `Sum32`, `newFileEncoder`, `lg.Info`; the new handle `h'` (`cuts ++
  [|H|]`, tail `g.ino` at `o0 = |headers|`, `out = pend = []`, `sz = |g.bs|`, `pc + 1`): `walTailW` from `walCutQ`'s
  halves and tail record, `walDirH` at the claim's new history (`cutDir_largest`, `walOut_cut`), the old tail into
  `walLockH`, `walPipeH_next` with `tmpClaim_absent` (the tmp claim's halves joined, the name deleted), the crc
  by `tailCrc_cut`, `WalHS.split_fresh`, `tailMeta_synced`. New hypotheses: `fileutil.Fsync.specDirS` (replaces
  the unused `os.File.Sync.specDirS`), `os.File.Close.spec`, `fileutil.LockFile.spec`, `time.Now`/`Since`,
  `time.Duration.Seconds.spec`, `zap.String.spec`, `zap.Logger.Info.spec` (part copy added to
  `etc/gen-part-copies.py`). Steps 1-2 stay over `Truncate.specWalTail` (being proved on `wal-tc2`) and `sync.specCut`.
- **Statement changes**: `walDirH` takes the pipeline count `k` (`walHandleIn` passes `h.pc`) and bounds the
  tail's sequence by `sq < 2^63 + k` (was `sq + 1 < 2^64`, which the new handle cannot re-establish after an
  increment): with `cut.spec`'s `pc + 2 < 2^63` it gives `sq + 1 < 2^64`, and the cut keeps it (`sq + 1 <
  2^63 + (pc + 1)`). **For W4/W5**: `Create` produces it with `sq = 0`; `ReadAll` needs the read tail's
  sequence below `2^63`. `pipeFile` carries `m.size ≤ 0xffffffff000` (the new tail's size, `walHandleIn`'s
  `sz` bound; `alloc` proves it from the pipeline's size).
- *Gotchas*: `MethodResolve` on a `time.Duration` value needs `go.NotInterface go.int64`, which instance search
  does not find (`go.int64` a plain `def`; `notInterface_Named` does not unfold it): a local `haveI` (already in
  `notes/perennial-changes.md`, 2026-11-13). `wp_method_call` searches the
  hypotheses too: clear a used `wal.histSpec` (it mentions `methods hs.ty "Observe"`) before the next call. The
  proof's end-of-declaration processing needs `maxHeartbeats 1000000`.

## W4 implementation log (branch `wal-create`, 2026-11-13)

**Statements (`sorry`-stubbed proofs):** `LinuxFs/Spec/.../storage/wal/Create.lean` (`wal.Create.spec C Mr`),
`LinuxFs/Spec/.../client/pkg/v3/fileutil/{TouchDirAll,CreateDirAll}.lean`; vocabulary
`LinuxFs/Proof/.../wal/CreateDefs.lean` (`walAuMask`, `walAreaOk`, `walAreaRes`, `osSubtreeH`/`osSubtree`,
`ClReach`/`SubCover`, `tmpName`). The main-tree axioms stay until the clients move.

Statement decisions (against the old axiom and plan §3):
1. **Client atomic updates at `walAuMask = osAuMask \ ↑walN`**, not `⊤`: the WAL commits a client update
   inside an `os` call's `osAU` (whose mask is `osAuMask`), with `walInv` open. Every WAL spec with a client
   update needs the same (W2/W6: `Save`'s update).
2. **`walAreaOk C Mr R jr r`** = `walInv ∗ osInv ∗ osSharedInv R` (persistent). **`walAreaRes jr`** (the
   program's, exclusive): its half of the area claim on names `N ⊇` every WAL name (the invariant has the
   other half: `walInv_alloc`'s `harea`), and whole claims covering every directory under a non-WAL name
   of `N`. `N` is cofinite (`NameSet`), so the cleanup's `nm.broken.<time>` names cannot be kept out of
   it: they are split off when known, which needs both halves (so `Create` takes `walAreaRes`; it holds
   the whole call permission anyway, so the exclusivity costs nothing). Two claims of `jr` containing a
   WAL name have the same key (`NamesCoh.disj`): the lemma matching the program's half with the
   invariant's.
3. **`Create` takes `osCallPerm 1` and the spine `osPathS R r (own qp) jr`**; success gives back
   `osCallPerm ½` (the other half is the file pipeline's, in the handle until `Close`: W2/W10 to agree),
   an error before the rename `osCallPerm 1`, an error after it `osCallPerm ½`.
4. **Q4 (a) is not provable** (finding, for the coordinator). `cleanupWAL`'s rename of `dir` to
   `dir.broken.*` is never fsynced, so committing `walAbsent dir` there contradicts a crash that drops
   that rename (the fresh WAL, with its `.wal` file, back at `nm`: `AbsentOk` false). Even with a fork fix
   (fsync the parent after the cleanup rename) that fsync can fail, leaving the same state. So the
   post-rename error arm is `err ≠ nil ∗ Q ∗ osCallPerm ½`: the WAL committed, fresh and unnamed, its
   directory at `dir` or moved aside. `WalsOk` already allows that (nothing ties a WAL's layout to `nm`
   in the current tree; `CrashTo`'s left disjunct covers the crash keeping the cleanup rename, since
   `named = false`). Consequence: **`Exist`'s spec needs Q4 (b)** (`false → o = none ∨ o = some d` with
   `d.H = [] ∧ ¬ d.named`). Recommended: adopt (b) for `Exist` (W12); no fork change.
5. `md` non-nil (`mp ≠ slice.nil`: a nil metadata encodes without its `Data` field, `WalPbWire.lean`).
6. **No package-initialization premise yet**: the part's `wal` has no `IsPkgInit` instance (not in
   `etc/gen-init.py`'s `LFS_PKGS`); `Create` reads `SegmentSizeBytes` and `walFsyncSec`. To add with it.
7. **`TouchDirAll`/`CreateDirAll` at the file-system level**: pre `osSubtreeH jp name h` (the whole name
   and everything under it: `MkdirAll`, the `.touch` probe), the spine of `parent`, `osCallPerm 1`, roots
   holding `/` (the `Exist` loop may climb to any ancestor, each needing a spine); post on success `name`
   holds a directory and `osCommitLb n` with `h'.next ≤ n` (F-N2's parent fsync). The old `dirDurable d`
   is the WAL layer's, derived from this by a deposit into `walInv` (`DirsOk`); the old `d ∉ area` and
   `walAreaOk` premises are replaced by owning the subtree. `CreateDirAll`: success gives `name`'s claim
   and the empty directory's whole claim (`hJ.cur = ∅`).

**The invariant during `Create`** (design; no in-flight state needed before the rename):
- Before the rename the temporary directory is the program's (`nm.tmp`'s claim and `J`'s, whole, from
  `CreateDirAll`; the segment's `osMeta`/bytes from its create); the invariant keeps half of `nm`'s
  claim (split off the area claim), for `AbsentOk`.
- At the rename (inside `os.Rename.specDirS`'s update; the claim on `[nm, nm.tmp]` half the program's,
  half the invariant's): `s.wal dir := walDurFresh md`, a layout with the one segment (`cuts = []`,
  `first = 0`, bytes durable: `wr = so`), `J`'s claim half and the segment's halves deposited. `CrashOk`
  then: a crash drops the rename (`nm` absent, `named = false`: the left disjunct) or keeps it, and with
  it everything before it (`DirOpExcl`), so `J` names the segment (F-N1's fsync of `nm.tmp` committed its
  entry) and the segment holds its synced frames.
- **Needed: strong absence.** `renameWAL`'s `RemoveAll(dir)` must be a no-op, and the left disjunct needs
  `nm` absent, not merely free of `.wal` files: the invariant must say a WAL name with no WAL is absent
  (now and in every crash its claims allow); `AbsentOk` says only "no `.wal` file". Plan: a separate
  framed fact `AbsentNone s jr cl n` in the body (merges with W2's extension), established by
  `walInv_alloc` from a boot premise (WAL-less names absent: the area empty at the first boot) and carried
  by `walCrash_pure` (`CrashTo`'s left disjunct is absence). Otherwise a non-WAL directory at a WAL name,
  which `AbsentOk` allows, would need its whole subtree owned for `RemoveAll`.
- At the parent's fsync (`osCommitLb n`, `n` past the rename's entry): `named := true` (every crash keeps
  the rename: `RegionCrashed`'s `K` holds every claimed entry below `n`, and the rename is `nm`'s last
  writer), giving `walNamed dir`.

**Done (no `sorry`):**
- `Inv.lean`: **`WalsCreateOk jr cl`**, the framed `Create` part of `walInvBody` (a new last conjunct
  `⌜WalsCreateOk jr cl⌝`, apart from `WalsOk`): a claim of the area among `cl` holds every WAL name.
  `walInv_alloc` establishes it from `harea`; `walInv_crash` drops it (`Crash.lean`, two pattern edits).
  W2's extension: add its own conjunct after it.
- `CreateNamedPure.lean`: `regionCrashed_mono`, `LastWrite` (the claim's last entry writing a name),
  `regionCrashed_lastWrite` (a committed last writer decides its name in every crash), `crashOk_named`,
  `crashOk_named_of_lastWrite`.
- `CreateNamed.lean`: `crashOk_mono`, `walsOk_mono`, `walAbsD_named`, `setNamed`, `walsOk_named`;
  `osNames_same_name` (two claims of one directory holding a name are one: same key, same history);
  **`walInvBody_named`** (the parent fsync's commit point: the invariant's contents at `s`, the program's
  claim fraction on `N ∋ nm` whose last writer of `nm` (`x`) left a directory, `osCommitLb n` with
  `x < n` ⟹ the contents at `setNamed s dir` and `walNamed dir`).

**Open, for the coordinator:** (i) every WAL operation opening `walInv` meets the `walCrashTok` branch,
which nothing the program holds excludes; `walInvBody_named` is stated on the contents for that reason.
A program-side exclusion (e.g. a fraction of a generation token the crash takes whole) is needed by every
W-unit. (ii) Q4 (a) (above). (iii) `AbsentNone` (strong absence) not yet added.

**Next:** the commit at the rename (`osAU` for `os.Rename.specDirS` built from `walInv` and the client's
update: `s.wal dir := walDurFresh md`, the new layout and its `CrashOk`); then `syncDir`, `renameWAL`,
`cleanupWAL`, `Create`'s body; `TouchDirAll`/`CreateDirAll`.

**Hypotheses the proof will take** (callee specs not yet over `fsExt`): `os.RemoveAll`, `os.MkdirAll`
(`wal-osau3`), `os.Stat` of a regular file, `fileutil.LockFile`/`FcntlFlock`, `fileutil.Preallocate`,
`File.Seek`, `newFileEncoder`/`encode`/`saveCrc` (`wal-enc4`), `WAL.SaveSnapshot` (W6/W11), `WAL.Close`
(W10), `Open`/`ReadAll` (W5/W3, for `renameWALUnlock`), `newFilePipeline` (W2), `Exist` (W12),
`filepath.Clean`/`Dir`/`Join`, `fmt.Sprintf`, `time.Now`/`Format`, prometheus `Observe`.

**Second session (branch `wal-create2`, 2026-11-13).**
- *Done:* the `nc` variants of the `os` specs `Create` uses (`os.Rename.specDirSnc`, `os.Mkdir.specSnc`,
  `os.Remove.specFileSnc`, `os.OpenFile.specCreateSnc`/`specCreateTruncSnc`), proved as `specFileSnc` was
  (the proof renamed to the `nc` variant, `wp_au_step` → `wp_aunc_step`; the old spec derived through
  `osAU_osAUnc`). `Create.spec`: the after-rename error arm was already Q4 (b) (`Q` only); it now takes
  `isPkgInit wal`. `walAreaRes`'s claim also holds every `nm.<sfx>` of a WAL name `nm` (**spec gap fixed**:
  `Create` needs `nm.tmp`'s and the cleanup's `nm.broken.<time>`'s claims, which "every WAL name" did not
  give: `walNameOk` excludes `.`).
- *`Create` cannot return `walOpenWF`* (W6's sealed handle) as `walHandleIn` stands: it requires
  `w.state ≠ nil` (`⌜sp ≠ null⌝`), and `Create` leaves `state` nil (S/wal.go:164-168; `hsIn` reads nil as
  the zero state, so the conjunct should be dropped or made `sp = null → st = zero`); `walPipeH` is W2's
  placeholder. Also: `Create` calls `SaveSnapshot` *before* the rename, on a `w` with no `dirFile` and no
  `fp`, on a file in `nm.tmp` that no WAL layout tracks, so W6's `SaveSnapshot` spec (over `walOpenWF`,
  crash-tracked tail) does not apply there: `Create` needs a pre-rename variant (the tail owned wholly,
  not in `walInv`; the encoder's `encode.specG` over a whole-resource writer, `os.File.writerStream`).
  Until W6's handle allows both, `Create` returns the ghost-only `walOpenW`.
- **Finding: the rename's client update cannot find its claim in `walInv`.** `os.Rename.specDirSnc`'s
  update must hand out `osNames jr N ½ h`, the key `(jr, N)` and history `h` the program's half has.
  `walInv` holds some claim `(jr, N1, h1) ∈ cl` holding `nm` (`WalsCreateOk`), and only `osSharedInv`'s
  coherence (`NamesCoh.disj`, `osNames_same_name`) shows `N1 = N`; `osShN ∉ osAuMask` (the step opens it),
  so the update's opening cannot. Fragments of different keys cannot be compared without the authority.
  **Proposed** (internal ghost state, not client-visible): a `WalGS` field `γcr` and a `walInvBody`
  conjunct `walCreatingAuth`: `ghostMapAuth γcr CR` with `∀ dir N h, CR !! dir = some (N, h) → (jr, N,
  h) ∈ cl`; the program's token `walCreating dir N h := dir ↪[γcr] (N, h)` (whole), made at a program
  step at `⊤` (`wp_notCrashed_acc`; both invariants open, the agreement by `osNames_same_name`), put in
  the update's `P` (`osAUnc_coiter`): its opening reads `(jr, N, h) ∈ cl` from the authority and takes the
  invariant's half; the commit updates the entry (or deletes it). `walGhost_init` allocates it empty;
  `walInv_crash` drops it, `walInv_alloc` makes it empty (pattern edits, as `WalsCreateOk`'s).
- **The commit's pure core** (`walsOk_create`, to state with it): from `WalsOk s Ls cl n`, `s.wal dir =
  none`, `InArea r dir nm`, the claim `(jr, N, h) ∈ cl` with `h.cur !! tmp = some (.dir J)`, `h.cur !! nm =
  none`, the rename logged at `x` (call begun at `st ≥ h.next`), `J`'s claim `(J, .except X, hJ)` (`hJ.cur`
  = the segment `walFileName 0 0 ↦ file g.ino` and non-`.wal` names, every entry `< st`), the segment `g`
  (bytes `(S ++ zeros).map durB`, `S` the fresh WAL's stream, meta sized), **`AbsentNone`** for `nm` (every
  crash of `cl` leaves `nm` absent): `WalsOk s' Ls' cl' n` with `s'.wal = <[dir := walDurFresh md]>`,
  `Ls' = <[dir := lay]>` (`cuts = []`, `first = 0`, `segs = [g]`, `old` zeros, `wr = so = |S|`, `z0 = 0`),
  `cl' = ` the claim logged, `J`'s appended. Its pieces: (a) the fresh WAL's `CrashOk`: a crash dropping
  `x` leaves `nm` as `cl`'s crash did (`regionCrashedK_unlog`), absent (`AbsentNone`): `CrashTo`'s left;
  keeping it keeps every entry before `st` (`Follows`), so `J` names the segment, synced: `crashTo_synced`;
  (b) the other WALs', `AbsentOk`, `DirsOk`: a crash of `cl'` is one of `cl` on the tree with `tmp`/`nm`
  restored (as W2's `treeDel` for a file rename; `Named` is reachability-free, so moving `J` changes no
  file's naming), the WALs' directories distinct from `jr`; (c) `Nodup` of the inodes by the meta
  halves' validity. Not stated yet (its `AbsentNone` premise and the claim's agreement need the two
  conjuncts above first).
- **`walCreating` in (coordinator's decision, same session):** `WalGS.γcr`; `walCreatingAuth CR` (the
  invariant's, a ghost map `dir ↦ (N, h)`) and `walCreating dir N h` (the program's whole element),
  `Ghost.lean`; `walInvBody`'s last conjunct `∃ CR, walCreatingAuth CR ∗ ⌜CreatingOk jr cl CR⌝`
  (`Inv.lean`: every entry a claim `(jr, N, h)` of `cl`); `walGhost_init` allocates it empty, `walStart`
  carries it, `walInv_alloc` puts it in, `walInv_crash` drops the old one. No other statement changed.
- *Not done:* the commit lemma, `AbsentNone`; `wal.Create.wp_proof`,
  `fileutil.TouchDirAll.wp_proof`, `fileutil.CreateDirAll.wp_proof` (still `sorry`).

**Third session (branch `wal-create3`, 2026-11-13).**
- *`AbsentNone` and `DirsAvoid`* (`Inv.lean`): `walInvBody`'s last conjunct (after W6's `walTailsRes`) is
  `⌜AbsentNone s jr cl n ∧ DirsAvoid R jr s⌝`. `AbsentNone`: a WAL name of the area with no WAL is absent,
  in every area claim of `cl` holding it (now) and in every crash the claims allow. `DirsAvoid`: every
  durable directory's lookup depends on no entry of `jr` at an `AreaSlot` name (a WAL name or `nm.<sfx>`),
  so the rename leaves `DirsOk` true (a stronger reading of `dirDurable` the area's own durable directories
  satisfy; nothing deposits one yet). `WalsStart`'s third conjunct is now "a WAL-less name of the area is
  absent" (was "holds no `.wal` file"); `walCrash_pure` proves it from `AbsentNone` or `CrashTo`'s left
  disjunct (`han` premise); `walInv_alloc` builds `AbsentNone` from it (`absentNone_start`) and takes
  `hav : DirsAvoid R jr s`; `walInv_crash` returns `⌜s'.area = r ∧ DirsAvoid R jr s'⌝` (the crash keeps
  `dirs`); `walInvBody_named` carries both (`absentNone_named`, `absentNone_mono`).
- *`CreatingOk` strengthened*: an entry `dir ↦ (N, h)` is a claim `(jr, N, h)` of `cl`, **coherent**
  (`ClaimCoh h jr N`), and **no other claim of `jr` in `cl` holds a name of `N`**. Both are facts of the
  shared invariant (`NamesCoh`) the rename's commit cannot open (`osShN ∉ osAuMask`); they are checked
  where the `walCreating` token is made (a step at `⊤`). A unit replacing a claim (`replClaim`, same key)
  keeps them as long as it does not replace the creating claim (its key is `(jr, .only [...])`, never a
  WAL directory's `(j, .except X)`).
- *`os.Rename.specDirS`/`specDirSnc` take a log lower bound* `lb` (`osLogLb lb` in the pre; `renDirOut … lb`,
  the call's start `≥ lb`; it was 0). The commit needs `hJ.next ≤ st` of the new directory's claim, which
  the rename is not given (proof: `CallBeginS` at `max h.next lb`).
- *`walsOk_create`* (`CreateCommit.lean`, proved, no `sorry`): from `WalsOk`, `AbsentNone`, `DirsAvoid`, the
  WAL-less `dir = r/nm`, the area claim `(jr, N, h) ∈ cl` coherent, holding `nm` and `tmp` (`tmp ↦ dir J`),
  exclusive on them (`hothers`), the call's start `st` with `h.next ≤ st ≤ x`, `J`'s claim `(J, except X,
  hJ)` coherent with `hJ.next ≤ st`, `J ≠ jr`, the new layout `lay` (`jr`, `nm`, `J`; `WalAbsD` of
  `walDurFresh md` over `hJ.cur`, every byte durable, stream then zeros, inodes distinct from `segsAll Ls`):
  `WalsOk` and `AbsentNone` of `createSt s dir md`, `<[dir := lay]> Ls` and `createClaims` (the area claim
  logged with `renDirEnt`/`renCur`, `J`'s appended). Pieces: `regionCrashedK_create_drop` (a crash dropping
  the rename is one of `cl`), `regionCrashedK_create_keep` (keeping it: `treeUnren`, the tree with the rename
  undone, is a crash of `cl`), `crashTo_congr`, `crashOkW_create_other`, `crashOk_create_new`
  (`crashTo_synced`), `walDirClaim_create`, `absentNone_create`, `dirsOk_create`, `walsCreateOk_create`.
- *`walOpenWF` gap (task 4, done)*: `walHandleIn`'s `⌜sp ≠ null⌝` dropped (W6's `Handle.lean`): `hsIn` reads
  nil as the zero state, and the Go code is nil-safe (`Save` replaces a nil `w.state`; `saveState`'s
  `IsEmptyHardState` reads through getters). Nothing used the conjunct.
- **Open: the client update `walCreate_osAUnc`** (not written). Its opening opens `walInv`, finds the
  claim by `walCreating`/`CreatingOk`, opens the client's update (`walAbsent dir`: `walOwn_agree` gives
  `s.wal !! dir = none`), hands out the invariant's half of `(jr, N, h)`; its commit applies
  `walsOk_create` and `walGhost_upd` (the client's `walDiskAt dir (walDurFresh md)`), deposits `J`'s half
  and the segment's halves, deletes the `walCreating` entry. **One premise it cannot get**: `hdisj`, the
  new segment's inode distinct from every `segsAll Ls` inode. With `walTailsRes`, a segment with a write in
  flight is held in the invariant as a `pwTok` (no `osMeta`), so the validity argument (the program's whole
  `osMeta` of the fresh inode against the invariant's half) covers only the segments with no write in
  flight. Options: the invariant records that every segment inode is below the file system's next inode
  (an `os` fact: a fragment of the inode allocator), or `segResF`'s in-flight case keeps half of `osMeta`.
  For W6/the coordinator.
- *Not done:* task 3 (the pre-rename `SaveSnapshot`/`encode` variant over `os.File.writerStream` and
  `io.writerStreamP`), task 5 (`wal.Create.wp_proof`, `TouchDirAll`/`CreateDirAll` `wp_proof`s: still
  `sorry`).

**Fourth session (branch `wal-create4`, 2026-11-13).**
- *The inode-clash gap, closed without an allocator fact.* Neither option of the third session works as
  stated: the shared mode exposes no fragment of the inode allocator (a create takes `st.fs.nextIno`, a
  fresh key of the `OsMeta` map, `TreeSharedCreate.lean`), and a write in flight's `pwTok` holds the
  segment's `OsMeta` *whole* (`wp_osPWriteStart` takes it), so no half of it can stay in the invariant.
  Instead **`SegFl.Ok` gains a last conjunct `0 < fl.off`** (the tail's writes come after its header
  records, synced when the segment was named): the invariant then keeps half of byte 0 of every segment
  with a write in flight (`segResF`'s `osBytes … 0 ½ (bs.take off)`, nonempty), and half of the `OsMeta`
  of every idle one. `InvInos.lean`: `segResF_ino_ne`, **`laysResF_ino_ne`** (a file the program holds
  wholly, its `OsMeta` and byte 0, is no segment of the layouts). Nothing to establish at
  `walInv_alloc` (no writes in flight) or carry through the crash (`F` starts empty). **For W6**: the
  announce step (`wp_tailPWriteStart`) must show `0 < off`; it follows from `WalAbsD.synced` (the last
  segment's synced frames, its header records among them, end at or below `so ≤ wr = off`), a lemma
  `walAbsD_so_pos` not yet written. `cut`'s deposit of its `N.tmp` (W2) gets its inode's distinctness
  from the same lemma (the pipeline's file is preallocated, so it holds byte 0).
- *`CreatingOk` strengthened* (internal): an entry's claim occurs **once** in the claims (`ClaimOnce`,
  so the commit's `replClaim` replaces exactly the occurrence the update took) and is **no other entry's**
  (the commit deletes only its own). Both hold where a token is made (the claim is split off the area
  claim then, a key not in `cl` before); `walInv_alloc` unchanged (empty map).
- *`walN_sub_au`* moved from `InvOpenTest.lean` to `CreateDefs.lean` (next to `walAuMask`).
- *`walCreate_osAUnc`* (**proved**, `CreateAu.lean`; lemmas `CreateAuLemmas.lean`): `Create`'s update for
  `os.Rename.specDirSnc` (α = the invariant's half of the area claim, `r = ½`, `renDirOut … lb`), from
  `walInv` and `walCreateP` (the `walCreating` token, the client's update, half of `J`'s claim, the
  segment whole). Abort / no effect: everything back. Commit: `walOwn_agree` gives `s.wal !! dir = none`,
  `laysResF_ino_ne` the inode's distinctness, `walsOk_create` the pure facts (`st := s0`, `lb ≤ s0` from
  `logOut`, `s0 ≤ x` from `osLogged`), `walGhost_upd` and the client's commit to `walDiskAt dir
  (walDurFresh md)`, the creating entry deleted, the claims rebuilt (`osClaims_create`), the layout
  inserted with `F` minus the new inode (`laysResF_insert`, `laysResF_congr`, `walTailsRes_create`).
  `walCreateQ (some _)`: `Q`, the segment's other halves, a past state with the fresh WAL in `dir`.
  Premises the body must establish: `J ≠ jr`, `h.next ≤ lb`, `hJ.next ≤ lb`, the layout's facts
  (`WalAbsD` over `hJ.cur`, `lay.segs = [g]`, `g.bs ≠ []`, every byte durable, stream then zeros).
- *Task 3, statements* (`Spec/.../wal/WAL__SaveSnapshotPre.lean`, built; proofs not started):
  `walPreIn` (the pre-rename `w`'s fields: no `dirFile`/`fp`/`state`, one lock), `snapFrame`,
  `walPreSyncOk f W S` (the fdatasync as a hypothesis triple: `W out` to `S out`, or back),
  **`WAL.sync.specPre`** and **`WAL.SaveSnapshot.specPre Mr`**, over `io.writerStream (wal.fileWi f) lim
  W B` (whole-resource mode; `Create` takes `os.File.writerStream` with `os.fileW`/`os.fileB`, and
  `encode.specG` through `io.writerStream_P`). On an error the file comes back in a writer state, for
  `Create`'s deferred `f.Close()`.
- *Not done:* the proofs of the two `specPre`s (callees: `encoder.flush`, `encode.specG`,
  `ValidateSnapshotForWrite`, `MustMarshalMessage`, `time.Now`/`Since`, zap `Warn`, `Observe`,
  `w.tail()`), `wal.Create.wp_proof`, `TouchDirAll`/`CreateDirAll` (their translation calls
  `syncDir(filepath.Dir(filepath.Clean(dir)))`, F-N2, and `IsDirWriteable` → `os.WriteFile`/`Remove`/
  `filepath.Abs`, none specified over `fsExt` yet), and the step at `⊤` that makes the `walCreating`
  token (split `(jr, .only [nm, nm.tmp])` off the area claim, both halves).

**Fifth session (branch `wal-create5`, 2026-11-13).**
- *Proved (no `sorry`):* `WAL.sync.wp_proofPre` and `WAL.SaveSnapshot.wp_proofPre`
  (`Proof/.../wal/WAL__SaveSnapshotPre.lean`, over their callees' specs as hypotheses); `WAL.tail`
  (`WAL__tail.lean`: `locks ↦* (ls ++ [lt])` gives `lt`); `walpb.ValidateSnapshotForWrite` (over
  `walSnapAt`, conf state non-nil unless the index is 0: `nil`). `walpb.Snapshot.GetIndex` is
  `wal-int`'s (W5, over `walSnapIdTerm`; mine dropped at the merge).
- *Leaf specs added:* the part's copies of zap's `Logger.Warn`, `Duration`, `String`, `Error`, `Int64`
  and of `time.Duration.Seconds_ptr` (`etc/gen-part-copies.py`: their main modules import the cache's
  `Base`/the server's `BaseApply` for instances only); `pbutil.MustMarshalMessage.specWalSnap Mr`
  (`LinuxFs/Spec/go_etcd_io/etcd/pkg/v3/pbutil/MustMarshalMessageWalSnap.lean`): the marshalling law,
  a hypothesis: a fresh non-nil slice of `Mr.encSnap sm`. **Open (W6/W11):** `walSnapAt sp sm cs`
  does not determine the encoding (the conf state's content, unknown fields), so the law over-constrains
  `Mr` (W6's `SaveSnapshot.spec` has the same gap); `Create`'s snapshot (`Index: 0, Term: 0`) is
  determined. `time.Now`/`Since` are Perennial's, `Observe` is `wal.histSpec` (from `encEnv`), `flush`
  was proved.
- *Spec changes (`WAL__SaveSnapshotPre.lean`, minor):* `walPreIn` gains `⌜e ≠ null⌝` (`sync` flushes
  only a non-nil encoder; no `structFieldRef` fact gives it); both `specPre`s take `isPkgInit zap`
  (the slow-fdatasync warning), `SaveSnapshot.specPre` also `isPkgInit pbutil` and `lim < 2^47`
  (`encode`'s record bound; `Create`'s `lim` is the segment size). **For `Create`:** `e ≠ null` needs
  `newFileEncoder.spec`'s post to say it (`newEncoder` allocates `e`: `typedPointsto_not_null` before
  `iStructNamed`), and the two package facts come from `isPkgInit wal`'s dependencies.
- *Tactic note:* `wp_apply` of a hypothesis triple introduced by `intro` from the spec's binders
  (`walPreSyncOk`) fails with "unknown free variable" (plain `wp_apply` then leaves the goal untouched,
  no error at the call); `ihave H := hs $$ [..]` then `wp_apply H` works.
- *Not done:* the leaves of `TouchDirAll`/`CreateDirAll` (`syncDir`, `IsDirWriteable`, `os.WriteFile`,
  `os.Remove`, `filepath.Abs`); the `walCreating` minting step; `wal.Create.wp_proof` (now with
  `wal-cut3`'s `newFilePipeline.spec`, which needs `dir.length < 2^61`), `TouchDirAll`/`CreateDirAll`
  `wp_proof`s: still `sorry`.

**Sixth session (branch `wal-create6`, 2026-11-13).**
- *Proved (no `sorry`):* `fileutil.Fsync.specDirS` (`FsyncS.lean`, over `os.File.Sync.specDirS`);
  **`fileutil.syncDir`** (`syncDir.lean`: spine fraction and call permission fraction, `osLogLb n` →
  `osCommitLb n` on success; note Go returns `Close`'s error after a successful fsync, so success = both);
  **`os.WriteFile.specEmptyS`** (`LinuxFs/{Spec,Proof}/os/WriteFile.lean`: an empty file at an absent name
  whose claim the caller holds whole; outcome `crOut`, success ⇒ created), with `os.osAU_triv` (the
  update of a caller holding all of `α`) and `os.crOut_join`; **`fileutil.IsDirWriteable`**
  (`IsDirWriteable.lean`: `.touch` absent in the directory, its `.only [.touch]` claim whole; success ⇒
  absent again), with `os.rmFileOut_join`, `osPathS_cleanAbs_keep` (the pure fact without consuming the
  spine), `abs_child`; `TouchLemmas.lean`: `os.ancPath` (`/` or `/c₁/…/cₖ`) `Clean`/`Dir` facts
  (`dir_take`, `dir_take_ne`), `osSpine_app`/`osSpine_split`, **`wp_statAnc`/`wp_syncDirAnc`** (`Stat`/
  `syncDir` of any ancestor of `parent`: a borrowed spine prefix below the root, the hypotheses above).
- *Model finding (for the coordinator, [user]):* **`os.Stat` and `os.Open` of a strict ancestor of a root
  are stuck** (the extension's `Open` needs `TreePath`; `model.stat` does not ask `PathKind` as
  `MkdirAll`'s model does). `TouchDirAll`'s `Exist` loop climbs while `Stat` fails, and the model lets
  `Stat` of the root fail (any errno), so it can reach the root's parent; its last loop then `syncDir`s it.
  Proposed: `model.stat` (and `fileutil.OpenDir`'s `Open` of a directory, for `syncDir`) answer at
  `PathKind 0` with no step (stat: a directory; open: any errno, or an fd the extension cannot fsync —
  the simplest is an error). Until then the proof takes **`os.Stat.specAboveRoot`** and
  **`fileutil.syncDir.specAboveRoot`** (`LinuxFs/Spec/os/StatAbove.lean`, `syncDir.lean`: any result,
  nothing changed) as hypotheses, unprovable against the current model.
- *Statement changes (`TouchDirAll.spec`, `CreateDirAll.spec`):* (1) **`name` absent**
  (`h.cur !! name = none`, the claim `osNames jp (.only [name]) 1 h` in place of `osSubtreeH`): the os
  layer has no spec of `OpenFile(O_TRUNC)` over an existing `.touch` (it needs the file's `OsMeta`, which
  a subtree of claims does not hold), nor of `Stat`/`MkdirAll` of an existing name; (2) the old premise
  `("/", j0) ∈ R` was **vacuous** (`RootForm` needs at least one component: `/` is never a root), dropped;
  (3) `isPkgInit fileutil` (`filepath`'s calls), `d.length < 2^60` (`filepath.Join`); (4) success post
  concrete: `name ↦ dir J`, the claim on `name` and `J`'s whole claim with `hJ.cur = ∅`, `osCommitLb n`,
  `h'.next ≤ n` (as `CreateDirAll`'s). **Consequence for `Create`:** it must reach `CreateDirAll` with
  `nm.tmp` absent: `RemoveAll(dir.tmp)` (`specDirS` needs `FilesOnly`, from `wal-owner` via
  `walAreaRes`, a hypothesis until then) when `Exist` says it exists; but `Exist` may answer `false` for
  an existing `dir.tmp` (a `Stat` error), and then `CreateDirAll` runs on an existing name: `Create`'s
  proof needs `CreateDirAll` on an existing directory of files too (spec: error, or success with it
  emptied — not available from the os layer), or a `Stat` spec that a success-free error on an existing
  name is excluded. Open.
- *`TouchDirAll`'s proof plan* (statement above; callees: `Exist.spec` over `wp_absentS`/`wp_statAnc`,
  `filepath.Clean`/`Dir`, `MkdirAll.specS` with `osAU_triv`, `wp_syncDirAnc`, `IsDirWriteable.spec`, a
  local `verify.Assert(true)` lemma): decompose the spine once (`osPathS` → root `/rcs`, `cs`;
  `parent = ancPath (rcs ++ cs)`, `d = ancPath full`, `full = rcs ++ cs ++ [name]`, `n = |full|`);
  `Exist(d)` false (absent); loop 1 invariant `d ↦ ancPath (full.take k)`, `created ↦* (range' (k+1)
  (n-k)).map (ancPath ∘ full.take)` (`k = n` uses `wp_absentS`, `k < n` `wp_statAnc`; break at `k = 0`
  by `dir_take`/`dir_take_ne`); `MkdirAll` (error: `osSubtreeH` with `cl = []` or `[(J, except [], hJ)]`,
  `SubCover` since `J` holds no directory); `osLogLb h'.next`; loop 2 over `created` (element `m`:
  `syncDir(ancPath (full.take (m-1)))`, invariant `i < |created| ∨ osCommitLb`; the last element's sync is
  below the root, so it commits); `IsDirWriteable` with the spine of `d` (`osPathS_child`: a common
  fraction of the spine and the claim, `qp` may exceed 1 when `parent` is a root) and `J`'s claim split
  at `.touch` (`osNames_split`/`rekey`/`merge`; success: the merged `cur = ∅`). **Needed first:**
  `IsDirWriteable`'s post must also say `.touch` holds no directory (for the error arm's `SubCover`).
- *Not done:* `TouchDirAll`/`CreateDirAll` `wp_proof`s (`sorry`), the `walCreating` minting step,
  `wal.Create.wp_proof`.

**Seventh session (branch `wal-create7`, 2026-11-13).**
- *Proved (no `sorry`):* **`fileutil.TouchDirAll.wp_proof`** and **`fileutil.CreateDirAll.wp_proof`**
  (`LinuxFs/Proof/.../fileutil/TouchDirAll.lean`), over hypotheses `Exist.spec`, `filepath.Clean`/`Dir`,
  `os.MkdirAll.specS`, `IsDirWriteable.spec`, `syncDir.spec`, `ReadDir.spec` (CreateDirAll) and the two
  above-root hypotheses (`os.Stat.specAboveRoot`, `syncDir.specAboveRoot`; `wal-above` replaces them).
  Structure: `wp_existAnc` (`Exist` of the path of the first `k` components of `rcs ++ cs ++ [name]`:
  `false` at `k = |full|`), the first loop as a `wp_join` at the `doFor` (invariant `d = ancPath (full.take
  k)`, `created ↦* touchC full (k+1)`), `MkdirAll` with `osAU_triv` (`mkOut_join`), the second loop
  (`forRange`; invariant `i < |created| ∨ osCommitLb h1.next`: the last element's `syncDir` is the parent's,
  below the root), `IsDirWriteable` on `J`'s claim split at `.touch` and merged back (`merged_cur`); error
  arms through `osSubtreeH_none`/`osSubtreeH_dir` (`subCover_noDirs`). `CreateDirAll`: `ReadDir` of the
  fresh directory finds `[]` (its claim's `cur = ∅`), so the `fmt.Errorf` branch is unreachable.
- *Spec change (minor):* `IsDirWriteable`'s post also says `.touch` holds no directory (`∀ J', hJ'.cur !!
  .touch ≠ some (.dir J')`; `os.rmFileOut_join` gives the entry kept or deleted), for the error arm's
  `SubCover`.
- **Finding (task 2, for the invariant's owner/coordinator): `CreatingNew`'s third clause cannot be
  established at the minting.** "No other creating entry's directory is `J`" needs, at the step at `⊤`
  that mints `walCreating dir N h J`, that every entry `dir' ↦ (_, _, J')` of `CR` has `J' ≠ J`. Nothing the
  program or the invariant holds says so: the invariant records no fragment of `J'`'s claim, and the
  program's whole `J` claim can be compared (`NamesCoh`) only with fragments it holds. Only one `Create` is
  ever in progress (it holds `osCallPerm 1` and the lock token throughout), so the fix is to know `CR = ∅` at
  the minting. Proposed (internal ghost, no client-visible change): a conjunct tying `CR` to the parking flag
  (`CR ≠ ∅ → CR` a singleton `∧` the parking flag `false`), the minting doing `walUnlockedTok_lock` (which
  `walCreateP`'s `walLockedTok` needs anyway; `b = true ⇒ CR = ∅`) and inserting the entry; the abort path
  (an unminting step: claims merged back, entry deleted, `walLockedTok_unlock`) restoring `CR = ∅`; `Close`
  (W10, not yet stated) needing `CR = ∅` when it unparks: an open handle's `walHandleDir` (registered after
  `Create`'s commit / at `Open`) could witness it (`CR ≠ ∅ →` no handle registered). The other three clauses
  and `CreatingOk`'s facts are the shared invariant's at the minting (as designed). Also needed by the
  minting (not written): the claim split's preservation of `WalsOk`/`AbsentNone`/`WalsNamed`/`walParked`/
  `DirKeysOk` (replacing `(jr, N0, h0)` in `cl` by its `.inter [nm, nm.tmp]` and `.diff` parts:
  `RegionCrashed` is the same for both claim lists under `ClaimCoh h0 jr N0`, since every logged entry of
  `h0` writes a name of one part and `valAfter` of a part agrees with `h0`'s on its names), and for the
  success post's `walAreaRes jr` the reverse merge after the parent fsync. Not started.
- *Not done:* the minting step (above), `wal.Create.wp_proof` (`sorry`). For `Create`'s handle: `walHandleIn`
  now has `walDirH` (`wal-cut5`): `Create` must give the key `walDirKey dir J X` (from `walCreateQ`), half of
  `J`'s claim, a path fraction to `dir`, half the call permission and the tail's name.

**Eighth session (branch `wal-create8`, 2026-11-13).**
- *Task 1, the creating map tied to the lock (done, `Ghost.lean`).* Implemented without touching
  `walParked` or the shape of `walInvBody` (so the concurrent units' `icases` patterns are unchanged):
  **`walCreatingAuth CR`** is the map's authority and `⌜CR = ∅⌝ ∨ ⌜CR` a single entry`⌝ ∗ walLockedTok`
  (the invariant holds the lock token, its parking flag `false`, while an entry exists).
  `walCreating_mint` (from `walCreatingAuth CR`, `walParkAuth b`, `walUnlockedTok`: `CR = ∅` (a non-empty
  map holds the one token), `b = true`, the lock taken by `walUnlockedTok_lock`, its token deposited with the
  one entry); `walCreating_delete` (now in `Ghost.lean`: the entry's deletion empties the map and gives the
  lock token back: `Create`'s commit, or the unminting on an abort, which then `walLockedTok_unlock`s);
  `walCreating_lookup` moved there. `walCreateP` no longer holds `walLockedTok` (the invariant has it);
  `walCreateQ`'s commit arm gets it from the deletion (`CreateAu.lean` repaired). **`Close`** needs nothing
  more: it holds `walLockedTok`, so a non-empty map (holding the other copy of the token) is excluded
  (`walLockedTok_excl`). The "single entry" is stated (cheap), though only the emptiness is used.
- **Finding (blocks task 2/3; for the coordinator): `Create` cannot take the claim on `nm.tmp`.** The
  minting needs `J`, so it comes after `CreateDirAll(nm.tmp)`, and `RemoveAll`/`CreateDirAll`/the segment's
  creation need the **whole** claim on `.only [nm.tmp]` (`TouchDirAll.spec`, `osSubtreeH`). But the area
  claim's other half is the invariant's (`walInv_alloc`'s `harea`; `N` cofinite, so it holds every
  `nm.tmp`), so the program must take the invariant's half: **drop** `(jr, .only [tmp], hT)` from the
  invariant's claims `cl` (W4 log's "giving back the invariant's halves"). Every pure fact of the invariant
  quantifies over `RegionCrashed cl n m'`, and fewer claims allow more crashed trees: the facts must be
  re-proved. Semantically they do not depend on `jr/tmp`, so it suffices that each crash `m'` of the smaller
  list is, with `jr/tmp` reset, a crash of the larger one: extend its kept set `K` to the dropped claim's
  entries, `K' y := (y` a remaining claim's index `∧ K y) ∨ (y` not one `∧ (y < n ∨ ∃` a kept remaining entry
  `x, y < x.start))`. The closure of `K'` needs **`Starts`** (`e.start ≤ x` for the log's entries: a kept
  dropped entry `x < n` forces every `y < x.start`) and the claims' entries at one index being the same log
  entry. Neither is available where the drop happens: the shared invariant (`osSharedInv`) has `NamesCoh`
  (every claim's history is `namesOf Vs`: the consistency) but not `Starts Vs.2`, which only the state
  interpretation's `TreeCohS` has (Ghost.lean of the extension). Without `Starts` the extension is false in
  general (a dropped entry below `n` with a large `start` forces later entries of other claims). The other
  directions are fine: adding names to `cl` (the minting's merge of `.only [tmp]` into the creating claim, the
  return of `tmp` on an error, the merge back into the area claim after the commit) only shrinks the crashed
  trees, and a split keeps them (every entry of `namesOf` writes a name of its set).
  **Proposed** (GooseLang/Ext/Fs, ghost layer, untrusted): `osSharedInv`'s pure part gains `Starts Vs.2`
  (each shared-mode step closes it with the new state's `TreeCohS.starts`, `Vs.2` being the state's log by the
  `γs` agreement); a law `osClaims_log : osSharedInv R -∗ osClaims L cl ={E}=∗ osClaims L cl ∗ ⌜∃ log, Starts
  log ∧ ∀ c ∈ cl, ∀ (x, e, _) ∈ c.ents, log[x]? = some e⌝`; on the WAL side the drop lemma (pure, the `K'`
  above, for a one-name claim: the crashed tree with `jr/tmp` set by `treeSetE`) and each fact's independence
  of `jr/b` for a non-WAL `AreaSlot b` (`crashTo_congr`/`crashOkW_create_other` do most of it for
  `treeUnren`). The same drop is needed by `cleanupWAL`'s `nm.broken.*` (W4's error arm).
- *Task 2, pure part (done, `CreateDrop.lean`, no `sorry`):* `valAfter_congrK`, `valAfter_restrict`,
  `mem_restrict_ents`/`restrict_ents_mem`/`restrict_ents_writes`; **`regionCrashedK_cover`** (a crash of
  claims covering others, entry for entry and name for name, is one of theirs: adding names, splits,
  merges); **`mintClaims cl jr N h nm tmp hC`** (the area claim `(jr, N, h)` replaced by its part off `nm`,
  `(jr, .only [nm, tmp], hC)` appended) and **`regionCrashedK_mint`** (a crash of `mintClaims` is one of
  `cl`, given `(jr, N, h) ∈ cl`, `h.restrict jr N = h` (`namesOf_restrict_self` at the step), `N ∋ nm`,
  `hC.restrict jr (N.inter [nm]) = h.restrict jr (N.inter [nm])` (`osNames_merge`'s)); **`dropK`,
  `regionCrashedK_drop1`** (the drop of a one-name claim, under `Starts log` and `ClaimsLog log cl`: the
  finding's lemma, ready for the infrastructure). Every RC-quantified fact of the invariant carries over
  to `mintClaims` by `regionCrashedK_mint` (the same tree).
- *The minting step, plan (not written):* at a step with `walInv` and `osSharedInv` open, from the
  program's `walUnlockedTok`, its half of the area claim `(jr, N, h)` (`N ∌ tmp`, after the drop), its
  whole `.only [tmp]` claim (holding `J`) and `J`'s whole claim: `walCreating_mint` (so `CR = ∅` and the
  parking flag was `true`: `walParked`'s `D = []`, so **`(jr, N, h)` is not `WalDirClaimOf Ls`**, else its
  program half would be parked as well as in hand: three halves); find `(jr, N, h)` in `cl` (WalsCreateOk's
  claim holding `nm` has the same key by `osNames_same_name`, `osNames_agree` the history; once, by the
  halves' validity); join the halves, `osNames_split` at `[nm]`, `osNames_merge` of `N.inter [nm]` with
  `.only [tmp]` into `.only [nm, tmp]`, halve both. The facts: the RC parts by `regionCrashedK_mint`;
  `WalDirClaim` memberships kept (a WAL directory's claim is `WalDirClaimOf`, so not the replaced one);
  `AbsentNone`'s first part (`nm`: `hC.cur !! nm = h.cur !! nm` from the restrictions' `cur`); `WalsCreateOk`
  (`nm` in the creating claim, the rest in the part off `nm`); `walParked` (neither new claim is
  `WalDirClaimOf`: `.only`, and `N.diff [nm]` iff `N`, `nm` not a `.wal` name); `DirKeysOk` (keyed claims
  are of `j ≠ jr`, untouched); `CreatingOk` of the singleton map (`ClaimOnce` from the halves; `CreatingNew`:
  `J ≠ jr` and no claim of `J` in `cl` holds a `.wal` name, both by `NamesCoh.disj` against the program's
  whole `J` claim; the third clause vacuous, the map being a singleton; `.only [nm, tmp]` leaves out a
  `.wal` name). The unminting is the reverse (`walCreating_delete`, then `walLockedTok_unlock`), the claims
  merged back by `regionCrashedK_cover`.

**Ninth session (branch `wal-create9`, 2026-11-13).**
- *Task 1, `Starts` in the shared invariant (done; GooseLang/Ext/Fs, untrusted).* Put in as a field of
  `NamesCoh` (`starts : Starts V.2`), not a new conjunct of `osSharedInv`'s pure part: every site that opens
  the invariant binds `%hcoh` and closes with `exact hcoh` unchanged; only the three places building a
  `NamesCoh` changed (`namesCoh_log` takes `e.start ≤ |V.2|`, the step passing `TreeCohS.callsLe`;
  `namesCoh_init` takes `Starts V.2`, the switch passing `TreeCohS.starts`; `CohEx.coh` takes it, the
  split/merge/rekey laws passing `hcoh.2.starts`). **`osClaims_log`** (`TreeShared.lean`, proof
  `osClaims_log'` in `TreeSharedCrash.lean`): `osSharedInv R -∗ osClaims L cl ={E}=∗ osClaims L cl ∗
  ⌜∃ log, Starts log ∧` every claim's entry `(x, e, _)` has `log[x]? = some e⌝`. No statement changed;
  the `LinuxFs` leaves rebuilt clean.
- **Finding and fix (internal, the crash condition's file premise).** The drop's carry-over of
  `CrashOkA` failed: a crash `m'` of the remaining claims is one of the old with `nm.tmp` reset to what
  the area claim says (`treeSetE`), and that value may be a file (nothing records that `nm.tmp`'s
  history held none: at boot, or after an error of `CreateDirAll`, whose post hides the claim's
  entries), so the reset tree may *name* a segment's inode the crash left without a file, and
  `CrashOkA`'s premise `∀ g ∈ lay.segs, Named m' g.ino → (fo g.ino).isSome` could not be given for it.
  Every proof used that premise only for segments the WAL directory lists (`named_of_mem_walInos`), so
  the premise is now **`g.ino ∈ walInos (entsOf m' lay.j) → (fo g.ino).isSome`** (`CrashOk`, `Abs.lean`;
  `CrashOkA`, `Cut.lean`; a stronger condition, weaker premise): the consumer (`walCrash_pure`) gives it
  from the crash's `Named` fact, the producers lost their `named_of_mem_walInos` steps, the transfers
  (`named_treeUnren`, `named_treeDel`) became `walInos` equalities (`mem_walInos_treeDel`, `CutCrash.lean`).
  Edited: `Abs`, `Cut`, `CrashPure`, `CrashStart`, `CutCrash`, `CutCommitPure`, `CutSynced`, `TailCrash`,
  `CreateCommit`, `CreateKeys` (one or two lines each). **For the concurrent units**: a new proof of a
  `CrashOk`/`CrashOkA` gets the premise for listed segments only (use it directly where it used
  `named_of_mem_walInos`).
- *Task 2, the drop (done, no `sorry`).* `CreateDropInv.lean` (pure): `dropClaims cl jr N h b` (the area
  claim replaced by its part off `b`), **`DropOk`** (the claims one log's with `Starts`, the area claim
  among them, its own restriction, holding `b`, no other claim of `jr` holding `b`), **`DropOk.crash`**
  (a crash of `dropClaims` is, with `b` set to some value, one of `cl`: `regionCrashedK_drop1` over the
  claims split at `b`, then `regionCrashedK_cover`), and the facts carried over: `walsOk_drop`,
  `absentNone_drop`, `walsNamed_drop`, `walsCreateOk_drop`, `dirKeysOk_drop` (`b` no WAL name, no `.wal`
  name, an `AreaSlot`; the area claim no `WalDirClaimOf`). `CreateDropStep.lean`: `osClaims_keys` (a
  list's claims of the directory sharing a name with a claim held are it), `osNames_self`,
  `osNames_halves`/`osNames_halve`/`osNames_three_halves`, `walUnlocked_park`, `parked_drop`, and
  **`walInvBody_drop`**: `walInvBody s -∗ osSharedInv R -∗ walUnlockedTok -∗ osNames jr N ½ h ={Em}=∗
  walInvBody s ∗ walUnlockedTok ∗ osNames jr (N.diff [b]) ½ _ ∗ osNames jr (.only [b]) 1 _` (premises:
  `N ∋ nm` a WAL name, `N ∋ b`, `b` neither a WAL nor a `.wal` name, an `AreaSlot`; `↑osShN ⊆ Em`). The
  area claim is found through `WalsCreateOk` at `nm`; once (a second occurrence: three halves); no WAL
  directory's (the lock free, the flag `true`, `walParked` holds its program half: three halves); the
  creating map empty (a non-empty one holds the lock token).
- *Not done:* the merge back (the reverse: adding names only shrinks the crashed trees, every RC fact
  carries by `regionCrashedK_cover` on the same tree; the non-RC facts need the merged claim to be no
  `WalDirClaimOf`, which after the commit, the lock being the handle's, `walParked` no longer gives:
  needs `jr ≠ lay.j` for every layout, e.g. a `WalsOk` fact that the area directory is no WAL's
  directory, or the merge done before the lock goes to the handle), the minting, the unminting,
  `wal.Create.wp_proof` (`sorry`).

**Tenth session (branch `wal-create10`, 2026-11-13).**
- *Task 1 (done)*: `lay.j ≠ jr` in the invariant (`WalsAt`), and the creating map's token (W1 log, ninth
  session). Both built with every `Inv` importer.
- *Covering changes of the area claims* (`CreateMerge.lean`, pure): **`CoverOk jr cl cl' n`** (crashes of `cl'`
  are `cl`'s, its claims of other directories `cl`'s with their multiplicities, its claims of `jr` say of a WAL
  name what one of `cl` said and hold every WAL name one of `cl` held); every pure fact carries over
  (`walsOk_cover`, `absentNone_cover`, `walsNamed_cover`, `walsCreateOk_cover`, `dirKeysOk_cover`,
  `walsAt_cover`); **`mergeClaims cl c1 c2 c`** (`replClaim c1 c (cl.filter (· ≠ c2))`) covers under `MergeOk`
  (`coverOk_merge`); `mintClaims` covers (`coverOk_mint`).
- *Coherence of a held claim* (`CreateCoh.lean`): **`namesOf_coh`** (`ClaimCoh (namesOf V j N) j N` under
  `Starts`: the log's entries in order, and `now_entry_slotAfter`, the tree now has each slot as its last
  writer left it, `prefTree_frame`), **`osNames_coh`**. This gives `CreatingOk`'s `ClaimCoh` at the minting.
- *The steps* (`CreateMergeStep.lean`, `CreateMint.lean`; ghost updates with `walInvBody` and `osSharedInv`
  open, at a mask holding `osShN`): **`walInvBody_merge2`** (the program's halves of two area claims, each
  found through a WAL name it holds, merged; a lock token `T` the program holds, excluding a non-empty
  creating map): the merge back after the commit (`T = walLockedTok`) and after the unminting
  (`T = walUnlockedTok`); **`walInvBody_mergeIn`** (half an area claim and a whole claim of the area with no
  WAL name, e.g. `nm.tmp`'s, the invariant holding none of it): an abort before the minting;
  **`walInvBody_unmint`** (the entry deleted, the free token back); **`walInvBody_mint`** (premises: `nm` a
  WAL name in `N`, `tmp ∉ N`, `N.diff [nm]` non-empty, `tmp` no WAL nor `.wal` name, `nm ∉ X`, `X` no `.wal`
  name; the program's free token, half area claim, `tmp`'s claim whole, `J`'s `.except X` claim whole (given
  back); out: the token `walCreating dir (.only [nm, tmp]) hC J`, halves of `(jr, N.diff [nm], …)` and of the
  creating claim, `hC.restrict jr (.only [tmp]) = hT.restrict …` (so `hC.cur !! tmp` is `nm.tmp`'s entry,
  `cur_of_part`), `hC.restrict jr (N.inter [nm]) = h.restrict …`, `hC.next = max …`). Helpers:
  `osClaims_once`, `osClaims_not_mem`, `osClaims_excl` (a whole claim held shares no name with the
  invariant's claims of its directory), `osClaims_filter_once`, `walCreating_empty`, `walParked_cover`.
  No `sorry` in any of them. **`CreateSteps.lean`**: `walInv_step` (a step of the contents as an update of
  `walInv`, with the generation's `notCrashed`, which a program step has by `wp_notCrashed_acc`) and the five
  steps in that form (`walInv_drop`, `walInv_mint`, `walInv_unmint`, `walInv_merge2`, `walInv_mergeIn`; at a
  mask `E ⊇ walN` with `osShN ⊆ E \ walN`, `walN_osShN_top` for `⊤`).
- *For `Create`'s body* (not started): the sequence is `walInvBody_drop` (tmp) → `RemoveAll`/`CreateDirAll`
  /segment/`SaveSnapshot.specPre`/fsync of `nm.tmp` → `walInvBody_mint` (J's claim split `.except walTmps` +
  `walTmpsRes J` first) → `walCreate_osAUnc` → parent fsync (`walInvBody_named`) → `walInvBody_merge2` (the
  part off `nm` and the renamed creating claim, `T = walLockedTok`; `b1` a WAL name other than `nm`, e.g.
  `nm ++ "a"`) → the handle; error arms `walInvBody_mergeIn` (before the minting) or `walInvBody_unmint` +
  `walInvBody_merge2` (after it, before the rename). Each step needs `walInv` open at a program step
  (`walInv_open` with the generation's `notCrashed`) and `osSharedInv`. Then `walAreaRes`'s pure facts of the
  merged claim (`N'' ⊇` every WAL name and `nm.<sfx>`; `SubCover`/`FilesOnly` of the program's whole claims).

**Eleventh session (branch `wal-create11`, 2026-11-14).** `wal.Create.wp_proof` started: the body is
proved from the start through `CreateDirAll(nm.tmp)` (both its arms' exits), frontier `sorry` at the
success arm (next: `walName(0,0)`/`Join`, `createNewWALFile`).
- *Done (no `sorry`):* `CreateTmp.lean` (`wp_existTmp`, `wp_removeAllTmp`: `fileutil.Exist`/`os.RemoveAll` of a
  `tmpDirH`), `CreateArea.lean` (`area_takeTmp`, `area_give`: `nm.tmp`'s claims out of `walAreaRes` and
  `walAreaRes` rebuilt), `CreateAbsent.lean` (`walInvBody_absent`/`walInv_absent`: `nm` absent in the program's
  area claim, from `AbsentNone` and the client's `walAbsent dir` read off its update, aborted; for `renameWAL`'s
  `RemoveAll(dir)` and the rename's `h.cur !! bt = none`), `CreateAbort.lean` (`create_abortTmp`: every exit
  before the minting), `CreateNamedStep.lean` (`walInv_stepS`, `walInv_named`: the parent fsync's commit at a
  program step, `dir`'s WAL from a past state), `CreatePure.lean` (names), `wal.syncDir` (spec and proof,
  `fileutil.syncDir`'s). In `Create.lean`: `Exist(dir)` (its `ErrExist` exit), `Clean`, the drop of `nm.tmp`
  (`walInv_drop`, with `walInv_absent` and `osNames_self` at the same step), `Exist(nm.tmp)`, `RemoveAll` and its
  error exit, the deferred `RemoveAll`, `CreateDirAll` and its error exit.
- *Statement changes (minor, logged here):* `Create.spec` takes `NameOk nm` (`walNameOk` allows a NUL byte;
  the syscalls need none) and `dir.length < 2^59` (`CreateDirAll`'s and `Join`'s bounds on `dir.tmp`'s paths).
  **`walAreaRes` restructured** (`CreateDefs.lean`; nothing constructs it yet): the whole claims are tagged with
  the name they are under (`cl : List (GoString × Claim)`, `clOf cl b`), `SubCover (clOf cl b)` per non-WAL name,
  and `TmpOk`: `nm.tmp` holds nothing or a directory of files (excluding a file there, which no `os` spec
  removes). Without the tags, giving back `walAreaRes` after `RemoveAll` removed `nm.tmp`'s directory `J` (its
  claim gone) needs that no other claim reaches `J` (a unique-parent fact of the tree no lemma exposes).
- *Hypotheses of `wal.Create.wp_proof`* (`LinuxFs/Spec/.../wal/CreateCallees.lean`): `wal.Exist.specCreate`
  (W12: returns with `Create`'s resources), `fileutil.CreateDirAll.specTmp` (`CreateDirAll.spec` extended to a
  leftover directory of files, which `Exist` can miss or `RemoveAll` return `nil` on, and its error arm narrowed
  from `osSubtreeH` to `tmpDirH`: provable by `TouchDirAll.lean`'s error arms, which already have the no-directory
  fact, plus the existing-directory case), `os.RemoveAll.specAbsentN` (`specAbsentS` for a fraction of a claim on
  any names: the extension's leaf steps take `.only [b]`; needed by `renameWAL`'s `RemoveAll(dir)` and the deferred
  `RemoveAll(nm.tmp)` after the rename, which hold half of `.only [nm, nm.tmp]`; not used yet), and `hErrExist`
  (**`os`'s `isPkgInit` does not record `ErrExist`**, which its initializer allocates: `etc/gen-init.py`'s
  `SPECIAL` for the part's `os` should add it, non-nil).
- *For the coordinator:* `Create`'s post is still the ghost-only `walOpenW` (sealed: handle mode and
  `walLockedTok`), so the out-record `walOutFrag (WalOut.empty.create …)` and `walTailsFrag ∅` that
  `walCreateQ`'s commit returns are dropped there; whoever moves `Create` to `walOpenWF` puts them (and
  `walDirH`'s `walNamed`, the md bound: the caller's `mp ↦*□ md`, a slice, so `md.length < 2^63`) in the
  handle. Proposed next unit: `WAL.renameWAL` as its own spec for `Create` (pre: `walPreIn` without `fp`/
  `dirFile`, the creating claim's half with `nm` absent (`walInv_absent`), `walCreateP`, `osLogLb lb`, `walTmpsRes J`,
  the whole call permission; post: committed (`Q`, the logged claim's half, the handle alloc'd:
  `walOpenW`/`walLenLb 0`/`walSyncedLb 0`/`walPurgeW`, half the permission) or not (everything back) or committed
  with an error), its `renameWALUnlock` (`Close`, `Open`, `ReadAll`) a hypothesis; then `Create` after it is the
  parent fsync (`walInv_named`), the merge back (`walInv_merge2`, `b1 := nm ++ "a"`) and `area_give`.

**Twelfth session (branch `wal-create12`, 2026-11-14).** `Create` continued past `CreateDirAll`: frontier `sorry`
now at `f.Seek(0, io.SeekEnd)` (after `createNewWALFile`'s success).
- *Done (no `sorry`):* `walName(0, 0)`/`Join` (`p = child (child r nm.tmp) (walFileName 0 0)`); `createNewWALFile(p,
  false)` over `CreateSeg.lean`'s **`wp_createSeg`** (the `OpenTriple` over `os.OpenFile.specCreateSnc`, trivial
  update, as `PipeLemmas.wp_createTmp`; `walOpenFlag_create`), with `J`'s claim split at the segment's name
  (`osNames_split` + `osNames_rekey` to `.only [b]`) and the spine to `nm.tmp` (`os.qp_common`, `osPathS_child`,
  `os.osPathS_unchild` after); its error arm proved to the abort (`segClaim_back`/`filesOnly_merge`: the segment's
  claim merged back into `J`'s, files only, so `tmpDirH` again; the deferred `RemoveAll`; `create_abortTmp`).
  `Create.lean` is now at `HeapGS HasLC.hasLC` (the handle's).
- *`hErrExist` dropped* (task 4): the part's `io/fs` fact records `ErrExist` non-nil and the part's `os` fact
  records `os.ErrExist` (`LinuxFs/Proof/os/PkgInit.lean`; `etc/gen-init.py`'s `LFS_SPECIAL['io.fs']`/`['os']`,
  variants of the main tree's, which is unchanged; `--check` passes). Read in `Create` by `isPkgInit_access`.
- *`Create.spec` returns `walOpenWF P Mr`* (task 3; ledger entry 2026-11-14): binders `P Mr`, `walAreaOk walCodec Mr`,
  `HasLC.hasLC`; success `Q ∗ walOpenWF ∗ walNamed ∗ walLenLb 0 ∗ walSyncedLb 0 ∗ walPurgeW` (the call permission's
  half inside the handle's `walDirH`). No new client-visible ghost state.
- *`renameWAL` stated* (task 1): `Spec/.../wal/WAL__renameWAL.lean` (`renameWAL.spec P Mr`, `RenameWALOk`,
  `renameWALPost`), generic in the rename's update `U` (`Create`'s is `walCreate_osAUnc`'s, `U := walCreateQ`; an
  aborted `U none` must rebuild the update, for the retry), four post arms (committed with `w`'s pipeline and
  directory fd; committed with a reopened client handle, from `renameWALUnlock`; not committed; committed with an
  error). `WAL__renameWALUnlock.lean`: its retry, same vocabulary and post, a hypothesis of `renameWAL`'s proof.
  `Proof/.../WAL__renameWAL.lean`: `sorry` stub over its callees (`specAbsentN`, `Rename.specDirSnc`,
  `newFilePipeline`, `OpenDir`, `renameWALUnlock`). `Create.wp_proof` takes `renameWAL.spec` (unused yet).
- **Finding G-spine (for the invariant's owner; blocks `renameWAL` and every `walDirH` producer):** no
  `osPathS R dir dq J` to a WAL directory can be built. `osSpine` is made of fractions of `.only [c]` claims, but
  `nm` is only ever in the creating claim `.only [nm, nm.tmp]` (half `walInv`'s) and, merged back, in the cofinite
  area claim (half `walInv`'s); `osPathS_child` needs a `.only [nm]` fraction. `newFilePipeline` (`pipeRes`),
  `OpenDir(w.dir)` and `walDirH` all need one. `renameWAL.spec` takes it as a caller-supplied law (`Sp`/`SpR`,
  `RenameWALOk`'s third conjunct), which nothing supplies. Possible fix: each WAL name's `.only [nm]` claim kept
  apart from the area claim (split at creation, half in `walInv`, fractions of the program's half for spines;
  `WalsCreateOk` restated), or a spine through a fraction of any claim holding the name (an `Fs` change; but a
  fraction held by a spine pins the area claim, which the next `Create` must change).
- **Finding (renameWALUnlock):** `os.Rename`'s errors are all `*os.LinkError`, so every failed rename takes
  `renameWALUnlock`, whose `w.Close()` reaches `w.dirFile.Close()` with a nil `dirFile` (`ErrInvalid` in Go, stuck
  in the trusted model: plan §0 item 6); and its `Open`/`ReadAll` need `walAreaRes`, split up by `Create` then. Its
  spec is a hypothesis until the model handles a nil `*os.File`'s `Close`.
- *Next:* `f.Seek(0, io.SeekEnd)` is a promoted method of `*fileutil.LockedFile` (`methods (ptr LockedFile) "Seek"
  lf`): needs a lemma unfolding it to the embedded `*os.File`'s (`os.File.Seek.wp_end`, size 0 after the create);
  the deferred `f.Close()` likewise (`LockedFile`'s `Close`). Then `Preallocate` (`PreallocateAu`/`preallocExtend`
  specs), `newFileEncoder`, the encoder's records and `SaveSnapshot.specPre`, `syncDir(nm.tmp)` (proved), the
  minting (`walInv_mint`, after `J`'s `.except walTmps` + `walTmpsRes J` split), `renameWAL` (blocked on G-spine),
  the parent fsync (`walInv_named`), `walInv_merge2`, `area_give`, the handle (`walOpenWF_iff`, `⧗ 0`).
- *`Create.wp_proof`'s hypotheses now:* `wal.Exist.specCreate`, `fileutil.Exist.spec`, `filepath.Clean.spec`,
  `os.RemoveAll.specAbsentS`/`specDirS`, `fileutil.CreateDirAll.specTmp`, zap `String`/`Error`/`Warn`,
  `fmt.SprintfWalName.spec`, `filepath.Join.spec`, `createNewWALFile.specLocked`, `os.OpenFile.specCreateSnc`,
  `WAL.renameWAL.spec`.

**For `wal-create6` (the invariant's owner, 2026-11-13).** (1) `walAreaRes jr` gains `⌜∀ nm J, walNameOk nm →
h.cur !! tmpName nm = some (.dir J) → ∀ hJ, (J, NameSet.except [], hJ) ∈ cl → FilesOnly hJ.cur⌝` (a leftover
`nm.tmp` holds only files; `CreateDefs.lean`, importing `LinuxFs.Spec.os.RemoveAll`), for `os.RemoveAll.specDirS`
of a leftover `dir.tmp`. (2) The `walCreating` token is `walCreating dir N h J` and the minting must establish
`CreatingNew` (W1 log, seventh session, task 2). (3) `walCreate_osAUnc`'s commit (task 3) needs more of the
program: see the W1 log's task-3 entry.

## 11. Coordinator decisions after W2 and W4 (2026-11-13)

- **Q4 revised to (b)** (W4 found (a) unprovable: `cleanupWAL`'s rename to `dir.broken.*` is never fsynced,
  so a crash can bring the fresh WAL back after a committed `walAbsent`; a fork fsync could itself fail):
  `Create`'s after-rename error arm returns `Q` only, and `Exist`'s `false` arm allows `o = none ∨` a fresh,
  unnamed WAL (`d.H = [] ∧ ¬ d.named`). No fork change.
- **`walInv` and the crash case**: `walInv`'s body is `body ∨ C` with Perennial's crash tokens (`NC q` held by
  the running program's operations, `C` deposited by the crash step, `NC ∗ C ⊢ False`), so an operation that
  opens `walInv` with an `NC` fraction always finds the body. W1's crash lemmas restated accordingly (branch
  `wal-nc`).
- **Masks**: every WAL client update sits at `walAuMask = osAuMask \ ↑walN` (it commits inside an `os` call's
  update with `walInv` open); `Save`'s and `SaveSnapshot`'s too.
- **Call permission**: `Create`/`Open` return `osCallPerm ½`; the file pipeline holds the other half until
  `Close` (W2, W10).
- **Invariant extensions** are separate conjuncts of `walInvBody` (W4's `WalsCreateOk`, then W2's, W6's), so
  the units merge.

## W6 implementation log (branch `wal-save`, 2026-11-13)

**Statements (stubs, `sorry` proofs, pushed first for W2):** in `LinuxFs/Spec/.../wal/`, spec names under the
full Go path (`go_etcd_io.etcd.server.v3.storage.wal.WAL.<M>.spec P Mr`, the main tree's `wal.WAL.<M>.spec`
being another name): `Save`, `SaveSnapshot`, `Sync` (client: `walAreaOk walCodec Mr R jr r`, the sealed handle
`walOpenWF P Mr w dir`, the update at `walAuMask`, plan §11); `sync`, `saveEntry`, `saveState`, `cut` (internal,
over `walHandleIn P Mr w dir h`); `encoder.encode.specG` and `WAL.saveCrc.spec` (`encoder__encodeG.lean`, over a
guarded writer). Proof stubs `LinuxFs/Proof/.../wal/WAL__{Save,SaveSnapshot,Sync,sync,saveEntry,saveState}.lean`
take their callees' specs as hypotheses (`cut`'s is W2's to prove or restate).

**Vocabulary** (`Handle.lean`):
- `WalHS`: the program's knowledge of its open WAL (history `H`, metadata, cuts, tail inode, encoder start
  offset `o0`, writer bytes `out`, pending `pend`, records of the last operation not yet encoded `rest`, the
  hard state at `w.state` `st`, ghost names `γH`/`γS`/`γW`, `enti`/`snapi`). `walHandleIn`: the struct's
  fields, the encoder with CRC `h.crc` (chain end after the encoded records), the tail's lock and file
  (O_WRONLY fd), `walTailW` (offset, the program's halves of the tail's `OsMeta`/bytes, its half of the write
  position `γW`), the tail's guarded writer, `ghostVar γH ½ (H, md, cuts)` (to agree with the invariant),
  `walPipeH` (W2's placeholder: the pointer only), `walOpenW` (the ghost handle). `walOpenWF := ∃ h,
  walHandleIn h ∗ ⌜h.Done⌝` (sealed; `Done`: `rest = 0`, `st = walLastHS H`). **Create/ReadAll should return
  `walOpenWF`** (W4's spec returns the ghost-only `walOpenW`).
- **`io.writerStreamG wi W G`** (finding): `io.writerStream`'s `Write(p)` quantifies over every `p`; for the
  crash-tracked tail no `W` makes it true (a write of non-stream bytes breaks `CrashOk`, and the bridge cannot
  know `p` is the stream). The guarded contract adds `G (out ++ p)`, `G` persistent and prefix-closed: the
  tail's `G` is a mono-list lower bound of its intended stream (`walTailG γS`), grown at `Save`'s commit. The
  page writer's and encoder's proofs need re-running over it (`encode.specG` is a hypothesis till then); the
  bridge (`wal-bridge`) should prove `io.writerStreamG (wal.fileWi f) (walTailW f i γW o0) (walTailG γS)`.
- `WalPbIn` (the raft messages `Save` reads: `hsIn`, `entIn`): the part cannot import the main tree's
  `hsRO`/`entRoC` (the raft-root clash, §10); clients instantiate it, the proofs will take the laws
  (`MustMarshalMessage`, `GetIndex`, `IsEmptyHardState`, `MustSync`) as hypotheses.
- Package init: no `isPkgInit wal` (the part's `wal` has none, as `Create`); `encEnv`/`walCrcTable` in the handle.

**Spec decisions:** Save/SaveSnapshot's error arm `∃ d, Q d` (committed, handle lost: Q6). **`Sync`'s error arm
loses the handle** (deviation from the main tree, which kept it): `sync` flushes the page writer first, and a
failed flush leaves part of `pend` written with the buffer emptied. Spec defects for the ledger: this one.

**Invariant extension (designed, not yet in `walInvBody`):** a conjunct `walTailsRes s Ls` (after W4's and W2's):
per WAL with an open handle, `ghostVar γH ½ (d.H, d.metadata, lay.cuts)`, `monoListAuthOwn γS 1 (segStream …
last)` (the tail's intended stream), `ghostVar γW ½ lay.wr`, the names keyed by the tail's inode; plus a write in
flight's `pwTok` in place of the tail's `segRes` halves between `PWriteStart` and `PWriteFinish` (the bridge's;
the crash lemma must then take files with tokens, I3). Also needed in it: F-Z's fact that `old` is zeros from
`z0` on (`walAbsD_snoc`'s `hZ`).

**Proved (pure, no `sorry`):** `SaveRecs.lean`: `tailRecs_snoc`, `allRecs_snoc`, `tailStream_snoc` (an appended
operation's records extend the tail's and the WAL's, chained from the CRC after all records). `SaveAbs.lean`:
the commit keeps the crash condition (`walImg_snoc`, `crashTo_snoc`, `crashOkA_snoc`, `crashOk_snoc`) and the
static relation (`walAbsD_snoc`, premises `hZ` and the new records' fit); `segRecs_snoc_op`; the sync's commit
keeps the static relation with `d.m := |H|` (`syncLay`, `walAbsD_sync`; its crash condition is W2's
`crashTo_synced`).

**Left (hardest first):** the append's crash condition (bytes `[wr, wr+k)` from `durB old` to `[(old,0),(x,n)]`:
`CrashTo` of any image mixing old zeros and the new frames under W1G, via the encoding layer's prefix lemma); the
`walTailsRes` conjunct and its repair of the W1 lemmas that destructure `walInvBody`; the Iris proofs of
`sync`, `saveEntry`, `saveState`, `Save`, `SaveSnapshot`, `Sync`; NC tokens once `wal-nc` lands.
- **W6, the file as a stream writer** (`wal-bridge`, 2026-11-13). `io.writerStream wi lim W B`: on
  success all of `p` and `n = len(p)`; on an error the broken state `B out xs` and **any count**
  (`os.File`'s trusted `Write` returns `ArbitraryInt` and sets the offset to `-1` on an error, so
  "the count is the bytes written" is unprovable over the unchanged model); `lim` bounds the total
  (`o0 + lim < 2^62`, the model's `offMax` panic). PageWriter/encoder specs and proofs follow (their
  error posts: `B (out ++ a) b`, `a ++ b` a prefix of pending ++ input). `os.File.WriteAt.specLong`
  (any length, chunks of `maxRW`; premise `m.lo ≤ m.size`; post `pwPost m off A j`, `PwOutA`):
  proved up to 1 GiB, **`sorry` past it** (`Proof/os/WriteLong.lean`, plan in its header).
  `os.File.Write.wp_empty`/`wp_long` (`OffLong.lean`) and the bridge `os.File.writerStream`
  (`Proof/os/WriterStream.lean`: `fileW`/`fileB` over `StreamOk`, whole resources) proved.
  **Open:** `wal-save`'s `io.writerStreamG` keeps the old error clause (`W (out ++ ys)`, `n = |ys|`),
  which no `os.File` can meet (offset `-1`, arbitrary count): it needs the `B` form. And the guarded
  bridge for `walTailW` (program halves) needs a crash-aware `Write` that opens `walInv` around each
  `PWriteStart`/`PWriteFinish` (the in-flight write's token in `walTailsRes`), not this whole-resource bridge.

- **(W4, branch `wal-create3`, 2026-11-13) `walHandleIn` no longer has `⌜sp ≠ null⌝`**: `Create` leaves
  `w.state` nil and `hsIn` reads nil as the zero state, so `Create` can return `walOpenWF`; nothing used the
  conjunct. A `cut`/`saveState` proof that wants a non-nil pointer gets it from `Save`'s nil check.

## fileutil, the rest (branch `wal-fu2`, 2026-11-13)

Specs in `LinuxFs/Spec/go_etcd_io/etcd/client/pkg/v3/fileutil/` (and `wal/createNewWALFile.lean`), proofs
beside them in `LinuxFs/Proof/...`:
- **`ZeroToEnd`** (proved): pre the offset `o ≤ size`, the file unmapped, whole `OsMeta` and the bytes
  `[o, size)`; success: offset `o`, same size and mappings, `[o, size)` an `osZerosA` run; error: some
  offset, some size `w ≥ o`, some `w - o` bytes from `o`. Callees `os.File.Truncate.spec`, `Preallocate.spec`.
- **`LockFile`** (proved, ofd and flock variants over the package fact `fileutilInit`): **generic in
  the open spec** (decision: one statement for every open variant instead of one spec each):
  `fileutil.OpenTriple P path flag perm A C` (`LockDefs.lean`) is the premise, `{{P}} os.OpenFile
  {{ fileutil.openPost A C }}`, the shape of `specCreateS`/`specCreateTruncS`/`wp_fileS` (outcome `x`,
  resources `A x ok`, on success a fresh file and fd on `i` with `C x i`); post `fileutil.lockPost`
  (the locked file `fileutil.lockedFile lf f`, persistent, with the file and fd whole; on an error a
  nil pointer and `∃ b, A x b`: a lock error closes the file it opened). Callees `os.File.Fd`,
  `Close`, `syscall.Flock`, `fmt.ErrorfErrs` (`ofdLockFile` wraps the open error with `%w`).
  **Open, blocking instantiation:** `openPost`'s error branch needs `fmtErrorOkOrNil err` (for that
  `%w`), which the part's open specs do not give yet: add it to `os.OpenFile.specCreateS`,
  `specCreateTruncS` and `wp_fileS`'s error posts (their model's error is `pathError "open" name
  (errno e)`; `os.wp_wrapErrno_ok`'s argument, `pathError_fmtErrorOk` + `errnoErr_fmtErrorOk`).
- **`createNewWALFile`** (proved, `wal/`): `specLocked` (`LockFile`'s post) and `specFile`
  (the open's), generic the same way at `wal.walOpenFlag forceNew` (`0x41`/`0x241`), mode `0600`.
- **`Exist`** (proved): generic in the `Stat` spec. **`WithExt`** (proved): `fileutil.withExtFn g ext`
  (persistent closure contract).
- **`ReadDir`**: spec over `Open/Readdirnames/Close.wp_dirS` (result `fileutil.ReadDirOut names
  (optsExt es) rs`: sorted, filtered); **proof `sorry`** (two loops left).
- Not done: `TryLockFile` (the WAL does not call it; needs `errors.Is(err, EWOULDBLOCK)`),
  `IsDirWriteable` (reached through `TouchDirAll`: `os.WriteFile`, `Remove`).
- Build note: the seeded `.lake` replayed stale `Proof/.../storage/WalEncDecode` and
  `GooseLang/Ext/Fs/TreeSharedRes` artifacts after the `wal-int` merge; deleting them fixed it.

**W6, second session (branch `wal-save2`, 2026-11-13): the tail's invariant conjunct and the writer
contract.**
- *`ByteOk` generalized* (`Abs.lean`): an unsynced byte is the candidate `(y, 0)` then candidates of
  its intended value `x` stamped by the writes that announced it (any number: retries, a write in
  flight, a write that stopped short), none past the stream (new `a` argument, `b < |S|`); written
  ⇒ cache `x` and at least one. Lemmas `byteOk_durB`, `val_unw`, `val_w`, `ByteOk.snoc`,
  `byteOk_sync`; CutLay/CutSynced/CrashPure/SaveAbs repaired.
- *Writes in flight in `walInv`* (`Inv.lean`): `SegFl` (token, offset, data, change number, the
  segment's `OsMeta`/bytes before it); `segResF F g` (idle: `segRes`; in flight: `pwTok` and the halves
  around the range, as `cfInv`'s `invRes`), `laysResF F Ls` in place of `laysRes`, the layout holding
  the segment *as announced* (`SegFl.Ok`: `cfMeta`, `pwAnn` in the range), so `WalAbsD`/`CrashOk` are
  unchanged. `walInv_crash` takes segments with tokens (`CrashTakeSeg.lean`: `crashRestAt_take_tok`,
  the fixed-crash `crashRest_take_tok_keep`; `crashRest_take_segs` replaces `crashRest_take_files`).
  **In-size writes only** (`SegFl.Ok`: `off + |data| ≤ m.size`): a write in flight past the size has no
  ghost candidates for the bytes it extends the file with; the `Save` crossing `SegmentSizeBytes`
  writes there. Open (next unit): extend `old` with zeros at the announce, candidates from `OsMeta.pc`.
- *`walTailsRes s Ls F`*, the last conjunct of `walInvBody` (after W4's `walCreating`): a new
  `WalGS` field `γt`, the tails' authority `walTailsAuth T` (`dir ↦ γ`), the handle's `walTailKey dir
  γ`; per open tail `ghostVar γ ½ (tailG d lay g.ino (F !! g.ino))` = `(H, md, cuts, wr, ino, write
  in flight)`, the WAL, layout and last segment, and F-Z (`TailZeros`). The record replaces the
  design's `γH`/`γS`/`γW` (one name; no mono list: the program's `H` ties the guard to the
  invariant's history). `walTailsRes_mono` (CreateNamed's `setNamed`).
- *The writer contract* (decision): a **pure guard**, `io.writerStreamP wi ok W B`
  (`Proof/io/WriterStream.lean`; `io.writerStream_P`: the length bound is `ok ys := |ys| ≤ lim`), not
  the Iris-guarded `writerStreamG` (removed). The tail: `ok := tailOk Mr H md cuts o0 sz` (a prefix of
  the intended stream past `o0`, inside the preallocated size `sz`), `W := walTailW f fd name dir γ i
  H md cuts o0 sz` (file, offset, program halves, key, the record at `wr = o0 + |out|`), `B := True`
  (the handle is lost on an error). `encode.specG`/`saveCrc.spec` restated over `writerStreamP`
  (`B` error form; `ok` prefix-closed): `cut`'s owned `N.tmp` instantiates them with
  `os.File.writerStream` + `io.writerStream_P` (the coordinator's "second tail mode" is this: the
  encoder specs are generic, only `walHandleIn` is the crash-tracked mode).
- *Stated, `sorry`* (`TailWriter.lean`): `wp_tailPWriteStart`, `wp_tailPWriteFinish` (the two
  `pwrite` steps opening `walInv`), `wal.tailWriter`. Plans in the file header. Needed below them:
  the pure `walsOk_announce`/`walsOk_finish` (static relation and **the append's crash condition**,
  the hard part), a `Write`-over-any-`WriteAt` lemma (`Off.lean`'s `Write.wp_spec` generalized), the
  WAL copy of `WriteAt.wp_proof_crash`'s loop, and the page writer/encoder re-proved over
  `writerStreamP` (mechanical: their length side conditions become `ok` of a prefix).
- *Handle* (`Handle.lean`): `WalHS` has `γ` (tail record) and `sz` (tail size) in place of
  `γH/γS/γW`; locks are `fileutil.lockedFile lf f` (persistent, `wal-fu2`'s) with the file whole.
  Not yet: the `cuts.length + 2 < 2^63` bound `cut` needs (Save must carry it: a premise of `Save`, or
  derived from the name bound); Save/saveEntry/saveState/sync/Sync/SaveSnapshot proofs (still `sorry`).

**W6, third session (branch `wal-save3`, 2026-11-13): the append's crash condition, its core.**
- *Proved* (`TailCrashPure.lean`, pure, no `sorry`): `TailCands X Y cs so z0` (the tail's candidates:
  durable `X b` below `so`; above, `(Y b, 0)` then candidates of `X b` stamped `> 0`; `Y = X` below `z0`,
  zeros from `z0`: `ByteOk` + F-Z), `AsOf` (`AsOfOneG` over a candidate function, `asOfOneG_asOf`),
  `tail_frame_match` (a frame the reader accepts at a record boundary is the intended frame: as of one
  change its core is the intended bytes; as of the sync it is the intended bytes below `max so z0` and
  zeros above, a zero length word; the padding is the intended zeros since `Y` is zero past `z0`),
  `tail_decode` (the reader of the crashed tail, from the segment's chain start, reads the intended
  records `R.take j` for some `j ≥ jE`, their frames a prefix of the image, and rejects the next).
  It needs W1 only along the reader's path (`acceptsFrom`), not `NoCollisionFrom`'s every boundary.
- *Its premises the invariant must carry* (new, for the lift): **`max so z0` is a record boundary** of
  the last segment (`(recFrames C (R.take jE)).length = max so z0`): `z0` ends the frames found, and a
  tail fdatasync (`sync`) comes after the encoder's flush, at the end of the records encoded (`cut`'s and
  ReadAll's syncs: at a boundary too). Proposed home: `walTailsRes`'s per-tail pure part (beside
  `TailZeros`), since appends happen only under an open handle; the sync's commit re-establishes it from
  the handle's `pend = []`.
- *Next (the lift to `CrashTo`)*: the bridge `cs b := if b < g.bs.length then (g.bs.getD b (0, [])).2
  else [(0, 0)]` (`TailCands` from `WalAbsD.last`'s `ByteOk` + `TailZeros`; `AsOf` from `W1G`, every
  accepted core lying in the image, which `FileCrashedR`'s `hi = g.bs.length` keeps inside `g.bs`); the
  record count `j` to an image `I` of the history (`walImg_histCut` + `walImg_lift` +
  `flatMap_histCut`, as `walDecodeFiles_walImg`; the earlier segments unchanged since `lastStart ≤ d.m`);
  the tree part of `CrashTo` (entry, `q`, `walInos`, purge bound) from the old `CrashOk`, the pwrite steps
  leaving the claims alone (an `fo₀` with the old last image, `OsFile.ofBytes` of the stamp-0 values,
  satisfies the old `FileCrashedR` once `metas` also says `zf ≥ size`).
- *Writes past the preallocated size (task 1), findings, not yet implemented*:
  1. `WalAbsD.metas` (`lo = hi = |bs|`) cannot hold of a tail written past its size: `pwPost` keeps
     `lo` at the old size and raises `hi` to `off + len`; a short write leaves `hi > size`. The last
     segment needs `so ≤ lo ≤ |bs| ≤ hi`, and bytes in `[|bs|, hi)` need candidates.
  2. `FileCrashedR` (`GooseLang/Ext/Fs/CrashFiles.lean`) ignores `OsMeta.tc`, so a crash image's bytes in
     `[size, hi)` are unconstrained, and `w1G_of_W1` needs the image no larger than `g.bs`. The fix: a
     segment's ghost tail `[size, hi)` from `tc` (idle: `MetaOk.tail`; in flight: `OsCoh.tok_cand`,
     `ti.m0.pc`), taken by a WAL-local variant of `crashRestAt_take`/`_tok` (as `CrashTakeSeg.lean` does),
     `SegG` gaining the tail's candidates and `SegFl.Ok` recording `pwTail`'s (the layout's `om.tc`, which
     `FileCrashedR` does not read, can carry them: `wp_osPWriteFinishK true` gives `pwTail`).
  3. **The candidates past the size are zeros only if the size is page-aligned**: after a sync,
     `OsMeta.synced` sets `zf := pageUp size`, `tc := ∅`, and the model keeps stale bytes in the last page
     past the size (`OsFile.ofDisk`, "stale ones included"); a write past an unaligned size has arbitrary
     durable candidates there (`wp_osPWriteFinishK`'s `zs` unconstrained), against which W1 cannot exclude a
     stale frame. Reachable: a crossing `Save` grows the tail to an unaligned `curOff`, a crash after
     `cut`'s truncate and before its rename leaves it the last file, `ReadAll`'s `ZeroToEnd` keeps that
     size, and the next `Save` writes past it at once. Cut's and Create's segments (64 MB, aligned) are
     fine. **For the coordinator** (trusted-semantics question, [user]): either the model's truncate and
     sync zero the page past the size (ext4 does: `block_truncate_page`, writeback zeroes past `i_size`),
     or the WAL's proof needs `pageUp size = size` of a reopened tail, which it cannot establish.
     *Answered 2026-11-13* (`notes/axiom-review/eof-page.md`, branch `wal-eof`): ext4 zeroes the tail at every
     `ftruncate` (not at a sync: a clean page keeps a stale tail), so the model is loose; proposal P2
     (`ftruncate` announces zeros to the end of the old end's page) gives every byte from `off` on the one
     candidate `(0, 0)` after `ZeroToEnd` and its `Fdatasync`; and a soundness gap found there (P1: writeback
     zeroes the tail, a byte at or past `sizeLo` may come back zero). Both pending the user [user].
  So task 1 changes `WalAbsD.metas` and `SegG` (W1/W2/W4's files: `CrashPure`, `CrashStart`, `CutLay`,
  `CutSynced`, `CreateCommit`, `CrashTakeSeg`) and waits on item 3; not started, to avoid conflicts with
  the concurrent branches.
- *Not done this session*: the step specs (`wp_tailPWriteStart`/`Finish`), `wal.tailWriter`, PageWriter and
  encoder over `writerStreamP`, the cuts budget, `saveEntry`/`saveState`/`sync`/`Save`/`SaveSnapshot`/`Sync`
  (all still `sorry`).

**W6, fourth session (branch `wal-save4`, 2026-11-13): the record boundary and the append's crash
condition lifted to `CrashOkA`.**
- *`TailBound`* (`Inv.lean`, decided): `walTailsRes` takes `C Mr` and its per-tail pure part gained
  `TailBound C Mr d lay` beside `TailZeros`: some `jE ≤ |R|` (`R` the last segment's records) with
  `|recFrames (R.take jE)| = max so z0`. Depends on `d` only through `H`/`metadata` (`TailBound.congr`), so
  `walTailsRes_mono`/`walTailsRes_create` carry it. **Obligations it adds**: whoever adds a tail record
  (`Create`, `ReadAll`) and whoever moves `so`/`z0`/the tail (`sync`'s commit: `so := wr` with `pend = []`,
  `jE = |R|`; `cut`'s new segment) proves it.
- *Proved, pure, no `sorry`* (`TailCrash.lean`): `lastRecs`/`lastC0`/`lastHdr`/`lastOps` (the last segment's
  records split off, `lastRecs_eq`, `allRecs_split`, `chainEnd_allRecs_split`, `chainOk_lastRecs`);
  `tailImg Mr d cuts n` (the history before the last cut, then `histCut` of the last segment: a `walImg`
  when `n` covers the synced records, `tailImg_walImg`; its last records are the first `|hdr| + n`,
  `lastRecs_tailImg`; `walImg_toRaw`); **`crashTo_tail`** (the reader's `j` from `tail_decode` to
  `CrashTo`, the tree part from a `CrashTo` over any other image `fo0` of the tail; the fresh reader of W1G
  and the chained one agree since a cut segment starts with its CRC record, intact below `so`,
  `acceptsFrom_crc0`); **`crashOkA_tail`** (a step changing only the tail's bytes and `wr` keeps
  `CrashOkA`: the old condition applied with the tail imaged as of the last sync, `syncImg`, on which W1G
  holds by itself, `w1G_sync`); `walAbsD_so_pos` (for `SegFl.Ok`'s `0 < off`, `wal-create4`).
- *`crashOkA_tail`'s hypotheses the step proofs must discharge*: the tail's `OsMeta.zf` is none or at least
  its length (`MetaOk.zf` gives it from the state); the tail's length unchanged (in-size writes); **no
  alternative layout holds the tail** (`halt`): true in practice (a cut's alternative is the layout
  before its rename, whose segments are the new one's but the last), but `AltOk` says only "a prefix";
  proposed: `AltOk` gains `lay0.segs.length < lay.segs.length` (`crashOkA_cut` has it from `cutLay`), a W2
  file, not changed here.
- *`walTailW`* (`Handle.lean`): the fd is any with write access (`∃ rd, osFd fd 1 ⟨i, rd, true⟩`;
  `ReadAll`'s tail is `O_RDWR`).
- *Not done*: the Iris step specs (`wp_tailPWriteStart`/`Finish`: open `walInv` via `wp_atomic_nc`, update
  `F`/`Ls`, `crashOkA_tail` for the crash part, `walAbsD` of the announced layout), `wal.tailWriter`, the
  PageWriter/encoder over `writerStreamP`, the cuts budget, `saveEntry`/`saveState`/`sync`/`Save`/
  `SaveSnapshot`/`Sync` (still `sorry`).

**W6, fifth session (branch `wal-save5`, 2026-11-13): the tail's two `pwrite` steps proved.**
- *Pure* (`TailStepPure.lean`, no `sorry`): `tailLay lay pre g wr` (the layout with the tail and write
  position replaced), `segAnn` (the tail as a write's first step announces it; `segAnn_ok`: its
  `SegFl.Ok`) and `segFin` (as the second step leaves it, `finBytes`); `walAbsD_tail` (the static
  relation from the new tail's `ByteOk`), `walAbsD_announce` (needs the change number `n > 0`),
  `walAbsD_finish` (the written bytes' intended values come from the announced candidates:
  `n > 0` puts `(data_j, n)` among the stamped ones); `crashOkW_tail` (`crashOkA_tail`; the
  alternative's segments are a prefix of `pre` by `wal-cut3`'s strict `AltOk`, merged here);
  `walsOk_tail` (the invariant's `WalsOk` with the layout replaced).
- *Iris* (`TailAcc.lean`, no `sorry`): `walInvBody_tail`, the handle's access to its tail (with
  `walTailKey` and its half of the record: the WAL, layout, tail's `segResF`, the other half; given
  back with any tail, write position and writes in flight changed on the tail only, given the new
  layout's static relation); `osBytes_agree`; `tailVar` (a tail record's half with the WAL's camera:
  `ghostVar` without `letI := walAllG` resolves another `AllG` instance, so the specs use `tailVar`).
- *Proved* (`TailWriter.lean`): `wp_tailPWriteStart` and `wp_tailPWriteFinish` (each opens `walInv`
  with `wp_atomic_nc` + `walInv_open`). Statement changes: the record halves are `tailVar`; the start
  takes `TailMeta m bs` and gives `0 < n`; the finish takes `fl.rz = none`, `0 < fl.n`,
  `TailMeta fl.m fl.bs` and gives `TailMeta` of the result and its unchanged size.
- *`TailMeta m bs`* (`Handle.lean`, in `walTailW`, decided): the program's tail facts the invariant
  does not keep: `|bs| = m.size` (byte agreement needs equal lengths), `m.maps = ∅` (`wp_osPWriteStart`'s
  cells), `zf ≥ size` (`MetaOk.zf`, a fact of the state only a step sees; `crashOkA_tail`'s `hzf`).
  **Obligation** for whoever builds `walTailW` (`Create`, `ReadAll`): prove it of the tail's concrete
  `OsMeta`.
- *Writes past the preallocated size*: still a hypothesis (`tailOk`'s size clause; `SegFl.Ok`); untouched
  pending `wal-p12`.
- *Not done*: `wal.tailWriter` (`sorry`; plan: a tail `WriteAt` from `Crash.lean`'s
  `WriteAt.wp_proof_crash` loop with these steps, maxRW chunks up to 1 GiB as there, then `Off.lean`'s
  `Write.wp_spec` over it, then the `writerStreamP` bridge as `os.File.writerStream`); PageWriter/encoder
  over `writerStreamP`; the cuts budget; `saveEntry`/`saveState`/`sync`/`Save`/`SaveSnapshot`/`Sync`;
  the coordinator's `SaveSnapshot` fix (`walSnapAt` with the full protobuf content model, `encSnap` a
  function of it) and `newFileEncoder.spec`'s `e ≠ null`.

**W6, sixth session (branch `wal-save6`, 2026-11-13): the tail writer over a `WriteAt` contract.**
- *A retry rewrites* (finding): the model's `PWriteFinish` may return `EINTR` with `k > 0` bytes landed
  (`((k = |data| ∨ 0 < k) ∧ e = 0 ∨ e ≠ 0)`), and `WriteAt`'s loop then retries from `nn`, rewriting them. So
  the steps are generalized (`TailStepPure.lean`, `TailWriter.lean`, proved): `wp_tailPWriteStart` takes a write
  at `off ≤ wr` (the record's write position), its intended bytes from `off`, with `off = wr ∨` the program's
  byte at `off` carries a candidate stamped positive (so `off` is past the synced bytes: `ByteOk.synced_stamps`,
  a synced byte is `durB`); `walAbsD_announce` past `so`, at or below `wr` (`ByteOk.ann`: an announced
  candidate of the intended value keeps an unsynced byte's `ByteOk`, written or not); `wp_tailPWriteFinish`
  (any `wr ≥ fl.off`) leaves `max wr (fl.off + k)` and gives the range's positive candidates (`segFin_cand`);
  `walAbsD_finish` derives `so ≤ fl.off` from the announced byte. The start's continuation gives `0 < off`.
- *Proved over `wp_tailWriteAt`*: `wp_tailWrite` (`(*os.File).Write` on the tail, `Off.lean`'s `wp_long` with
  the tail's `WriteAt`) and **`wal.tailWriter`** (the `writerStreamP` bridge, empty writes by `wp_empty`).
  `walTailW`'s pure part gained `sz < 2 ^ 62 ∧ 0 ≤ fd.toInt` (the model's `Write` bound and an open fd):
  **obligation** for `Create`/`ReadAll` when they build it (the size is at most ext4's `s_maxbytes`).
- *`wp_tailWriteAt` is `sorry`*: the loop (Löb over attempts, chunks of `maxRW` by `ownSlice_slice`, the
  invariant `off + nn ≤ wr ≤ off + nn + min (len - nn) 2^30`, `off + nn = wr ∨` a positive candidate at
  `off + nn`, `TailMeta`, the size) is drafted, but `omega` explodes (> 14 GB) in the loop's contexts: the
  facts on `sint.Z (nnv + W64 2^30)`/`sint.Z (sl.len - nnv)` (toInt of `BitVec` sums) make each call
  case-split hugely; clearing them per call helped only partly. Next: every arithmetic step through top-level
  `Nat` lemmas (`tw_minA`/`tw_minB` are the first), or clear the `BitVec` facts right after use. The draft is
  the body of `wp_tailWriteAt` at commit `df9397b7b4` (`wal-save6`'s "tail WriteAt loop, WIP") plus the
  isolation edits in this log.
- *Repairs*: `walInvBody_tail`'s callers pass the name fact (`rfl`); my own `walParked` repair of `TailAcc`
  was dropped for the owner's (`segResP`).
- *Not done*: PageWriter/encoder over `writerStreamP` (`encode.specG`, `saveCrc.spec`), `newFileEncoder`'s
  `e ≠ null`, the `SaveSnapshot` fix, the cuts budget (with the coordinator's requests: the handle should
  carry `∀ b ∈ h.cuts, b < |H|`, needed by `cut.spec` with `walCutPos`), `saveEntry`/`saveState`/`sync`/
  `Save`/`SaveSnapshot`/`Sync`.

**W6, seventh session (branch `wal-save7`, 2026-11-13): the tail `WriteAt` loop; the encoder over the guarded
stream.**
- *`wp_tailWriteAt` proved* (`TailWriter.lean`; with it `wp_tailWrite` and `wal.tailWriter`, no `sorry` in the
  file). The loop's arithmetic goes through small top-level lemmas over `Nat` (`tw_*`: `tw_sub`, `tw_addMax`,
  `tw_offAdd`, `tw_full_iff` for the `BitVec` conversions, each proved in an empty context; `tw_eintr`,
  `tw_short`, `tw_full` for the invariant), the invariant written without `min` (`wr ≤ off + len`,
  `wr ≤ off + nn + 2^30`) and the `max` of the finish generalized to a variable with its three facts
  (`tw_max`). No `omega`/`word` in the loop's context but on linear facts; peak memory stayed low (the
  check ran under a 12 GB cgroup, `systemd-run --user --scope -p MemoryMax=12G`, a guard worth keeping).
- *The page writer and the encoder over `io.writerStreamP`* (statement changes, internal): `PageWriter.{flush,
  Flush,Write}.spec` and `wal.write.spec` now take a prefix-closed guard `ok` (premise `ok (out ++ pend [++ xs])`)
  in place of the length bound `lim` (the bound is the instance `io.writerStream_P`); the proofs' writes are
  prefixes of `out ++ pend ++ xs`. `encoder.encode.wp_proofG : encode.specG` and `encoder.flush.specP` /
  `wp_proofP` (new) are the main proofs; `encode.spec`/`flush.spec` (length-bounded, used by `SaveSnapshotPre`,
  `cutPre`) are derived (`wp_proof` from the guarded one), unchanged. Gotcha: `wp_auto` unfolds
  `encodeFrameSize`'s length word into an `if`; to pass it by name, fold it back (`efs_fst_eq`) and
  `generalize` it before `wp_auto`.
- *`WAL.saveCrc.spec` proved* (`WAL__saveCrc.lean`, over `encode.specG`; `recSize_crc`, with a local copy of
  raft's `varintSize_le_succ`, which the part cannot import).
- *`newEncoder`/`newFileEncoder` give `e ≠ null`* (post conjunct at the end; no user had destructured it).
- *Merged `wal-int` (`wal-cut7`)*; everything above builds against it.
- *Findings for the remaining units* (not done):
  1. **`sync`, `saveEntry`, `saveState` are blocked on writes past the tail's size** as stated: the tail's guard
     `tailOk` needs `o0 + |out ++ written| ≤ sz`, and nothing in `walHandleIn` bounds `o0 + |out| + |pend|` (or
     the next frame) by `sz` (only by `0xffffffff000`); a `Save` that crosses `SegmentSizeBytes`, and
     `sync.specCut` (`wal-cut7`: pending bytes past the truncated size), write there. These wait for
     `wal-zte`'s past-size design; with an in-size premise they are provable now over `tailWriter`.
  2. **The cut bound is `≤`, not `<`**: right after `cut`, `h'.cuts = h.cuts ++ [|H|]`, so the handle can carry
     only `∀ b ∈ h.cuts, b ≤ |H|`; `Save` gets `cut.spec`'s strict premise after its append (`|H| + 1`). Not yet
     added to `walHandleIn` (it changes the pure conjunct `wal-cut7` just edited; to add with the next `cut`
     merge: `cut`'s post keeps it, `Create`/`ReadAll` establish it).
  3. **The cuts budget does not fit receipts as such**: a handle could hold `⧗ k` (one receipt per cut of this
     lifetime, `[ReceiptBoundLe GF (2^62)]`, `receipt_lt`), but `ReadAll`'s handle starts with the cuts of the
     WAL it read (`c0`, bounded only by a slice length, `< 2^63`), and `c0 + k` can pass `2^63 - 2`. Options: bound
     `c0` by the tail name's sequence (an invariant fact `cuts.length ≤ sq`, then `sq + 1 < 2^64` is still too
     weak for `2^63`), or weaken `cut.spec`'s `cuts.length + 2 < 2^63` (where `cut` needs it: the `int`
     arithmetic on the sequence?) to what the name bound gives. For the coordinator: which bound `cut` really
     needs.
  4. `SaveSnapshot`'s `walpb.Snapshot` registration not started.

**W6, eighth session (branch `wal-save8`, 2026-11-13): the tail's fdatasync, proved down to `fileutil.Fdatasync`.**
`wal-zte2` (the `WalAbsD` relaxation) was not pushed during the session, so task 1 (writes past the
size) did not start; the session did the fdatasync half of `sync`, which every remaining unit needs.
- *`syncLay` reshaped* (`SaveAbs.lean`, W6's own; no other user): `syncLay lay pre g0` replaces only the
  tail, by `syncTail g0` (its `OsMeta` `om.synced` — the invariant's half must be the state's — and every
  byte `durB`); the earlier segments are untouched (durable already, `intact`). `walAbsD_sync` restated
  over it (`hs : lay.segs = pre ++ [g0]`), its proof by named fields (`refine { names := …, … }`), so the
  `metas` field is the only place `wal-zte2`'s relaxation touches it.
- *`crashTo_tailM`* (`TailCrash.lean`): `crashTo_tail` with the tree part taken from a `CrashTo` of the
  WAL at any mark `m0` covering the earlier segments (`{ d with m := m0 }`); `crashTo_tail` is the
  wrapper at `d.m` (callers unchanged).
- *Pure, no `sorry`* (`TailSyncPure.lean`): `walSyncS s dir d` (the mark at `|H|`); `tailBound_sync` (the
  record boundary is the stream's end: `jE = |R|`, `max wr z0 = wr`); **`crashOk_sync`** (as
  `crashOkA_tail`: the old condition with the tail imaged as of the last sync, then `crashTo_tailM` at the
  raised mark: a crash after the sync reads the whole history); `walsOk_sync`, `dirKeysOk_sync` (no cut
  pending), `absentNone_sync`, `dirsAvoid_sync`, `walsNamed_relay`.
- *Iris, no `sorry`* (`TailSync.lean`): **`walInvBody_sync`** — with `walTailKey`, the tail record's half
  and `walCutFrag none` (the lock token's: no cut's rename pending, so `CrashOkA … none`), the tail's part
  out, and *two* closings as an `∧`: the success (`F !! ino = none`, `wr` the stream's end, `zf`; the
  synced tail's `segRes`) to `walInvBody (walSyncS s dir d) ∗ walPast …`, and the unchanged one
  (`segResF F g0 -∗ walInvBody s`) for a failed fdatasync. Helpers: `walTailsRes_zeros` (F-Z and the
  record boundary from the tail record), `segsAll_sep_relay`, `walParked_relay` (any relayout with the
  same directory and tail inode/length), `walMapLe_sync`, `absLe_sync`, `walKeysInArea_sync`.
- *Steps, no `sorry`*: **`wp_tailFsync`** (`TailFsync.lean`, the extension's `Fsync` with `walInv` open:
  halves joined, `wp_osFsync`, success gives the program's synced halves and `walSyncedLb dir |H|`, failure
  nothing); `syscall.Fdatasync.wp_tail` and **`fileutil.Fdatasync.wp_tail`** (`TailFdatasync.lean`, over
  `walTailW` with `o0 + |out| = |tailStream|`; takes `os.File.Fd.spec`; `TailMeta.synced`).
- *What `sync.wp_proof` still needs*: (a) `encoder.flush.specP` over `wal.tailWriter` with the guard
  `tailOk … (out ++ pend)`: **blocked on writes past the size** (the page writer's pending bytes may pass
  `sz` even when `curOff < SegmentSizeBytes`), task 1 once `wal-zte2` lands; (b) the handle's
  `walCutFrag none` (inside the sealed `walOpenW`'s `walLockedTok`: the proof unseals with `import all`
  of `Ghost.lean`); (c) the leaf calls `time.Now`/`Since`, `Duration.Seconds`, `zap.Duration`,
  `Logger.Warn`, `walFsyncSec.Observe` (`wal.metricsInit`, `Metrics.lean`); (d) `o0 + |out ++ pend| =
  |tailStream|` from `WalHS.Split` at `rest = 0`.
- *Not done*: tasks 1-4 of the brief (writes past the size; the handle facts `∀ b ∈ cuts, b ≤ |H|` and
  `walLastIdx` only when `Done` — note for whoever does it: `saveEntry`/`saveState` then need a premise
  covering the case their post is `Done`, e.g. `rest = 1 → walLastIdx H ≤ max(e.Index, snapi)`, which
  `Save` must supply from a `snapi`-bounds fact the handle does not carry today; the cuts budget; the
  `walpb.Snapshot` registration).

**W6, ninth session (branch `wal-save9`, 2026-11-13): `sync` over the tail, the handle's index facts, the cuts
budget, `walpb.Snapshot`'s wire format.**
- *`sync.wp_proofIn` proved* (`WAL__sync.lean`; `sync.specIn`, the spec with `o0 + |out ++ pend| ≤ sz`): the
  encoder's `flush.specP` over `wal.tailWriter` (guard `tailOk`, from `WalHS.split_rest0`/`tailOk_rest0`), the
  crash-aware `fileutil.Fdatasync.wp_tail` (`walCutFrag none` out of the sealed `walOpenW` by Ghost's existing
  law `walOpenW_cut`, so no `import all`), the leaf calls (`time.Now`/`Since`, `Duration.Seconds_ptr`, zap's
  `Duration`/`Warn`, `walFsyncSec.Observe` from `encEnv`'s `wal.histSpec`). `sync.wp_proof` (`sync.spec`) still
  `sorry`: it is `wp_proofIn` once the tail writer accepts writes past the size (task 4). Gotcha: `wp_if_destruct`
  did not find the `took > warnSyncDuration` test here (it did in `wp_proofPreL`); a `by_cases` on the condition
  with `decide_eq_true/false` and `wp_pures` works.
- *`walHandleIn` (statement changes, internal; obligations for the producers `Create`, `ReadAll`, `cut`)*:
  `⌜e ≠ null⌝` after the encoder field (`sync` tests it; `newFileEncoder` gives it); `isPkgInit wal` beside
  `encEnv` (zap's init for the log lines, by `iPkgInit`); the index facts are now `(rest = 0 → walLastIdx H ≤
  max(enti, snapi)) ∧ walMaxSnapIdx H ≤ snapi` (new `walMaxSnapIdx`, `walLastIdx_snap` by `rfl`): `saveEntry`
  sets `w.enti` per entry, and a `Save` going back below an earlier snapshot record needs the snapshot bound
  (ledger 2026-11-13, "withdrawn"). **`ReadAll`'s obligation**: `walMaxSnapIdx H ≤ snapi` (every snapshot record
  before its first segment is below that segment's name index ≤ the target snapshot's index, which it reads
  and raises `snapi` to); `Create`'s: `0 ≤ 0`. `cut`'s proof repaired (two patterns, one rebuild).
  `saveEntry.spec` takes `e.Index < 2^64-1` and `rest = 1 → walLastIdx H ≤ max(e.Index, snapi)`; `saveState.spec`
  the `rest = 1` case of the bound. **The `SaveSnapshot` index premise is not added** (ledger): the code takes
  the maximum (S/wal.go:1161).
- *The cuts budget (decided, no client-visible statement change)*: `walOpenWF := ∃ h, walHandleIn h ∗ ⌜h.Done⌝ ∗
  ⧗ h.pc` (one receipt per file the pipeline handed over this lifetime); `walAreaOk` gains `⌜ReceiptBoundLe GF
  (2 ^ 62)⌝` (the area's owner keeps the adequacy theorem's constant, bounds-plan rules 1-2; appended last, so
  `⟨#Hinv, #Hos, -⟩` patterns still match); `walPc_bound`: `walAreaOk -∗ ⧗ (n + 1) -∗ ⌜n + 2 < 2^63⌝`. `Save`'s
  proof takes a step's receipt (`wp_take_receipt`, `Proof/ReceiptTactics.lean`) before `cut`, merges it
  (`receipt_add`), gets `cut.spec`'s premise and repacks `⧗ (pc + 1)`. **Obligations**: `Create`/`ReadAll` return
  `walOpenWF` with `⧗ 0` (`receipt_zero`, an update); whoever builds `walAreaOk` (the boot, `walInv_alloc`'s
  caller at adequacy) proves `ReceiptBoundLe GF (2 ^ 62)`.
- *`walpb.Snapshot`'s wire format* (`Proof/.../storage/WalPbSnapWire.lean`, main tree, pure: `WalSnapC`/`WalCsC`,
  `snapEnc`/`csEnc` (non-packed repeated `uint64`s, `auto_leave` 0/1), `snapSize`, `walSnapSchema`/`walCsSchema`,
  `WalSnapC.levels`) and its Go test `examples/stdlib/walpb/snapshot_test.go` (`TestSnapshotEncoder`: 200,000 random
  contents, `proto.Marshal`/`proto.Size`/`proto.Unmarshal` against `snapEnc` at both levels; `TestSnapshotSchema`;
  passes, protobuf-go of `examples/go.mod`, go1.27.3).
- *Not done (next, in order)*: (1) the registration in the part (`walpb/PbSnapshot.lean`, as `PbRecord.lean`:
  `snapRoC` with a frozen `*raftpb.ConfState` of the part's raftpb and both levels' hidden fields in invariants,
  `snapDecode` opaque, the axioms `snapEncC_ok` and `pbSnapC_reg` **pending the user's review**; the model
  `WalSnapC.model : SnapshotMetadataM` there, the part's `PbModel`); (2) the content-model fix: `walSnapAt Mr sp
  md` := a frozen `walpb.Snapshot` at some content `c` with `c.model = md` and `snapEnc c = Mr.encSnap md` (the
  client chooses `Mr.encSnap`, one wire form per metadata: a C6 obligation, plausible since the server builds
  every `walpb.Snapshot` the same way, `storage.go:62`), `cs` derived from `c.confState`; `pbutil
  .MustMarshalMessage.specWalSnap` then derived from the registered type's `MarshalPb`; its users
  (`SaveSnapshotPre`, `Create`); (3) task 4, writes past the preallocated size: after `wal-zte2`, a write past
  the size opens a window (`pwPost` raises `hi`), so `TailMeta`'s `lo = hi = size` and `wp_tailPWriteStart`'s
  in-size `SegFl.Ok` must be extended (candidates of the new bytes from `OsMeta.pc`, P2's zeros), then `tailOk`'s
  size clause dropped and `sync.wp_proof := wp_proofIn`; then `saveEntry`, `saveState`, `WAL.sync.specCut`,
  `Save`, `SaveSnapshot`, `Sync`.

**W6, tenth session (branch `wal-save10`, 2026-11-14): `walpb.Snapshot` registered, `walSnapAt` over its content,
`Sync` proved; writes past the size designed (I3b log).**
- *`walpb.Snapshot` registered in the part* (`walpb/PbSnapshot.lean`, as `PbRecord.lean`): the content `WalSnapC`
  (`WalPbSnapWire.lean`), its model `WalSnapC.model : SnapshotMetadataM` (a nil conf state as the zero one),
  `snapRoC` (field-wise frozen, the conf state frozen too, `walCsRoC`; both levels' hidden fields in invariants,
  `snapHidden`/`walCsHidden`, raft's `pbMsg` shape: **at C6** the conf state the server passes is raft's own object,
  `storage.go:62-66`, whose hidden fields are in raft's `pbMsg raftpb.ConfState` invariant, which `walCsHidden` must
  then be), `snapOwnC` (the decoded object owned whole), `pbSnapM`/`pbSnapC`. **Two axioms pending the user's
  review** (§10): `snapEncC_ok` (protobuf-go decodes `snapEnc c` to `c.model` when both levels' unknown fields
  are valid; evidence `TestSnapshotEncoder`/`TestSnapshotSchema`) and `pbSnapC_reg` (the registration). Not yet
  used by any result.
- *The content-model fix* (ledger 2026-11-14): **`walSnapAt Mr sp md cs`** (statement change, the part's specs):
  a frozen snapshot at a content `c` with `c.model = md`, `Index`/`Term` set, `cs = c.confState.isSome`,
  `snapEnc c = Mr.encSnap md`; `walSnapIdTerm sp s` over the content's getters; `walSnapsAt` unchanged in form.
  They replace the main tree's in the part: `etc/gen-part-copies.py`'s `Whole` gained `omit` (top-level
  declarations left out of a copy) and the part's `WalDisk` copy omits the five and imports `PbSnapshot`, so every
  importer keeps the names. Laws: `walSnapAt_idTerm`, `snapRoC_ne`, `recCell_of_eq_some`, `walCsOptRoC_null`.
  Repaired: `Snapshot.GetIndex` (now also of a nil `Index`), `ValidateSnapshotForWrite` (spec `∀ Mr`), `Clone`,
  `SaveSnapshotPre`. **C6 obligation**: one wire form per snapshot metadata (`Mr.encSnap`), plausible as the
  server builds every `walpb.Snapshot` the same way, given raft's conf states carry no unknown fields.
  `MustMarshalMessage.specWalSnap` stays a hypothesis (true of the real marshaller now; derivable from the generic
  `pbutil` spec at `pbSnapC` once the part has a copy of it, plus protobuf-go's non-nil result).
- *`Sync.wp_proof` proved* over `sync.spec` (`WAL__Sync.lean`): `walHandleIn_lenLb` (`HandleLaws.lean`, `import
  all` of `Handle`; with `walOpenWF_iff`, the unsealing law) bounds the caller's `walLenLb w dir n` by the handle's
  history, opening `walInv` at the call's first step (`wp_notCrashed_acc`), from `walInvBody_lenLb`
  (`TailLenLb.lean`: the tail record agrees with the invariant's WAL, `walPast_ghost_le`'s `absLe`).
- *Writes past the size*: designed, not implemented (I3b log, "Writes past the preallocated size open a window too":
  the tail needs `zf = some size`; the window's continuation is `wal-tc2`'s, shared).
- *Not done (next, in order)*: (1) the append commit, `Save`'s and `SaveSnapshot`'s shared unit: an invariant step
  appending an operation to the WAL's history with the client's update committed (`walDiskAt` moved, the tail record's
  `H`, `rest` the operation's record count, `walAbsD_snoc`/`crashOk_snoc` for the pure part), at the first step
  after the lock (the error arms already need `Q d`); (2) `Save` over it (`cut.spec`'s premises now include
  `h.cuts.Pairwise (· < ·)` and `h.md.length + (Mr.encState h.st).length < 2^42` from `wal-cut9`: the cuts are
  pairwise increasing as positions in a growing history, so the handle can carry it, `cut`'s post appending `|H|`;
  the `2^42` bound is not derivable from the handle today and must come from the area or the WAL's creation:
  `md` is fixed at `Create` (a premise there, the server's metadata is a small protobuf: `Create` should take
  `md.length < 2^41` and the handle carry it), but `Mr.encState` is the client's marshaller parameter, about
  which nothing is known: the real one is protobuf's `HardState` encoding (three optional `uint64`s, at most 33
  bytes), so the bound is a property of `Mr` the client must state (e.g. `∀ hs, (Mr.encState hs).length < 2^41`
  in `walAreaOk` beside `Mr`, or a premise of `Save`): **a client-visible statement change, for the
  coordinator** (proposal: in `walAreaOk`, discharged at C6 by the server's `Mr`, as the one wire form per
  metadata of the ledger's 2026-11-14 entry));
  (3) `SaveSnapshot` over `SaveSnapshotPre`-style steps and the commit; (4) the past-size writes once `wal-tc2`'s
  window continuation lands, then `saveEntry`/`saveState`/`sync.wp_proof`.

**W6, eleventh session (branch `wal-save11`, 2026-11-14): the append's commit; the marshaller's law; the metadata's
bound.**
- *The append's commit, `Save`'s and `SaveSnapshot`'s shared step, proved (no `sorry`)*: `AppendPure.lean` (pure:
  `walAppS s dir d o`, the WAL state with `o` appended; `walsOk_append` (`walAbsD_snoc` with F-Z from the tail record,
  `crashOk_snoc`: no cut pending, so no alternative layout), `dirKeysOk_append` (any pending cut), `absentNone_append`,
  `dirsAvoid_append`, `tailBound_snoc`, `absLe_append`, `walKeysInArea_append`, `walDurLe_append`); `Append.lean`:
  `walTailsRes_append` (both halves of the tail record moved to `H ++ [o]`), `walInvBody_append` (the program's map
  `walOwn` moved with the state, `walGhost_upd`), **`walTail_append`** (at an update of mask `⊤`, before any step of the
  call, `wp_notCrashed_acc`: `walInv` opened with `notCrashed`, the client's update at `walAuMask` committed through
  `atomic_update_mask_weaken`; out: `Q d` with `d.H` the handle's history, `walLenLb w dir (|H| + 1)`, and the static
  relation's cut facts `walCutPos`/`Pairwise`, i.e. `cut.spec`'s premises); its fit premise is a function (the WAL's
  records fitting, so do they with `o`'s), so the caller needs only `o`'s records' fit. `HandleAppend.lean`:
  **`walHandleIn_append`** (a quiescent handle, `rest = 0`: the handle at `{h with H := H ++ [o], rest := |opDs o|}`,
  its CRC and stream split unchanged, `WalHS.encRecs_snoc`/`crc_snoc`/`split_snoc`; premises: `∀ c, RecsFit walCodec
  (chainRecs walCodec c (opDs Mr o.toM))` and the new history's index facts, `saveOp_idx` for a `Save`).
  `SaveSnapshot` cannot use the handle form (its `w.snapi` is raised after the encode, so the handle's
  `walMaxSnapIdx ≤ snapi` fails in between): its proof uses `walTail_append` on the unsealed handle's pieces.
- *The marshaller's law (decided, ledger 2026-11-14)*: `walAreaOk`'s last conjunct `⌜∀ hs, (Mr.encState hs).length <
  2^32⌝` (`walAreaOk_encState`); patterns repaired (`walPc_bound`, `Create.lean`'s `⟨…, %hrb, -⟩`).
- *The metadata's bound*: in the sealed client handle, `walOpenWF := ∃ h, walHandleIn h ∗ ⌜h.Done⌝ ∗ ⌜h.md.length <
  2^41⌝ ∗ ⧗ h.pc` (`walOpenWF_iff`, `Sync` repaired), not in `walHandleIn` (no internal spec changes; `md` never
  moves, so `Save` keeps the fact in its context). **Obligations**: `Create` (when it returns `walOpenWF`) takes
  `md.length < 2^41`; `ReadAll` needs the invariant to keep `d.metadata.length < 2^41` (from `Create`'s commit).
  `h.cuts.Pairwise` is not carried: `walTail_append` returns it.
- *Spec defect (ledger 2026-11-14, pending)*: nothing bounds the records' size (`Mr.encEntry e`, `Mr.encSnap md`), which
  the commit needs (`WalAbsD.fit`, `2^56`) and the encoder needs (`2^47`): proposed premises of `Save`/`SaveSnapshot`.
- *Records' size (minor fix, ledger 2026-11-14)*: `Save` takes `∀ e ∈ es, (Mr.encEntry e).length < 2^40`,
  `SaveSnapshot` `(Mr.encSnap md).length < 2^40`; `saveOp_fit` (over `recsFit_chainRecs_small`, `recSize_le`)
  gives the append's fit premise for a `Save`.
- *`Save.wp_proof` started* (`WAL__Save.lean`): the commit at the call's first step (`wp_notCrashed_acc`,
  `walHandleIn_append` with `saveOp_fit`/`saveOp_idx`), then **`sorry`** (the body). What the body needs, in order:
  (1) `wp_with_defer`, `sync.Mutex.wp_Lock` on `w.mu` (`walHandleIn`'s `isMutex … True`; `import all` of `Handle`
  to reach it, then fold back before each callee); (2) the shortcut (`WalPbIn.IsEmptyLaw`, `WAL__cutPre.lean`'s,
  as a hypothesis; `len(ents) = 0`): `walOpenWF` back at `H ++ [save hs []]` (`rest = 0`; `Done` needs `walLastHS`
  of an empty save unchanged, a small lemma), `Hlb`, `Q d`, `walMustSync` vacuous; (3) `st == nil`/`w.state == nil`
  → `&raftpb.HardState{}`: a law of `P` (a fresh zero `HardState` holds `hsZero`; `P.hsIn null hs → hs = hsZero`),
  a new hypothesis; (4) `raft.MustSync` over `P.hsIn` (a new law, `MustSync(st, prev, n) = (n ≠ 0 ∨ vote/term
  differ)`, which with `Done`'s `st = walLastHS H` is `walMustSync` off the shortcut); (5) the entries loop
  (invariant: the handle at `rest = |opDs| - i`, `enti` the last saved entry's index; `saveEntry`'s record premise
  from `tailRecs_snoc`/`chainRecs`, its `rest = 1` index premise from `walLastIdx` of the new history); (6)
  `saveState`; `w.tail().Seek(0, SeekCurrent)` (`wp_tail`, `os.File.Seek.wp_cur` on `walTailW`'s offset, as
  `cut`'s step 1) against `SegmentSizeBytes`; then `sync` if `mustSync` (`sync.spec`, blocked on writes past the
  size only through its own proof) or `cut` (premises: `walPc_bound` with a step's receipt, `hcp` for the cuts,
  `walCutPos` of `|H ++ [o]|` since the save wrote a record, `hmd` and `walAreaOk_encState` for `2^42`); (7) the
  deferred `Unlock`. `saveEntry`/`saveState` stay `sorry` (the tail writer's guard `tailOk` still has the size
  clause: writes past the size wait for `wal-tc2`'s window continuation).
- *Not done*: `saveEntry`, `saveState`, the body of `Save`, `SaveSnapshot` (its commit is `walTail_append` on the
  unsealed handle: `w.snapi` is raised after the encode).

## W3/W5 implementation log (branch `wal-read`, 2026-11-13)

**Proved (no `sorry`, `lake build`):**
- `decoder.isTornEntry` (the decoder's last `sorry`; W3a above). Its premise is now
  `off + 8 + len(data) < 2^62` (was `len(data) < 2^62`): `fileOff = lastValidOff + 8` advances by
  each chunk as an `int64`, so the old premises allowed an overflow by up to 6. `decodeRecord` passes
  it (`hys2o`, from the frame being a prefix of the file). Proof: the chunks as bounds into `data`
  (`chunkBnds`, `chunkBnds_map`: their contents are `sectorChunks`), each chunk's points-to split out
  of `data` with `ownSlice_slice` around the inner loop (`wp_join` at the inner loop) and put back.
  Gotcha: `ys[k]'h` terms in an Iris goal gave kernel "application type mismatch" errors in
  `_proof_` auxiliaries under `lake build` too (not only `lean-check`): use `ys[k]? = some b`.
- `parseWALName` (over `strings.HasSuffix.spec` and `fmt.SscanfWalName.spec`, hypotheses),
  `searchIndex` (`walSearch`: the last position whose index is at most `index`), `isValidSeq`
  (`walSeqOk 0`, Go's `lastSeq != 0` quirk kept): both over names that are segments'
  (`fmt.walNameStr`), so their `lg.Panic`s are unreachable (`walNameStr_suffix`,
  `fmt.scanWalName_walNameStr`).

**Specs (statements; proofs `sorry`):** `LinuxFs/Spec/.../wal/{Open,WAL__ReadAll}.lean`.
- Both as the main tree's with §3's binders: `walAreaOk walCodec Mr R jr r`, the update at
  `walAuMask`, `InArea r dir nm`/`cleanAbsPath r`, the area's spine `osPathS R r (own qp) jr` framed.
  `Open` takes `walAreaRes jr` (framed) and `osCallPerm 1`, returns `walOpeningF w dir s` and
  `osCallPerm ½` (the pipeline's half, as `Create`), or the token and the permission back.
  `ReadAll` takes a call permission fraction (framed: `syncDir` of the area) and `walOpeningF`;
  success: `walReadAllOk` (the ledger's restated post), `P.hsIn hp σ.hs`, `walEntsIn P esL σ.ents`
  (the main tree's `walSaveEnts false`, and I9, do not arise: `entIn` has no size flag),
  `mdp ↦*□ d.metadata`, **`walOpenWF P Mr w dir`** (W6's write-mode handle), `walNamed`,
  `walSyncedLb dir |H|`, `walLenLb`, `walPurgeW`; error: `walReadFailedF w dir`. Both arms `Q d`
  (the history does not change; the update commits wherever the proof reads it).
- New vocabulary `ReadDefs.lean`: `walOpeningF`/`walReadFailedF`, sealed, program-level
  counterparts of the ghost `walOpening`/`walReadFailed`. **Draft bodies**: the ghost handle and
  the fields `lg`/`dir`/`start`; the decoder (`ownDecoder` over `DecFile`s tied to the segments'
  program halves), the locks, the pipeline, `dirFile` are for `Open`'s and `ReadAll`'s proofs to add
  (no client statement changes). Note `WAL.decoder` is the `Decoder` *interface*.
- Not specified: `OpenForRead` (read mode: no locks, no pipeline, `ReadAll` tolerating
  `ErrUnexpectedEOF`; VSE/`Verify` use it, W8), `openAtIndex`/`selectWALFiles`/`openWALFiles`/
  `readWALNames` (internal; their shapes follow from the design point below).

**Open design points (for `Open`'s and `ReadAll`'s proofs):**
1. *Reading the WAL directory*: `readWALNames` → `fileutil.ReadDir` takes an `osNames` fraction of
   the directory's claim non-atomically, but the WAL directory's claim is the invariant's
   (`WalDirClaim`). Needed: an atomic (`osAUnc`) readdir spec, or a read-only fraction of the claim
   held by the open handle (then `cut`'s rename must reassemble it).
2. *The decoder's files*: `DecFile.bs` is fixed; the segments' bytes are split between the
   invariant and the program (halves). The read handle must own the program halves of the files
   from the opened one on (the last one's is the tail's: `walTailsRes`), so that the bytes cannot
   change during the read; the non-tail files' halves come from the invariant (W1 `laysRes`).
3. *ReadAll's establishment of `walTailsRes`* (W6, merged in `f5de562941`): after `ZeroToEnd`
   + `Fdatasync`, the tail's record with `TailZeros` past `z0` = the decoder's `LastOffset`; the
   commit is a ghost update inside the fdatasync's step (`wp_atomic_nc`).
4. *F-N4*: `Fsync(w.dirFile)` and `syncDir(filepath.Dir(dir))` give `osCommitLb`; `walNamed` by
   `walInvBody_named` (W4) needs the last writer of `nm` below the commit bound.

**Second session (branch `wal-read2`, 2026-11-13).**
- *Proved* (no `sorry`, `lake build`): `checkWALNames` (`WalNamesSel`: an order-preserving selection
  holding every name that parses, only names that may: `fmt.Sscanf`'s model leaves `.unknown`),
  `readWALNames` (`WalNamesOut N h`: non-empty, sorted, exact on the claim's names that parse; error
  `errOk`), `selectWALFiles` (`WalSelected`: `walSearch` position, `walSeqOk` from it; premise
  `WalDirNamesOk N h`: every `.wal` name in `N`, and the directory's are `fmt.walNameStr`s), walpb
  `Snapshot.GetIndex` (over `walSnapIdTerm`). Hypotheses: the callees' specs, `fmt.ErrorfErrs.spec`,
  `zap.String`/`Logger.Warn`, `strings.HasSuffix`.
- *Statement change*: `fileutil.ReadDir`'s error arm gives `fmtErrorOkOrNil err` (`readWALNames` wraps
  it with `%w`, which `ErrorfErrs` accepts only of an `errOk` error). Its proof (`sorry`) then needs the
  same of `os.Open.wp_dirS`'s and `Readdirnames.wp_dirS`'s error posts (`os.wp_pathError_ok`).
- *Specs, proofs `sorry`*: `openWALFiles` (file-system level: the names from `nameIndex` files of the
  claim, each `walOpenedFile`: fd whole, offset 0, `*fileReader{f}`, lock or nil), `openAtIndex`
  (`write`; `Open`'s update, raising `unl` only in write mode; success: `walOpening ∗ walReadH true`
  and half the permission, or the token, `walReadH false` and the whole permission; `dirFile` nil),
  `OpenForRead` (the token and an identity update, as the main tree's `ValidSnapshotEntries`; success
  `walReadOnlyF`, the whole permission).
- *The handles' bodies* (`ReadDefs.lean`): `walReadH write` (the fields `openAtIndex` leaves: decoder
  live at 0 with CRC 0 over `fs`, `decEnv`, locks, `readClose` nil and `walPipeH fp dir 0` in write mode,
  the zero fields, the mutex), `walReadTie` (the program's half of the WAL directory's claim `.except X`;
  each decoder file `F` the segment `g` from the opened one on: `F.bs` the page cache's values of
  `g.bs`, `hj.cur !! g.name = file g.ino`, `F.S = walFileS f fd … g`, the stream state holding the file,
  its offset and the program's halves of `g`), `walOpeningF = walOpening ∗ walReadH true ∗ dirFile`
  (a shared directory fd), `walReadOnlyF`. The `Open`/`ReadAll` statements did not change.
- **Decision 1 not needed** (deviation, for the coordinator): the read handle holds the program's half
  of the WAL directory's claim (parked in `walInv` with the segments' halves, decision 2's pattern), so
  the plain `Readdirnames.wp_dirS` with that fraction reads it exactly. An atomic readdir "at the read
  step" would not do anyway: `Readdirnames` is a loop of `DirReadNext` steps whose exactness needs the
  claim's history fixed across them (`wp_osDirReadNextS`'s `h.next ≤ r0`).
- **Gaps found:**
  1. *`WalAbsD` does not tie a segment's `name` to its directory entry* (`names`: only `walInos ents =
     segs.map ino` and the names sorted), so `nameBound` (about `g.name`) says nothing of the names
     `Open` reads; `selectWALFiles`' premise (every `.wal` entry a file named `walNameStr`) and which
     file `searchIndex` picks need `ents !! g.name = some (.file g.ino)` and "every `.wal` entry is a
     file". Proposed: a `WalAbsD` field (cut, create and the crash establish it; W1's owner).
  2. *The parked halves are not yet a `walInvBody` conjunct.* Design: `∃ O, [∗list] g ∈ segsAll Ls, if
     g.ino ∈ O then True else segRes g` plus, per WAL without a handle, the program's half of its
     directory's claim; returning needs no token (a third half contradicts). `walInv_alloc` deposits
     what it now returns (`laysRes Ls`, the claims' halves); a cut deposits the old tail's halves.
  3. *`walTailW`'s fd `⟨i, false, true⟩`* excludes `ReadAll`'s tail, opened `O_RDWR` by `openWALFiles`
     (`openFd i (2 ||| O_CLOEXEC)` reads too): generalize the read flag (W6).
  4. *`ZeroToEnd` on the crash-tracked tail*: its spec takes the whole `OsMeta` and bytes `[o, size)`,
     the handle has the program's halves. The truncate and the fallocate on a segment of `walInv` need
     an in-flight token as `pwTok` for writes (crash images mixing the old junk past `z0` and zeros,
     under W1) — an I3-level unit; decision 3's commit at the fdatasync comes after it.
  5. *Callees with no spec* (for `Open`'s proof): `fileutil.TryLockFile`, `NewFileReader`, `OpenDir`,
     `closeAll`, the `os.File` reader bridge (`decFile` of a `walFileS` stream: `Read` over the
     program's half of the bytes, `Stat`), `walpb.Snapshot.Clone`; `newFilePipeline` is `sorry`.
- *Not done*: the proofs of `openWALFiles`, `openAtIndex`, `OpenForRead`, `Open`, `ReadAll`.

## I3b: resizes in flight on a crash-tracked file (branch `wal-i3b`, 2026-11-13)

The W3/W5 log's gap 4 (`ZeroToEnd` on the tail; `cut`'s truncate of the old tail): `ftruncate` and
`fallocate`'s growth on a file whose `OsMeta`/bytes are split between the program and `walInv`.

- *The extension level needed nothing new*: `Truncate.lean`/`Falloc.lean`'s two-step specs already
  have an in-flight token (`rsTok`, as `pwTok` for writes: the `OsMeta` whole, the bytes cut off,
  `rsAnn`'s zero candidates). The split forms are **atomic-update specs** (`LinuxFs/Proof/os/
  ResizeAu.lean`, proved, over `osAUnc`/`wp_aunc_step`, so the update's owner can open `walInv` with
  `notCrashed`): `wp_osFtruncateStart_au`/`wp_osFallocStart_au` (caller: half the `OsMeta`, and of the
  bytes cut off; the update lends the other halves and commits with `rsTok`, outcome `(t, n)`),
  `wp_osFtruncateFinish_au`/`wp_osFallocFinish_au` (the update lends the token, commits with the
  whole outcome `rsOutT`/`rsOutF`; its `Q e` gives the caller its share). Files unmapped
  (`m.maps = ∅`). Derived from the whole-resource specs, which stay (the case of updates owning nothing).
  `GooseLang/Ext/Fs` unchanged (no rebuild).
- *Go wrappers*: `syscall.Fallocate.wp_growAu` (`Proof/syscall/FallocateAu.lean`, **proved**): one
  `fallocAu` = the start's update whose commit is the finish's; post `∃ n, Q n e`.
  `os.File.Truncate.specAu` (`Spec/os/File__TruncateAu.lean`; proof **`sorry`**,
  `Proof/os/File__TruncateAu.lean`, plan in its header): the `EINTR` loop needs an update pair per
  attempt, so the caller gives a **persistent supply** `□ ∀ m0 xs0, ⌜os.TruncFrom m xs tg m0 xs0⌝ -∗
  os.truncAu p tg m0 xs0` (the states an attempt starts from: `m` or as announced, or landed); each
  finish's commit hands the caller its halves (`os.truncOutH`); post `File__Truncate.lean`'s at half
  (`os.ftDoneH`, `os.ftUndoneH`). The WAL can supply it from `walInv` (persistent) and agreement
  with the halves it holds.
- *`walInv`* (`Inv.lean`, additive): **`SegFl.rz : Option Nat := none`** (a resize to `tg` in flight;
  `off`/`data` unused). `segResF`'s in-flight case splits on it: a write as before; a resize holds
  `rsTok fl.t g.ino tg fl.m (fl.bs.drop lo) fl.n` and the half of `fl.bs.take lo` (`lo = min size
  tg`), the layout holding the segment as announced (`SegFl.OkR`: `g.om = m.announce lo (max size tg)
  tg`, `g.bs = bs.take lo ++ rsAnn n (bs.drop lo)`, `0 < lo` so the invariant keeps half of byte 0).
  `walTailsRes`'s record carries `F !! ino`, so a resize in flight is in the tail record with no
  change. Repaired: `segResF_timeless`; `InvInos.segResF_ino_ne` (`segFlR_take_cons`);
  `CrashTakeSeg.crashRestAt_take_seg` takes a resize's token (`runsCover_rz`) — so `walInv_crash`'s
  segment take accepts it, `SegCrashAt` unchanged. **For W6**: `SegFl` anonymous constructors need
  the 7th field (`TailWriter.lean`'s two `⟨t, wr, data, n, m, bs, none⟩`).
- **Open (not done)**:
  1. *`WalAbsD.metas`* (`lo = hi = |bs|`) fails for a segment as a resize announced it (`lo = min`,
     `hi = max` of the sizes): as for W6's writes past the size, the last segment needs
     `lo ≤ |bs| ≤ hi` with candidates past `|bs|`; the static relation and `CrashOk` across a resize's
     two steps (`walsOk_resizeStart`/`Finish`, pure) are the next unit, and with them the WAL-level
     `os.truncAu`/`fallocAu` instances.
  2. *A growth's crash bytes past the old size* (`fallocate` in flight): `FileCrashedR` bounds them only
     by `zf`, and the truncate before it raised `zf` past them (`OsMeta.announce`); the wal-eof
     proposals (`notes/axiom-review/eof-page/`, P1/P2: writeback and `ftruncate` zero the page past
     the size) decide whether they are zeros. Until then `ZeroToEnd`'s crash images past `o` are
     unconstrained, against W1.
  3. *`fileutil.ZeroToEnd`/`Preallocate` split variants*: not written. Shape: `ZeroToEnd`'s
     `Seek`s take the halves' fraction; its `Truncate(o)` is `specAu`; `Preallocate(f, S, true)` →
     `preallocExtend` → `Fallocate.wp_growAu` (the `ENOTSUP` fallback `preallocExtendTrunc` →
     `specAu` again); post: halves of the `osZerosA` run.

**The known-zero tail (branch `wal-kz`, 2026-11-13)**: the fact `eof-page.md`'s P2 left to the ghost
state (a sync after `ZeroToEnd` gives zeros known from the size, `zf := some size`, not from the end of
its last page).
- *Design* (decided; untrusted): an `OsMeta` field **`cz : Nat := 0`**, "the page cache is zero on
  `[size, cz)`" (`MetaOk.cz`), not a separate ghost resource: the page cache past the size is the
  state's, which only `osInv`'s coherence sees, and a resource tied to it would have needed the same
  upkeep in every step lemma plus a new piece in the resize and sync specs. Every step keeps the clause
  with `cz` unchanged (a write lands only below its new size, a growth's new size is at least the old,
  a sync keeps the page cache in the size's last page and zeroes past it, a crash or creation starts at
  0), so the default is right everywhere `{ m with ... }` is built. `rsPost` raises it for an
  `ftruncate`: `cz := rsCz tr m.size tg m.cz` (`max m.cz (rsHi true s tg)`, the end of what it
  announced; `fallocate` keeps it); `resize_done_world` takes `htr : tr = true → rsHi tr s tg ≤ e` (a
  truncate lands all it announced: its three callers pass it). `OsMeta.synced`'s `zf` is `some m.syncZ`
  (`syncZ` = the size if `pageEnd size ≤ cz`, else `pageEnd size`; `size_le_syncZ`, `syncZ_le`):
  **`OsMeta.synced_zf_size : pageEnd m.size ≤ m.cz → m.synced.zf = some m.size`**. `bsynced` unchanged.
- *The lemma for `ZeroToEnd`* (`LinuxFs/Proof/os/Base.lean`): `os.rsPost_cz_true` (`pageEnd (max s tg) ≤
  (rsPost true m tg sz').cz`), `os.le_rsPost_cz` (a resize never lowers it), **`os.zeroToEnd_cz`**
  (`o ≤ m.size → pageEnd m.size ≤ (rsPost tr (rsPost true m o o) m.size sz').cz`, either growth: the
  `fallocate`, or `preallocExtendTrunc`'s `ftruncate` fallback) and **`os.zeroToEnd_synced_zf`** (with
  the sync: `zf = some m.size`). The split specs' posts name these metas exactly (`os.ftDoneH`'s
  `rsPost true m tg tg`, `rsOutF`'s `rsPost false …`), so the split `ZeroToEnd`'s post gets them for
  free; `ReadAll`'s `TailZeros` then holds from `o` on: `[o, size)` the bytes made `durB 0` by the
  sync, past the size `zf = some size`.
- *Whole-resource specs*: `fileutil.ZeroToEnd.spec`'s success post gains `pageEnd m.size ≤ m'.cz`
  (proved; `ftDone_shrunk` gives it); `preGrown` gains `m.cz ≤ m'.cz` (`Defs.lean`'s lemmas,
  `preGrown_trans` takes `hcz`). bboltfs: `synced_eq` takes `m1.cz = m2.cz`, `WReach.cz` (a write loop
  keeps it). `wp_osPWriteFinishK` needed `maxHeartbeats 400000` (one more `OsMeta` field).
- *`os.File.Truncate.specAu` proved* (`Proof/os/File__TruncateAu.lean`, no `sorry`): the loop at half
  (`ftStateH`), the supply instantiated per attempt (`os.TruncFrom`'s left case, or `rsPost true m tg tg`
  with no bytes after a landing), `os.ftDoneH_of`, `os.truncOutH_again`.
- *Not done*: the split `fileutil.ZeroToEnd`/`Preallocate`/`preallocExtend`/`preallocExtendTrunc` (item 3
  above; its post can state `pageEnd S ≤ m'.cz` by `zeroToEnd_cz`); the WAL-level supplies
  (`os.truncAu`/`fallocAu` from `walInv`, item 1). (The split fileutil specs: done in the next entry,
  over a reshaped `specAu`.)
- *Integration*: `wal/checkWALNames` built again at `wal-int` (`zap.Logger.Warn` now takes `zapLoggerOk l`
  itself: `iexact Hlg`).

**The updates' shape; the split `ZeroToEnd` (branch `wal-zte`, 2026-11-13)**.
- **Finding: the first split form could not be supplied by `walInv`.** `os.truncAu p tg m0 xs0` had the
  update lend the *other halves* of a state `m0` the caller names (`os.TruncFrom`: `m`, as announced, or
  landed), from a persistent supply. An invariant's update does not see the caller's halves, so it cannot
  know the state it holds is `m0` (the three are different `OsMeta`s); and the second update (lending the
  token at the finish) has no resource tying it to the invariant's record of the change, so it cannot find
  *its* token (`segResF`'s `fl.t`) either (`osTok` is `own 1`, no witness). Both need agreement with
  something the program holds.
- **Decision (the `os`-level shape, untrusted):** the caller **hands its halves and a tie `K` to the supply**;
  the update lends the *whole* (`LinuxFs/Proof/os/ResizeAuW.lean`: `wp_osFtruncateStart_auW`,
  `wp_osFallocStart_auW`; the finish lemmas of `ResizeAu.lean` already lend the whole token) and gives back
  the caller's halves of the outcome with `K`. `K` is the program's tie with the owner's record (the WAL: its
  `walTailKey dir γ ∗ tailVar γ (H, md, cuts, wr, i, none)`): the start's commit updates the record to the
  change in flight with both halves of `tailVar` and keeps the program's in the finish's update, which finds
  `fl` by agreement and returns it as `none` again. Definitions: `os.truncAuW K p tg m0 xs0`,
  `os.truncSup K p tg` (`□ ∀ m0 xs0, ⌜|xs0| = m0.size - tg⌝ -∗ K -∗ ½ m0 -∗ ½ xs0 -∗ truncAuW …`;
  `Spec/os/File__TruncateAu.lean`), `fallocAuW i tg m Q`, `fallocSup K i tg` (from any `m0.size ≤ tg`),
  `fallocOutH`/`fallocDoneH` (the caller's halves of `rsOutF`; `Proof/syscall/FallocateAu.lean`).
  `os.truncAu`/`os.TruncFrom` are gone (no user).
- *Proved* (no `sorry`, `lake build`): `os.File.Truncate.specAu` restated over `K`/`os.truncSup` (pre: `½ m`,
  `½ xs`, `K`, the supply; post `File__Truncate.lean`'s at half and `K`; the loop carries `K`);
  `syscall.Fallocate.wp_growAuW` (`fallocAuW`, post `∃ n, Q n e`); the split fileutil specs
  (`LinuxFs/{Spec,Proof}/.../fileutil/*Au.lean`, `.specAu`/`.wp_proofAu`; shared `DefsAu.lean`:
  `preGrownH` = `preGrown` at half, `_same`, `_trans`, `fallocOutH_preGrownH`, `ftDoneH_preGrownH`):
  - `preallocExtendTrunc.specAu`: `½ m`, `K`, `truncSup K i sz`; post `preGrownH i m w` (`w` as the whole spec's) and `K`;
  - `preallocExtend.specAu`: adds `fallocSup K i sz`;
  - `Preallocate.specAu`: both supplies; post `preallocPostH` (`preGrownH`, or `½ m` unchanged) and `K`;
  - **`ZeroToEnd.specAu`**: `½ m`, `½` of the bytes `[o, size)`, `K`, `truncSup K i o`, `truncSup K i size`,
    `fallocSup K i size`; success: offset `o`, `∃ m'`, `m'.size = m.size ∧ m'.maps = m.maps ∧ pageEnd m.size ≤
    m'.cz`, `½ m'`, `osZerosA i o (size - o) ½`, `K` (so `OsMeta.synced_zf_size` applies to the fdatasync after:
    `os.zeroToEnd_synced_zf` is the special case of the direct growth; the post states the `cz` bound, which
    every path gives — the fallback's `ftruncate` from a failed growth's state too); error: as the whole spec's,
    at half, with `K`. The update's owner holds the other halves (it committed each step's outcome).
- **Not done: the WAL-level supplies** (`truncSup`/`fallocSup` from `walInv`), blocked on two decisions for
  the invariant's owner:
  1. *The static relation does not admit a resize's states* (pure, checked against the definitions):
     during `cut`'s truncate of the old tail at `wr` (bytes `[wr, size)` zeros past the stream), the
     announced segment (`SegFl.OkR`) has `om.lo = min m.lo wr = wr ≠ |bs|` (`WalAbsD.metas`) and its bytes past
     `wr` carry `(y, 0) :: [(0, n)]` (`rsAnn`), which `ByteOk` refuses past the stream (`a = false → ex = []`);
     once landed, `om.hi` stays the old size (`≠ |bs|`) and `|bs| = wr ≠ |old|` (`WalAbsD.last`) until the
     fdatasync. `ZeroToEnd`'s growth adds the same (`hi` past `|bs|`, then zeros with fresh candidates).
     Proposed: `metas` as `om.lo ≤ |bs| ≤ om.hi` for the last segment (W6's writes past the size need the
     same), `last`'s `ByteOk` with zero candidates allowed past the stream (`∀ q ∈ ex, q.1 = x ∨ (a = false ∧
     q.1 = 0)`) and `|bs| ≤ |old|`; then `CrashTo` holds (the reader stops at the zeros or at the end of the
     file). A change to `WalAbsD` (the invariant's content, 20 uses of `.metas` in 12 files): not made here.
  2. *`ReadAll`'s `ZeroToEnd` has no tie*: its tail is not yet in `walTailsRes` (the record is made after the
     fdatasync, needing `TailZeros`), so no program resource agrees with `F !! ino`. Either `ReadAll` registers
     the tail before `ZeroToEnd` (then `TailZeros` must admit the junk past `z0` until the sync, e.g. a
     registered `z0 = |old|` lowered at the sync's commit), or the invariant gets a tie for an unregistered
     tail. `cut`'s truncate has the tie (`tailVar`).
  `cut`'s hypothesis `os.File.Truncate.specWalTail` (`wal-cut7`, `WAL__cutTail.lean`) is `specAu` at
  `K := walTailKey dir γ ∗ ghostVar γ ½ (H, md, cuts, o0 + |out|, i, none)` (exactly `walTailW`'s tie) with
  the supply below, the post's halves rebuilding `walTailW … (o0 + |out|)`.
  With 1 decided, the supplies are: open `walInv` in the update (`walInv_open` at `osAuMask`), take the
  tail by `walInvBody_tail` (`TailAcc.lean`), agree the caller's halves with `segResF`'s
  (`osMeta_agree'`, `osBytes_agree`), lend the whole; at the commit put `rsTok` in `F` (`segResF`'s `rz` case,
  `OkR` from `rsKind_meta`), update `tailVar` with `K`'s half, close with the new layout (the pure
  `walsOk_resizeStart`); the finish's update, owning `K`'s half, finds `fl`, lends the token, splits
  `rsOutT`/`rsOutF` into `segRes` and the caller's halves (`walsOk_resizeFinish`).

**The relaxation and `ReadAll`'s tie (branch `wal-zte2`, 2026-11-13).**
- *Open item 1 done*: `WalAbsD` admits the tail's resize window (`SegExact`/`TailLast`/`TailWin`; the W1 log's
  ninth session). Item 2 stands and now shows in the statements: in the window `TailWin` constrains no byte
  from `wr` on, and `W1G` says nothing of an image longer than the bytes the ghost knows, so `CrashOk` across a
  resize (`walsOk_resizeStart`/`Finish`) still needs a fact the extension does not give: after a truncate lands,
  `FileCrashedR` bounds the bytes `[size, hi)` only by `zf` (the cut-off bytes' candidates, old value or the
  zero stamped `n`, are the state's, held by no resource after `rsDone`). Proposal (untrusted, `GooseLang/Ext/Fs`):
  `rsDone`/`rsPost` of a truncate keep the cut-off bytes' candidates in `OsMeta.tc`, and `FileCrashedR`
  constrains a byte past the runs by `tc` (the clause it lacks today). `SegFl.OkR`/`segResF`'s resize case are
  `ftruncate`-only (`rsTok true`, `rsHi true`): `ZeroToEnd`'s growth (`fallocate`) needs `rz : Option (Bool × Nat)`.
- **`ReadAll`'s tie (option a), designed, not implemented** (no flag in `TailG`):
  - `walTailsRes`' per-tail `TailZeros lay` becomes `TailZeros lay ∨ lay.wr = lay.z0` (nothing appended past the
    start's frames). `ReadAll` registers its tail (key, `tailVar` at `wr = so = z0`, `TailBound` at `z0`) at an
    invariant step before `ZeroToEnd`, so `ZeroToEnd`'s supplies have `K = walTailKey dir γ ∗ ghostVar γ ½ (…, none)`.
  - `ReadAll`'s fdatasync commit (the window closes) sets the invariant's `om` to `OsMeta.synced` (exact; `zf = some
    size` by `OsMeta.synced_zf_size`), every byte `durB`, and `old := old.take z0 ++ replicate (|old| - z0) 0`
    (`TailLast`'s `ByteOk` forces it: a synced zero past `wr` has `y = old b = 0`); `TailZeros` then holds.
  - The appends get `TailZeros` from the disjunction by a pure lemma (to write): `WalAbsD` + `SegExact g` + the
    program's bytes from `wr` on of value 0 → `old b = 0` there (`TailLast`'s unwritten, unsynced `ByteOk`: `g.1 =
    y`), so `wr = z0` gives `TailZeros`. `walTailW` gains `∀ b, o0 + |out| ≤ b → b < |bs| → bs[b].1 = 0` (from
    `ZeroToEnd.specAu`'s `osZerosA` after the sync; writes keep it: they write below the new `wr`).
  - **Obligation for `wal-read7`**: the registration step, the sync commit above, `walTailW`'s new conjunct, and
    `TailMeta`'s exactness (W1 log, ninth session) when building `walTailW`.

**The cut-off bytes' candidates in `tc`; `rz` with the kind (branch `wal-tc`, 2026-11-14).** Tasks 1-2 of the
coordinator's decision (the item-2 proposal above); task 3 (the supplies) not done.
- *Extension (`GooseLang/Ext/Fs`, untrusted; `Impl.lean` unchanged).* Sound against the crash rule: a landing
  (`OsFile.land`) leaves every byte's candidates as they were, so a byte cut off keeps `c0 ++ [(0, n)]`, which a
  crash may pick from, or zero past `sizeLo` (P1's clause, `FileCrashedR`'s `m.lo` disjunct).
  - `Truncate.lean`: **`rsTail tr m tg sz' n xs`** (the `tc` a landing to `sz'` leaves: each announced byte at or
    past `sz'` with its candidates, below the old size `xs`'s, past it `(m.pc b).map (· ++ [(0, n)])`, the rest as
    the announcement left them); **`rsPostK keep tr m tg sz' n xs`** = `rsPost` with `tc := cond keep (rsTail …) _`
    (`rsPostK_false` is `rsPost`, by `rfl`; projections `rsPostK_size`, …; `rsPostK_true_tc`, `_tc_past`);
    `rsDoneK keep …` (`rsDoneK_false` = `rsDone`); `resize_done_worldK keep … (hkeep : keep = true → m.cut = none)`
    (the byte resources' candidates are the state's only without a sync cut), `wp_osFtruncateFinishK`; `RsFacts`
    gains `hcandP` (an announced byte past the size has `m.pc`'s candidates then `(0, n)`, from `tok_cand`).
    `Falloc.lean`: `wp_osFallocFinishK` (a partial growth keeps `[w, tg)`'s). `Zeros.lean`: `rsDoneK_zeros`,
    `rsDoneK_zerosA`. The old statements stay (wrappers at `keep := false`): no user outside changed.
  - `CrashFiles.lean`: **`FileCrashedR` gains a sixth clause**: `∀ b c, m.size ≤ b → m.tc !! b = some c → b <
    f'.size → (∃ s, (f'.cache b, s) ∈ c) ∨ (m.lo ≤ b ∧ f'.cache b = 0)` (from `MetaOk.tail`). Users that build a
    `FileCrashedR` add it (`TailCrash`/`TailSyncPure`'s synced images: vacuous, `size = |bs|`); `CrashWrite`'s
    patterns take the extra component.
- *The split outcomes* (`LinuxFs/Proof/os/ResizeAu.lean`): `rsOutT`/`rsOutF` are over **`rsDoneK m.cut.isNone`**
  (the whole outcome the update's owner gets knows the cut-off bytes for a file with no sync cut: every WAL
  segment). The caller's halves hold the `OsMeta` **up to `tc`**: `OsMeta.withTc m tc` (`{ m with tc }`, simp
  projections, `withTc_self`, `touch_withTc`, `announce_withTc`, `rsPost_withTc`, `synced_withTc`); `os.ftDoneH`
  and `fallocDoneH` are `∃ tc, osMeta ½ ((rsPost … ).withTc tc)`. Repaired: `File__TruncateAu` (`truncOutH_again`
  takes the landed state's `tc0`), `DefsAu`, `ZeroToEndAu`. **For the supplies**: the invariant splits
  `osMeta 1 (rsPostK …)` and hands the program `½ (rsPost …).withTc (rsPostK …).tc` (`rsPostK_withTc`, `rfl`).
- *Pure* (`LinuxFs/Proof/os/CrashResize.lean`): **`fileCrashedR_rsPostK`** — a crash after a truncate landed
  (`rsPostK true`, bytes `ys` below `tg`) is a crash of the file as announced (`m.announce …`, `ys ++ rsAnn n
  xs`): `CrashOk` across a truncate need only hold of the in-flight state (`SegFl.OkR`'s), which the layout
  already describes. Suggested use: the landed tail's crash take converts with it, so `walsOk_resizeFinish`
  reduces to `walsOk_resizeStart`'s state.
- *Task 2* (`Inv.lean`): **`SegFl.rz : Option (Bool × Nat)`** (`some (tr, tg)`: `ftruncate` if `tr`, else
  `fallocate`'s growth); `SegFl.OkR fl tr tg g` (`rsHi tr`); `segResF`'s case `rsTok tr`. Repaired:
  `InvInos.segFlR_take_cons`, `CrashTakeSeg` (`runsCover_rz`, the take: `rsKind_meta`/`rsKind_lo` rewrite the token,
  `rsKind tr` no longer reduces). `lake build` of every importer of `Truncate`, `CrashFiles`, `ResizeAu`, `Inv`:
  clean (a seeded `.lake` needs its stale `Proof/io/ReaderStream` `.olean` removed).
- **Open for task 3** (the supplies, `os.File.Truncate.specWalTail`, `ZeroToEnd`'s instance):
  1. *A crash while `fallocate` is in flight* (`ZeroToEnd`'s regrowth over `[o, size)`): the token's `OsMeta`
     (`TokInfo.meta` = `announce`) drops `tc` over the announced range, so `FileCrashedR` of it does not bound the
     regrown bytes (the state's are `tc ++ [(0, n)]`, `tok_cand`'s third clause). Either a token-aware take
     (`crashRestAt_take_tok` also giving `∀ b ≥ m0.size` in range, `m0.pc b = some c` → the byte is in `c ++
     [(0, n)]` or zero past `lo`; from `CrashSeenR`'s `OsCoh`), or `TokInfo.meta` keeping them (an `Ext/Fs`
     change: `osCoh_start`, `Write.lean`'s `htm`, `rsKind_meta`'s users).
  2. The supplies themselves (`walInvBody_tail`'s continuation requires `SegExact g`; a resize needs a
     continuation closing with `TailWin` and `CrashOk` in the window, by `fileCrashedR_rsPostK` and item 1).

**The token-aware take; the window's access; `CrashOk` across `cut`'s truncate is not provable (branch
`wal-tc2`, 2026-11-14).** Task 1 of the coordinator's decision done; tasks 2-3 stopped at a finding.
- *Task 1, option (a)* (`CrashTakeSeg.lean`, proved, no `Ext/Fs` change): **`TokPast ti fo`** (a byte the
  change announced at or past `ti.m0.size` with `ti.m0.pc b = some c` came back as one of `c ++ [(val, n)]`,
  or zero at or past `ti.meta.lo`), **`tok_crash_past`** (from `OsCoh.tok_cand`, `OsCrash`); `crashRestAt_take_tok`
  now also returns `TokPast` (its only users are in the file).
- *The layout's `OsMeta` of a resize in flight* (`Inv.lean`): **`rzMeta tr m tg n`** = the token's `TokInfo.meta`
  with `tc := rsTail tr m tg m.size n []` (the announced bytes past the size, `m.pc b` then `(0, n)`); `SegFl.OkR`'s
  third clause is now `g.om = rzMeta tr fl.m tg fl.n` (was the bare announcement; same `size`/`lo`/`hi`/`cut`, so
  `WalAbsD.metas` is unchanged; no constructor of `OkR` existed). `crashRestAt_take_seg`'s resize case gives
  `SegCrashAt` of it (**`fileCrashedR_rzMeta`**), so `CrashOk`'s `FileCrashedR` premise now carries the regrown bytes'
  candidates (the I3b open item 1 of `wal-tc`). **`fileCrashedR_rsPostK_rz`**: a crash after a truncate landed
  (`rsPostK true`) is one `rzMeta true` allows (`fileCrashedR_rsPostK` plus the bytes past the old size).
- *Pure, the window's static relation* (`RzStepPure.lean`, proved): `rzSeg g0 tr tg n` (the tail as a resize's first
  step announces it; `rzSeg_ok : SegFl.OkR …`), **`walAbsD_win`** (`WalAbsD` of a layout whose tail is in a window, from
  `TailLast`/`TailWin` of it), **`walAbsD_rzStart`** (from an exact tail, `lay.wr ≤ tg`).
- *The window's access* (`TailAccW.lean`, proved): **`walInvBody_tailW`**, `walInvBody_tail` whose continuation takes
  the new layout's `WalsOk` and `DirKeysOk` from the caller (no `SegExact`, no equal length: a landing shortens the
  tail), and returns `Ls`, `cl`, `n`, `WalsOk`, `TailZeros`, `TailBound` at the opening; `walParked_tailW` (no length
  premise: the tail is out). The supplies (`truncSup`/`fallocSup`) are this plus a pure `CrashOk` of each window layout.
- **Finding (blocks `cut`'s supply and `os.File.Truncate.specWalTail`; for the coordinator, W1 is pending the user's
  review [user])**: `CrashOk` of the layout in `cut`'s truncate window is **not provable from W1 as stated**. `cut`
  truncates at the file offset (`Seek(0, SeekCurrent)`), which the `PageWriter` leaves at a page boundary, in general inside a frame: the
  encoder still buffers the rest of the frame straddling `wr` (`sync()` flushes it after the truncate;
  `wal.go:882-895`, `pagewriter.go` `Write`). The truncate announces `[wr, pageEnd old)` with the zero stamped `n`
  (`tok_cand`). A crash may then keep the file as of `n`: the straddling frame's bytes below `wr` are the intended
  ones (written by changes before `n`), those from `wr` on are the truncate's zeros, and every core byte has a
  candidate stamped in `(0, n]`, so the frame **is `AsOfOne` at `n`** and W1 does not stop the reader from accepting
  it (a CRC32-C collision on a torn frame, which W1's evidence, "no collision on torn data", excludes, but its
  formal statement does not: a resize's zeros count as a change that wrote the frame's tail). The same crash with no
  truncate (the tail unwritten past `wr`) is excluded by W1, because unwritten bytes have no candidate stamped
  positive. If the reader accepts it, `CrashTo` fails (a record other than the intended one), so `CrashOk` is false of
  the window layout in the formal model, from the truncate's first step until `cut`'s fdatasync (the flush's writes
  past the size do not remove the as-of-`n` state). Options: (1) restate W1 so that a resize's zero candidates do not
  make a frame "written" (e.g. the change disjunct over write stamps; the state does not record a stamp's kind today,
  so this needs a recorded kind or a different formulation: a trust-base change, the user's); (2) a fork change to
  `cut` (flush the encoder before the `Seek`: the truncate is then at the stream's end, a record boundary, and every
  frame from `wr` on is zeros as of `n`; the code is correct as is, so this goes against "no code change if not a
  bug"); (3) a WAL-specific premise next to W1 (no accepted frame at a record boundary whose core is the intended
  bytes up to some offset then zeros). **Not decided here.** `ReadAll`'s `ZeroToEnd` truncates at `z0`, a record
  boundary, so this does not arise there (as of the truncate every frame from `z0` on is zeros: rejected).
- **For `ZeroToEnd`'s window** (open, design-independent of the finding): after the truncate lands, and during the
  `fallocate` growth, the image may be longer than the tail's bytes (`|bs| = z0 < size`), and `W1G` says nothing of
  such an image (`(img i).length ≤ bs.length`). `rzMeta`/`rsPostK true` now know the candidates past `|bs|` (`pc`),
  so the proposal is `W1G` over the bytes and the known candidates past them (`segBytesOf` extended by
  `g.om.pc` on `[|bs|, hi)`), with `SegCrashAt` giving `f.cand b = c` for `|bs| ≤ b`, `g.om.pc b = some c`
  (`MetaOk.pc_cand` when idle, `tok_cand` in flight, as in `tok_crash_past`), and its users given the frame's fit
  instead of the image's length (`acceptsFiles_bound`). Then each `ZeroToEnd` state's frames from `z0` on are as of
  the sync (the old bytes: `tailStop`) or of a resize (zeros): rejected.
- **Obligations**: `wal-cut10`: `os.File.Truncate.specWalTail`'s success post `walTailW … (o0 + |out|) out` is
  unprovable as stated even with the finding resolved: `walTailW`'s `TailMeta` requires `m.lo = m.hi = m.size`, and
  after the truncate lands the window is open (`rsPost true`: `hi` the old size) until `cut`'s fdatasync; the post
  needs a window form of `walTailW` (the `OsMeta` half `rsPostK true …` without exactness, closed by
  `WAL.sync.specCut`'s commit). `wal-save10`: the window's closing sync (`walInvBody_tailW` with the synced layout's
  `WalsOk`, `TailLast` again).

**Writes past the preallocated size open a window too (W6, branch `wal-save10`, 2026-11-14; for `wal-tc2`,
which writes the window's continuation and closing sync: one continuation for both).** Design only, nothing
changed in the invariant or the tail steps.
- *What the extension gives a write past the size.* `pwPost m off n k` raises `hi` to `max size (off + n)`, keeps
  `lo` (`announce`'s `min m.lo tg` with `tg = max size (off + n)`: the old `lo`, the old size outside a window),
  and sets the size to `pwSize`; `announce` moves `zf` to `max z (off + n)`. The bytes the write adds
  past the old size are not in the program's byte run (`cfRange` takes only existing bytes); their candidates are
  in `tc`: `pwTail` (`wp_osPWriteFinishK true`) gives each `(m.pc b).map (· ++ [(d_b, n)])`. **When the tail's
  zeros are known from its size (`m.zf = some m.size`), `m.pc b = some [(0, 0)]` for every `b ≥ size`**, so each
  new byte's candidates are `[(0, 0), (d_b, n)]`: exactly `ByteOk`'s shape for an unsynced byte of intended
  value `d_b` over an `old` extended by zeros. A retry (`EINTR` with bytes landed, `k < n`) finds `tc`'s entry
  (`pc` reads `tc` first) and appends another stamped candidate: still `ByteOk`.
- *The fact this needs, which no statement carries yet*: `zf = some size` of the tail before its first write past
  the size. `TailMeta` has only `size ≤ z`. It holds of every tail the WAL builds: `cut`'s and `Create`'s segments
  are `fallocate`d to 64 MB (page-aligned) and synced (`OsMeta.synced`: `zf = some syncZ = size`), `ReadAll`'s
  after `ZeroToEnd` and its fdatasync (`os.zeroToEnd_synced_zf`); writes inside the size keep it (`announce`:
  `max z (off + n) = z`). Proposed: `TailMeta`'s third conjunct `m.zf = some m.size` in the exact state; in the
  window `m.zf = some m.hi` with `tc` holding `ByteOk`-shaped candidates on `[size, hi)` (a short write).
- *The window it opens* (`SegExact` fails: `lo` the old size `< |bs|`): the layout's tail as announced must have
  `g.bs` extended to the announced size (`metas`: `size = |bs|`), the new entries `(0, [(0, 0), (d_b, n)])`, and
  `lay.old` extended by zeros (`TailWin`: `|bs| ≤ |old|`); `TailWin`'s `ByteOk` below `wr` then holds by the shape
  above. `CrashOk` in the window: a crash image is at least `lo` (the old size, at or past every synced byte and
  every frame of the history before this `Save`) and its bytes past `lo` are zeros or the intended frame bytes, so
  `tail_decode`'s argument (the reader stops at zeros or at the image's end) goes through with the image's length
  free in `[lo, hi]`: this is the window-crash lemma `wal-tc2` needs for `ZeroToEnd`'s regrowth (bytes past `lo`
  zero or candidates), at a write's candidates in place of `(0, n)`. **Request to `wal-tc2`**: state the window's
  continuation of `walInvBody_tail` (and its crash lemma) over a byte-candidate predicate general enough for both
  (`∀ b ∈ [lo, hi), cands b ⊆ {0} ∪ {intended b}`), so that the tail's `PWriteStart`/`Finish` past the size use it.
- *Then on W6's side*: `SegFl.Ok`'s `off + |data| ≤ m.size` dropped (the announced tail extended as above),
  `wp_tailPWriteStart`'s `hin` dropped, `TailMeta` relaxed to the window, `tailOk`'s size clause dropped (so
  `wal.tailWriter`, `encode.specG`'s guard, `sync.wp_proof := wp_proofIn`, and `saveEntry`/`saveState` over the
  encoder need no size premise); the window's closing fdatasync is `wal-tc2`'s (`walInvBody_sync` from the window).

**Third session (branch `wal-read3`, 2026-11-13).**
- *Gaps 1 and 2 closed* as the coordinator decided: `WalsNamed` and `walParked` in `walInvBody`, the parking
  flag in the lock token (W1 log, sixth session, for the design and the other units' obligations).
  `walReadOnlyF` holds `walLockedTok`. `Open`'s proof: `walUnlockedTok_lock` at its first invariant opening,
  then take its WAL's segments into `O` and its directory claim into `D`; `selectWALFiles`' premise
  `WalDirNamesOk` from `WalsNamed`'s current clause.
- *Gap 5, partly*: `fileutil.NewFileReader` (interface `*fileReader{f}`, the cell owned) and
  `fileutil.OpenDir` (`os.Open.wp_dirS`'s triple) specified and proved (`LinuxFs/{Spec,Proof}/.../fileutil/`).
  Not done: `TryLockFile` (as `LockFile`, plus `errors.Is(err, EWOULDBLOCK)`), `closeAll`,
  `walpb.Snapshot.Clone`, the `os.File`-reader bridge to `decFile`.
- *Not done*: the proofs of `openWALFiles`, `openAtIndex`, `OpenForRead`, `Open`, `ReadAll`.
- *Pipeline obligations* (the coordinator, after `wal-cut3`): `newFilePipeline.spec` takes `dir.length <
  2^61`; `tmpClaim j b` owns what `N.tmp` holds (nothing, or a leftover file whole), so after a crash `Open`
  must hand over a leftover `N.tmp`'s resources with its claim.
- *Build note*: `filePipeline__alloc` fails at `wal-int` `6f367bb4bf` merged here (`wp_LError ... cannot frame
  zapLoggerOk lg`, line 136; not touched here, nor are its imports' statements).

**Fourth session (branch `wal-read4`, 2026-11-13).**
- *Proved* (no `sorry`, `lake build`): `fileutil.TryLockFile` (as `LockFile`, post `lockPost` plus an
  `errOk` error, which `openWALFiles` wraps with `%w`); `wal.closeAll` (over `wal.rcFile`, `CloseDefs.lean`:
  an `*os.File` or a `*LockedFile` with the file and fd whole, consumed; error `nil` or `errOk`);
  `walpb.Snapshot.Clone` (over `walSnapIdTerm`).
- *New hypotheses* (spec files, not axioms; to discharge when linking):
  - `errors.IsErrno.spec` (`LinuxFs/Spec/errors/IsErrno.lean`): `errors.Is(errno, errno)` returns. Perennial's
    `errors.Is` admits only pointer targets (`notes/perennial-changes.md`, 2026-11-13).
  - `proto.CloneWalSnap.spec` (`LinuxFs/Spec/google_golang_org/protobuf/proto/CloneWalSnap.lean`): `proto.Clone`
    of a `*walpb.Snapshot` keeps `walSnapIdTerm`. It is `proto.ClonePb.spec` at `walpb.Snapshot` once that type
    is registered in the part with `walSnapAt` over its content model (W6's `SaveSnapshot` fix); not done here
    to avoid a second registration (and its two trusted axioms) racing W6's.
- **Finding, blocks the `os.File`-reader bridge** (for the coordinator): `decFile`'s `io.readerStream`
  quantifies over every buffer `p`, and the trusted `os.File.Read` model panics when `off + len(p) ≥ 2^62`
  (`model.offMax`, "not modelled"), so `decFile` of an `*os.File` reader is unprovable as stated (a GooseLang
  slice may be that long). The decoder never reads past the file (frame checks; `bufio`'s 4 KiB buffer), so
  either (a) `io.readerStream` takes `r.length + xs.length < 2^62` (its clients: `bufio.Reader.Read`'s proof,
  `io.ReadFull`, the decoder's specs: each read is inside the file or one buffer past it, with `|F.bs| + 2^12 <
  2^62` in `decFile`), or (b) the trusted `Read` model reads `min(len, offMax - off)` instead of panicking (a
  trusted change: the user's review). Recommended (a). Also needed for the bridge, either way: an EOF-aware
  `os.File.Read` spec (`wp_osPRead` already allows `xs.length = min n (size - off)`, `k = 0` at the end;
  `Off.lean`'s `Read.wp_spec` requires the read inside the file): `0 < k` bytes and `nil`, or `0, io.EOF` at
  `off = size`, or a `*PathError`.
- *Statement change* (`openWALFiles`): `filepath.Join(dir, name)` needs `CleanAbs dir` (from
  `osPathS_cleanAbs`) and `|dir| + |name| + 2 < 2^62`: the spec takes `d.length < 2^61` and, per name,
  `b.length < 2^61` (`openAtIndex` has both: the pipeline's `dir.length < 2^61`, the names `walNameStr`s).
- *`openWALFiles`, started* (proof still `sorry`): `walOpenedRc` (an opened file with the closer it
  collected), `walOpenedRc_file`/`_rcFile`, `walOpenedRcs` (by position over `is.take j`) with `_snoc` and
  `_close` (to `closeAll`'s `[∗list] rc ∈ rcs, wal.rcFile rc`), proved. Plan for the rest: three `make2`s,
  `ownSlice_slice` on `names[k:]` (as `selectWALFiles`), the range loop with the invariant `walOpenedRcs ... j
  frs lfs rcs` and the three slices; per name `Join` (`join_child`), then `TryLockFile` with `OpenTriple`
  from `os.OpenFile.wp_fileS` (flag 2, `X := Unit`, `C _ i' := i' = i`) or `wp_fileS` (flag 0), `NewFileReader`
  (persist `rl ↦`), three appends; on an error `walOpenedRcs_close` → `closeAll`, `ErrorfErrs` of the error.
  The proof takes `[os.Assumptions] [os.file.FieldAssumptions] [fileutil.Assumptions]`.
- *Not done*: `openWALFiles`' loop, `openAtIndex`, `OpenForRead`, `Open`, `ReadAll` (blocked on the bridge
  above for the decoder's `decFile`s).

**Fifth session (branch `wal-read5`, 2026-11-13).**
- *Option (a) carried out* (no trusted change): `io.readerStream` takes `len(r) + len(p) < 2^62` of each
  `Read` (§10 records the weakened `io.ReadFull` axiom). Ripple: `bufio.ownReader` records the buffer at
  most 4 KiB; `bufio.Reader.Read.spec` and `FileBufReader.Read.spec` take, besides the read's own bound,
  `□ ∀ r, S r -∗ ⌜|r| + 2^12 < 2^62⌝` of the underlying stream (a refill reads a whole buffer at the
  position); `decFile`'s bound is `|F.bs| + 2^12 < 2^62`; `readInt64` takes `|r0| + 8 < 2^62`. The decoder
  discharges both of its reads (the frame ends at most 8 bytes past the file: Go's size check counts from
  `lastValidOff`, not past the length word). All re-proved (`lake build`).
- *`decFile`'s `FileInfo` triple is now from any stream state, which it keeps* (`□ ∀ r, {{ F.S r }} ...
  {{ F.S r ∗ ... }}`; was `{{ True }}`): an `*os.File`'s `Stat` needs the fd and the `OsMeta`, which only the
  stream state holds. `NewFileBufReader.spec` takes the same form (proof: `bufio.ownReader_open` lends the
  state out of the reader). `NewDecoder`, `decodeRecord`, `Decode` re-proved unchanged.
- *Proved*: `os.File.Read.wp_eof` (`LinuxFs/Proof/os/ReadEof.lean`): `Read` over the whole file's bytes from
  0 and its `OsMeta`: `k` bytes from the offset (`k ≤ len(p)`, inside the file), `nil` with `k > 0` unless `p`
  is empty, `0, io.EOF` only at or past the end, or `0` and a `*PathError` (`fmtErrorOk`); any `len(p)` (reads
  of more than 1 GiB are short).
- *Proved: the bridge* `walDecFile_ok` (`wal/ReadBridge.lean`): `walDecFile rl f fd name fl g` (the
  `*fileReader` at `rl`, the bytes `g.bs.map (·.1)`, the state `walFileS`) satisfies `decFile IoE eof`, given
  `osInv`, `io.EOF`'s value, `rl ↦□ fileReader{f}`, the fd readable of `g.ino`, `g.om.size = |g.bs|`,
  `|g.bs| + 2^12 < 2^62`, and `IoE` holding of every pointer error (`Read`'s `*PathError`, `Stat`'s error).
  `walFileS` now also records `r <+: g.bs.map (·.1)` (ReadDefs; nothing constructed it yet).
- **Finding (trusted model gap, for the coordinator/user)**: the `os` model's `fileStat` has no `name` and
  `Name()` no body (its method set lists it, no unfold), so `fi.Name()` is stuck; the decoder calls it (the
  "frame too large" error message, `fileInfoOk`). The bridge takes `os.fileStat.Name.spec`
  (`LinuxFs/Spec/os/fileStat__Name.lean`, no proof) as a hypothesis. Discharge: the model keeps the base name
  in `fileStat` (`Stat` stores it, `Name` returns it) — a trusted change for the user's review.
- *Statement change*: `openWALFiles` takes each name below `2^60` (was `2^61`: `|d| + |b| + 2 < 2^62` fails
  at `|d| = |b| = 2^61 - 1`); `openAtIndex`'s names are `walNameStr`s.
- *`openWALFiles`, in progress*: `walOpen_triple` (`os.OpenFile` of a claim's file as `TryLockFile`'s
  `OpenTriple`, `X := Unit`, `C _ i' := i' = i`), the loop invariant (three slices, `walOpenedRcs`, the claim's
  resources, `names[k:]` split out with `ownSlice_slice`), the exit, the write-mode success iteration
  (`TryLockFile`, the two appends, `l.File`, `NewFileReader` persisted, `walOpenedRcs_snoc`) and the
  write-mode error (`closeAll` over `walOpenedRcs_close`, `Errorf` `%w`, `wp_for_post` of the return) proved;
  left `sorry`: the read mode only (`os.OpenFile.wp_fileS` at flag 0; its error is `fmtErrorOkOrNil`, made
  `errOk` by `fileutil.errOk_of_fmtErrorOk`; `Errorf`'s `%q` of `p` by `argWf_string`; appends `nil` and
  `rf`; the same tail as the write mode). Gotcha: `omega`/`word` facts inside
  this long proof gave kernel "application type mismatch" on `_proof_` auxiliaries (an instance argument
  dropped): moved into top-level lemmas (`walOpen_lt_sub`, `walOpen_eq_sub`, `walOpen_succ`, `walOpen_getElem?`).
- *Coordinator messages noted*: `walHandleIn`'s new `walDirH` conjunct is `ReadAll`'s to provide (not done
  here); the known-zero lemma after `ZeroToEnd` (branch `wal-kz`) stays a hypothesis of `ReadAll` until it
  lands.

**Sixth session (branch `wal-read6`, 2026-11-13).**
- *Proved* (no `sorry`, `lake build`): `openWALFiles` (read mode: `os.OpenFile.wp_fileS` at `O_RDONLY`, its
  error made `errOk` by the local `walOpen_errOk`; the error arm `closeAll` and `Errorf` with `%q` of the
  path, `argWf_string`, and `%w`). New modules, proved: `HandleAlloc.lean` (`import all` of `Ghost.lean`:
  `walHandle_alloc`, `walHandleP_mint`/`walOpening_mint` (a handle from `walHandleAuth` and `walLockedTok`),
  `walHandleP_set` (`ReadAll`: `opening` to `append`/`failed`), `walGhost_handleAuth`); `OpenFiles.lean`
  (`walDecFiles_mk`: `openWALFiles`' `walOpenedFile`s and the opened segments' program halves `segHalves`
  give `NewDecoder`'s `[∗list] F ∈ fs, decFile IoE eof F ∗ F.S []`, `fs.map (·.fr)` the readers, and
  `WalDecTie` (`walReadTie`'s per-file facts) and the locks; over `walDecFile_ok`); `OpenNames.lean` (pure:
  `walFileName_walNameStr` (`hex16 = fmt.hexPad 16`, last 16 digits), `walName_unique`/`walName_seg` (a
  present `.wal` name is a segment's, the inodes distinct), `walDirNamesOk_of` (`selectWALFiles`' premise from
  `SegsNamed`, `WalAbsD.names`, `nameBound`), `walNamesOut_segs` (`readWALNames`' names are exactly
  `lay.segs.map name`, by `Perm.eq_of_pairwise`), `walOpenNames_ok` (`openWALFiles`' name premise from the
  selected position; names are 37 bytes)).
- **Statement change, `openAtIndex`'s read mode**: its read-mode success returned
  `walUnlockedTok`, but `walReadH false` holds the program's halves of the WAL's files and directory claim
  (`walReadTie`), which only a `walLockedTok` holder may have out of `walParked`; `walReadOnlyF` already
  holds `walLockedTok`. The read-mode success now returns `walLockedTok` (`OpenForRead`'s statement does not
  change).
- **Gaps found (`openAtIndex`'s pinning step; for the invariant's owner):**
  1. *The WAL directory's path.* `readWALNames`/`openWALFiles`/the pipeline need `osPathS R dir dq j` with
     `j = lay.j`: from the area's spine `osPathS R r qp jr` and the program's half of the area claim
     (`walAreaRes`: `osNames jr N ½ h`) it needs `h.cur !! nm = some (.dir lay.j)` for a present WAL. The
     invariant does not say it: `WalsOk` has `InArea s.area dir nm ∧ lay.nm = nm` only, `AbsentNone` is the
     absent case. Proposed: a framed pure conjunct (or a `WalsNamed` clause) `∀ dir lay, Ls !! dir = some
     lay → ∀ N h, (lay.jr, N, h) ∈ cl → N.Mem lay.nm → h.cur !! lay.nm = some (.dir lay.j)`, with the
     agreement of the program's area claim with the invariant's (`WalsCreateOk`'s claim holding `nm`, the
     same key by the shared invariant's disjointness, a step at `⊤`). Kept by `cut` (area untouched),
     `Create`'s commit (the rename sets `nm ↦ J`), the crash (`WalsStart`'s `m.entry jr nm = .dir lay.j`).
  2. *The absent case* (`o = none`): `os.Open(dir)` must fail; `readWALNames`' spec takes the directory's
     claim, so `selectWALFiles` needs a variant for a missing directory (`AbsentNone`: the area claim
     holds no `nm`), or the pin must find the directory present.
  3. *The pipeline's claims* (write mode): `newFilePipeline` takes `tmpClaim j (pipeTmp 0)` (the whole claim
     on `0.tmp`, and a leftover file whole); the `N.tmp` claims are outside `WalDirClaim` and not in
     `walParked`: where `walInv_alloc` puts them (half the invariant's, half returned to the program) they
     must reach `Open` whole.
  4. *`decFile`'s size bound* `|g.bs| + 2^12 < 2^62` and `os.fileStat.Name.spec` (`wal-above`), and
     `isEofOk IoE eof ueof` for `IoE` the pointer errors (`errors.Is` of a `*PathError` against `io.EOF`:
     Perennial's `errors.Is` spec), are hypotheses-to-be of `openAtIndex`.
- *Plan for `openAtIndex`* (not started in the proof file): the pin at the call's first step
  (`wp_notCrashed_acc`, mask unchanged: open `walInv`, `walUnlockedTok_lock`, the AU's commit, the WAL's
  segments into `O` and its claim into `D`, exact halves by agreement with `segResF` (idle: the flag was
  `true`, no handle, so no write in flight), write mode `walOpening_mint` from `walGhost_handleAuth`); then
  `selectWALFiles` (premise `WalDirNamesOk` from `WalsNamed`), `openWALFiles` (names from the selected
  position: `walNamesOut_segs`, `walOpenNames_ok`), `walDecFiles_mk`, `NewDecoder`, the struct; the error arms unpin at a later step (the `Errorf`
  call) with `walLockedTok_unlock`.

**Seventh session (branch `wal-read7`, 2026-11-13).**
- *Gaps 1 and 3 closed in the invariant* (W1 log, eighth session: `WalsAt`, `walTmpParked`, `walInv_alloc`'s new
  premises; the lemmas the other units apply).
- *Gap 2, a missing WAL directory, proved* (no `sorry`): `os.OpenFile.wp_absentS`/`os.Open.wp_absentS`
  (`LinuxFs/Proof/os/NsAbsentS.lean`, over `wp_osOpenAbsentS`, `EINTR` retried); `fileutil.ReadDir.specAbsent`
  (no option, `d/b` with `b` absent in a claim fraction: an error, `fmtErrorOkOrNil`) proved
  (`ReadDir.wp_proofAbsent`: `applyOpts` over `nil` by `wp_method_call`, the empty loop by `wp_for`);
  `readWALNames.specAbsent`, `selectWALFiles.specAbsent` (an `errOk` error; claim and path back), proved over
  them and `fmt.ErrorfErrs`.
- *`openAtIndex`'s pin, the area part* (`OpenPin.lean`, proved): `walDirAt_pure` (from `WalsOk`, `WalsAt`,
  `AbsentNone`, a claim `(jr, N, h) ∈ cl` holding `nm`: `s.wal !! dir = none → h.cur !! nm = none`, and for a WAL
  its layout with `h.cur !! nm = some (.dir lay.j)`), `walInvBody_areaAt` (the program's area-claim fraction is
  the invariant's claim, `osNames_same_name`; at a mask with `osShN`).
- *ReadDefs repaired after `wal-cut7`*: `walReadH`'s pipeline is `∃ j, walPipeH fp dir j 0` (`walPipeH` now takes
  the directory inode); `ReadAll` ties `j` to `walReadTie`'s claim, and must establish `walHandleIn`'s new facts
  (`walDirH` with `j`, the dir fd, `walTmps ⊆ X`, the tail name; the size and `enti`/`snapi` bounds).
- *Not done*: `openAtIndex` (beyond the pin's area part), `OpenForRead`, `Open`. The rest of the pin: at the
  first step (`wp_notCrashed_acc`), open `walInv`, `walInvBody_areaAt`'s facts for the AU's `o` (`walDirIs` agrees
  with `s.wal` through `walMapLe`), `walUnlockedTok_lock`, take the segments and directory claim out
  (`walParked`) and, in write mode, `walTmpParked_take` (the pipeline's `tmpClaim j (pipeTmp 0)` and the handle's
  `pipeTmp 1`); `o = none`: commit `Q none` and continue on `selectWALFiles.specAbsent` with the token back.

**Eighth session (branch `wal-read8`, 2026-11-13): the pin, two gaps in the invariant; nothing proved.**
Two facts the pin and the error arms need are not in `walInv`; both are invariant designs (W1's owner), not
`openAtIndex`'s to make. No statement or proof changed this session.
- **Gap A, the put-back (`openAtIndex`'s error arms, `Close`, a failed `ReadAll`).** After the pin, the error
  arms (`selectWALFiles`' errors, e.g. no file at the snapshot's index; `openWALFiles`' `EMFILE`/`EIO`) must
  return `walUnlockedTok`, i.e. turn the flag back to `true`, which needs `O = D = []` and `T = []` in
  `walParked`. The program holds what *it* took, but nothing in the invariant says `O`, `D`, `T` are exactly
  that: at the put-back `walParked`'s `O'`, `D'`, `T'` are existentials no resource of the program ties to
  (another unit with the flag `false` could, as far as the invariant says, have taken more). Dropping halves
  is no way out (they would be lost to the next `Open`). Needed: a ghost record of what is out with a
  program-held half, e.g. `WalGS.γpo` holding `(O, D-keys, T)`, the invariant's half in `walParked`
  (`b = true ↔ record = ([], [], [])`), the program's half in the handle (`walReadH`/`walOpenWF`/`walCreateP`:
  sealed bodies, no client statement changes), `walUnlockedTok` holding the empty record's half. Every
  unit that changes `O`/`D`/`T` then updates both halves: `Open`'s pin, `ReadAll`'s return, `cut`'s rename
  (new tail in, old tail out, the claim's new history), `Create`'s commit, `Close`. Recording `D` by claim
  key `(j, N)` rather than by value avoids an update at every directory step. (A weaker "everything out is
  one WAL's" clause does not suffice: the put-back must supply `segResP g` for each out inode, so it needs
  `O'` ⊆ what it holds.)
- **Gap B, the parked segments are idle (the pin's exact halves).** The pin turns the parked `segResP g`
  (any contents) into `segHalves g` (the layout's `g.om`, `g.bs`; `walDecFiles_mk` needs `g.om.size =
  |g.bs|` from `WalAbsD.metas`) by agreement with `segResF F g` — only when `F !! g.ino = none`. Nothing in
  `walInvBody` excludes a change in flight on a parked segment: in `segResF`'s in-flight cases the
  invariant holds no `osMeta` (the token's `tokRes` holds it whole, in the extension's interpretation), so
  the parked half contradicts it only through the state interpretation (`tokRes_meta_whole`,
  `World.lean`). Two fixes: (1) pure, in the invariant: `∀ i, F !! i ≠ none → i ∈ O` (a change in flight
  only on a segment taken out; `walParked` would need `F`, or a new last conjunct of `walInvBody` stating it
  over `walParked`'s `O`, which then must be visible: same record as gap A); kept by the tail's writes and
  `cut`'s truncate (their segment is out), established at `walInv_alloc` (`F = ∅`). (2) A step lemma giving
  both `notCrashed` and the `fsExt` interpretation (`wp_notCrashed_acc` and Perennial's `wp_ext_acc` in
  one; `goose_bstateInterp_eq`), then `gAuth_lookup` of the token and `tokRes_meta_whole` inside the pin's
  update. Recommended: (1) with gap A's record (one design, no extension-level work).
- *What the pin must take* (for when A and B land): the segments **from the selected position `k` on**
  (`k = walSearch (lay.segs.map (walNameIdx ∘ name)) s.1`, a function of the layout, known at the pin), not
  all of them: a handle cannot drop a parked half; the directory claim (`WalDirClaim lay.j hj cl`'s, into
  `D`); write mode `walTmpParked_take`. If `walSearch` fails, the pin takes only the claim. Note for `Open`
  (write mode, the coordinator's `wal-cut9` heads-up): a leftover `N.tmp` handed to `newFilePipeline` must
  satisfy `trFile`'s new `cut = none ∧ lo ≤ size`, and the handle starts `walPipeH … h.pc` at `pc = 0`.
- *Callees for `openAtIndex`'s write mode*: `os.File.Name` and `filepath.Base` have specs
  (`LinuxFs/Spec/os/File__Name.lean`, `LinuxFs/Spec/path/filepath/Base.lean`); `*LockedFile`'s promoted
  `Name` and `WAL.tail` over `walReadH`'s locks (`WAL__tail` is over the write handle) are to check.

**Ninth session (branch `wal-read9`, 2026-11-13): gaps A and B closed in the invariant** (W1 log, tenth
session: `WalOut`, `walParked Ls cl F`, `Parked.lean`). For `openAtIndex`'s pin, at its first step
(`wp_notCrashed_acc`): open `walInv`, `walParked_lock` (with `walUnlockedTok`: `walLockedTok`, the empty
record, and no change in flight anywhere), then `walParked_takeSegs` with `S = lay.segs.drop k` (`k` the
`walSearch` position; `segsAll_nodup_iff` for the distinct inodes), `walParked_takeClaim` (the WAL directory's
claim, `WalDirClaimOf` from `WalsOk`/`DirKeysOk`), in write mode `walParked_takeTmps`; each `segResP g` with
`⌜F !! g.ino = none⌝` and the invariant's `segResF F g = segRes g` gives the exact halves (`osMeta_agree`,
`osBytes_agree`). The handle's body (`walReadH`) must then hold `walOutFrag ⟨S.map ino, [(lay.j, .except X)],
[dir] or []⟩` (a `ReadDefs` change, sealed: no client statement changes). The error arms put back with
`_putSeg`/`_putClaim`/`_putTmps`, then `walParked_unlock`; the put-back of the WAL's **last** segment needs
`F !! ino = none`, open (W1 log, tenth session, "Open": a `walTailsRes` clause, a change only on a registered
tail). Task 3 (the pin, `openAtIndex`, `OpenForRead`, `Open`) not started.

**Tenth session (branch `wal-read10`, 2026-11-14).**
- *The last segment's put-back* (the ninth session's open item): closed in the invariant (W1 log, eleventh session:
  `TailsOnly`, and the tails' authority halved with the lock holder, `walTailsFrag`): a holder with `walTailsFrag ∅`
  gets `∀ i, F !! i = none` from `walTailsRes_none`, so `walParked_putSeg`'s `hF` holds for every segment it took.
- *The pin, proved* (`OpenPinTake.lean`, no `sorry`): **`walInvBody_pin … (hd : s.wal !! dir = some d) (k : Nat)
  (write : Bool) : ⊢ walInvBody s -∗ walUnlockedTok ==∗ ∃ lay X hj, ⌜InArea s.area dir lay.nm ∧ lay.jr = jr ∧
  (∀ b ∈ X, walNameP b = false) ∧ ClaimCoh hj lay.j (.except X) ∧ WalAbsD C Mr d lay hj.cur⌝ ∗ walInvBody s ∗
  walLockedTok ∗ walTailsFrag ∅ ∗ walOutFrag ⟨(lay.segs.drop k).map ino, [(lay.j, .except X)], if write then
  [dir] else []⟩ ∗ ([∗list] g ∈ lay.segs.drop k, segRes g) ∗ osNames lay.j (.except X) ½ hj ∗ (if write then
  walTmpsRes lay.j else emp)`** (the program's halves exact: `segsRes_exact`, by agreement with the invariant's,
  nothing in flight once the lock is taken). Helpers: `bigSepL_take_drop`, `segRes_exact`, `segResF_empty`,
  `walOutFrag_eq'`. `k` is the caller's (`walSearch` of the layout's names, which `selectWALFiles` computes).
- *What the pin's caller still needs*: (1) the update's commit raises `unl` in write mode, so `walInvBody s` must
  become `walInvBody s'` with `dir`'s `unl` raised (a `walInvBody_unl`, as `walInvBody_named`: `WalsOk`, `DirKeysOk`,
  `WalsNamed`, `AbsentNone` do not read `unl`; to check); (2) the put-back lemma for the error arms at a later state
  (W1 log, eleventh session, gap C: the claim's survival; the segments by inode and length); (3) the handle's body
  (`walReadH`) to hold what the pin returns (`walOutFrag`, `walTailsFrag ∅`, the exact halves are already
  `walReadTie`'s `walFileS`), a `ReadDefs` change (sealed); (4) the absent case (`s.wal !! dir = none`): no pin, the
  token kept, `selectWALFiles.specAbsent`.
- *Callees checked*: `WAL.tail`'s spec (`WAL__tail.lean`) is over the `locks` field and the slice only, so it holds
  over `walReadH`'s `locks ↦* lfs` (nonempty: `openWALFiles` opens at least the selected file); `*LockedFile`'s
  promoted `Name` is `os.File.Name` after `iStructNamed` of `fileutil.lockedFile` and `wp_method_call`, as `WAL.cut`'s
  proof does (no new spec).
- *The segments' put-back at a later state, proved* (`ParkedPut.lean`): **`walParked_putSegIno Ls cl F o g hnd (hF :
  F !! g.ino = none) (hlen : ∀ g' ∈ segsAll Ls, g'.ino = g.ino → g'.bs.length = g.bs.length)`**: onto the segment of
  `Ls` with `g`'s inode (`segResP_congr`: the program's halves depend only on the inode and length), or dropped
  if none has it (`segsP_forget`). `hlen` at the error arm: the invariant's `segRes g'` (nothing in flight,
  `walTailsRes_none`) and the held `segRes g` agree on the `OsMeta`, and `WalAbsD.metas` gives `size = |bs|` at both
  ends (the pin's `WalAbsD` for `g`). The claim's put-back waits for gap C (W1 log, eleventh session).
- *Not done*: the body-level put-back (`walInvBody_unpin`: gap C), `walInvBody_unl` (the commit's `unl` raise),
  `openAtIndex`, `OpenForRead`, `Open` (the proofs; `Open`'s leftover `N.tmp` meeting `trFile`'s `cut = none ∧ lo ≤
  size` and `walPipeH` at `pc = 0` are for its pipeline step). The `ZeroToEnd` instance on the crash-tracked tail
  (`wal-tc2`) stays a hypothesis of `ReadAll`.

**Eleventh session (branch `wal-read11`, 2026-11-14).** Gap C closed (W1 log, twelfth session); no `sorry` added.
- *The pin keys its WAL* (`OpenPinTake.lean`): **`walInvBody_pin`'s post gains `walDirKey dir lay.j X`** and the
  pure fact `(lay.segs.map ino).Nodup` (`walDirKeys_pin`: the generation's key if any, `walDirKeysAuth_get`, else
  made, `dirKeysOk_key`; the claim's `X` by `DirClaimOk.eq_of_mem`). `ReadAll` no longer makes the key: the
  handle's body carries the pin's.
- *Proved, the put-back* (`OpenUnpin.lean`): **`walInvBody_unpin … dir j X hj S write (hS : ∀ g ∈ S, g.om.size =
  g.bs.length) : ⊢ walInvBody s -∗ walLockedTok -∗ walTailsFrag ∅ -∗ walOutFrag ⟨S.map ino, [(j, .except X)], if
  write then [dir] else []⟩ -∗ [∗list] g ∈ S, segRes g -∗ osNames j (.except X) ½ hj -∗ (if write then walTmpsRes j
  else emp) -∗ walDirKey dir j X ==∗ walInvBody s ∗ walUnlockedTok`** (at any `s`: the key gives the layout and
  the claim once, `osNames_agree` its history; segments by inode, `walParked_putSegsRes`; `hS` from the pin's
  `WalAbsD.metas`).
- *Proved, the commit's `unl`* (`OpenUnl.lean`): **`walInvBody_unl … s dir p M : ⊢ walInvBody s -∗ walOwn M ==∗
  ⌜walMapLe M s.wal⌝ ∗ walInvBody (unlSt s dir p) ∗ walOwn (unlSt s dir p).wal ∗ walPast (unlSt s dir p)`**
  (`unlSt s dir p := absDiskUpd s dir (fun d => {d with unl := max d.unl p})`; nothing in the invariant reads `unl`).
- *Proved, the tail's registration* (`TailReg.lean`): `walTails_register`/`_unregister` (both halves of the tails'
  authority combined, the key inserted/deleted, split back) and **`walTailsRes_register`** (from `walTailsFrag ∅`
  and the record's facts: a fresh `γ`, the invariant's half in `walTailsRes`, the program's half, the key and
  `walTailsFrag {dir ↦ γ}`).
- *Not done*: `openAtIndex`, `OpenForRead`, `Open`, `ReadAll` (proofs still `sorry`). **Plan for `openAtIndex`**
  (the next session): (1) a step lemma for the pin, at the first call (`startSnap.Clone()`, `wp_notCrashed_acc`):
  `walInv_open` at `⊤`, the AU opened at `walAuMask` (as `CutAu`'s `fupd_mask_subseteq`), `walDirIs dir o`'s
  `walOwn M` against `walGhost s` (`walOwn_agree`); `o = some d`: `walInvBody_pin` with `k lay := walSearch
  (lay.segs.map (walNameIdx ∘ name)) s.1` (the program's `d.H` is the real one's, `walDurLe`), in write mode
  `walInvBody_unl` with `p = walOpenPos …` and the commit from `walOwn (unlSt …).wal`, read mode the commit
  unchanged; `o = none`: commit `Q none`, keep the token, continue on `selectWALFiles.specAbsent`. (2)
  `selectWALFiles` (premise `WalDirNamesOk` from the pin's new `SegsNamed lay.segs hj.cur`, `walDirNamesOk_of`;
  its position is `k lay` by `walNamesOut_segs`), `openWALFiles` (`walOpenNames_ok`), `walDecFiles_mk`,
  `NewDecoder`, the struct; write mode `WAL.tail`, `os.File.Name`, `filepath.Base`, `parseWALName`,
  `newFilePipeline` (with the pin's `walTmpsRes`). (3) The error arms: `walInvBody_unpin` at the step of the
  `Errorf` call (`wp_notCrashed_acc` again), `hS` from the pin's `WalAbsD.metas`. (4) `walReadTie` from the pin's
  outputs (it now holds them, `ReadDefs`). **Coordinator obligations noted**: `walDirH` takes the pipeline count
  `k` (`sq < 2^63 + k`, `wal-cut10`): `ReadAll`/`openAtIndex` establish the read tail's sequence number below
  `2^63` with `k = h.pc`; `wal-save11`'s handle facts (`h.cuts` increasing from the layout, the metadata's
  length bound) are `ReadAll`'s.
## W7-W12 implementation log (branch `wal-small12`, 2026-11-14)

**First session.** Task order: `Exist` (W12), then `ValidSnapshotEntries` (W8), then `ReleaseLockTo` (W9).

- **`wal.Exist.spec`** (`LinuxFs/Spec/.../wal/Exist.lean`): the old axiom over `fsExt` with plan §3's binders,
  `Create`'s resources (`walAreaOk C Mr`, the area's spine, `walAreaRes`, `osCallPerm 1`), **`walUnlockedTok`
  framed** (reading a present WAL's directory takes its claim out of `walParked`, which needs the lock, as
  `Open`'s pin), the update at `walAuMask`, and Q4 (b)'s `false` arm (`wal.ExistFalseOk o`: `o = none` or a
  fresh unnamed WAL). Ledger entry 2026-11-14.
- **Model finding [user]: `Exist` may answer `false` on a present WAL in the model.** `false` comes from
  `errors.Is(err, os.ErrNotExist)` on `ReadDir`'s error, and `fsExt` lets a failing `open`/`getdents` return
  any errno, `ENOENT` included. On configuration C, `open(2)` gives `ENOENT` only for a missing component and
  `getdents64` only on a removed directory. The proof takes the hypothesis `fileutil.ReadDir.specChildIs`
  (`ExistCallees.lean`: a present directory's read fails only with an error `errors.Is` does not take for
  `os.ErrNotExist`), unprovable until the model says "`ENOENT` only when the path does not resolve" for
  `Open` and `Readdir` (`GooseLang/Ext/Fs/Impl.lean`; note §3 of `notes/wal-fsext-models-review.md`: the same
  tightening for `Unlink` would break `RemoveAll`'s model, so it must not be extended there). Weakening
  `false` to claim nothing instead would leave the server's bootstrap without the `walAbsent` that `Create`
  needs.
- **Infrastructure gap (shared with `Open`'s pin): a path to a WAL directory.** `ReadDir.spec` needs
  `osPathS R dir dq J`, i.e. a spine through a `.only [nm]` claim of the area directory; the program holds half
  of the area claim on a cofinite `N`, which cannot be split (`osNames_split` needs the whole claim). The
  hypothesis `specChildIs` therefore reads `d/b` through a fraction of a claim on names holding `b` (as
  `ReadDir.specAbsent` does for a missing name). To prove it: a child form of `wp_osOpenDirS'`
  (`GooseLang/Ext/Fs/TreeSharedOpenDir.lean`, whose only path-dependent step is `osPathS_lookup`; the child
  lookup through a claim is `wp_osOpenFileS'`'s), then `os.OpenFile`/`os.Open` and `ReadDir` child variants.
  `openAtIndex` needs the same for `readWALNames` of a present WAL (W3/W5's gap 1 closed only the invariant's
  side).
- **Other hypotheses** (`ExistCallees.lean`): `fileutil.ReadDir.specAbsentIs` (`specAbsent` with an option
  slice; its `errors.Is` part needs the error tree of the part's `os` errors, as `errors.IsErrno.spec`), and
  `hErrNotExist` (`os`'s `isPkgInit` does not record `os.ErrNotExist`, as `hErrExist` for `Create`).
- **Proof design** (`LinuxFs/Proof/.../wal/Exist.lean`, `ExistPin.lean`): a core lemma generic in the
  linearization (`A`, `Lin`), from which `wal.Exist.wp_proof` (the AU, committed at a ghost step before
  `ReadDir`, the state unchanged) and `wal.Exist.wp_specCreate` (`Create`'s hypothesis, `A := emp`) both
  follow. Start step: `walInvBody_areaAt`'s facts; absent → `h.cur !! nm = none`; present → `walParked_lock`,
  `walParked_takeClaim` of the WAL directory's claim, `walPast s`, and a `.wal` name present
  (`WalsNamed`, `WalAbsD.nonempty`), so the read gives `true` (or an error `errors.Is` rejects: `true`). End
  step (present case): the claim found again in the new state's claims (`absLe` keeps the WAL; `WalsAt` with
  the program's area claim gives the same directory; `osClaims_keys` the same key and history; a duplicate
  would be a third half), `walParked_putClaim`, `walParked_unlock`. This put-back argument is the one
  `openAtIndex`'s error arms and `Close` need (gap A's record says what is out, not that it is still in `cl`).
- **Proved (no `sorry`)**: `ExistPure.lean` (a `.wal` name's extension; a read with a `.wal` name is
  non-empty; `false` gives `wal.ExistFalseOk`), `ExistPin.lean` (`walInvBody_existAU`, `walInvBody_existPin`,
  `walInvBody_existUnpin` and their program-step forms `walInv_existStart`/`walInv_existEnd`), `Exist.lean`
  (`wal.Exist.wp_core`, generic in the linearization; **`wal.Exist.wp_proof`** and
  **`wal.Exist.wp_specCreate`**). Hypotheses of both: `WithExt.spec` (proved), `fileutil.ReadDir.specAbsentIs`,
  `fileutil.ReadDir.specChildIs`, `hErrNotExist`. `walInvBody_existUnpin` is the put-back `openAtIndex`'s error
  arms and `Close` can reuse for a directory claim.
- **Statement change (minor):** `wal.Exist.specCreate` (`CreateCallees.lean`) takes `NameOk nm` (both `ReadDir`
  hypotheses need it; `walNameOk` allows a NUL byte); `Create.lean` passes its own `hnmO`. `wal-create12`: replace
  the hypothesis `wp_Exist` by `wal.Exist.wp_specCreate C Mr wp_WithExt wp_RDabs wp_RDchild hErrNotExist`.
- *Not started*: `ValidSnapshotEntries` (W8), `ReleaseLockTo` (W9).
