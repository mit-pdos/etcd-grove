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
