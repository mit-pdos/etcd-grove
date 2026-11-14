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

**Amended (2026-11-14, `wal-tc3`; the coordinator's option 1 of `wal-tc2`'s finding, I3b): a resize's
zeros do not write a frame.** The second disjunct now asks that the candidate `valAt (cand b) n` reads
(`latestAt`) be stamped in `(0, n]` by a change that announced a nonzero byte of the core (`WroteIn`), so
`cut`'s truncate inside a frame (the frame as of the truncate: intended bytes, then zeros) is excluded,
as a torn frame should be. The state keeps no landed change's kind (only `inflight` has it), and a
`pwrite` and a resize can leave the same candidates, so "a `pwrite`" is approximated by "nonzero": exact
for resizes, conservative for an all-zero `pwrite` over the core. Recording the kind instead would need
`OsFile`/`OsMeta` fields, their coherence in every step and a rebuild of `LinuxFs` (and the ghost would
need a witness after the landing), for no gain: either way W1 excludes a few real crashes that leave
the *intended* frame when part of it is zeros (unwritten, zeroed by the truncate, or written as zeros),
which the old W1 already did for unwritten zeros. Both are in `W1.lean`'s docstring for the review.

**Restated exactly (2026-11-14, `wal-tc4`; trusted bookkeeping pending the user's review).** The
amendment above excluded real crashes: a frame split by the page writer whose second `pwrite`'s share of
the core is zeros (the data's trailing zeros) comes back intact, yet that `pwrite` "wrote no nonzero
byte". The state now records each file's resize stamps (`OsFile.rzs`, appended by `OsFile.announce` for
a `truncate`/`falloc` kind, `[]` at `ofDisk`; read by no step: `examples/osfs/semantics/data_resize_stamps.go`),
and the change disjunct asks `p.2 ∉ f.rzs` in place of `WroteIn`. Allowed: the split frame
(`AsOfW.split_zero`); excluded: the truncate window (`AsOfW.not_rz_window`). What W1 still excludes of
real crashes: an intended core whose zero tail no announced `pwrite` has written yet (still in the
encoder's buffer when the crash comes, the bytes under it zeros): the state has no record of buffered
bytes (`W1.lean`'s docstring). Not reset at a sync (a resize in flight keeps its candidates across one;
stamps are never reused).

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
- `wal/`: `Create.wp_proof` (`Create.lean`) (`Open`, `OpenForRead`, `openAtIndex` proved over hypotheses, `wal-read12`/`wal-read13`),
  `openWALFiles.wp_proof`, `WAL.ReadAll.wp_proof`, `WAL.Save.wp_proof`, `WAL.SaveSnapshot.wp_proof`,
- `wal/`: `Create.wp_proof` (`Create.lean`), `Open.wp_proof` (`OpenForRead`, `openAtIndex` proved, `wal-read12`),
  `openWALFiles.wp_proof`, `WAL.ReadAll.wp_proof` (`WAL.Save.wp_proof`/`WAL.SaveSnapshot.wp_proof` proved over
  hypotheses, `wal-save12`, W6 log, twelfth session; `Save` re-proved over the batch bound and the window form,
  `SaveSnapshot` one `sorry` for its stream bound, `wal-save13`, thirteenth session; that `sorry` gone and
  the stream bounds withdrawn over the model's `maxBytes`, `wal-maxb14`, fourteenth session),
  `WAL.sync.wp_proof` (`saveEntry`/`saveState` proved over `encode.specTail`, `wal-save15`), `encode.specTail`;
- `fileutil/`: none (`ReadDir.wp_proof` proved, `wal-small14`; `TouchDirAll`/`CreateDirAll` proved, `wal-create7`, over the above-root hypotheses);
- `os/`: `File.Truncate.wp_proofAu` (`File__TruncateAu.lean`), `File.WriteAt.wp_proof_long` (`WriteLong.lean`,
  past 1 GiB).
Not yet stated (no `sorry`, no statement): `Close`, `ReleaseLockTo`, `Repair`, `ValidSnapshotEntries`, `Exist`
(§4.2's W7-W12), the WAL-level resize updates (I3b's open items). `Create`'s ghost steps (drop, mint, unmint, merges) are proved (`wal-create10`; W4 log, tenth session). The record of what is out of the parked state and the changes in flight only on segments out (W3/W5's gaps A and B) are in the invariant, with the pin's and the put-back's moves (`Parked.lean`, `wal-read9`; W1 log, tenth session). A change in flight only on a registered tail (`TailsOnly`), the tails' authority halved with the lock holder (`walTailsFrag`), and `openAtIndex`'s pin (`walInvBody_pin`, `OpenPinTake.lean`) are proved (`wal-read10`; W1 log, eleventh session; W3/W5 log, tenth session). Gap C (every WAL's directory claim once and exclusive, `DirClaimsOk` in `DirKeysOk`), the pin keying its WAL, the put-back (`walInvBody_unpin`), the commit's `unl` raise (`walInvBody_unl`) and the tail's registration (`walTailsRes_register`) are proved (`wal-read11`; W1 log, twelfth session; W3/W5 log, eleventh session).
`Exist` proved over hypotheses (`wal-small12`, W7-W12 log; no `sorry`); `hErrNotExist` dropped and the
`os`/extension layer of its `ReadDir` hypotheses proved over the provisional `ENOENT` rule (`wal-enoent13`,
W7-W12 log, second session); `ReadDir`'s loops and the names' bound proved (`wal-small14`, W7-W12 log, third session: `Readdirnames`' model assumes Go's `growslice` limit, pending review); left: `errors.IsPathErrnoNotExist.spec`. `ReleaseLockTo` proved; `Close` (append mode) stated and proved over `WAL.sync.specC` and the invariant law `WalCloseLaw`; `WAL.Close.specOpening` (`Open`'s hypothesis) still a hypothesis (`wal-close15`, W7-W12 log, fourth session); `WalCloseLaw` proved, `Close` (append mode) over `WAL.sync.specC` only; `specOpening`'s three gaps (the unregistered tail's fdatasync: `TailSynced` designed; the pipeline's directory inode in `walReadH`; an empty `gs`) and `Repair` stated, not proved (`wal-close16`, W7-W12 log, fifth session). `TailSynced` in the invariant, the idle tail's fdatasync proved (`walInvBody_syncIdle`, `wp_idleFsync`); `specOpening` waits for `walReadTie`'s last-name fact; `specNoDir` is over the pre-rename handle, for `wal-create14` (`wal-close17`, W7-W12 log, sixth session). `Repair`'s laws L1 (the pin of the last segment, with `TailIdle`), L2 (its reader stops only at `wr`) and L5's unchanged case proved; L3 (the `.broken` file: the invariant must own the WAL directory's non-`.wal` files), L4, `openLast`'s spec and `Repair.wp_proof` open (`wal-repair18`, W7-W12 log, seventh session). `WAL.Close.specOpening` proved (`WAL.Close.wp_proofOpening`, over `WAL.sync.specIdle`, proved, and leaf specs); L3's design fixed (the WAL directory's other files parked with its claim), not made; `openLast` stated and proved (`wal-repair19`, W7-W12 log, eighth session). L3's create step: its pure core (`brokenHist_pure`), the `O_CREAT` open over a claim on any names (`wp_osOpenCreateSN`, `os.OpenFile.specCreateTruncSncN`) proved; the invariant step waits for a WAL directory claim's exclusivity on all its names (`wal-repair20`, W7-W12 log, ninth session). The exclusivity in (`DirClaimExcl` in `DirClaimsOk`; `CreatingNew` off `walTmps`) and the create step proved (`walBroken_osAUnc`, absent-name case); the leftover `.broken`'s `O_TRUNC` (the WAL directory's other files owned by the invariant), L4 (a tail registered for an idle WAL, then `walTail_truncSup`) and `Repair.wp_proof` open (`wal-repair21`, W7-W12 log, tenth session). The WAL directories' non-`.wal` files owned by the invariant whether the claim is parked or out (`walParked`'s `walOthersL`, lent by the pseudo-key `lendKey j b` in `WalOut.D`; `walInv_lendOther`/`walInv_unlendOther`, `walBroken_osAUnc` lends the new name; `walInv_alloc` takes the others); L4 blocked: `Repair` truncates a pending tail (kind `true`) whose word at `wr` is a torn frame's, and the truncate window's crash outcomes (the image's bytes mixed with the truncate's zeros) are outside W1 (finding, W1 extension proposed); `Repair.wp_proof` not started (`wal-repair22`, W7-W12 log, eleventh session). L4's crash step proved with no trusted change (`TailCrashRep.lean`: `RepOld`, `crashTo_tailR`, `crashOkA_tailRep`, `rzStart_pureR`: the reader stops at `wr` in every crash image through W1's exact form; the eleventh session's finding withdrawn); the truncate supply's use of it waits on a channel for `RepOld` of a kind-`true` tail at later attempts (design, coordinator's), and `Repair`'s truncate/fsync failure arms cannot unregister a tail left in a window (finding); `Repair.wp_proof` not started (`wal-repair23`, W7-W12 log, twelfth session). Not yet stated (no `sorry`, no statement): `ValidSnapshotEntries`
(§4.2's W7-W11), the WAL-level resize updates (I3b's open items). `Create`'s ghost steps (drop, mint, unmint, merges) are proved (`wal-create10`; W4 log, tenth session). The record of what is out of the parked state and the changes in flight only on segments out (W3/W5's gaps A and B) are in the invariant, with the pin's and the put-back's moves (`Parked.lean`, `wal-read9`; W1 log, tenth session). A change in flight only on a registered tail (`TailsOnly`), the tails' authority halved with the lock holder (`walTailsFrag`), and `openAtIndex`'s pin (`walInvBody_pin`, `OpenPinTake.lean`) are proved (`wal-read10`; W1 log, eleventh session; W3/W5 log, tenth session).
(§4.2's W7-W12), the WAL-level resize updates (I3b's open items). `Create`'s ghost steps (drop, mint, unmint, merges) are proved (`wal-create10`; W4 log, tenth session). The record of what is out of the parked state and the changes in flight only on segments out (W3/W5's gaps A and B) are in the invariant, with the pin's and the put-back's moves (`Parked.lean`, `wal-read9`; W1 log, tenth session). A change in flight only on a registered tail (`TailsOnly`), the tails' authority halved with the lock holder (`walTailsFrag`), and `openAtIndex`'s pin (`walInvBody_pin`, `OpenPinTake.lean`) are proved (`wal-read10`; W1 log, eleventh session; W3/W5 log, tenth session). Gap C (every WAL's directory claim once and exclusive, `DirClaimsOk` in `DirKeysOk`), the pin keying its WAL, the put-back (`walInvBody_unpin`), the commit's `unl` raise (`walInvBody_unl`) and the tail's registration (`walTailsRes_register`) are proved (`wal-read11`; W1 log, twelfth session; W3/W5 log, eleventh session). `openAtIndex` and `OpenForRead` are proved, over two invariant hypotheses (`WalPinSized`: the segments' size bound; `WalDirPathLaw`: a path to the WAL directory, `wal-path13`'s to replace) and `WalDecEnvSupply` (`wal-read12`; W3/W5 log, twelfth session). `Open` is proved over `openAtIndex.spec`, `WalDirPathLaw`
and the hypothesis `WAL.Close.specOpening` (W10's to discharge); `Open`'s success keeps the client's half of the call
permission in `walOpeningF` (ledger 2026-11-14) (`wal-read13`; W3/W5 log, thirteenth session). `WalPinSized`'s
invariant conjunct is designed, not made (same log). `ReadAll`'s pure core (the running files' decode, the fold to `walReadAllOk`, the read position below
`walOpenPos`: `readAll_success`) is proved, over the hypothesis `WalReadState` (and `Decode.spec`); its wp proof
not started (`wal-readall14`; W3/W5 log, fourteenth session). The decoder's error identity (`Decode.spec` strengthened, `specR` gone), `WalTailIdle` in the invariant
(`walTailsRes`), `WalReadState`'s idle part proved (`walInvBody_readIdle`) and `walReadTie`'s selection fact are done
(`wal-readall15`; W3/W5 log, fifteenth session: open are the cuts' positivity, the pinned segments' law, `nameBound`'s
`ix < 2^64`, and the finding that `WalDecEnvSupply` is unsatisfiable). `WalDecEnvSupply` restated satisfiably (`IoE` the
`*PathError`s; `walDecEnv_eof_not`), still not true of Go (`isEofOk` over a pure `IoE`: ledger 2026-11-14, pending the user's
decision on `io.ReadFull`'s axiom); `WalReadState` restated satisfiably (the pinned names); the hypotheses' audit (`wal-readall16`;
W3/W5 log, sixteenth session). The readers' errors carry their `errors.Is` evidence through `io.readerStream` and the restated
`io.ReadFull` axiom (adopted provisionally, pending the user's review), so `WalDecEnvSupply` is true of Go (unprovable only
for `errors.newVar`'s lost allocation identity, a Perennial gap); new hypothesis `errors.IsPathErrnoEof.spec`; `walReadH`
ties the pipeline's directory inode to the claim's and `walReadTie` records `gs ≠ []` (`wal-readall17`; W3/W5 log,
seventeenth session) `WalReadState` proved and deleted (`walInvBody_readState`: the pinned
segments from `walReadTie`'s new name fact and the claim halves' agreement, no invariant law), the cuts positive
(`WalAbsD.cutPos`, `WAL.cut.spec`'s `0 < |H|`: ledger) and the names' indices below `2^64` (`WalAbsD.nameBound`);
`ReadAll.wp_proof` still `sorry`, its four-phase plan logged (`wal-readall18`; W3/W5 log, eighteenth session); its loop's pure invariant (`ReadAllLoop`: `RdLoop`, `rdLoop_ok`/`_stop`/`_fold_eof`, the indices `raIdx`, no arm panics: `readFiles_dec`), the look at the invariant before the loop (`walInv_readFiles`, no step), the arms' callees as hypotheses (`ReadAllCallees`: `UnmarshalEntLaw`, `WalHsOwn`, `CloneHsLaw`, `MustUnmarshalMessage.specWalSnap`, `GetTerm`s) and the proof's prologue through the first `Decode` are in (`wal-readall19`; W3/W5 log, nineteenth session). The loop (phase 1) and three of its five arms (state, metadata, CRC with its mismatch exit) are proved; the entry, snapshot and default arms and the loop's exit (phases 3-4) `sorry`; the error exits' rule (`readAll_failWp`), the halves lent out of the decoder, the metadata records' uniformity (`RecMd`) and no I/O error `nil` (`WalDecEnvSupply`, `walReadH`; ledger) are in (`wal-readall20`; W3/W5 log, twentieth session). All five arms and every error exit of the loop are proved (the entry arm with `ErrSliceOutOfRange`, the snapshot arm with `ErrSnapshotMismatch`, the default arm's `unexpected block type`), and the exit through the mode check (`w.tail()` non-nil, `errors.Is(err, io.EOF)`, the decoder's error returned) and the pure facts at `io.EOF` (`rdLoop_stop`); phases 3-4 (from `Seek`) one `sorry` (`wal-readall21`; W3/W5 log, twenty-first session). `Decode` gives back the streams of the files it leaves (ledger; at `io.EOF` it holds none), so the loop ends with every file's stream; the decoder's end offset/CRC (`rdLoop_stop_end`) and the residue's `LastCRC` (`ReadAllTail`) are in; phases 3-4 still one `sorry`, the decoder-end-is-`wr` pure lemma next (`wal-readall22`; W3/W5 log, twenty-second session). The reader ends at `lay.wr` with the chain's CRC (`walReadFiles_running_end`, pure); `LastOffset`, `Seek`, the tail registered at the look before the loop and `ZeroToEnd` on it (named hypotheses `walInvRegisterTailLaw`, `ZeroToEnd.specWalTail`, until `wal-tc14`), the fdatasync, with their error exits, proved; one `sorry` left from `fileutil.Fsync(w.dirFile)` on (the two directory syncs with the AU's commit, `match`, phase 4) (`wal-readall23`; W3/W5 log, twenty-third session). The update commits at the look before the loop (`walInv_readCommit`, which also lends the registered name claim); the named step by a coherent committed claim (`walInv_namedBy`) and the synced mark at the commit's state (`walInv_tailH`) are proved lemmas; one `sorry` left, same place; not yet adapted to `wal-tc15` (`wal-readall24`; W3/W5 log, twenty-fourth session). Every program step of `ReadAll` is proved (both directory syncs with `walNamed` and the synced mark at the commit's state, `!match` to its return, `match` to its return); one `sorry` left, the success arm's `walOpenWF` (its obligations listed, the first: the history at the registration equals the commit's); the zero length word at the reader's stop proved (`readAll_tailZeroWord`); switched to `wal-tc17`'s `walInvRegisterPendLaw`/`walTailP`, `ZeroToEnd.specWalTail` restated over it, the pending fdatasync a named hypothesis (`Fdatasync.specWalPend`, `wal-tc18`'s) (`wal-readall25`; W3/W5 log, twenty-fifth session). The commit and the registration at one opening (`walInv_readCommitReg`, `wp_register` dropped); `walOpenWF`'s (b), (c)'s `st.md = some _`, (e) and `w.dirFile`'s inode (`walOpeningF` records the directory key, `walDirKey_agree`) proved; three obligations blocked on open ledger entries (an empty metadata read back `nil`, the index bound `max + 1 < 2^64`, the tail's sequence bound); (d)'s fold bounds, (f)'s give-back law and (g) to do; one `sorry` (`wal-readall26`; W3/W5 log, twenty-sixth session). `walOpenWF` assembled: obligations (d), (f), (g) proved (`readAll_idx`, `walInv_readGive`, `readAll_splitLeft`, the tie's `walTmps ⊆ X`), the empty-metadata entry decided as Fix B (`Create` takes `md ≠ []`, `WalsBounded` keeps it) and the index bound as `WalsBounded`'s `¬ walHasMaxIdx` (kept by `Save`/`SaveSnapshot`'s appends); one `sorry` left, the tail's sequence bound (task 3, designed in `notes/bounds-plan.md`, not made) (`wal-readall27`; W3/W5 log, twenty-seventh session).
invariant conjunct is designed, not made (same log). Each registered WAL name has its own claim (`walNamesRes`, a framed conjunct; registration pending linked to the lock token, `walNamesFrag`), and the path law `walInv_dirPath` (a kept fraction of `osPathS R dir _ j` from `walDirKey`, with `walNamesFrag none`) is proved (`wal-path13`; W1 log, thirteenth session); `walAreaRes` holds every WAL name not split out (`walSplitFrag`), `Exist`/`openAtIndex`/`Create` read a registered name through its own claim, `openAtIndex` takes its path from `walInv_dirPath`, and `Create`'s post-commit split (`walInv_splitNew`) and registration (`walInv_register`) are proved, not yet used by `Create`'s body (`wal-path14`; W1 log, fourteenth session). Open: `renameWAL`'s path law, `Open`'s `WalDirPathLaw`, `WalsBounded`.
`ix < 2^64`, and the finding that `WalDecEnvSupply` is unsatisfiable).
invariant conjunct is designed, not made (same log). Each registered WAL name has its own claim (`walNamesRes`, a framed conjunct; registration pending linked to the lock token, `walNamesFrag`), and the path law `walInv_dirPath` (a kept fraction of `osPathS R dir _ j` from `walDirKey`, with `walNamesFrag none`) is proved (`wal-path13`; W1 log, thirteenth session); `walAreaRes` holds every WAL name not split out (`walSplitFrag`), `Exist`/`openAtIndex`/`Create` read a registered name through its own claim, `openAtIndex` takes its path from `walInv_dirPath`, and `Create`'s post-commit split (`walInv_splitNew`) and registration (`walInv_register`) are proved, not yet used by `Create`'s body (`wal-path14`; W1 log, fourteenth session). `WalsBounded` (metadata `< 2^41`, a framed conjunct; the segments' size read at a step, `wp_segs_size`) replaces `WalPinSized`, and `Open` takes its path from `walInv_dirPath` (`WalDirPathLaw` deleted); `renameWAL.spec`'s spine law restated with `notCrashed` and the update's result (ledger); the nil-receiver `File.Close` proved (`wal-path15`; W1 log, fifteenth session). `renameWAL` proved over `renameWALUnlock.spec` (a hypothesis, unprovable as stated: ledger 2026-11-14) and `errors.AsLinkError.spec`; `Create` through `Preallocate` (`wal-create14`; W4 log, sixteenth session). `Create`'s header phase proved through `syncDir(nm.tmp)` (the encoder, `saveCrc`, the metadata record, the initial snapshot frozen by `walSnapAt_lit` over the new premise `WalMarshalCreateOk Mr`, `SaveSnapshot.specPre`, every error exit), `os.Rename.specAbsentSrc` proved (`wal-create15`; W4 log, seventeenth session). `Create` proved through the call of `renameWAL` (the fresh layout's `WalAbsD`, `J`'s claims and `hJC`, the minting, the update `createFresh_osAUnc`, `RenameWALOk`'s laws `create_spine`/`createU_none`); `CreateDirAll.specTmp`'s post says the new directory names nothing at any crash (ledger; obligation on the extension's `mkdir` law) (`wal-create16`; W4 log, eighteenth session). `renameWALPost`'s error arms restated (the lock file open or closed, `walLockLeft`; the spines' area part the invariant's lend, `walInv_areaPath`), `renameWAL` re-proved, `Create`'s committed-error arm proved (registration, `create_areaBack`); the second close `os.File.Close.specClosed` a hypothesis (the model is stuck on a closed fd: trusted change proposed) (`wal-create17`; W4 log, nineteenth session). `hJC` limited to the crashes keeping `J`'s entries (the commit bound raised past them), `specTmp`'s false `valAfter` clause dropped (ledger); the closed-file `Close` model change made but not merged (blocked: the open-fd `Close` proofs cannot refute `fd = -1`, §10) (`wal-create18`; W4 log, twentieth session). The fd predicates carry `0 ≤ fd.toInt` (`gFdElem`, option (a)), the closed-file model merged, `os.File.Close.specClosed` proved (pre with `isPkgInit pkg_id.os`, ledger), arm 3 (the unminting, `CreateUnmint.lean`) proved (`wal-create19`; W4 log, twenty-first session). The handle before naming (`walOpenWFU`, `walDirH`'s naming parameter, registered but not named; its laws in `HandleUnnamed.lean`), `renameWALPost`'s arm 2 over it (the caller's residue `UH`, `Create`'s `createUH`; ledger), `createSpR` with the rename as the last writer (`wal-create20`; W4 log, twenty-second session). The commit registers the fresh WAL's tail (`walCreateQ`'s `walTailReg`), arm 1 builds the handle before naming (`CreateHandle.lean`: `create_ghost`, `create_handleIn`, proved; `WalPbIn.NilLaw` a new hypothesis), `walDirH`'s tail name under any parent, the handle's `decoder` field an interface, `SaveSnapshot.specPre`'s indices (ledger) (`wal-create21`; W4 log, twenty-third session). Both success arms of `Create` proved through one continuation (`create_named_cont`: the parent's `OpenDir`/`Fsync`/close, `walInv_named`, `RemoveAll(nm.tmp)`, `create_areaBack`, `walPurgeW_fresh_lbs`); left `sorry`: the three error exits after the rename (`cleanupWAL`, designed, not made) and the fsync-failed-close-succeeded path, a code bug (`Create` returns `(nil, nil)`: `nonissues/etcd-wal-create-parent-fsync-nil-nil.md`, fork diff 0005 pending the user) (`wal-create22`; W4 log, twenty-fourth session). The cleanup's `Close` (`WAL.Close.specU`, over `walOpenWFU`, no update, `walCloseLawU`; the free token and the `dir` field back, or the lock token when the sync failed) proved; `WAL.sync.specC`'s error arm keeps the lock token, `walHandleC`/`specC` generic in the naming fact (ledger) (`wal-create23`; W4 log, twenty-fifth session). Open: `cleanupWAL` (its rename to `nm.broken.<t>` needs a `time.Time.Format` spec bounding the timestamp's characters and length, a trust-boundary change for the user; then the invariant step and the broken name's claim), `Create`'s four `sorry` sites (fix 0005 translated; the deferred `f.Close()` needs the tail lock's identity through `walOpenWFU` and, on a failed `Close`, the tail file back from `sync`: ledger), `renameWALUnlock` (its `RenameWALOk` law for `UH`, now unregistering the tail too).

The resize stamps reach the WAL's crash condition (`OsMeta.rz`, `MetaOk.rz`, `OsCoh.tok_rz`; `CrashOk` passes `segRzOf`) and `W1G.drop_rz` transports W1 across a truncate's zeros (`wal-tc5`; W1 log, fifteenth session). `W1G` is over the known candidates past the bytes (`segBytesX`, the crash take exporting `om.pc`'s candidates), and the truncate window's pure `CrashOk` from an exact tail is proved (`crashOkA_win`, over `crashTo_tailL`) (`wal-tc6`; W1 log, sixteenth session); the landing step (`crashOkA` from the in-flight layout to the landed one), the window-to-window form (a `Save`'s window before the truncate), the WAL-level supplies, `specWalTail` and the `ZeroToEnd` instance remain (I3b, `wal-tc6` entry). A write in flight past the size is in the layout (`wrMeta`) and the crash take; `saveEntry`/`saveState` proved over `encode.specTail`; the writer past the size waits on known zeros past the size (lost by `OsMeta.synced`), the window's size fact and `TailWin`'s past-size clause (`wal-save15`; W6 log, fifteenth session).
The resize stamps reach the WAL's crash condition (`OsMeta.rz`, `MetaOk.rz`, `OsCoh.tok_rz`; `CrashOk` passes `segRzOf`) and `W1G.drop_rz` transports W1 across a truncate's zeros (`wal-tc5`; W1 log, fifteenth session). `W1G` is over the known candidates past the bytes (`segBytesX`, the crash take exporting `om.pc`'s candidates), and the truncate window's pure `CrashOk` from an exact tail is proved (`crashOkA_win`, over `crashTo_tailL`) (`wal-tc6`; W1 log, sixteenth session); the window-to-window form (`crashOkA_rzStart`, over the invariant's new `WalAbsD.winLo` and the extension's `OsMeta.TcZ`/`0 < n` at the start's commit) and the landing's facts (`rzLand`, `segBytesX_rzLand`) are proved (`wal-tc7`; W1 log, seventeenth session); the WAL-level supplies, `specWalTail` and the `ZeroToEnd` instance remain (I3b, `wal-tc7` entry). The start's `zf ≥ size` is in the commit's `OsMeta.TcZ`, the landing's static relation and crash condition and the invariant's transports over any crash step are proved (`walAbsD_rzLand`, `crashOkA_rzLand`, `walsOk_tailA`/`dirKeysOk_tailA`, `tailCrashStep_rzStart`/`_rzLand`); the not-landed outcome needs the extension's `rsUndone` to keep the stamp and the candidates past the size (`rsUndoneK`, designed); `truncSup`, `specWalTail`, growth and `ZeroToEnd`'s instance not started (`wal-tc8`; W1 log, eighteenth session; I3b, `wal-tc8` entry). `rsUndoneK` is in (a not-landed truncate's `OsMeta` keeps the candidates past the size and the stamp, `rsUnMeta`; `os.ftUndoneH` up to `tc`/`rz`); `specWalTail`'s `TailZ` post needs `os.ftDoneH`/`ftUndoneH` to carry a domain fact on their `tc` (`TcKnows`, proposed); `truncSup`, growth and `ZeroToEnd`'s instance not started (`wal-tc9`; W1 log, nineteenth session; I3b, `wal-tc9` entry). `TcKnows` is on `os.ftDoneH`/`ftUndoneH` (ledger); the truncate supply at the write position (`walTail_truncSup`) and `os.File.Truncate.specWalTail` are proved, `WAL.cut.wp_proof` no longer takes the latter; growth (`fallocSup`, the growing truncate) and `ZeroToEnd`'s instance not started (`wal-tc10`; W1 log, twentieth session; I3b, `wal-tc10` entry). The growth's pure pieces are proved (`RzGrow.lean`: the first step `rzSeg … tr tg` with `size ≤ tg ≤ hi`, `crashOkA_rzGrow`/`tailCrashStep_rzGrow`/`rzGrow_pure`; the landing `rzLandG`, `crashOkA_rzLandG`/`walAbsD_rzLandG`/`rzLandG_pure`, given that the bytes grown over have the candidates the `OsMeta` knew, `hzs`) and `fallocDoneH` carries `TcKnowsF` (ledger); the supplies (`fallocSup`, the growing truncate's) wait on three extension facts (`fallocate`'s start: `0 < n ∧ m.TcZ`; its not-landed outcome: `rsUndoneK`; `rsDoneK`'s `zs`: the `OsMeta`'s known candidates), and `ZeroToEnd`'s instance (`ZeroToEnd.specWalTail`, named) on them and on `ZteMeta` (ledger, proposed) (`wal-tc11`; W1 log, twenty-first session; I3b, `wal-tc11` entry). The three extension facts are in (`wp_osFallocStart`'s `0 < n ∧ m.TcZ`, `fallocAuW`'s commit; `rsOutF`'s undone arm `rsUndoneK m.cut.isNone false`, `fallocOutH`'s up to `tc`/`rz` with `TcKnowsF`; `rsDoneK`'s `zs` the `OsMeta`'s known candidates), `preGrownH i m w Z` carries `PcKeep` and `Z → ZeroPg`, `ZeroToEnd.specAu`'s post `ZteMeta` (ledger, adopted); the WAL's growth supplies are **blocked on an invariant fact**: at their commits they need the target `tg` (the size `ZeroToEnd` found) `≤ |lay.old|` and `≤ g.om.hi`, which neither the tie nor the state found gives (`wal-tc12`; W1 log, twenty-second session; I3b, `wal-tc12` entry). The tails' old-length map (`walOldsRes` in `walTailsRes`, `walOldFrag`, minted by `walInvBody_tailW`) is in on `wal-tc13`, not merged: the window's fdatasync (`syncLayW`) shortens `old` with the cuts unchanged, so the length is not fixed per key, and `tg ≤ hi` cannot be persistent; the growth supplies and `ZeroToEnd.specWalTail` wait on the coordinator's choice among (d) lending the tail record, (c) supply premises, (a') `old` kept long (`wal-tc13`; W1 log, twenty-third session; I3b, `wal-tc13` entry). Option (d) is in instead: the map removed, the lent tails (`walLentRes` in `walTailsRes`, `walLentTok`, `walTailKeyL` in `walInvBody_tailW` and `walTail_truncSup`, `walInv_lend`/`walInv_unlend`); the weaker registration designed, not made; the growth supplies and `ZeroToEnd.specWalTail` not started (`wal-tc14`; W1 log, twenty-fourth session; I3b, `wal-tc14` entry). The registration is made (`walPendTok`, `TailZ0` per tail, `ZerosOk`/`IdleZ0` in `walLentRes`, `walTailsRes_registerPend`, `walLentRes_unpend`); `ZeroToEnd`'s truncate from a registered, not yet zeroed tail is **blocked**: the truncate's crash step needs F-Z of the exact tail (a crashed tail's bytes past `z0` mixed with the truncate's zeros are not covered by W1), coordinator's choice; growth supplies and `ZeroToEnd.specWalTail` not started (`wal-tc15`; W1 log, twenty-fifth session; I3b, `wal-tc15` entry). Option (i): the pending tail's crash step is proved (`crashOkA_tailPend`, `TailCrashPend.lean`: the length word at `wr` zero, `TailPend`, any tail step); the pending supplies are blocked on two findings, the in-flight layout's `WinZero` and no channel for `LenZ` into the invariant (both with proposed fixes, coordinator's choice); tasks 2-4 not started (`wal-tc16`; W1 log, twenty-sixth session; I3b, `wal-tc16` entry). Fixes A (`WinLast`'s `WinZero` given F-Z) and B (`walLentRes_pendStop`, a lent tail F-Z or `TailPend`) are in, and the resize steps' pure forms no longer need F-Z; `walTailP`/`TailMetaR`/`TailMetaZ` and the restated registration law (`walInvRegisterPendLaw`) are in, its proof blocked on two invariant gaps (an unregistered tail's `maps = ∅` and `TailBound`; proposed: `TailIdle` gains `so = wr` and `TailMaps`); `ZeroToEnd.specWalTail` not started (`wal-tc17`; W1 log, twenty-seventh session; I3b, `wal-tc17` entry). Findings C and D fixed (`TailIdle` gains `so = wr` and `TailMaps`; `TailIdle.bound`), the registration law proved (`walInvRegisterPendLaw_holds`) and folded with `ReadAll`'s commit (`walInv_readCommitReg`, one invariant opening); the truncate supply at `wr` from a pending tail in (`rzStart_pureP`); `fallocSup`, the growing truncate's supply, `ZeroToEnd.specWalTail`, the pending-form fdatasync not done (`wal-tc18`; W1 log, twenty-eighth session; I3b, `wal-tc18` entry).
The resize stamps reach the WAL's crash condition (`OsMeta.rz`, `MetaOk.rz`, `OsCoh.tok_rz`; `CrashOk` passes `segRzOf`) and `W1G.drop_rz` transports W1 across a truncate's zeros (`wal-tc5`; W1 log, fifteenth session). `W1G` is over the known candidates past the bytes (`segBytesX`, the crash take exporting `om.pc`'s candidates), and the truncate window's pure `CrashOk` from an exact tail is proved (`crashOkA_win`, over `crashTo_tailL`) (`wal-tc6`; W1 log, sixteenth session); the landing step (`crashOkA` from the in-flight layout to the landed one), the window-to-window form (a `Save`'s window before the truncate), the WAL-level supplies, `specWalTail` and the `ZeroToEnd` instance remain (I3b, `wal-tc6` entry). A write in flight past the size is in the layout (`wrMeta`) and the crash take; `saveEntry`/`saveState` proved over `encode.specTail`; the writer past the size waits on known zeros past the size (lost by `OsMeta.synced`), the window's size fact and `TailWin`'s past-size clause (`wal-save15`; W6 log, fifteenth session). The known zeros past the size survive a sync: the extension's `MetaOk.zc` and `pwCz` (a complete write up to the zeros known raises `cz`), the tail's `TailZ` in `TailMeta`/`TailMetaW` (`ZeroPg` on the pipeline's files; `filePipeline.alloc`'s `ZeroPg` a `sorry` pending `trFile`/`preGrown` posts; `Create`/`ReadAll`/`specWalTail` obligations); finding 2 restated (false of `ZeroToEnd`'s window), finding 3 not added; bboltfs's `DB.init`/`initCrash` exact `cz` to repair (`wal-save16`; W6 log, sixteenth session). Minibolt's `DB.init`/`initCrash` repaired (posts' `cz` `pwCz m 0 16384 16384`; `WReach.cz_done`; `WriteAt.specCrashS` says `nn = |data|`; ledger); `alloc`'s `ZeroPg` is not provable from strengthened `trFile`/`preGrown` posts alone (a `fallocate` to an unaligned or partly landed size leaves `cz` behind the zeros it announces, and the leftover `N.tmp`'s `O_TRUNC` gives no zeros fact): an extension change proposed (`rsCz` for a `fallocate` landing); finding 3's clause, as proposed, false of `ZeroToEnd`'s window (torn bytes past `z0`, durable): amended design (stamp-0 candidates are `old`'s bytes, and the window's bytes in `[wr, |bs|)` constrained too), not implemented (`wal-save17`; W6 log, seventeenth session). `alloc`'s `ZeroPg` proved: the extension's `MetaOk.ce` (the page cache zero past the size's last page) lets a landed resize raise `cz` (`rsCz`); `preGrown` takes a condition `Z` (`ZeroPg` on success), `trFile` carries `ZfGe ∧ (P → ZeroPg)` (ledger); the amended `TailWin` not started (`wal-save18`; W6 log, eighteenth session). The amended `TailWin` is in (`WinCands` over `segBytesX`, `TailLast.win` over `SegExact`), finding 2 as `WalAbsD.last`'s `WinZero` (bytes from `wr` on zero in a window), and the window's fdatasync's static relation (`syncLayW`, `walAbsD_syncW`); its crash half (`crashOk_syncW`, designed), the writer past the size, `encode.specTail` and `sync` not started (`wal-save19`; W6 log, nineteenth session). The window's fdatasync proved through the invariant step (`crashOk_syncW`, `walsOk_syncW`/`dirKeysOk_syncW`, `syncLay_any`; `walInvBody_sync`, `wp_tailFsync` and `syscall.Fdatasync.wp_tail` no longer need `SegExact`, `fileutil.Fdatasync.wp_tailW`); the writer past the size is blocked on two invariant facts (`winLo` is false of a write past the size from an exact tail; the candidates past `hi` are unconstrained), designed, not made; `sync` not started (`wal-save20`; W6 log, twentieth session). A window's `|old| ≤ hi` is in the invariant (`WinLast`, `WalAbsD.oldHi_any`) and `wal-tc13`'s old-length map merged (the window's fdatasync takes its element, `walOldOpt`: `ZeroToEnd`'s flow has it, `cut`'s does not); `winLo` stays, since the truncate at `wr` needs it of the crash size (finding B: a handle-level fact with a predicate on `os.truncSup`'s meta recommended), `WinHead` derived; `PastCands` is false of a crash's tail and goes on the handle (`PastZ`); the writer past the size, task 2 and `sync` not started (`wal-save21`; W6 log, twenty-first session). Option (A) made (`os.truncSup`'s `P`, `walTailW`'s `LoWr`), `winLo` replaced by `WinHead` in the invariant, `PastZ` in `TailMeta`/`TailMetaW` (with `os.ftDoneH`'s `TcFrom`; ledger); the pipeline's `PastZ` obligation moot (tails enter after an fdatasync); the writer past the size, `encode.specTail` and `sync` not started (`wal-save22`; W6 log, twenty-second session). `PastZ.winShape` (task 1); the decoding over abstract read facts (`tail_decodeV`), `TailShape`, `crashTo_tailW` and `crashOkA_tailAny`/`crashOkW_tailW`: any tail step's crash condition from the two layouts' static relations; `WinLo` (a window's `lo` past `so`, `z0`) in `WinLast`; the writer's steps (`walAbsD_announceW`, the Iris steps, `wal.tailWriterW`), `encode.specTail` and `sync` not started (`wal-save23`; W6 log, twenty-third session). A window's bytes written past a resize cannot have `ByteOk` (`cut`'s flush after its truncate: the truncate's zero past the size), and a write past the size makes the tail longer than `old`: internal invariant change (`TailWin`'s `ByteOk` below `lo`, not `wr`; `WinLast`'s new `WinLow`, the bytes from `lo` to `wr` `WinW`; `TailWin`'s `|bs| ≤ |old|` now `z0 ≤ |old|`; `syncLayW` pads `old`); `walAbsD_announceW` (`segAnnW`) and `segFinW`'s bytes proved, `walAbsD_finishW`, the Iris steps, `encode.specTail` and `sync` not started (`wal-save24`; W6 log, twenty-fourth session). The writer past the size proved: `walAbsD_finishW` (`segFinW_candsX`: the finish keeps `segBytesX`'s candidates), the handle's facts between a `WriteAt`'s attempts `TailMetaL`/`TailZE` (finding: `TailZ` fails after a short write past the zeros known), `wp_tailPWriteStartW`/`wp_tailPWriteFinishW` (`tailCrashStep_any`), `wp_tailWriteAtW`, `wal.tailWriterW` (`tailOkW`, `walTailWS`), `encoder.encode.wp_proofTail` and `WAL.sync.wp_proof` (no `sorry`); `specCut`, `specC` and dropping `sync`'s and `specTail`'s hypotheses from `cut`/`Close`/`Save`/`SaveSnapshot`/`saveEntry`/`saveState` not started (`wal-save25`; W6 log, twenty-fifth session). `specCut`, `specC` proved from one core with `sync.wp_proof` (`wp_core`, the window's fdatasync giving `TailMetaS`), and the WAL's `Link.lean` (`etc/gen-link.py --walfs`, 179 results; 8 axioms, 3 `sorry`s; section 8, "Links") (`wal-save26`; W6 log, twenty-sixth session).
The resize stamps reach the WAL's crash condition (`OsMeta.rz`, `MetaOk.rz`, `OsCoh.tok_rz`; `CrashOk` passes `segRzOf`) and `W1G.drop_rz` transports W1 across a truncate's zeros (`wal-tc5`; W1 log, fifteenth session). `W1G` is over the known candidates past the bytes (`segBytesX`, the crash take exporting `om.pc`'s candidates), and the truncate window's pure `CrashOk` from an exact tail is proved (`crashOkA_win`, over `crashTo_tailL`) (`wal-tc6`; W1 log, sixteenth session); the window-to-window form (`crashOkA_rzStart`, over the invariant's new `WalAbsD.winLo` and the extension's `OsMeta.TcZ`/`0 < n` at the start's commit) and the landing's facts (`rzLand`, `segBytesX_rzLand`) are proved (`wal-tc7`; W1 log, seventeenth session); the WAL-level supplies, `specWalTail` and the `ZeroToEnd` instance remain (I3b, `wal-tc7` entry). The start's `zf ≥ size` is in the commit's `OsMeta.TcZ`, the landing's static relation and crash condition and the invariant's transports over any crash step are proved (`walAbsD_rzLand`, `crashOkA_rzLand`, `walsOk_tailA`/`dirKeysOk_tailA`, `tailCrashStep_rzStart`/`_rzLand`); the not-landed outcome needs the extension's `rsUndone` to keep the stamp and the candidates past the size (`rsUndoneK`, designed); `truncSup`, `specWalTail`, growth and `ZeroToEnd`'s instance not started (`wal-tc8`; W1 log, eighteenth session; I3b, `wal-tc8` entry). `rsUndoneK` is in (a not-landed truncate's `OsMeta` keeps the candidates past the size and the stamp, `rsUnMeta`; `os.ftUndoneH` up to `tc`/`rz`); `specWalTail`'s `TailZ` post needs `os.ftDoneH`/`ftUndoneH` to carry a domain fact on their `tc` (`TcKnows`, proposed); `truncSup`, growth and `ZeroToEnd`'s instance not started (`wal-tc9`; W1 log, nineteenth session; I3b, `wal-tc9` entry). `TcKnows` is on `os.ftDoneH`/`ftUndoneH` (ledger); the truncate supply at the write position (`walTail_truncSup`) and `os.File.Truncate.specWalTail` are proved, `WAL.cut.wp_proof` no longer takes the latter; growth (`fallocSup`, the growing truncate) and `ZeroToEnd`'s instance not started (`wal-tc10`; W1 log, twentieth session; I3b, `wal-tc10` entry). The growth's pure pieces are proved (`RzGrow.lean`: the first step `rzSeg … tr tg` with `size ≤ tg ≤ hi`, `crashOkA_rzGrow`/`tailCrashStep_rzGrow`/`rzGrow_pure`; the landing `rzLandG`, `crashOkA_rzLandG`/`walAbsD_rzLandG`/`rzLandG_pure`, given that the bytes grown over have the candidates the `OsMeta` knew, `hzs`) and `fallocDoneH` carries `TcKnowsF` (ledger); the supplies (`fallocSup`, the growing truncate's) wait on three extension facts (`fallocate`'s start: `0 < n ∧ m.TcZ`; its not-landed outcome: `rsUndoneK`; `rsDoneK`'s `zs`: the `OsMeta`'s known candidates), and `ZeroToEnd`'s instance (`ZeroToEnd.specWalTail`, named) on them and on `ZteMeta` (ledger, proposed) (`wal-tc11`; W1 log, twenty-first session; I3b, `wal-tc11` entry). The three extension facts are in (`wp_osFallocStart`'s `0 < n ∧ m.TcZ`, `fallocAuW`'s commit; `rsOutF`'s undone arm `rsUndoneK m.cut.isNone false`, `fallocOutH`'s up to `tc`/`rz` with `TcKnowsF`; `rsDoneK`'s `zs` the `OsMeta`'s known candidates), `preGrownH i m w Z` carries `PcKeep` and `Z → ZeroPg`, `ZeroToEnd.specAu`'s post `ZteMeta` (ledger, adopted); the WAL's growth supplies are **blocked on an invariant fact**: at their commits they need the target `tg` (the size `ZeroToEnd` found) `≤ |lay.old|` and `≤ g.om.hi`, which neither the tie nor the state found gives (`wal-tc12`; W1 log, twenty-second session; I3b, `wal-tc12` entry). The tails' old-length map (`walOldsRes` in `walTailsRes`, `walOldFrag`, minted by `walInvBody_tailW`) is in on `wal-tc13`, not merged: the window's fdatasync (`syncLayW`) shortens `old` with the cuts unchanged, so the length is not fixed per key, and `tg ≤ hi` cannot be persistent; the growth supplies and `ZeroToEnd.specWalTail` wait on the coordinator's choice among (d) lending the tail record, (c) supply premises, (a') `old` kept long (`wal-tc13`; W1 log, twenty-third session; I3b, `wal-tc13` entry). Option (d) is in instead: the map removed, the lent tails (`walLentRes` in `walTailsRes`, `walLentTok`, `walTailKeyL` in `walInvBody_tailW` and `walTail_truncSup`, `walInv_lend`/`walInv_unlend`); the weaker registration designed, not made; the growth supplies and `ZeroToEnd.specWalTail` not started (`wal-tc14`; W1 log, twenty-fourth session; I3b, `wal-tc14` entry). The registration is made (`walPendTok`, `TailZ0` per tail, `ZerosOk`/`IdleZ0` in `walLentRes`, `walTailsRes_registerPend`, `walLentRes_unpend`); `ZeroToEnd`'s truncate from a registered, not yet zeroed tail is **blocked**: the truncate's crash step needs F-Z of the exact tail (a crashed tail's bytes past `z0` mixed with the truncate's zeros are not covered by W1), coordinator's choice; growth supplies and `ZeroToEnd.specWalTail` not started (`wal-tc15`; W1 log, twenty-fifth session; I3b, `wal-tc15` entry). Option (i): the pending tail's crash step is proved (`crashOkA_tailPend`, `TailCrashPend.lean`: the length word at `wr` zero, `TailPend`, any tail step); the pending supplies are blocked on two findings, the in-flight layout's `WinZero` and no channel for `LenZ` into the invariant (both with proposed fixes, coordinator's choice); tasks 2-4 not started (`wal-tc16`; W1 log, twenty-sixth session; I3b, `wal-tc16` entry). Fixes A (`WinLast`'s `WinZero` given F-Z) and B (`walLentRes_pendStop`, a lent tail F-Z or `TailPend`) are in, and the resize steps' pure forms no longer need F-Z; `walTailP`/`TailMetaR`/`TailMetaZ` and the restated registration law (`walInvRegisterPendLaw`) are in, its proof blocked on two invariant gaps (an unregistered tail's `maps = ∅` and `TailBound`; proposed: `TailIdle` gains `so = wr` and `TailMaps`); `ZeroToEnd.specWalTail` not started (`wal-tc17`; W1 log, twenty-seventh session; I3b, `wal-tc17` entry). Findings C and D fixed (`TailIdle` gains `so = wr` and `TailMaps`; `TailIdle.bound`), the registration law proved (`walInvRegisterPendLaw_holds`) and folded with `ReadAll`'s commit (`walInv_readCommitReg`, one invariant opening); the truncate supply at `wr` from a pending tail in (`rzStart_pureP`); `fallocSup`, the growing truncate's supply, `ZeroToEnd.specWalTail`, the pending-form fdatasync not done (`wal-tc18`; W1 log, twenty-eighth session; I3b, `wal-tc18` entry). The growth supplies (`walTail_fallocSup`, `walTail_truncSupG`; the supplies' `P` generalized, ledger) and `ZeroToEnd.specWalTail` are proved (`ZeroToEnd.wp_specWalTail`, over `ZeroToEnd.specAu`; `TailMetaZ` the cache fact, `isPkgInit errors` in its pre); the pending-form fdatasync (`Fdatasync.specWalPend`) designed, not proved (`wal-tc19`; W1 log, twenty-ninth session; I3b, `wal-tc19` entry). The pending-form fdatasync is proved (`Fdatasync.wp_specWalPend`, over `walInvBody_syncP`: the lent token turned into the key at the sync's commit, the synced layout's F-Z by `syncLay_anyP`; the sync's `zf ≥ size` from the state, `Fs.wp_osMeta_zfGe`); `ReadAll`'s two tail callees are proved, its hypotheses for the `Link` (`wal-tc20`; W1 log, thirtieth session; I3b, `wal-tc20` entry).
The resize stamps reach the WAL's crash condition (`OsMeta.rz`, `MetaOk.rz`, `OsCoh.tok_rz`; `CrashOk` passes `segRzOf`) and `W1G.drop_rz` transports W1 across a truncate's zeros (`wal-tc5`; W1 log, fifteenth session). `W1G` is over the known candidates past the bytes (`segBytesX`, the crash take exporting `om.pc`'s candidates), and the truncate window's pure `CrashOk` from an exact tail is proved (`crashOkA_win`, over `crashTo_tailL`) (`wal-tc6`; W1 log, sixteenth session); the landing step (`crashOkA` from the in-flight layout to the landed one), the window-to-window form (a `Save`'s window before the truncate), the WAL-level supplies, `specWalTail` and the `ZeroToEnd` instance remain (I3b, `wal-tc6` entry). A write in flight past the size is in the layout (`wrMeta`) and the crash take; `saveEntry`/`saveState` proved over `encode.specTail`; the writer past the size waits on known zeros past the size (lost by `OsMeta.synced`), the window's size fact and `TailWin`'s past-size clause (`wal-save15`; W6 log, fifteenth session). The known zeros past the size survive a sync: the extension's `MetaOk.zc` and `pwCz` (a complete write up to the zeros known raises `cz`), the tail's `TailZ` in `TailMeta`/`TailMetaW` (`ZeroPg` on the pipeline's files; `filePipeline.alloc`'s `ZeroPg` a `sorry` pending `trFile`/`preGrown` posts; `Create`/`ReadAll`/`specWalTail` obligations); finding 2 restated (false of `ZeroToEnd`'s window), finding 3 not added; bboltfs's `DB.init`/`initCrash` exact `cz` to repair (`wal-save16`; W6 log, sixteenth session). Minibolt's `DB.init`/`initCrash` repaired (posts' `cz` `pwCz m 0 16384 16384`; `WReach.cz_done`; `WriteAt.specCrashS` says `nn = |data|`; ledger); `alloc`'s `ZeroPg` is not provable from strengthened `trFile`/`preGrown` posts alone (a `fallocate` to an unaligned or partly landed size leaves `cz` behind the zeros it announces, and the leftover `N.tmp`'s `O_TRUNC` gives no zeros fact): an extension change proposed (`rsCz` for a `fallocate` landing); finding 3's clause, as proposed, false of `ZeroToEnd`'s window (torn bytes past `z0`, durable): amended design (stamp-0 candidates are `old`'s bytes, and the window's bytes in `[wr, |bs|)` constrained too), not implemented (`wal-save17`; W6 log, seventeenth session). `alloc`'s `ZeroPg` proved: the extension's `MetaOk.ce` (the page cache zero past the size's last page) lets a landed resize raise `cz` (`rsCz`); `preGrown` takes a condition `Z` (`ZeroPg` on success), `trFile` carries `ZfGe ∧ (P → ZeroPg)` (ledger); the amended `TailWin` not started (`wal-save18`; W6 log, eighteenth session). The amended `TailWin` is in (`WinCands` over `segBytesX`, `TailLast.win` over `SegExact`), finding 2 as `WalAbsD.last`'s `WinZero` (bytes from `wr` on zero in a window), and the window's fdatasync's static relation (`syncLayW`, `walAbsD_syncW`); its crash half (`crashOk_syncW`, designed), the writer past the size, `encode.specTail` and `sync` not started (`wal-save19`; W6 log, nineteenth session). The window's fdatasync proved through the invariant step (`crashOk_syncW`, `walsOk_syncW`/`dirKeysOk_syncW`, `syncLay_any`; `walInvBody_sync`, `wp_tailFsync` and `syscall.Fdatasync.wp_tail` no longer need `SegExact`, `fileutil.Fdatasync.wp_tailW`); the writer past the size is blocked on two invariant facts (`winLo` is false of a write past the size from an exact tail; the candidates past `hi` are unconstrained), designed, not made; `sync` not started (`wal-save20`; W6 log, twentieth session). A window's `|old| ≤ hi` is in the invariant (`WinLast`, `WalAbsD.oldHi_any`) and `wal-tc13`'s old-length map merged (the window's fdatasync takes its element, `walOldOpt`: `ZeroToEnd`'s flow has it, `cut`'s does not); `winLo` stays, since the truncate at `wr` needs it of the crash size (finding B: a handle-level fact with a predicate on `os.truncSup`'s meta recommended), `WinHead` derived; `PastCands` is false of a crash's tail and goes on the handle (`PastZ`); the writer past the size, task 2 and `sync` not started (`wal-save21`; W6 log, twenty-first session). Option (A) made (`os.truncSup`'s `P`, `walTailW`'s `LoWr`), `winLo` replaced by `WinHead` in the invariant, `PastZ` in `TailMeta`/`TailMetaW` (with `os.ftDoneH`'s `TcFrom`; ledger); the pipeline's `PastZ` obligation moot (tails enter after an fdatasync); the writer past the size, `encode.specTail` and `sync` not started (`wal-save22`; W6 log, twenty-second session). `PastZ.winShape` (task 1); the decoding over abstract read facts (`tail_decodeV`), `TailShape`, `crashTo_tailW` and `crashOkA_tailAny`/`crashOkW_tailW`: any tail step's crash condition from the two layouts' static relations; `WinLo` (a window's `lo` past `so`, `z0`) in `WinLast`; the writer's steps (`walAbsD_announceW`, the Iris steps, `wal.tailWriterW`), `encode.specTail` and `sync` not started (`wal-save23`; W6 log, twenty-third session). A window's bytes written past a resize cannot have `ByteOk` (`cut`'s flush after its truncate: the truncate's zero past the size), and a write past the size makes the tail longer than `old`: internal invariant change (`TailWin`'s `ByteOk` below `lo`, not `wr`; `WinLast`'s new `WinLow`, the bytes from `lo` to `wr` `WinW`; `TailWin`'s `|bs| ≤ |old|` now `z0 ≤ |old|`; `syncLayW` pads `old`); `walAbsD_announceW` (`segAnnW`) and `segFinW`'s bytes proved, `walAbsD_finishW`, the Iris steps, `encode.specTail` and `sync` not started (`wal-save24`; W6 log, twenty-fourth session).
The resize stamps reach the WAL's crash condition (`OsMeta.rz`, `MetaOk.rz`, `OsCoh.tok_rz`; `CrashOk` passes `segRzOf`) and `W1G.drop_rz` transports W1 across a truncate's zeros (`wal-tc5`; W1 log, fifteenth session). `W1G` is over the known candidates past the bytes (`segBytesX`, the crash take exporting `om.pc`'s candidates), and the truncate window's pure `CrashOk` from an exact tail is proved (`crashOkA_win`, over `crashTo_tailL`) (`wal-tc6`; W1 log, sixteenth session); the window-to-window form (`crashOkA_rzStart`, over the invariant's new `WalAbsD.winLo` and the extension's `OsMeta.TcZ`/`0 < n` at the start's commit) and the landing's facts (`rzLand`, `segBytesX_rzLand`) are proved (`wal-tc7`; W1 log, seventeenth session); the WAL-level supplies, `specWalTail` and the `ZeroToEnd` instance remain (I3b, `wal-tc7` entry).

### Inventory (2026-11-14, integration, refreshed on `wal-int4`)

Branch `wal-int4` (from `wal-int` `5c98a6197a`, `wal-save22` merged): every `LinuxFs` and `GooseLang/Ext/Fs`
target builds (3215 jobs, no failure, nothing to fix); `etc/gen-part-copies.py --check`, `etc/gen-init.py --check` and `etc/goose.py
--check` for projects `bboltfs`, `crashlog`, `walfs` pass. Scripted from the source (the theorems
`*.wp_proof*` under `S/` and `fileutil/`: their binders; a callee spec counts as proved when some `theorem` or
`axiom` of this repository or Perennial has it as its type). The WAL is in no linked root yet. Paths: `S/` =
`LinuxFs/Proof/go_etcd_io/etcd/server/v3/storage/wal/`, `Sp/` = `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/`.

**`sorry`s (4 declarations, 6 `sorry`s; source lines)**
- `S/Create.lean:780`, `:782`, `:785` (`wal.Create.wp_proof`, :95): three of `renameWALPost`'s four arms
  (committed with `w` returned; committed with a reopened WAL; not committed); the committed-error arm is proved.
- `S/WAL__ReadAll.lean:300` (`WAL.ReadAll.wp_proof`, :140): the loop's EOF stop and what follows it.
- `S/WAL__sync.lean:210` (`WAL.sync.wp_proof`, :208): whole proof (writes past the tail's size).
- `LinuxFs/Proof/os/WriteLong.lean:56` (`os.File.WriteAt.wp_proof_long`, :41): writes past 1 GiB.
- `S/filePipeline__alloc.lean`: none now (was :137). `fileutil/`: none.
- (Not counted: `LinuxFs/GeneratedProof/os.lean:182-205`, generated instances of axiomatized types.)

**Non-callee premises of the `wp_proof`s (laws and supplies; 16 binders, 12 distinct)**
- `S/WAL__ReadAll.lean:142` `hU : U.Ok Mr`; `:143` `hHs : WalHsOwn P U HsO` (`Sp/ReadAllCallees.lean`).
- `S/WAL__ReadAll.lean` `hUs : U.SnapCoh` (`wal-leaf4`; `MustUnmarshalMessage.specWalSnap`'s premise).
- `S/WAL__ReadAll.lean:155` `WalPbIn.UnmarshalEntLaw`; `:157` `GetTermLaw`; `:158` `CloneHsLaw`.
- `WalPbIn.GetIndexLaw`: `S/WAL__ReadAll.lean:156`, `S/WAL__saveEntry.lean:34`.
- `WalPbIn.IsEmptyLaw` (`Sp/WAL__cutPre.lean:80`): `S/WAL__Save.lean:115`, `S/WAL__cutPre.lean:57`,
  `S/WAL__saveState.lean:35`.
- `S/WAL__Save.lean:116` `WalPbIn.MustSyncLaw`; `:117` `WalPbIn.ZeroLaw`.
- `WalPbIn.MarshalHsLaw`: `S/WAL__cutPre.lean:58`, `S/WAL__saveState.lean:35`.
- `S/WAL__saveEntry.lean:34` `WalPbIn.MarshalEntLaw`.
- `S/openAtIndex.lean:207` `hEnv : WalDecEnvSupply` (the decoder's environment; `errors.newVar`'s allocation
  identity, a Perennial gap).
- (Parameters `P`, `Mr`, `U`, `C : WalCodec`, and the generated `[…Assumptions]` instances are not listed.)

**Callee specs taken as hypotheses with no proof or axiom anywhere (13)**
- WAL's own variants: `WAL.renameWALUnlock.spec` (`S/WAL__renameWAL.lean:69`), `WAL.sync.specC`
  (`S/WAL__Close.lean:59`), `WAL.sync.specCut` (`S/WAL__cut.lean:112`), `encoder.encode.specTail` (3 uses, first
  `S/WAL__SaveSnapshot.lean:55`).
- `fileutil.CreateDirAll.specTmp` (`Sp/CreateCallees.lean`; `S/Create.lean:105`): proved (`wal-leaf5`,
  `CreateDirAll.wp_proofTmp`), over `TouchDirAll.specDir` (proved) and `CheckDirPermission.spec` (proved on
  `wal-leaf5-modeperm`, which translates `io/fs.ModePerm`; until it merges, a hypothesis).
- `os.File.Close.specClosed` (`LinuxFs/Spec/os/File__CloseClosed.lean:38`; `S/Create.lean:111`, `CreateLockedLeft`).
- `pbutil.MustMarshalMessage.specWalSnap`: proved (`wal-leaf3`, over `proto.MarshalPb.spec`; size premise added,
  ledger). `pbutil.MustUnmarshalMessage.specWalSnap`: proved (`wal-leaf4`, over `proto.UnmarshalPb.spec`, premise
  `U.SnapCoh`, which `ReadAll` now takes).
- Standard library / protobuf: `errors.AsLinkError.spec` (`S/WAL__renameWAL.lean:68`), `errors.IsErrno.spec`
  (`fileutil/TryLockFile.lean:300`), `errors.IsPathErrnoEof.spec` (`S/openAtIndex.lean:208`, `OpenFiles`),
  `fmt.ErrorfErrsNot.spec` (`S/decoder__decodeRecord.lean:47`), `proto.UnmarshalWalRecordE.spec`
  (`S/decoder__decodeRecord.lean:43`).
- Against the previous inventory's 10 left: the same 10, plus 3 the earlier count missed (the two `pbutil`
  `specWalSnap`s and `os.File.Close.specClosed`). The four `errors`/`fmt` leaves are unprovable from
  Perennial's present facts (the `wal-leaf2` log below).

### Links (2026-11-14, branches `wal-save26`, `wal-leaf6`)

**`LinuxFs/Proof/go_etcd_io/etcd/server/v3/storage/wal/Link.lean`**, generated by **`etc/gen-link.py --walfs`**
(`etc/link_walfs.py`; `--walfs --check` compares, and `etc/gates.sh` checks it with the other Links). As `--bbolt`, no
list file: the callees are read off each proof's binders. A result is generic in the proof's **model parameters** (`P :
WalPbIn GF`, `Mr`, `C`, `U`, `HsO`), a callee's matched against the caller's binder; the **premises** on them (the
client protobuf model's laws `WalPbIn.*Law`, `U.Ok`, `U.SnapCoh`, `WalHsOwn`, `WalDecEnvSupply`) and the **specs with no
proof in the part** are explicit hypotheses `h_<name>` of each result that reaches them (`section links_pending`); a
spec proved twice is linked by its `wp_proof<S>`. Roots: every proof under `S/` (with `walpb/`) and `fileutil/`, and the
part's proofs they reach (`os`, `syscall`, `ioutil`, `crc`, `filepath`, `bufio`, `proto`, ...), in namespace
`EtcdGrove.walfs`.

**195 results**, 169 with no hypothesis (2026-11-14, `wal-leaf6`; were 179 and 120 at `wal-save26`). Every WAL
`wp_proof` is linked (none rejected), including `cut` over `wp_proofCut`, `Close` over `wp_proofC`,
`Save`/`SaveSnapshot`/`saveEntry`/`saveState` over `encode.wp_proofTail`, `ReadAll` over `Fdatasync.wp_specWalPend`
and `ZeroToEnd.wp_specWalTail (wp_proofAu …)`, `Create` over `os.File.Close.wp_proofClosed` and
`Exist.wp_specCreate`, `pbutil`'s two `specWalSnap` proofs.

**What they rest on** (`etc/tcb-report.py --roots '^LinuxFs/Proof/go_etcd_io/etcd/server/v3/storage/wal/'`; collection
**`etc/tcb-collections/wal-fsext.txt`**, baseline 23 axioms, 3 `sorry`s; computed by running `etc/tcb-report.lean
--part=LinuxFs` on the Link alone, the rest of the repository's roots not being built here):
- *Axioms* (23, none new): the part's own trust boundaries `proto.{MarshalPb,SizePb,UnmarshalPb,
  MarshalAppendCachedRecord}.wp_proof`, walpb's `recEncC_ok`, `snapEncC_ok`, `pbRecordC_reg`, `pbSnapC_reg`; and,
  since `wal-leaf6`, **generated copies of fifteen main-tree trust-boundary axioms** (`etc/gen-part-copies.py`, the
  main `Proof/<pkg>/<F>.lean` word for word, its spec import pointed at the part's copy where there is one, as
  `proto.MarshalPb`'s): zap's `Duration`, `Error`, `Int64`, `String`, `Logger.{Warn,Error,Info}`,
  `time.Duration.Seconds{,_ptr}`, `proto.ClonePb`, `strings.HasSuffix`, `fmt.{SprintfWalName,SscanfWalName}`,
  `io.ReadFull`, `binary.ReadInt64LE`. The same statements as the main tree's (the same names); the last four were
  not in `etc/tcb-baseline.txt` (no main-tree result reached them) and are added there; `io.ReadFull`'s,
  `binary.ReadInt64LE`'s and `fmt`'s two are pending the user's review in the main tree already
  (`notes/perennial-changes.md`).
- *`sorry`s* (3): `WAL.ReadAll.wp_proof` (reached by `wp_ReadAll`), `wal.Create.wp_proof` (`wp_Create`),
  `os.File.WriteAt.wp_proof_long` (`wp_WriteAtLong`, `wp_cut`, `wp_Save`, `wp_Create`). 190 of 195 results reach none.
- *Hypotheses* (specs with no proof in the part; count of results taking each in the Link's header):
  `filepathlite.IsAbs` (6: `stringslite.HasPrefix` has no body in Perennial; `filepathlite.Dir` is proved since
  `wal-leaf6`), `errors.{AsLinkError,IsErrno,IsPathErrnoEof,IsPathErrnoNotExist}`, `fmt.ErrorfErrsNot` (Perennial's
  `errors`/`fmt` facts and specs, leaf logs `wal-leaf1`/`wal-leaf2`), `proto.UnmarshalWalRecordE` (extends a trust
  boundary: the user's call); the WAL's own `WAL.renameWALUnlock.spec` and `fileutil.CreateDirAll.specTmp` (false as
  stated, ledger). Premises: the `WalPbIn` laws, `U.Ok`, `U.SnapCoh`, `WalHsOwn`, `WalDecEnvSupply`. Semantic premise
  class: `[UntypedRuneSemantics]` (a section instance, from `filepath`).

## Leaf specs log (branch `wal-leaf6`, 2026-11-14)

The Link's standard-library hypotheses (task decided by the coordinator). Merged `wal-int` `1801a73d71` (the Link regenerated, built, the collection unchanged).

**Copied axioms (existing main-tree trust boundaries, not new axioms).** `etc/gen-part-copies.py` now copies the main
tree's proof files `Proof/go_uber_org/zap/{Logger__Warn,Logger__Info,Logger__Error,Duration,String,Error,Int64}`,
`Proof/time/Duration__Seconds{,_ptr}`, `Proof/google_golang_org/protobuf/proto/ClonePb`, `Proof/strings/HasSuffix`,
`Proof/fmt/{SprintfWalName,SscanfWalName}`, `Proof/io/ReadFull`, `Proof/encoding/binary/ReadInt64LE` to `LinuxFs/`
(`Whole`, as `proto.MarshalPb`'s: each a single `axiom <F>.wp_proof : <F>.spec`, the import of its spec pointed at the
part's copy where the part has one, else the main spec the part's proofs already import). The link generator links only
the part's proofs, hence copies rather than imports of the main modules. Each axiom states exactly what the main
tree's does; they are in `etc/tcb-collections/wal-fsext.txt`, and the four the main tree's results did not reach
(`fmt.{SprintfWalName,SscanfWalName}`, `io.ReadFull`, `binary.ReadInt64LE`) are added to `etc/tcb-baseline.txt`.

**Proved.** `filepathlite.Dir.spec` (`LinuxFs/Proof/internal/filepathlite/Dir.lean`, over `VolumeName`,
`IsPathSeparator`, `Clean`: the volume name empty, the scan back to the last `/` as `Base`'s, `Clean` of
`p[:i+1]`, the `dir == "." && len(vol) > 2` branch dead; `path.dirModel`).

**Not proved, and what is missing** (all Perennial changes; `notes/perennial-changes.md`):
- `filepathlite.IsAbs.spec`: `IsAbs` is `stringslite.HasPrefix(p, "/")`, and Perennial's `internal/stringslite`
  translates nothing but `Clone`; the part cannot translate it (it would declare Perennial's names). Entry
  "`internal/stringslite.HasPrefix`/`HasSuffix` and `strings.HasSuffix` without bodies" (new). No axiom: still a
  hypothesis.
- `strings.HasSuffix.spec` (now on its copied axiom): `strings.HasSuffix` names-only in Perennial (same entry).
- `fmt.SprintfWalName.spec`, `fmt.SscanfWalName.spec` (copied axioms): Perennial's `Sprintf` model accepts a width
  only before `d` (`%016x` unmodelled), `Sscanf` names-only (entry "`Sprintf`'s `%0Nx`, ...", status added).
- `io.ReadFull.spec`, `binary.ReadInt64LE.spec` (copied axioms): `ReadFull`/`ReadAtLeast` and `binary.Read` names-only
  in Perennial (entry "`io.ReadFull`/`ReadAtLeast` and `binary.Read`'s fast path", status added).
- `zap`, `time.Duration.Seconds`, `proto.Clone`: trust boundaries by design (names-only packages), no proof route.

**Build.** Seeded from `agent-a21b088973d4f6ae2`. The seed was inconsistent: 34 modules' traces disagreed with their
`.olean.hash` (a trace rewritten in place through the shared hard link while the seed was building, before the traces
were unshared), so Lake replayed stale `.olean`s (`readInt64.spec` with a `Prop`-valued `E`) and eight unrelated WAL
proofs failed. Found by comparing each trace's recorded `o` hash with the `.olean.hash` beside it; deleting those 34
traces (after unsharing their outputs) fixed it. Worth doing after any `cp -al` seed. Then `Link` (3050 jobs).
  `os.File.WriteAt.wp_proof_long` (`wp_WriteAtLong`, `wp_cut`, `wp_Save`, `wp_Create`). 174 of 179 results reach none.
- *Hypotheses* (specs with no proof in the part; count of results taking each in the Link's header): zap's
  `Duration`, `Error`, `Int64`, `String`, `Logger.{Warn,Error,Info}` and `time.Duration.Seconds{,_ptr}` (the part's
  copies of main-tree trust-boundary specs, whose axioms the part cannot import); `strings.HasSuffix`,
  `fmt.{SprintfWalName,SscanfWalName,ErrorfErrsNot}`, `errors.{AsLinkError,IsErrno,IsPathErrnoEof,IsPathErrnoNotExist}`,
  `filepathlite.{Dir,IsAbs}`, `io.ReadFull`, `binary.ReadInt64LE`, `proto.{ClonePb,UnmarshalWalRecordE}`; the WAL's own
  `WAL.renameWALUnlock.spec` and (until `wal-leaf5`) `fileutil.CreateDirAll.specTmp`; since `wal-leaf5`,
  `fileutil.CheckDirPermission.spec` in its place (proved on `wal-leaf5-modeperm`). Premises: the `WalPbIn`
  laws, `U.Ok`, `U.SnapCoh`, `WalHsOwn`, `WalDecEnvSupply`. Semantic premise class: `[UntypedRuneSemantics]` (a section
  instance, from `filepath`).

## Leaf specs log (branch `wal-leaf5`, 2026-11-14)

The three tasks the coordinator decided after `wal-leaf4` (the `.touch` ownership, `CheckDirPermission`,
`CreateDirAll.specTmp`).

**Adopted: a temporary directory's `.touch` file owned** (ledger 2026-11-14, "a leftover `.touch` needs its
file", decision recorded there). In the proposal's "only `.touch`'s" form, not "every file": `tmpSub`'s
directory arm holds `WalFs.tmpEnt (hJ.cur !! .touch)` (`TmpDir.lean`). Every file whole would have made
`Create`'s unminting give the new WAL's first segment back as a `trFile` (`walCreateP` has its `OsMeta` and
bytes, not `trFile`'s facts), for no consumer: the other files are only unlinked (`RemoveAll`, which takes
no file). Threaded through:
- `walAreaRes` (`CreateDefs.lean`): its claims are `areaCls cl` (the claims whole and, per tagged claim,
  `tmpClTouch`: the `.touch` of a whole claim under a WAL name's `nm.tmp`); `area_takeTmp`/`area_give`,
  `walAreaRes_open`/`_close` and the `Create*` lemmas over `areaCls`; `bigSepL_tag_split`, `tmpClTouch_not`
  (`CreateArea.lean`). Callers that only pass the claims along (`Exist`, `openAtIndex`, `openLast`) unchanged.
- `RemoveAll`: `os.RemoveAll.specDirS` unchanged (it unlinks, needs no file); its wrapper
  `rmAllOut_tmpDirH` (`CreateTmp.lean`) gives the file back if `.touch` is still there.
- `TouchDirAll`'s error arms: `IsDirWriteable.spec`'s error post now gives the probe's file back
  (`⌜none⌝ ∨ ∃ i, ⌜file i⌝ ∗ trFile i False`), over `os.WriteFile.specEmptyS`'s new `crTr False o`
  (`os.crTr_false`; `trFile_false` is now `trFile_mono`'s instance). `tmpDirH_dir` takes the `tmpEnt`,
  `tmpDirH_dirE` (an empty directory), `touchOut_tmpEnt` (`TouchDirAll.lean`).
- `Create`'s exits: the directory has no `.touch` (`segClaim_back` and `create_Jback` now say so;
  `create_unmint` takes `hJ.cur !! .touch = none`; `touch_ne_walFileName`).
- The crash rebuild: `osFileStart_trFile` (`S/Crash.lean`): a file a crash kept, once taken from
  `crashRest`, is a `trFile i False` (`initMeta`): what the area's establishment at boot (C6, not written:
  nothing establishes `walAreaRes` from a boot yet) gives of a leftover `nm.tmp/.touch` (and `walTmpsRes` of
  a leftover `N.tmp`). Its premise there: the leftover files' inodes distinct.

**Proved**
- `fileutil.TouchDirAll.specDir` (`LinuxFs/{Spec,Proof}/.../fileutil/TouchDirAllDir.lean`): `TouchDirAll` of a
  name holding a directory of files (`tmpDirH` pre, the claim unchanged on success, `J` files only and
  `.touch` none; error: `tmpDirH`). Both branches of `Exist(d)`: `CheckDirPermission` (logged), `syncDir(parent)`
  over the spine; or the climbing loop (`wp_existAncDir`), `os.MkdirAll.specDirS`, the syncs; then the probe on
  whatever `.touch` holds (`wp_isDirWriteableAny`: `IsDirWriteable.spec` or `specFile`; `wp_touchProbe`).
  Takes `CheckDirPermission.spec`, `zap.Error.spec`, `zap.Logger.Warn.spec` (the part's) as hypotheses.
- `fileutil.CreateDirAll.specTmp` (`fileutil.CreateDirAll.wp_proofTmp`, `.../fileutil/CreateDirAllTmp.lean`):
  absent, `CreateDirAll.spec`; a directory, `specDir` then `ReadDir`, the files found (if any) named by
  `fmt.Errorf("expected %q to be empty, got %q", dir, ns)`.
- `fmt.ErrorfStrs.spec` (`LinuxFs/{Spec,Proof}/fmt/ErrorfStrs.lean`): `Errorf` whose arguments are basic, an
  `io/fs.FileMode` or a `[]string` (a fraction of its contents held), proved over Perennial's `Errorf` model
  (`errors.New(format)`) as `fmt.ErrorfErrs` is; the header says why the model is faithful for these
  arguments (Go formats a `[]string` without methods; `FileMode.String` is total and pure). No new axiom;
  a wider use of the trusted model, for the coordinator's review. The general fix is a Perennial `ArgWf`
  case (`notes/perennial-changes.md`).

**Stated; proved on branch `wal-leaf5-modeperm`**
- `fileutil.CheckDirPermission.spec` (`.../fileutil/CheckDirPermission.lean`): a spine to the directory, any
  `perm`, a fraction of the call permission: no effect, some error. Its proof needs `FileMode.Perm`'s mask
  `io/fs.ModePerm`, which the part's `io/fs` did not translate (`axiom ModePerm : val`, names-only): branch
  `wal-leaf5-modeperm` adds `"ModePerm"` to `LinuxFs/Code/io/fs.toml` (the translation: `axiom` to
  `#(W32 511)`, `etc/goose.py --project bboltfs`) and proves it (`CheckDirPermission.wp_proof`, over `Exist`,
  `os.Stat.wp_dirS`, `fmt.ErrorfStrs.spec`). Kept apart because the generated `LinuxFs/Code/io/fs.lean`
  changes, which rebuilds the whole part (680 modules) for everyone who merges it: the coordinator's call when.

**Statement changes** (internal, the part's): `tmpSub` (the `.touch` file), `walAreaRes` (`areaCls`),
`IsDirWriteable.spec`'s and `os.WriteFile.specEmptyS`'s posts (the probe file back), `segClaim_back`,
`create_Jback`, `create_unmint`'s premise. New: `TouchDirAll.specDir`, `CheckDirPermission.spec`,
`fmt.ErrorfStrs.spec`.

## Leaf specs log (branch `wal-leaf1`, 2026-11-14)

The inventory's leaf callee specs not owned by another agent (`proto.UnmarshalWalRecordE.spec` skipped: it
extends a trust-boundary axiom, the user's call). None of the proofs below is linked yet (the WAL has no
`Link.lean`); each takes its callees' specs as hypotheses, all proved or trust-boundary specs.

**Proved**
- `walpb.Snapshot.GetTerm.spec`: `LinuxFs/Proof/.../wal/walpb/Snapshot__GetTerm.lean`, as `GetIndex`'s.
- `os.RemoveAll.specAbsentN`: `LinuxFs/Proof/os/RemoveAllAbsentN.lean` (`os.RemoveAll.wp_proofAbsentN`).
  `specAbsentS`'s proof over the absent case of `RemoveAllLeaf.lean`'s loops restated for any claim `N ∋ b`
  (`os.model.wp_{unlinkLoop,openLoop,rmdirLoop,removeAllFrom}_absentN`), over two extension steps stated in the
  same file, `Fs.wp_osUnlinkAbsentSN`/`wp_osRmdirAbsentSN` (the extension's `wp_osUnlinkS_none'`/`_none'` for
  `N ∋ b` and an absent name; they belong in `GooseLang/Ext/Fs/TreeSharedCallEnd.lean`, as `SharedExt.lean`'s
  do: moved there when the extension is next edited, to avoid a rebuild of the part now).
- `fmt.ErrorfErrs.spec`: `LinuxFs/Proof/fmt/ErrorfErrs.lean`, over Perennial's model of `Errorf` (`errors.New(format)`)
  and `errors.New.spec`, as Perennial's `fmt.Errorf.wp_proof`. The model is used beyond the arguments its spec
  admits (`ArgsWf`): its only departure there, not calling the arguments' `Error()`, is harmless under the
  premise (`errOk`: each such call returns some string), and the post says no more than Go gives (the file's header).
- `proto.CloneWalSnap.spec`: `LinuxFs/Proof/google_golang_org/protobuf/proto/CloneWalSnap.lean`, over
  `proto.ClonePb.spec` at `pbSnapC` (`pbSnapC_reg`) and `snapOwnC_freeze`/`walCsOwnC_freeze` (a decoded snapshot
  frozen: both levels' hidden fields into the protobuf invariant). `ClonePb.spec`'s part copy is generated
  (`etc/gen-part-copies.py`); its axiom `proto.ClonePb.wp_proof` is **not** copied (no axiom added): the part's
  link will need it, as it has `MarshalPb`'s.

**Not proved**
- `walpb.Record.Reset.spec`: no body to prove it from. `Reset` is names-only in the part (`walpb.toml` excludes
  `*.Reset`: `*x = Record{}` then `protoimpl.X.MessageStateOf(protoimpl.Pointer(x)).StoreMessageInfo(mi)`, unsafe
  protobuf runtime plumbing), so `MethodUnfold … "Reset"` does not exist and the call does not step. Needs a
  translation of `Reset` with a trusted model of the `MessageStateOf`/`StoreMessageInfo` pair (a trust-base
  change: the user's), or an axiom (excluded here).
- `errors.IsErrno.spec`, `errors.IsPathErrnoEof.spec`: `errors.is` walks into `syscall.Errno.Is` (and, for the
  second, `(*fs.PathError).Unwrap`), names-only in the part (`LinuxFs/Code/syscall.toml`, `io/fs.toml`): the method
  calls do not step. Need those translated (`Errno.Is` reads `oserror`'s variables and `errors.ErrUnsupported`, so
  their package facts too) and, for `IsErrno`, Perennial's `errors.is.spec` at a comparable non-pointer target
  (`notes/perennial-changes.md`, 2026-11-13 entry).
- `errors.AsLinkError.spec`: Perennial's `errors.As.spec` (an axiom) says nothing of the result (`(b v')`, any
  boolean and value), and `As` is not translated; the spec needs a first-match `As` spec in Perennial
  (`notes/perennial-changes.md`, 2026-11-14, "The WAL's leaf specs").
- `fmt.ErrorfErrsNot.spec`: the result (a fresh `*errorString` under the model) is not `t` only by freshness, and
  nothing gives a points-to of `t`'s pointer (`errors.newVar` forgets it: the 2026-11-14 entry of
  `notes/perennial-changes.md`); with it, `errors.Is(err, t)` is `false` by the model's walk.
- `fileutil.CreateDirAll.specTmp`: **false as stated** (ledger 2026-11-14, "`specTmp`'s `valAfter` clause and
  `.touch`"): the success post's `∀ K b, hJ.valAfter J K b = none` fails at `b = .touch` even when `CreateDirAll`
  makes the directory (its `IsDirWriteable` logs `.touch`'s creation and removal in `J`'s claim, and a crash that
  keeps the first but not the second leaves the file). The coordinator's decided restatement (drop the clause;
  `wal-create17`) removes it. After it, the proof still needs the error post narrowed from `osSubtreeH` to
  `tmpDirH` (what `TouchDirAll` leaves: one directory of files) and the existing-directory case (`MkdirAll`,
  `IsDirWriteable` with `.touch` possibly present, `ReadDir` on a directory of files), or the pre restricted to an
  absent name (the only case `Create` reaches, the ledger's note): not started, pending that restatement.

## Leaf specs log (branch `wal-leaf4`, 2026-11-14)

The two leaves `wal-leaf3` left (tasks decided by the coordinator).

**Proved**
- `pbutil.MustUnmarshalMessage.specWalSnap`: the ledger's restatement adopted (2026-11-14 entry, "`U` says
  nothing of protobuf-go"): `WalEnc.WalUnmarshal.SnapCoh U` (`Sp/ReadAllCallees.lean`, a pure law of `U`: every
  `bs` it decodes as `(index, term)` is `snapEnc c` of a content `c` with valid unknown fields and that index and
  term; for C6 to discharge) is the spec's premise, `isPkgInit pbutil` in the pre. Proof:
  `LinuxFs/Proof/go_etcd_io/etcd/pkg/v3/pbutil/MustUnmarshalMessageWalSnap.lean`
  (`MustUnmarshalMessage.wp_proofWalSnap`), over the part's `proto.UnmarshalPb.spec` at `pbSnapC` (D2), the
  decoded `snapOwnC` frozen by `snapOwnC_freeze` (a lemma of `proto.CloneWalSnap`'s proof module, imported: it
  belongs in `walpb/PbSnapshot.lean`). `WAL.ReadAll.wp_proof` takes `hUs : U.SnapCoh` (its call passes it); the
  same edit fixed a pre-existing break at the `fmt.Errorf` argument of the unknown-record-type arm (`cases hii` on
  `GoInterface.ok ii = GoInterface.ok …` no longer substitutes: `injection`).
- `os.MkdirAll.specDirS` (`LinuxFs/{Spec,Proof}/os/MkdirAllDir.lean`): `MkdirAll` of a name holding a directory,
  no effect; with `os.Stat.wp_childDirS`/`os.Lstat.wp_childDirS` (a spine to `d/b` from fractions of `d`'s and of
  the claim) and `os.Mkdir.wp_takenS`.
- `os.WriteFile.specTruncS` (`LinuxFs/{Spec,Proof}/os/WriteFileTrunc.lean`): `WriteFile(d/b, "")` of an existing
  file held whole (`trFile i False`), over `os.OpenFile.wp_truncS`; no claim changes. `trFile_false`.
- `fileutil.IsDirWriteable.specFile` (`LinuxFs/{Spec,Proof}/.../fileutil/IsDirWriteableFile.lean`): the probe on a
  leftover `.touch` file `i`, given `trFile i False`; on an error the file is given back if still there.
- `TouchDirAll.spec`/`CreateDirAll.spec`: error post narrowed from `osSubtreeH` to `tmpDirH` (proofs repaired:
  `tmpDirH_none`/`tmpDirH_dir`; the `osSubtreeH_*`/`subCover_*` lemmas there deleted). `tmpSub`/`tmpDirH` moved
  from `Sp/CreateCallees.lean` to `LinuxFs/Spec/.../fileutil/TmpDir.lean`.

**Restated, not proved**
- `fileutil.CreateDirAll.specTmp`: success post without the commit bound (ledger 2026-11-14, "the commit bound on
  an existing directory": false when `Stat` of the existing directory fails once, `created = []`, nothing synced;
  `nonissues/etcd-fork-touchdirall-stat-error-no-parent-sync.md`); `Create` never used it (pattern repaired).
  Still blocked: (1) a leftover `.touch` in the existing directory needs its file's `OsMeta` and bytes for
  `WriteFile`'s truncation, which `tmpDirH` and its producers do not hold (ledger 2026-11-14, "a leftover `.touch`
  needs its file": the coordinator's call, proposed `tmpSub` holding each file's `trFile`); (2) `TouchDirAll`'s
  `Exist` branch calls `CheckDirPermission` (`Stat`, `FileInfo.Mode().Perm()`, `fmt.Errorf` of `FileMode`s), which
  has no spec in the part; (3) the existing-directory `TouchDirAll` proof itself (the `Exist` branch's
  `syncDir(parent)`, and the climbing loop of the other branch with `Exist(d)` answering either way, then
  `os.MkdirAll.specDirS`, the syncs of `created`, `IsDirWriteable`/`specFile`): not written, waiting on (1).
  The absent case is `CreateDirAll.spec` (proved, its error post now `tmpDirH`).

## Leaf specs log (branch `wal-leaf3`, 2026-11-14)

**Proved**
- `pbutil.MustMarshalMessage.specWalSnap`: `LinuxFs/Proof/go_etcd_io/etcd/pkg/v3/pbutil/MustMarshalMessageWalSnap.lean`
  (`MustMarshalMessage.wp_proofWalSnap`), over the part's `proto.MarshalPb.spec` at `pbSnapC` (main pbutil's
  translation with bodies). Statement fix (ledger 2026-11-14): premise `(Mr.encSnap sm).length < 2 ^ 48`
  (`Marshal`'s `maxAlloc`); `SaveSnapshot`/`SaveSnapshotPre` pass it (`< 2^40`; the frame bound `< 2^47`). The
  non-nil result is derived (`snapEnc_ne_of_index`).

**Not proved**
- `pbutil.MustUnmarshalMessage.specWalSnap`: unprovable as stated (ledger 2026-11-14): `U.decSnap bs = some s` is
  about the client's parameter, untied to protobuf-go, so `Unmarshal` may fail (panic) or decode another
  index/term; and the pre lacks `isPkgInit pbutil`. Proposed premise on `U` in the ledger (coordinator's call:
  a new obligation for `ReadAll`'s callers).
- `fileutil.CreateDirAll.specTmp`: not started; the existing-directory case needs specs that do not exist:
  `os.MkdirAll.specS` and `os.WriteFile.specEmptyS` require the name absent, so `IsDirWriteable.spec` requires
  `.touch` absent (a leftover `nm.tmp` may hold `.touch`: `WriteFile` with `O_TRUNC` on an existing file, and
  `MkdirAll` on an existing directory, need new specs/proofs over the extension); and the error post
  `tmpDirH` needs `TouchDirAll.spec`'s proved error post narrowed from `osSubtreeH` (its proof in
  `fileutil/TouchDirAll.lean`, 577 lines, re-done over a narrower `MkdirAll`/`IsDirWriteable` error post).

## Leaf specs log (branch `wal-leaf2`, 2026-11-14)

The four `errors`/`fmt` leaves and `Record.Reset` (tasks decided by the coordinator).

**Proved**
- `walpb.Record.Reset.spec`: `LinuxFs/Proof/.../wal/walpb/Record__Reset.lean`, over the trusted model
  `Record.Reset.impl` (`LinuxFs/TrustedCode/go_etcd_io/etcd/server/v3/storage/wal/walpb.lean`; the toml's
  `trusted = ["Record.Reset"]`, an empty `LinuxFs/ManualProof/.../walpb.lean`). **Trusted, decided
  provisionally, pending the user's review** (§10). The model is Go's first statement, `*x = Record{}` (a store
  of the zero value, every field, `state` included); it leaves out `MessageStateOf(x).StoreMessageInfo(mi)`, an
  atomic store of the package's fixed descriptor into `state`'s message-info cache, which nothing but the
  protobuf runtime reads, and only through `ProtoReflect`, which stores the same `mi` when it finds the cache
  `nil` (`record.pb.go`): a `nil` cache and one holding `mi` behave alike (the docstring). Nothing more than the
  fields' reset was needed. The model names `Record`'s type by its name (`model.Record`; the translation's
  `Record.ty` cannot be named from the trusted file it imports): `walpb_model_Record_eq` (by unfolding).
  Retranslated with `etc/goose.py --project etcd` keeping only walpb's change (the pin `0b50f0426` would undo the
  fork fixes in `wal`/`fileutil`, translated from `f15d88841`: those files reverted to the branch's).

**Not proved (blocked by Perennial's facts and specs; no local route without an axiom)**
- `errors.IsErrno.spec`: translating `Errno.Is` with its body is not enough. Its `switch` loads
  `errors.ErrUnsupported` (the fourth case, reached for an errno target: the first three compare an `Errno`
  with `oserror`'s `*errorString`s, different types, `false`), and Perennial's `errors` fact is `True`
  (`Perennial/Proof/errors/Base.lean`: `define_is_pkg_init iprop(True)`), so nothing gives the global's
  points-to and the load does not step. The part cannot add it: `errors` is Perennial's package (`ExternalInit`),
  and syscall's initializer, which runs `errors.initialize'` only if not yet run, learns nothing of it. Needs
  Perennial's `errors` fact to record `ErrUnsupported` (`errors.newVar ErrUnsupported "unsupported operation"`).
  The `errors.is` walk at a comparable non-pointer target would then be the local part (symbolic execution of
  `is` on a two-error tree; `errors.is.spec` admits only pointer targets).
- `errors.IsPathErrnoEof.spec`: the same load of `errors.ErrUnsupported`, and also `io.EOF` distinct from
  `oserror.ErrPermission`/`ErrExist`/`ErrNotExist` and `ErrUnsupported` (else `Errno.Is(io.EOF)` returns
  `e == EACCES || ...`, which may be `true`): both are `*errorString`s, and `errors.newVar` (what `io`'s and
  `oserror`'s facts keep, Perennial's packages) forgets the allocation (2026-11-14 entry of
  `notes/perennial-changes.md`), so no fact of the part can say so ("`oserror`'s errors distinct in the part's
  package facts" is not available: the part's `io/fs` and `os` facts copy `oserror`'s values, they never see the
  allocations). Needs `newVar` to keep `x.s ↦□ msg` (different messages, different pointers).
- `errors.AsLinkError.spec`: `errors.As` has no translation and no model (`Perennial/Code/errors.toml` leaves it
  out, no `As_unfold`), only the axiom `errors.As.wp_proof` whose post is `∃ b v'`. A first-match lemma cannot be
  derived from it: it would be an axiom (excluded). Needs Perennial's `As` spec with the first-match case (the
  existing 2026-11-14 entry), or a model of `as`'s first iteration.
- `fmt.ErrorfErrsNot.spec`: the model's result is a fresh `*errorString` (`errors.New(format)`), but "not `t`"
  needs a points-to of `t`'s pointer (`t` = `io.EOF`'s value in every caller: `decodeRecord`, `Validate`), and
  `io`'s fact is Perennial's `newVar`: the same gap. No part fact can carry it (the part does not translate
  `io`). With `newVar` keeping `x.s ↦□ msg`: the fresh `x'.s ↦ format` (full, before it is persisted) and
  `y.s ↦□ "EOF"` give `x' ≠ y`, then `errors.Is` of a leaf (`errors.wp_Is_leaf`) answers `false`.
- **Translation not kept**: `Errno.Is` (with `EACCES`, `EPERM`, `EEXIST`, `ENOTEMPTY`, `ENOTSUP`,
  `EOPNOTSUPP`; imports `errors`, `internal/oserror`) and `PathError.Unwrap` translate cleanly
  (`etc/goose.py --project bboltfs`), but unblock nothing until Perennial's facts change, and rebuild 679 part
  modules (`etc/importers.py --count`): reverted. To redo: add those names to `LinuxFs/Code/syscall.toml`'s
  `translate` and the two packages to its `imports`, `"PathError.Unwrap"` to `LinuxFs/Code/io/fs.toml`, rerun
  goose and `etc/gen-init.py` (syscall's initializer then runs `errors`'/`oserror`'s initializers).

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

**Thirteenth session (branch `wal-tc3`, 2026-11-14): W1 amended (option 1 of `wal-tc2`'s finding).** `W1.lean`:
`latestAt` (the candidate `valAt` reads), **`WroteIn cs o len s`** (change `s` announced a nonzero byte of
`[o, o + len)`), **`AsOfW cs v o len`** (as of the last sync, or as of `n > 0` with each byte's `latestAt`
stamped in `(0, n]` by a change that `WroteIn` the core), `AsOfOne f f' := AsOfW f.cand f'.cache`,
`AsOfW.congr`, **`AsOfW.weak`** (gives the old form). `Abs.lean`: `AsOfOneG := AsOfW` over the ghost
candidates; `w1G_of_W1` by `AsOfW.congr`. Users repaired minimally: `asOfOneG_asOf` is `AsOfW.weak` (every
existing user consumes the old form), `w1G_durable` a `show`. `W1Sat` unchanged. All 31 importers built.
New statement (Lean):
```lean
def WroteIn (cs : Nat → Cands) (o len s : Nat) : Prop :=
  ∃ b, o ≤ b ∧ b < o + len ∧ ∃ v : w8, (v, s) ∈ cs b ∧ v ≠ 0
def AsOfW (cs : Nat → Cands) (v : Nat → w8) (o len : Nat) : Prop :=
  (∀ b, o ≤ b → b < o + len → v b = valAt (cs b) 0) ∨
  ∃ n, 0 < n ∧ ∀ b, o ≤ b → b < o + len →
    ∃ p, latestAt (cs b) n = some p ∧ v b = p.1 ∧ 0 < p.2 ∧ WroteIn cs o len p.2
```
**For the window's `CrashOk` (the users that need the new disjunct)**: in `cut`'s window a byte from `wr` on
has `latestAt` the truncate's `(0, n_rz)` for `n ∈ [n_rz, k)` (`k` the flush's write), and no byte of the
core has a nonzero candidate stamped `n_rz`, so `AsOfW` at such `n` is false; below `n_rz` those bytes'
`latestAt` is stamped 0. So an accepted frame straddling `wr` is as of the flush (`n ≥ k`: intended) or
as of the sync.

**Fourteenth session (branch `wal-tc4`, 2026-11-14): W1 restated exactly over recorded resize stamps.**
- *Trusted* (`GooseLang/Ext/Fs/Impl.lean`, **pending the user's review**, bookkeeping only): `OsFile.rzs :
  List Nat := []`, `OsChangeKind.isResize`, `OsFile.announce` appends the stamp of a resize (so
  `FtruncateStart`, `FallocStart` and `open`'s `O_TRUNC` record it; `ofDisk`/`newFile` start empty). Go
  example `examples/osfs/semantics/data_resize_stamps.go` (indexed in `doc.go`). No extension proof
  changed (every `GooseLang/Ext/Fs` module rebuilt as is).
- *W1* (`W1.lean`): `WroteIn` dropped; the statement (Lean):
```lean
def AsOfW (cs : Nat → Cands) (rz : List Nat) (v : Nat → w8) (o len : Nat) : Prop :=
  (∀ b, o ≤ b → b < o + len → v b = valAt (cs b) 0) ∨
  ∃ n, 0 < n ∧ ∀ b, o ≤ b → b < o + len →
    ∃ p, latestAt (cs b) n = some p ∧ v b = p.1 ∧ 0 < p.2 ∧ p.2 ∉ rz
def AsOfOne (f f' : OsFile) (o len : Nat) : Prop := AsOfW f.cand f.rzs f'.cache o len
```
  `AsOfW.congr` takes `rz' ⊆ rz` (fewer resizes known is weaker); `AsOfW.weak` unchanged in form; sanity
  lemmas `AsOfW.of_last`, `AsOfW.split_zero` (allowed: the split frame, second share zeros),
  `AsOfW.not_rz_window` (excluded: a byte last zeroed by a resize after a byte written since the sync);
  `W1Sat` unchanged. The docstring's "excludes real crashes" caveat narrowed to the buffered-zeros case.
- *Ghost side* (`Abs.lean`): `AsOfOneG bs rz img o len`, **`W1G … bsOf rzOf`** (the resize stamps known of
  each file); `w1G_of_W1 … rzOf` asks, of each segment, `∀ s ∈ rzOf g.ino, s ∈ f.rzs`. **`CrashOk` and
  `CrashOkA` pass `fun _ => []`** for now: their users get exactly the weak form (as before), and no
  `CrashOk` proof changed. `w1G_durable`, `w1G_sync`, `w1G_prefix`, `crashTo_tailM`/its wrapper are generic
  in `rzOf`.
- **The ghost link `cut`'s window needs (next unit, not done)**: the WAL must know, at a crash, that the
  truncate's stamp is in the file's `rzs`. Plan: `OsMeta.rz : List Nat := []` (ghost, `Ghost.lean`), a
  `MetaOk` clause `∀ s ∈ m.rz, s ∈ f.rzs` (kept by every step: `rzs` only grows, `announce` keeps `m.rz`),
  `rsPostK … n …` sets `rz := n :: m.rz` (`rsPostK_false` and `ResizeAu`'s `withTc` form then need the
  `rz` field), the crash take (`crashRest_take_files`, `FileCrashAt`) exporting it next to the
  candidates, `walCrash_pure`'s `hfiles` carrying it, and `CrashOk`'s `W1G` passing `segRzOf lay i :=
  (find g.ino).om.rz`. Every `CrashOk` prover is unaffected (`asOfOneG_asOf` is generic in `rz`); the
  window's prover uses `AsOfW` with the truncate's stamp in `g.om.rz` (`AsOfW.not_rz_window`'s argument).

**Fifteenth session (branch `wal-tc5`, 2026-11-14): the ghost link of the resize stamps (the fourteenth
session's plan, as planned but for three choices below).** Untrusted; `Impl.lean` unchanged. All of
`GooseLang/Ext/Fs` and `LinuxFs` build (merged with `wal-int` `00fad0d493`).
- *Extension ghost* (`GooseLang/Ext/Fs`): **`OsMeta.rz : List Nat := []`** (stamps of resizes the client knows;
  `OsMeta.countable` encodes it); **`MetaOk.rz : ∀ s ∈ m.rz, s ∈ f.rzs`** (kept by every step: `announce`,
  `land`, `synced` keep `OsFile.rzs` or grow it; `OsMeta.announce_rz`/`touch_rz` simp); **`OsCoh.tok_rz`** (a
  resize in flight has its stamp among its file's `rzs`: what the landing needs, since the token's `OsMeta` is
  the announcement, which does not know the stamp; set by `osCoh_start`, kept by every coherence lemma);
  `metaOk_announce` takes `hrz` (the new file's `rzs` include the old's).
- *Choice 1*: **`rsPostK keep … n …` sets `rz := cond keep (n :: m.rz) (rsPost …).rz`**, so `rsPostK_false` stays
  `rfl` and `rsDone` (bboltfs, crashlog) is untouched; every WAL segment has no sync cut (`keep = m.cut.isNone`
  = true), so the WAL's landings record the stamp. `rsPost_rz`, `rsPostK_rz` (simp).
- *Choice 2*: **`OsMeta.synced` forgets `rz`** (`rz := []`): a sync with no change in flight leaves every byte one
  candidate stamped 0, so no stamp matters; this keeps `synced_eq` (bboltfs) as it was. `bsynced` keeps it.
- *Choice 3*: **`OsMeta.withTc m tc rz`** (two arguments, `{ m with tc, rz }`): the caller's halves of a resize's
  outcome are up to both (`os.ftDoneH`, `fallocDoneH`: `∃ tc rz`), since the owner's half (`rsPostK true`) knows
  the stamp; `rsPostK_withTc`, `rsPost_withTc`, `announce_withTc`, `synced_withTc` (`= m.synced`) restated.
  Repaired: `File__TruncateAu` (`truncOutH_again` takes `rz0`), `DefsAu`, `ZeroToEndAu`; `os.osMeta_eq` takes
  `h11 : a.rz = b.rz`.
- *Crash take*: **`FileCrashAt`** gains `∀ s ∈ m.rz, s ∈ f.rzs` (from `MetaOk.rz`, `crashRestAt_take`);
  `crashRestAt_take_tok` also returns `ti.kind.isResize → ti.n ∈ f.rzs` (`tok_rz`); **`SegCrashAt`** gains `∀ s ∈
  g.om.rz, s ∈ f.rzs`. **`rzMeta tr m tg n` now has `rz := n :: m.rz`** (the in-flight layout knows the stamp:
  the take gives it from `tok_rz`), so the window's `CrashOk` sees the truncate's stamp both in flight and landed.
- *`CrashOk`/`CrashOkA` pass **`segRzOf lay`*** (`(find g.ino).om.rz`; `segRzOf_mem`, `segRzOf_prefix`);
  `crashGood_exists`/`walCrash_pure`'s `hfiles` carry the stamps; `W1G.mono_rz`, `W1G.weak_rz`. Users repaired:
  `crashOkA_tail`, `TailSyncPure` (their synced images' `W1G` at `segRzOf`, by `w1G_sync`), `CutCrash` (`w1G_prefix`
  with `mono_rz`).
- *The window's W1 transport* (**`RzW1.lean`**, proved): `RzCands rz cs cs'` (`cs'` is `cs` or `cs ++ [(0, n)]`,
  `0 < n`, `n ∈ rz`), **`AsOfW.drop_rz`**, **`W1G.drop_rz`**: `W1G` over a window layout's bytes (a truncate's
  `rsAnn`) gives `W1G` over the exact tail's, with the same stamps. (`latestAt_append_lt`, `valAt_append_pos`.)

**Sixteenth session (branch `wal-tc6`, 2026-11-14): `W1G` past the ghost's bytes; the truncate window's
`CrashOk`.** Untrusted; `Impl.lean` unchanged; every importer of `CrashTakeFiles`, `Abs`, `TailCrash`, `RzW1`
builds (merged with `wal-int` `4fb9b41cd4`).
- *`W1G` past the bytes* (the design of the W6 log's thirteenth session, item 1; I3b `wal-tc6` entry for the
  names): `segBytesOf lay i` maps **`segBytesX g = g.bs ++ pcRun g.om |g.bs|`** (the run of `om.pc` below `om.hi`,
  up to the first unknown byte); an exact segment's is `g.bs` (`segBytesX_of_hi`). The crash side: **`FileCrashAt`**
  (`GooseLang/Ext/Fs`) carries `m.pc`'s candidates past the size (`MetaOk.pc_cand`), **`crashRestAt_take_tok`**
  exports `tok_cand` past the size, **`rzMeta_pc_cand`** turns both into `rzMeta`'s, **`SegCrashAt`** and
  `crashGood_exists`'s `hfiles` carry `g.om.pc`'s candidates, `w1G_of_W1` takes `segBytesX g`'s (`segBytesX_cand`).
  Users over exact layouts take `segBytesOf_some_ex`/`segBytesOf_mem_ex`.
- *`crashTo_tailL`* (`TailCrash.lean`): `crashTo_tailM` with the tail's image of any length in `[max so z0, |bs|]`,
  each byte below its size a candidate of the bytes (`crashTo_tailM` is now its corollary).
- *`W1G.drop_rz`* (`RzW1.lean`) takes `|bs| ≤ |bs'|` (was equal lengths).
- **`crashOkA_win`** (`WinCrash.lean`, proved): `CrashOkA` of a layout with the exact tail `g0` gives `CrashOkA` of
  one whose tail `g` (same inode) has `wr ≤ |g.bs|`, `g.om.size = |g.bs|`, `wr ≤ g.om.lo`, `g.om.hi ≤ |g0.bs|`,
  `|g0.bs| ≤ |segBytesX g|`, `segBytesX g`'s candidates `g0`'s below `wr` and `RzCands g.om.rz` of `g0`'s
  everywhere; no alternative layout holds the tail. Proof: `hok` at images as of the last sync (as
  `crashOkA_tail`), then `crashTo_tailL` on `lay0` with `W1G.drop_rz` (zero is a candidate stamped 0 of `g0`'s bytes
  from `wr` on: **`tail_zero_cand`**, from `TailLast`'s `ByteOk` and F-Z). Covers the truncate in flight (`rzMeta`,
  `rsAnn`: `|g.bs| = |g0.bs|`) and landed (`rsPostK true`: `|g.bs| = wr`, the cut-off bytes in `pcRun`).
- **`crashOkA_same`** (`WinCrash.lean`, proved): `CrashOkA` across a tail step that allows no new crash, keeps
  `segBytesX`'s candidates (no shorter) and the stamps: the truncate's finish, from the in-flight layout (the
  invariant keeps only the current layout's condition).

**Seventeenth session (branch `wal-tc7`, 2026-11-14): the truncate from a window; the landing's facts.**
Untrusted; `Impl.lean` unchanged. Task 1 done; tasks 2 (the supplies, `specWalTail`) and 3 (`ZeroToEnd`'s
instance) not started (I3b, `wal-tc7` entry, for what they now have).
- *Why the window case needs more than `crashOkA_win`*: in a window (`¬ SegExact g0`) `TailWin` says nothing
  of the bytes past `wr`, so `crashTo_tailL`'s argument (zero is a stamp-0 candidate of the bytes past `wr`,
  `tail_zero_cand`) is not available. It is not needed: a window's least crash size is at most `wr`, so the
  window's own `FileCrashedR` already allows a zero from `wr` on, and every crash of the truncate's layout is
  one of the window's (`fileCrashedR_rzMeta_win`); `W1G` drops the truncate's zeros (`W1G.drop_rz`).
- **Invariant change (`Abs.lean`)**: `WalAbsD.last`'s window clause is now `¬ SegExact g → TailWin … ∧ g.om.lo ≤
  lay.wr` (**`WalAbsD.winLo`**; `lastWin` unchanged in statement). True of every window the WAL opens: `cut`'s
  and `ZeroToEnd`'s truncate to `wr` (`lo := min lo wr`), `ZeroToEnd`'s growth after it (keeps `lo`), a write
  past the size (keeps `lo` at the size it found, below the write position). Repaired: `SaveAbs` (the append
  keeps it), `RzStepPure`. **Obligation for `wal-maxb14`** (the writer past the size): the window it opens
  gives `g.om.lo ≤ lay.wr`.
- *`RzStepPure.lean`*: `walAbsD_win` without `hex0` (a pre-segment is not the last by the names' order);
  **`walAbsD_rzStart`** from an exact tail or a window, premise `min g0.om.lo tg ≤ lay.wr` (true at `tg = wr`).
- *`WinCrashW.lean`* (new, proved): **`crashOkA_rz`** (`crashOkA_same` with `RzCands` in place of equal
  candidates), **`fileCrashedR_rzMeta_win`** (premises `lo ≤ tg ≤ size ≤ hi`, `zf ≥ size`, `OsMeta.TcZ m`),
  **`rzMeta_pc`**, `pcRunN_map`, **`segBytesX_rzSeg`** (as long, `RzCands` with the truncate's zero, `0 < n`),
  **`crashOkA_rzStart`** (the truncate's first step at `wr`, from an exact tail by `crashOkA_win` or a window by
  `crashOkA_rz`; premises `0 < n`, `zf ≥ size`, and for a window `lo ≤ wr ∧ OsMeta.TcZ g0.om`); the landing:
  **`rzLand g0 tg n`** (bytes `take tg`, `OsMeta` `rsPostK true true g0.om tg tg n (drop tg)`), `rsPostK_pc_ge`,
  `rsPostK_pc_mid`, `pcRunN_known`, `pcRunN_congr`, **`segBytesX_rzLand`** (`segBytesX` of the landed tail has
  the in-flight one's candidates, position by position: `crashOkA_same`'s `hlen`/`hcand`; its `hfc` is
  `fileCrashedR_rsPostK_rz`).
- **Extension change (untrusted: `GooseLang/Ext/Fs`, `LinuxFs/Proof/os`, `LinuxFs/Spec/os`)**: the window's
  zero-candidates clause needs that the candidates `m` knows past its known zeros are the zero, which `MetaOk`
  gives (`zf`, `tail`) but no pure fact of the layout does: **`OsMeta.TcZ`** and **`MetaOk.tcz`** (`Ghost.lean`).
  And the truncate's stamp `n` must be positive at the start's commit even when nothing is cut off (`wr = size`:
  `rzMeta` still appends `(0, n)` to the bytes past the size it knows): `n` is `stamp + 1`. So
  **`wp_osResizeStart`/`wp_osFtruncateStart`**'s post (and `wp_osFtruncateStart_au(W)`'s) is `⌜0 < n ∧ m.TcZ ∧ ∀ x ∈
  xs, …⌝`, and **`wp_osFtruncateStart_auW`**'s commit, like **`os.truncAuW`**'s (`Spec/os/File__TruncateAu.lean`),
  receives `rsTok … ∗ ⌜0 < n ∧ m0.TcZ⌝`: the supply's start learns both. Users of `%hn` take `.2.2`.

**Eighteenth session (branch `wal-tc8`, 2026-11-14): the truncate's start fact, its landing; the
not-landed outcome needs the extension.** Untrusted; `Impl.lean` unchanged. Tasks 1 and 2 (landed) done;
2 (not landed) designed, not done; 3 (`truncSup`, `specWalTail`) and 4 (growth, `ZeroToEnd`'s instance) not
started (I3b, `wal-tc8` entry).
- *The start's `zf ≥ size`* (`crashOkA_rzStart`'s `hzf`): the supply's tie `K` cannot mention the `OsMeta`
  (one supply serves every attempt of the `EINTR` loop, each from its own state) and the invariant does not
  keep the fact, but every state's `OsMeta` has it (`MetaOk.zf`). **`OsMeta.TcZ`** (`GooseLang/Ext/Fs/
  Ghost.lean`) now opens with `∀ z, m.zf = some z → m.size ≤ z` (`MetaOk.tcz` proves both halves), so the
  start's commit, which already receives `⌜0 < n ∧ m0.TcZ⌝` (`os.truncAuW`), has it: no statement changed.
  (The other routes: a premise of `os.truncSup` per attempt, which `File.Truncate.specAu`'s loop and every
  caller of the fileutil `Au` specs would have to supply; or a fact kept in the invariant through every
  tail step. Both cost more than a conjunct of a fact the extension proves anyway.) Users: `tcz_pc` (`.2`).
- **`RzLand.lean`** (new, proved): **`walAbsD_rzLand`** (the static relation after the landing, from the
  in-flight layout `tailLay lay pre (rzSeg g0 true lay.wr n) lay.wr`: a window with `|bs| = wr`, `lo ≤ wr`,
  `TailWin` below `wr` from the in-flight one's; exact only if nothing was cut off and the in-flight tail
  exact, then `TailLast` carried, the bytes equal), **`crashOkA_rzLand`** (`crashOkA_same` with
  `fileCrashedR_rsPostK_rz`, `segBytesX_rzLand`, the stamps `n :: m.rz` both), `rzLand_length`,
  `rzLand_getElem?`.
- **`RzWals.lean`** (new, proved): the invariant's pure transports over any crash step
  (**`TailCrashStep`**: for every alternative layout not holding the tail, `CrashOkA` of the old layout gives
  the new one's): **`crashOkW_tailA`**, **`walsOk_tailA`**, **`dirKeysOk_tailA`** (`walsOk_tail`/
  `dirKeysOk_tail` without the exact-tail crash step), and the truncate's two crash steps
  **`tailCrashStep_rzStart`** (from `OsMeta.TcZ` and `0 < n`; the window's `lo ≤ wr` from `WalAbsD.winLo`)
  and **`tailCrashStep_rzLand`**. With `walAbsD_rzStart`/`walAbsD_rzLand` they are what
  `walInvBody_tailW`'s continuation takes at the start's and the finish's commits.
- **The not-landed outcome (not done; needs an untrusted extension change)**: `rsOutT`'s `e ≠ 0` arm may be
  `rsUndone true p tg m xs n`, whose `OsMeta` is `m.announce …`: it forgets what the in-flight layout's
  `rzMeta` knows, the stamp `n` (`rz`) and the candidates past the size (`rsTail` at `m.size`), though the
  state still has both (`OsCoh.tok_rz`, `tok_cand`). Without `n` in the layout's stamps, `W1G` of the
  undone layout does not give the in-flight one's (`crashOkA_rz`'s `hrz`: the zeros stamped `n` that
  `rsAnn` left in the bytes are no known resize's), so no layout over `m.announce …` keeps `CrashOk`.
  Design: **`rsUndoneK keep`** (`Truncate.lean`), as `rsDoneK keep`: with `keep` its `OsMeta` is `{ m.announce
  (min size tg) (rsHi tr size tg) tg with tc := rsTail tr m tg m.size n [], rz := n :: m.rz }` (the WAL's
  `rzMeta`; `MetaOk.tail` from `tok_cand`, `MetaOk.rz` from `tok_rz`, a ghost update of `Γm` in
  `resize_undone_world`); `wp_osFtruncateFinishK`/`rsOutT` use it at `keep := m.cut.isNone`; `os.ftUndoneH`
  becomes `∃ tc rz, osMeta ½ ((m.announce …).withTc tc rz) ∗ …` (as `os.ftDoneH`), with
  `File.Truncate.specAu`'s loop (`os.ftDoneH_of`'s state set gains the `withTc` form) and
  `DefsAu.ftUndoneH_preGrownH` repaired. The supply's undone arm is then the in-flight layout kept, idle.

**Nineteenth session (branch `wal-tc9`, 2026-11-14): `rsUndoneK`; `specWalTail` needs a domain fact on the
caller's `tc`.** Untrusted; `Impl.lean` unchanged. Task 1 done; tasks 2 (`truncSup`, `specWalTail`) and 3 (growth,
`ZeroToEnd`'s instance) not started (I3b, `wal-tc9` entry).
- **`rsUndoneK keep`** (`GooseLang/Ext/Fs/Truncate.lean`), as designed: **`rsUnMeta keep tr m tg n`** is the
  announcement with, if `keep`, `tc := rsTail tr m tg m.size n []` and `rz := n :: m.rz` (`rsUnMeta true tr = rzMeta tr`
  by `rfl`; `rsUnMeta_false` is the announcement, `rsUndoneK_false` is `rsUndone`, both `rfl`; simp lemmas for the
  fields). It needs no `m.cut = none`: only bytes past the size, whose candidates are the state's. Ghost update in
  **`resize_undone_worldK`** (from `resize_undone_world`, then `gAuth_update` of `Γm`), over **`osCoh_setMeta`** (a file's
  `OsMeta` replaced by one with the same cut, `MetaOk`, no change in flight on it) and **`metaOk_rsUnMeta`** (`tail` from
  `RsFacts.hcandP`, `rz` from `OsCoh.tok_rz`; the other fields the announcement's, `MetaOk.zc` included).
  `wp_osFtruncateFinishK`'s not-landed arm is `rsUndoneK keep`; `wp_osFtruncateFinish` unchanged (`rsUndoneK_false`).
- `rsOutT`'s not-landed arm is `rsUndoneK m.cut.isNone true …` (`LinuxFs/Proof/os/ResizeAu.lean`); **`os.ftUndoneH`**
  (`LinuxFs/Spec/os/File__TruncateAu.lean`) is `(∃ tc rz, osMeta ½ ((m.announce …).withTc tc rz)) ∗ osBytes …`, as
  `os.ftDoneH`. Repaired: `File.Truncate.wp_proofAu` (the loop's state `ftStateH`: `m0 = m ∨ ∃ tc rz, m0 = (m.announce
  …).withTc tc rz`; `os.ftDoneH_of`, `os.truncOutH_again`), `DefsAu.ftUndoneH_preGrownH`, `preallocExtendTruncAu`,
  `ZeroToEndAu`.
- **Found: `specWalTail`'s post cannot get `TailZ` through `os.File.Truncate.specAu` as stated** (`wal-save16` put
  `TailZ m` in `TailMetaW`: the known zeros `zf = some z`, `pageEnd z ≤ max size cz`, and `tc` known on `[size, z)`).
  The post's `OsMeta` is `os.ftDoneH`'s `(rsPost true m wr wr).withTc tc rz` with `tc` existential: the supply knows it
  is `rsTail` (known on `[wr, size)` and wherever `m.pc` is, so `TailZ` of the landed meta follows from the pre's), but
  the caller of `specAu` does not. Proposed (next session, untrusted spec change): `os.ftDoneH`/`os.ftUndoneH` carry
  `⌜TcKnows m tg tc⌝`, `TcKnows m tg tc := ∀ b, KnownAfter m tg b → (tc !! b).isSome` (`KnownAfter`: known in the
  announcement's `tc`, or `tg ≤ b < rsHi true m.size tg` with `b < m.size` or `(m.pc b).isSome`); monotone in `tc`'s
  domain, so `truncOutH_again`/`ftDoneH_of` carry it across attempts (an attempt from `(rsPost true m tg tg).withTc tc0
  rz0` keeps `tc0`'s domain); the supply proves it of `rsTail`. The other route, reading the invariant's half after the
  call, needs an invariant opening outside an atomic step (no `notCrashed` there).

**Thirtieth session (branch `wal-tc20`, 2026-11-14): the pending-form fdatasync proved.** Untrusted; no
trusted change; no statement change. The twenty-ninth session's design, steps 1-4, with one addition.
- **`syncLay_anyP`** (`TailSyncPend.lean`, new, pure): `syncLay_any` under `TailZeros lay ∨ TailPend lay` and the
  handle's zeros `WinZero lay g0`. Exact tail: F-Z from `TailPend` by **`tailZeros_of_pendEx`** (`TailLast`'s bytes
  past `wr = z0` are `old`'s, `ByteOk.val_unw`, and zero by the handle), then `syncLay_any`; window: `TailZ0` and
  `tailZeros_syncW0`, `walsOk_syncW`/`dirKeysOk_syncW`.
- **`walTailsRes_cutP`** (same file): `walTailsRes_cut` by `walLentTokB dir γ k false`; facts (`walLentRes_lookup`:
  F-Z or `TailPend`); continuation `(∀ lay' g F', ⌜… TailZeros lay' … ∧ tailG d lay' g.ino (F' !! g.ino) = tg⌝ ==∗
  walTailKey dir γ ∗ walTailsRes … (<[dir := lay']> Ls) F') ∧ (walTailsRes s Ls F ∗ walLentTokB …)` (the key by
  `walLentRes_unpend`; everything back on failure).
- **`walInvBody_syncP`** (same file): `walInvBody_sync` by the lent token; success premise gains `WinZero lay g0`,
  its post `walTailKey dir γ`; failure gives the token back.
- **`wp_tailFsyncP`, `syscall.Fdatasync.wp_tailP`, `fileutil.Fdatasync.wp_specWalPend`** (`FdatasyncPend.lean`,
  new; `TailMetaZ.synced`: `TailZ.synced_of`, `PastZ.synced`). **Addition**: the invariant's sync step needs `hzf`
  (`∀ z, zf = some z → |bs| ≤ z`), which `TailMetaZ` does not carry; **`Fs.wp_osMeta_zfGe`** (same file, untrusted:
  `wp_osMeta_size`'s form over `MetaOk.zf`/`MetaOk.size`) reads it from the state before the call's first step.
- Build: seeded from `agent-aafd0850b15dad934`; `lean-check -a` of both files; `lake build` of `FdatasyncPend`,
  `WAL__ReadAll`.

**Twenty-ninth session (branch `wal-tc19`, 2026-11-14): the growth supplies and `ZeroToEnd.specWalTail`
proved; the pending fdatasync designed, not proved.** Untrusted; no trusted change. Merged `wal-int`
(`wal-readall26`, `wal-leaf3`). Tasks 1-2 done (`GrowSup`, `ZteWalTail`, `WAL__ReadAll` build); task 3 not done.
- **The supplies' `P`** (ledger, "the resize supplies' `P`"): `os.truncSup` is told `⌜P m0⌝` (was `m0.lo ≤ tg ∨
  P m0`, too weak for a growth to the size), `os.File.Truncate.specAu` takes `P m` and **`∀ m', m'.lo ≤ min m.lo
  sz → m'.size ≤ max m.size sz → P m'`** (later attempts); **`fallocSup K i tg (P := True)`** told `⌜P m0⌝`;
  `preGrownH` carries `m'.lo ≤ m.lo` (`preGrownH_trans` takes `hlo`); `preallocExtend(Trunc)`/`Preallocate`
  `specAu` take `P` with `∀ m', m'.lo ≤ m.lo → m'.size ≤ sz → P m'`; **`ZeroToEnd.specAu`** takes `P Q` with `P
  m` and `∀ m', m'.lo ≤ min m.lo o → m'.size ≤ m.size → P m' ∧ Q m'` (supplies `truncSup … o P`, `truncSup … size
  Q`, `fallocSup … size Q`), its success post gains `m'.lo ≤ min m.lo o`. `TruncWalTail` passes the new premise;
  `walTail_truncSup` reads `LoWr` directly.
- **Growth supplies** (`GrowSup.lean`, new, no `sorry`): tie **`growTie dir γ k H md cuts wr i`** (the lent token
  of kind `false`, the record's half, idle); **`walTail_fallocSup … tg (htg : tg ≤ k) : walInv -∗ fallocSup
  (growTie …) i tg (fun m => m.lo ≤ wr ∧ m.size ≤ tg)`**, **`walTail_truncSupG … : walInv -∗ os.truncSup (growTie
  …) i tg (fun m => m.lo ≤ wr ∧ m.size ≤ tg)`**; their finishes `walTail_fallocFin`/`walTail_truncGFin`
  (`growFinP`), the shared invariant steps `walTail_growLand` (landed with `w`: `rzLandG_pure`, `w ≤ |old| = k`)
  and `walTail_growUndone` (in-flight layout kept), `segResF_grow`, `rzSeg_of_okRG`. The start: `rzGrow_pure`
  (`tg ≤ k = |old| ≤ hi`, `WalAbsD.oldHi_any`; `min lo tg ≤ wr` from `P`); no F-Z needed (`crashOkA_rz*`).
- **`ZeroToEnd.specWalTail` proved** (`ZteWalTail.lean`, new, no `sorry`): **`ZeroToEnd.wp_specWalTail Mr (wp_zte
  : ZeroToEnd.specAu) : ZeroToEnd.specWalTail Mr`**. First step **`walInv_pendStop`** (`walInvBody_pendStop`, at
  `wp_notCrashed_acc`): the exact tail's bytes past `wr` are `old`'s (`lenZ_of_tailLast`), so `LenZ`; with
  `TailZ0`, F-Z or `TailPend`; **`walLentRes_pendStopZ`** (`walLentRes_pendStop` allowing F-Z; the original is
  unused, kept to avoid an `Inv.lean` rebuild); it also gives `k = m.size` (`walAbsD_old_exact`). Then the size
  bound (`Fs.wp_osMeta_size`), the three supplies, `ZeroToEnd.specAu`. **Statement changes** (ledger):
  `specWalTail`'s pre gains `isPkgInit errors` (`WAL__ReadAll` adapted: `iPkgInit`), its post `sz' = sz`;
  **`TailMetaZ m bs := |bs| = size ∧ maps = ∅ ∧ pageEnd size ≤ max size cz`** (not `TailZ`: unprovable of a
  crashed/synced tail; the fdatasync needs only this, `TailZ.synced_of`).
- **Not done: `Fdatasync.specWalPend`** (task 3). Design: a pure `syncLay_anyP` (`syncLay_any` with `TailZeros
  lay ∨ TailPend lay` and the handle's zeros from `wr`: the window case's `WinZero lay g0` from the bytes, the
  exact case's F-Z from `TailPend` and `TailLast`'s bytes past `wr` being `old`'s); `walTailsRes_cut` over
  `walTailKeyL` (the lent token); `walInvBody_syncP` (`walInvBody_sync` with the token; on success
  `walLentRes_unpend` on the synced layout, F-Z by `tailZeros_syncW0`, the key out); `wp_tailFsyncP`,
  `syscall.Fdatasync.wp_tailP`, `fileutil.Fdatasync.wp_specWalPend` (the post's `TailMeta` of `m.synced`:
  `TailZ.synced_of` from `TailMetaZ`, `PastZ.synced`, `LoWr.of_exact`).

**Twenty-eighth session (branch `wal-tc18`, 2026-11-14): findings C and D fixed; the registration law
proved, and folded with `ReadAll`'s commit.** Untrusted; no trusted change. `wal-readall25`, `wal-save24`
merged. Tasks 1-2 done (the 33 leaves importing `Inv.lean` build, 2846 jobs); task 4 (task 3 of the brief)
not done.
- **C/D fix** (`Inv.lean`): **`TailMaps lay`** (`∀ g, lay.segs.getLast? = some g → g.om.maps = ∅`);
  **`TailIdle C Mr d lay := TailExact lay ∧ lay.wr = |S| ∧ TailSynced lay ∧ lay.so = lay.wr ∧ TailMaps lay`**
  (accessors `TailIdle.synced`/`.so`/`.maps`; `h.2.2` is now `h.synced`). **`TailIdle.bound`** `(habs :
  WalAbsD …) (h : TailIdle …) : TailBound C Mr d lay` (jE all the tail's records: `max so z0 = wr = |S|`,
  `z0 ≤ wr` from `TailLast`). **`TailLast.so_eq`** `(h : TailLast C Mr d lay g) (hdur : ∀ y ∈ g.bs, y = durB
  y.1) : lay.so = lay.wr` (a written byte not synced has a second candidate, `ByteOk`; `durB` has one).
  Established: the crash (`Crash.lean`: `WalsStart`'s `wr = so`, `initMeta`'s maps), `Close`
  (`walInvBody_untail`, `CloseLaw.lean`: `TailLast.so_eq` of the synced tail, `TailMeta`'s maps), the idle
  fdatasync (`tailIdle_syncIdle`: `syncLay`'s `so := wr`, `OsMeta.synced` keeps `maps`), `Create`'s commit
  (`walCreate_osAUnc` gains **`hmaps : g.om.maps = ∅`** after `hcut`; `TailLast.so_eq` of its durable segment;
  `createFresh_osAUnc`/`createU_none` gain **`hm2m : m2.maps = ∅`**, from `Create.lean`'s `hmaps2`, through
  `StreamOk`'s `m.maps = m0.maps`). **For `wal-create21`**: a fresh tail left idle needs `so = wr` (from
  `TailLast.so_eq` with its durable bytes) and its last segment's `maps = ∅`; a tail registered at `Create`
  needs neither.
- **The law proved** (`ReadAllRegCommit.lean`, new, no `sorry`): **`walInvBody_readReg`** (the body-level
  look: `walInvBody_readState`'s with `walTailsRes_registerPend` inside; `TailIdle.tailMetaR` gives
  `TailMetaR gl.om gl.bs ∧ |old| = gl.om.size`), **`walInvRegisterPendLaw_holds : walInvRegisterPendLaw C Mr
  R jr r`**, and, the coordinator's decision, **`walInv_readCommitReg`**: `walInv_readCommit`'s premises plus
  `gl` with `gs.getLast? = some gl`, its post (`Q dc`, `walPast s`, `walLenLb`, the name claim fraction,
  `osLogLb`, the facts) plus the registration's (`walTailsFrag {dir ↦ γ}`, `walPendTok dir γ |lay.old|`, the
  record's half `tailG d lay gl.ino none`, `TailMetaR gl.om gl.bs ∧ TailZ0 lay ∧ |lay.old| = gl.om.size`),
  with `walDurLe dc d` for the record's `d` (same history, cut, metadata): one invariant opening. `ReadAll`
  (`wal-readall26`) replaces its `walInv_readCommit` and `wp_register` calls by it and drops the hypothesis.
- **The truncate at `wr` from a lent tail** (task 4, first piece; `TruncSupPend.lean`, new, no `sorry`):
  `rzSeg_zf` (the announced tail's `zf` past its bytes, from `TcZ`), `tailPend_tailLay`,
  **`tailCrashStep_rzStartP`** (the pending start's crash step, `crashOkA_tailPend`), **`rzStart_pureP`**
  (`rzStart_pure` under `TailZeros lay ∨ (TailPend lay ∧ |S| = wr)`). **`walTail_truncSup`'s premises are now
  `(hok : ∀ k, ok ≠ some (k, true)) (hS : ∀ kp, ok = some kp → wr = (tailStream Mr H md cuts).length)`**: the
  key, or a lent token of kind `false` (after `walLentRes_pendStop`; `TailZK.zp`); `TruncWalTail.lean`'s
  caller passes `(fun _ h => nomatch h)` twice. The landing (`rzLand_pure`) needs no F-Z. `WAL__cut`,
  `WAL__ReadAll` build.
- **Not done** (task 4, rest): `fallocSup` with a `P` (for `rzGrow_pure`'s `min lo tg ≤ wr`), the growing
  truncate's supply (crash steps: `crashOkA_tailPend` when pending, `crashOkA_tailAny` with F-Z),
  `ZeroToEnd.specWalTail` (pre `walTailP … TailMetaR` with the zero length word at `o0`; first step
  `walLentRes_pendStop`; post bytes from `o0` zero, `TailMetaZ`), the pending-form fdatasync
  (`walLentRes_unpend`, F-Z back by `tailZeros_syncW0`).

**Twenty-seventh session (branch `wal-tc17`, 2026-11-14): fixes A and B made; the registration law
restated, its proof blocked on two invariant gaps.** Untrusted; no trusted change. Tasks 1-2 done (the 38
WAL leaves importing `Abs.lean` build, 2851 jobs; statements in the I3b `wal-tc17` entry); task 3 half
done; task 4 not started.
- **Fix A** (finding A of the twenty-sixth session): `WinLast`'s `TailZeros lay → WinZero lay g`; the
  window's fdatasync takes `WinZero` (and `TailZ0` for its crash step, `tailZeros_syncW0`); the resize
  steps' pure forms (`walAbsD_rzStart`, `walAbsD_rzLandG`, `rzGrow_pure`, `rzLandG_pure`) no longer need
  F-Z: these are the exact-start growth forms task 4 wanted (no `TailZeros`, so a pending tail's growth
  steps use them as they are; only `rzStart_pure`'s crash step, `tailCrashStep_rzStart`, still takes F-Z,
  for which the pending truncate uses `crashOkA_tailPend`).
- **Fix B** (finding B): `walLentRes_pendStop`; a kind-`false` lent tail has F-Z or `TailPend`.
- **Task 3**: `TailMetaR`, `TailMetaZ`, `walTailP f fd name dir γ i H md cuts o0 sz out k p tm`
  (`HandlePend.lean`: `walTailW` with `walLentTokB dir γ k p` for the key; `k` the lent `|old|`, kept
  apart from `sz` since `ZeroToEnd` changes the size but not `old`) and **`walInvRegisterPendLaw`**
  (`ReadAllRegPend.lean`, the restatement; the old `walInvRegisterTailLaw` kept for `WAL__ReadAll` until
  `wal-readall25` switches). Not proved, blocked on:
- **Finding C: an unregistered tail's `maps = ∅` is not in the invariant.** `TailMetaR`'s `m.maps = ∅`
  (which `ZeroToEnd`'s truncate and `fallocate` need: their mapped cells, `zerosA_trFile`'s `hm`) holds of
  every WAL segment (no one maps a WAL file; a crash's `initMeta` has none; `Close`'s handle has
  `TailMeta`), but neither `WalAbsD` nor `walTailsRes` says so, so the registration cannot hand it out
  (the old law's `TailMeta` was a hypothesis too).
- **Finding D: an unregistered tail's `TailBound` is not in the invariant.** `walTailsRes_registerPend`
  needs `TailBound C Mr d lay` (each registered entry's); `TailIdle` (`WalTailIdle`) has `TailExact`, `wr =
  |S|`, `TailSynced`, not the boundary. It holds: every unregistered tail has `so = wr` (a crash's
  `crashLay`: `so = wr = z0 = |S|`; `Close` and the idle fdatasync: `syncLay`'s `so := wr`), and with `wr =
  |S|` the boundary is all the tail's records.
- **Proposed fix for C and D** (one change, internal): `TailIdle C Mr d lay := TailExact lay ∧ lay.wr = |S|
  ∧ TailSynced lay ∧ lay.so = lay.wr ∧ TailMaps lay` (`TailMaps lay := ∀ g, lay.segs.getLast? = some g →
  g.om.maps = ∅`); constructors: the crash (`crashLay`: `rfl`; `initMeta`'s maps), `Close` (the handle's
  `TailMeta` maps and its fdatasync's `so := wr`), the idle fdatasync (`syncLay`, `OsMeta.synced` keeps
  `maps`); then `TailBound` of an idle tail (a pure lemma: jE the tail's records, `segStream` their
  frames) and the law's proof (`walInvBody_readState`'s look with `walTailsRes_registerPend` inside before
  closing; `gl` the last of `lay.segs` from `lay.segs.drop kk = gs`; `F = ∅` gives `tailG … none`;
  `walAbsD_old_exact`).
- **Not done**: task 4 (`fallocSup`, the growing truncate's supply with the pending crash step,
  `ZeroToEnd.specWalTail` over `walTailP`, the pending-form fdatasync via `walLentRes_unpend`); the
  intended statements are unchanged from the I3b `wal-tc15`/`wal-tc16` entries, with `walTailP … o0 sz []
  sz true (fun m bs => TailMetaR m bs ∧ ∀ j < 8, (bs.getD (o0 + j) (0, [])).1 = 0)` as the pre and `∃ sz' ≥
  o0, walTailP … o0 sz' [] sz false (fun m bs => TailMetaZ m bs ∧ ∀ b x, o0 ≤ b → bs[b]? = some x → x.1 =
  0)` as the success post.

**Twenty-sixth session (branch `wal-tc16`, 2026-11-14): option (i), the pending tail's crash step,
proved; two findings block the pending supplies.** Untrusted; no trusted change. `wal-save23` merged.
- **Proved** (`TailCrashPend.lean`, new, no `sorry`): **`LenZ lay`** (`∀ j < 8, lay.old.getD (lay.wr + j) 0
  = 0`: the length word at `wr` zero, `getD` zero past `old`), **`TailPend lay`** (`lay.wr = lay.z0 ∧ LenZ
  lay`); **`decStep_zeroWord`** (the reader accepts nothing where the 8 bytes from `off` are zero or past
  the end: `eof`/`shortLen`/a zero word); **`crashTo_tailP`** (`crashTo_tailL`'s tree part from a
  `CrashTo` over another image `fo0`, the history whole, `I = H`: the tail's image at least `|S|` long, the
  stream's value below `|S| + 8`; no W1); **`WalAbsD.pendVals`** (every candidate of the last segment below
  `wr + 8` has the stream's value, exact or window, from `TailPend lay` and `|S| = wr`: `ByteOk` below `wr`,
  `WinShape` from `wr` on); **`crashOkA_tailPend`** (`crashOkA_tailAny` with `TailPend lay` and `|S| = wr`
  in place of `TailZeros lay`: any tail step, a truncate's first step, its landing, a growth; its skeleton
  `crashOkA_tailW`'s, per the coordinator's pointer; `crashOkA_tailAny` itself does not apply: `TailShape`'s
  `zero` needs the stamp-0 candidates past `z0` zero).
- **Finding A (blocks the truncate supply from a pending tail): the in-flight layout's `WinZero`.**
  `WinLast` (`WalAbsD.last`'s window branch) has `WinZero lay g` (the bytes from `wr` on zero-valued). A
  truncate's first step keeps the values (`rsAnn` adds the zero candidate only), so `rzSeg g0 true wr n` of a
  pending tail has `old`'s values past `wr + 8` (a torn frame's), and `walAbsD_rzStart`'s `hz : WinZero lay
  g0` (`h.zeroPast hZ`, F-Z) cannot be given; the not-landed outcome (`rsUndoneK`) keeps that layout. Only
  `walAbsD_syncW` (the window's fdatasync) reads `WinZero`. Proposed: `WinLast`'s conjunct `TailZeros lay →
  WinZero lay g` (true of every window: `cut`'s and `Save`'s have F-Z, and a pending tail's with F-Z has
  zero values past `wr`), and `walAbsD_syncW`/`walsOk_syncW` take `WinZero lay g0` as a premise (the key's
  holder: `h.zeroPast hZ`; the fdatasync after `ZeroToEnd`: the bytes past `wr` are the landing's none and
  the growth's zeros, `rzLand`/`rzLandG`, which the handle's bytes show by agreement, so
  `ZeroToEnd.specWalTail`'s post should say the bytes from `o0` on are zero-valued).
- **Finding B (blocks the supplies' use of `crashOkA_tailPend`): `LenZ` has no channel into the invariant.**
  The supplies' crash steps need `TailPend` of the invariant's layout at the commit; the registration is at
  the look before the loop (the decoder has not run), and a supply sees only `K`, the state's `OsMeta`
  (`P`), the bytes it is handed (`xs0`, which agree with the invariant's but which the supply cannot tie to
  the caller's earlier bytes) and the invariant. So the invariant must record it at a program step between
  the loop and the truncate. Proposed, no type change: an upgrade law **`walLentRes_pendStop`** (`walPendTok
  dir γ k` and `TailPend lay` of `Ls !! dir` ==∗ `walLentTok dir γ k`), with the kind `false` meaning "lent:
  F-Z or `TailPend`": `ZerosOk`'s clause for a kind-`false` entry `TailZeros lay ∨ TailPend lay` (for `M !!
  dir = none` still `TailZeros`), `TailZK (some (_, false)) := TailZeros ∨ TailPend`, `walLentRes_unlend`
  taking F-Z of the layout (its only user is the option (d) flow, which the fdatasync's `walLentRes_unpend`,
  generalized to both kinds, replaces), `walLentRes_insert_same` gaining `TailPend lay → TailZeros lay' ∨
  TailPend lay'` (`TailAccW`: from `wr' = lay.wr`, `old`/`z0` kept; `TailAcc`/`TailSyncIdle` hold the key,
  not lent). The program step: `ZeroToEnd.specWalTail`'s first step (`wp_notCrashed_acc`, as
  `walInv_lend`): the handle's `osBytes ½ bs` agree with the invariant's exact tail, whose bytes past `wr`
  are `old`'s (`ByteOk.val_unw`), so the spec's premise is on the handle's bytes: `∀ j < 8, (bs.getD (o0 +
  j) (0, [])).1 = 0` (in its `tm`, `TailMetaR` with the zero word). `ReadAll`'s obligation: the decoder
  stopped with `io.EOF` at `wr` over `gl.bs`'s values (`decStep … = .stop .eof`: no bytes left or a zero
  word; `shortLen` is `io.ErrUnexpectedEOF`, excluded by the mode check).
- **Not done**: task 2 (`walTailP`, `TailMetaR`/`TailMetaZ`, `walInvRegisterTailLaw` restated and proved),
  task 3/4 (`fallocSup`, the growing truncate's supply, `ZeroToEnd.specWalTail`): blocked on A and B, which
  change `WalAbsD` and `walLentRes` (a rebuild of most of the WAL); the coordinator's choice.

**Twenty-fifth session (branch `wal-tc15`, 2026-11-14): "registered, not yet zeroed", made.** Untrusted;
no trusted change. Task 1 done (the 31 leaves importing `Ghost.lean` build, 2833 jobs; `ReadAllReg` repaired for `walTailW`'s `LoWr`); tasks 2-3 (exact-start
`rzGrow_pure`/`rzLandG_pure`, `fallocSup`, the growing truncate's supply, `ZeroToEnd.specWalTail`) not
started; the two `ReadAll` hypotheses (`walInvRegisterTailLaw`, `ZeroToEnd.specWalTail`) not yet restated
(their statements below). `wal-save22`, `wal-readall23`, `wal-copy1` merged.
- **Ghost** (`Ghost.lean`): the lent map's value is `GName × Nat × Bool` (the kind); **`walLentTokB dir γ
  k p`**, `walLentTok dir γ k` its `p = false` (lent by the key's holder; statements unchanged) and
  **`walPendTok dir γ k`** its `p = true` (registered, not yet zeroed); `walLentTok_lookup`/`_insert`/
  `_delete` take `p`.
- **Invariant** (`Inv.lean`): **`TailZ0 lay := TailZeros lay ∨ lay.wr = lay.z0`** is now `walTailsRes`'s
  per-tail fact (was `TailZeros`). F-Z moved into `walLentRes`: **`ZerosOk T Ls M`** (every registered tail
  whose lent entry is not pending, `NotPend M dir`, has `TailZeros`) and **`IdleZ0 T Ls`** (every
  unregistered tail has `TailZ0`: a crash's `wr = z0`, `Create`'s F-Z, `Close`'s F-Z). `LentOk` reads
  `x.2.1`. **`TailZK ok lay`** (`TailZeros`, or `TailZ0` for `ok = some (k, true)`), `TailZK.zeros`/`.z0`.
- **Laws**: **`walLentRes_zeros`** (the key's holder reads `TailZeros`; used by `walInvBody_tail`, `Append`,
  `walTailsRes_zeros`), **`walLentRes_regPend`** (`T` gains `dir`, the key into the invariant, the holder
  gets `walPendTok dir γ |old|`), **`walLentRes_unpend`** (`walPendTok dir γ k -∗ walLentRes T Ls ==∗
  walTailKey dir γ ∗ ∀ lay', ⌜TailZeros lay'⌝ -∗ walLentRes T (<[dir := lay']> Ls)`: the token→key step, to
  be used inside the window fdatasync's commit, `syncLayW`, whose `TailZeros` holds from `wr = z0` as well
  as from F-Z), **`walLentRes_idle`**; `_init`, `_mono`, `_insert_same` (new premises `hz : TailZeros lay →
  TailZeros lay'`, `hz0 : T !! dir = none → TailZ0 lay → TailZ0 lay'`), `_insert_new` (`hz`, `hz0`), `_insert_key`/
  `_free`/`_reg` (F-Z of the new layout), `_lookup` (also F-Z for `p = false`).
- **The registration**: **`walTailsRes_registerPend`** (`TailReg.lean`): `walTailsRes C Mr s Ls F -∗
  walTailsFrag ∅ ==∗ ∃ γ, ⌜TailZ0 lay⌝ ∗ walTailsRes … ∗ walTailsFrag {dir ↦ γ} ∗ walPendTok dir γ |lay.old|
  ∗ ghostVar γ ½ (tailG d lay g.ino (F !! g.ino))`, premises `s.wal !! dir = some d ∧ Ls !! dir = some lay ∧
  lay.segs.getLast? = some g ∧ TailBound C Mr d lay` (no zero premise: `IdleZ0` gives `TailZ0`).
  `walTailsRes_register` (F-Z, the key) stays for `Create`.
- **Stepping**: `walTailKeyL dir γ : Option (Nat × Bool) → IProp` (`some (k, p)`: `walLentTokB`);
  `walInvBody_tailW`'s pure facts give `TailZK ok lay` and `∀ k p, ok = some (k, p) → |old| = k`; its
  continuation takes **`wr' = lay.wr ∨ TailZeros lay`** (a pending tail's `wr = z0` kept). `walTail_truncSup`
  takes **`hok : ∀ k, ok ≠ some (k, true)`** (see the finding).
- **Found (blocks the pending flow's resize supplies)**: `rzStart_pure`'s crash step (`crashOkA_rzStart` →
  `crashTo_tailL`, `tail_zero_cand`; and `h.zeroPast … hZ`) uses F-Z of the exact tail: every byte from `wr`
  on has the zero among its candidates. A crashed tail's `old` past `z0 = wr` is unknown (a torn frame), so
  `ZeroToEnd`'s truncate to `wr` from it makes images (old bytes mixed with the truncate's zeros) that W1 over
  the exact tail's candidates does not cover. `ZeroToEnd.specWalTail` over `walPendTok` needs a crash step
  for the truncate from a `TailZ0`-only exact tail: the images past `wr` are then bytes the reader at `z0`
  already stopped on, mixed with zeros, which W1 says nothing of (W1 is over candidates). Options: (i) a W1
  fact on the crash image's bytes past `z0` (`WalsStart`: the reader stops at `z0` on every mix of them with
  zeros: a torn-entry argument, as etcd's `isTornEntry`), carried in the invariant for pending tails; (ii)
  restrict to a model fact (a truncate's crash zeros whole sectors from the new size: `fsExt`'s semantics,
  trusted, user). Coordinator decision.

**Twenty-fourth session (branch `wal-tc14`, 2026-11-14): option (d), the lent tails; the old-length map
removed.** Untrusted; no trusted change. Task 1 done (builds); tasks 2-4 not done (task 2 designed below; 3-4
wait on task 2 and on supplies not started). `wal-save21` merged.
- **The map is removed** (`walOldsAuth`/`walOldFrag`/`OldOk`/`OldStep`/`walOldsRes`, and `wal-save21`'s
  `walOldOpt` arguments of `walInvBody_sync`, `wp_tailFsync`, `syscall.Fdatasync.wp_tail`,
  `fileutil.Fdatasync.wp_tailW`, `syncLay_any`'s `hold`/`hLo`): (d) does not need it. `walInvBody_tailW` is no
  longer an update.
- **Ghost** (`Ghost.lean`): `WalGS.γl`; **`walLentAuth M`** (`M : GMap GoString (GName × Nat)`, exclusive
  elements), **`walLentTok dir γ k`** (the tail of `dir`, record `γ`, lent, `|old| = k`), `_lookup`/`_insert`/
  `_delete`; **`walTailKey_excl`** (the key is exclusive); `walGhost_init` returns `walLentAuth ∅`.
- **Invariant** (`Inv.lean`): **`walLentRes T Ls := ∃ M, walLentAuth M ∗ [∗map] dir ↦ x ∈ M, ⌜LentOk T Ls dir
  x⌝ ∗ walTailKey dir x.1`** (`LentOk`: registered at `x.1`, `|old| = x.2`), a framed conjunct of `walTailsRes`
  (its last). While lent the invariant holds the tail's key, so no step needing the key (an append, a cut, the
  window's fdatasync, `Close`) runs. Laws: `_init`, `_mono`, **`_insert_same`** (a layout replaced, `old` as long:
  every tail step but a cut and the window's fdatasync), `_insert_new` (`Create`), **`_notLent`**/**`_insert_key`**/
  **`_free`** (the key's holder: the tail is not lent, any new layout), `_reg`, `_unreg` (`Close`, with the key),
  **`_lookup`** (the token: `LentOk`), **`_lend`**, **`_unlend`**. Threaded through every site of `walTailsRes`
  (`TailAcc`, `TailAccW`, `TailSyncIdle`, `CreateAuLemmas`: `_insert_same`/`_insert_new`; `CutAuLemmas`'s
  `walTailsRes_cut`: `_free`; `CloseLaw`: `_unreg`; `TailReg`: `_reg`; `Crash`: `_init`; the rest framed).
- **Stepping a lent tail**: **`walTailKeyL dir γ ok`** (`TailAccW.lean`: `none` the key, `some k` the token),
  **`walTailKeyL_lookup`**; **`walInvBody_tailW`** now takes and returns `walTailKeyL dir γ ok` (new argument
  `ok`) and its pure facts end in `∀ k, ok = some k → lay.old.length = k`. **`walTail_truncSup`**,
  `walTail_truncFin`, `truncStartP`, `truncFinP` take `ok` (`K = walTailKeyL dir γ ok ∗ tailVar …`);
  `os.File.Truncate.wp_specWalTail` uses `ok := none` (`walTailKeyL_none`).
- **Lending** (`TailLend.lean`, new, proved): **`walAbsD_old_exact`** (an exact last segment's `|old|` is its
  size), **`walInvBody_lend`** (key + idle record + the program's `osMeta ½ m` with `m.lo = m.size = m.hi` ⟹
  `walLentTok dir γ m.size`), **`walInvBody_unlend`**, and their `walInv`/`notCrashed` forms **`walInv_lend`**,
  **`walInv_unlend`** (at any program step: `wp_notCrashed_acc`).
- *Why the lending is at a program step, not at a supply's commit*: a supply quantifies over the `OsMeta`
  each attempt finds, so its first commit cannot tell it is the first (exact) one; the lend must come from
  the handle's exact `TailMeta`, before `ZeroToEnd`. And the post of a spec of `ZeroToEnd`'s call is at a
  value (no `notCrashed`), so the un-lend is the caller's, at its next step.
- **Task 2 (weaker registration) not done; found**: an entry fact `TailZeros lay ∨ lay.wr = lay.z0` alone is
  not enough: appends need `TailZeros` (`walsOk_tail`: past `z0` the stream grows over `old`), and nothing
  stops an append between registration and the fdatasync after `ZeroToEnd`; and an un-lend requiring
  `TailZeros` would come after the fdatasync, which needs the key. Design (next session): the entry's fact
  `TailZeros lay ∨ lay.wr = lay.z0`; `walLentRes` gains `∀ dir γ lay, T !! dir = some γ → M !! dir = none →
  Ls !! dir = some lay → TailZeros lay ∨ ZeroPending` with the pending state a second kind of lent element
  (`M`'s value `Option Nat` for "registered, not yet zeroed": the key in the invariant, the handle holding a
  token that allows the resize steps and the window's fdatasync, which restores `TailZeros` by
  `tailZeros_syncW` from `wr = z0`, and an un-lend only from `TailZeros`). `ReadAll` would register in that
  mode (`walTailsRes_register` with the disjunction, returning the token, not the key), and `specWalTail`
  and the fdatasync after it take the token.

**Twenty-third session (branch `wal-tc13`, 2026-11-14): the tails' old-length map (option (a)); found: it is not
fixed per `(dir, cuts)` once the window's fdatasync lands, and the growth supplies still need `tg ≤ hi`.**
Untrusted; no trusted change. Task 1 done as decided (builds); tasks 2 and 3 not done (blocked: I3b, `wal-tc13` entry).
- **Ghost** (`Ghost.lean`): `WalGS.γo`; **`walOldsAuth M`** (a ghost map `(dir, cuts) ↦ k` with persistent elements and
  a copy of each, as `walDirKeysAuth`), **`walOldFrag dir cuts k`** (persistent), `walOldFrag_lookup`/`_agree`/`_insert`,
  `walOldsAuth_get`; `walGhost_init` also returns `walOldsAuth ∅` (`Crash.lean`'s `walStart` carries it).
- **Invariant** (`Inv.lean`): **`OldOk M Ls`** (each element `(dir, c) ↦ k` is of a directory of `Ls` whose cuts extend
  `c`, `k = |old|` while the cuts are `c`), `OldOk.empty`/`insert_ext`/`insert_same`/`insert_new`; **`OldStep lay lay'`**
  (cuts extended, `old` as long while they stay; `.same`, `.cut`); **`walOldsRes Ls := ∃ M, walOldsAuth M ∗ ⌜OldOk M Ls⌝`**,
  `walOldsRes_init`/`_insert_ext`/`_insert_same`/`_insert_new`/`_step`, **`walOldsRes_mint`** (hands out `walOldFrag dir
  lay.cuts |lay.old|`), **`walOldsRes_agree`**. **Placement**: a framed conjunct of `walTailsRes` (its last, inside `∃ T`),
  not of `walInvBody`: only the steps that change `Ls` handle `walTailsRes` (18 sites), against 45 destructurings of
  `walInvBody` that frame `Htl` whole and stay unchanged.
- **Statement changes**: `walInvBody_tailW` is now an update (`==∗`) and also returns `walOldFrag dir lay.cuts
  |lay.old|` (minted at the access; `TruncSup`'s two uses `imod` it); `walTailsRes_cut`'s continuation takes `OldStep lay
  lay'` (`CutAu`: `OldStep.cut`; `TailSync`'s two uses: `OldStep.same rfl rfl`). Repaired: `TailAcc`, `TailAccW`,
  `CutAuLemmas`, `CreateAuLemmas` (`insert_new`), `TailSyncIdle` (`syncLay`: same), `Crash`, and the lookups that keep `Ls`
  (`CutSync`, `TailSync`, `TailReg`, `TailLenLb`, `CloseLaw`, `ReadAllLaws`, `Append`, `Inv`'s `walTailsRes_mono`/`_none`).
- **Found (blocks tasks 2-3): `|old|` is not fixed per `(dir, cuts)`.** `TailSyncWin.syncLayW` (`wal-save19`, not yet a
  step) sets `old := old.take wr ++ replicate (|bs| - wr) 0`, of length `|bs|`, cuts unchanged: shorter than `old` whenever
  the window's bytes are (cut's truncate to `wr`, then its fdatasync; or writes past the size short of `old`). `TailLast`
  forces it (`|bs| = |old|` for an exact tail). Once that step is wired through `walTailsRes_cut`, `OldStep` fails there,
  and no persistent value can survive it (a later `ReadAll` of the same cuts in the generation sees the shorter `old`).
  **Do not merge this branch's invariant change into `wal-int` before the coordinator decides** (I3b, `wal-tc13`).
- *Build*: the 181 importers of `Ghost.lean` build (`lake build` of their leaves, 2818 jobs) but `WAL__Close` and `WAL__CloseOpening`, which fail at `wal-int`'s merge independently of this change (`iexact: cannot unify zapLoggerOk lg2 and ⌜lg2 ≠ null⌝`, lines 220/281; neither mentions `walTailsRes`).
- **Also found: `tg ≤ hi` cannot go into the map** (the coordinator's suggestion): `hi` changes at every resize and
  every fdatasync (`OsMeta.synced` makes it the size), so no persistent element can carry it. Neither the tie nor the
  invariant gives it at the growth commits (a window found with `hi < tg` is allowed by `WalAbsD`).

**Twenty-second session (branch `wal-tc12`, 2026-11-14): the three extension facts; `PcKeep`, `preGrownH`'s `Z`,
`ZteMeta`; the growth supplies blocked on the tail's old length.** Untrusted (`GooseLang/Ext/Fs` WP specs, not
`Impl.lean`). Tasks 1 and 2 done; task 3 not started (designed, blocked: I3b, `wal-tc12` entry).
- **Extension** (`Falloc.lean`, `Truncate.lean`): `wp_osFallocStart`'s continuation takes `⌜0 < n ∧ m.TcZ⌝` (from
  `wp_osResizeStart`); `wp_osFallocFinishK`'s not-landed arm is `rsUndoneK keep false` (`resize_undone_worldK`);
  `rsDone`/`rsDoneK`'s pure fact gains `∀ j c, m.pc (m.size + j) = some c → j < zs.length → zs[j]? = some c`
  (`resize_done_worldK`, from `RsFacts.hcandP`). Users: destructurings `⟨hl, hzz⟩` → `⟨hl, hzz, -⟩` (`Zeros.lean`,
  `SegLog`), `CrashStOps` (`⟨hzs.1, hzs.2.1⟩`), the `FileOps` (`%_`). `ResizeAuW.wp_osFallocStart_auW`'s commit and
  `FallocateAu.fallocAuW`'s receive `rsTok … ∗ ⌜0 < n ∧ m.TcZ⌝`; `ResizeAu.rsOutF`'s undone arm `rsUndoneK
  m.cut.isNone false`; `fallocOutH`'s `∃ tc rz, ⌜TcKnowsF m tg m.size tc⌝ ∗ osMeta ½ ((m.announce …).withTc tc rz)`.
- **`PcKeep m m'`** (`LinuxFs/Proof/os/PcKeep.lean`, new, pure): `m'.pc` known wherever `m.pc` was, past both sizes;
  `refl`, `trans` (through a middle state no longer than one end), **`PcKeep.of_tc`** (any outcome of the size `sz'` with
  the announcement's `zf` whose `tc` knows `rsTail`'s domain: `TcKnows`, `TcKnowsF`).
- **`preGrownH i m w Z`** (`DefsAu.lean`), as `wal-save18`'s `preGrown`: `PcKeep m m'` and `Z → m'.ZeroPg`;
  `preGrownH_mono`, `preGrownH_same` (`Z → m.ZeroPg`), `preGrownH_trans` (`PcKeep m m1`), `fallocDoneH_preGrownH`
  (`m.size ≤ w ≤ tg`, `Z → m.ZeroPg`, `zeroPg_rsPost_false`), `fallocOutH_preGrownH` (`Z := e = 0 ∧ m.ZeroPg`),
  `ftDoneH_preGrownH` (`Z → m.ZfGe`), `ftUndoneH_preGrownH` (`Z := False`). Spec posts (ledger): `preallocExtend.specAu`
  `(err = nil ∧ m.ZeroPg)`, `preallocExtendTrunc.specAu` `(err = nil ∧ m.ZfGe)`, `Preallocate.specAu` (`preallocPostH`)
  `(err = nil ∧ m.ZeroPg)`.
- **`ZteMeta m m' := PcKeep m m' ∧ (m.ZfGe → m'.ZeroPg)`** on `ZeroToEnd.specAu`'s success post (ledger: adopted,
  simplified: `ZeroPg` replaces the proposal's `zf` bound and `cz` clause; with `TailZ m` and `m'.size = m.size` it gives
  `TailZ m'`, a lemma still to write beside `specWalTail`). `ftDoneH_shrunk` gives the truncate's `PcKeep`/`ZeroPg`; `TailZ.zte` (`ZteTailZ.lean`) proved.
- **Found: the growth supplies cannot be built with the tie `walTailKey dir γ ∗ tailVar γ (H, md, cuts, wr, i,
  none)`.** At the start's commit (state `g0` found, target `tg` = the size `ZeroToEnd` found) `rzGrow_pure` needs `tg ≤
  g0.om.hi` and `min g0.om.lo tg ≤ wr`; at the landing `walAbsD_rzLandG` needs `w ≤ |lay.old|` (`w = tg` on success).
  The supplies quantify over the state; `fallocSup` gives `m0.size ≤ tg` only, `os.truncSup` not even that (a growing
  truncate's supply meets any state). `TailWin` gives `|bs| ≤ |old|`, `wr ≤ |old|`, `winLo` `lo ≤ wr` (window); nothing
  relates `tg` to `|old|` or `hi`. In the flow they hold (`tg = |old| = hi` at `ReadAll`'s exact tail; the truncate to
  `wr` and the growths keep `hi`), but the supply cannot see it. I3b, `wal-tc12` entry, for the options.


**Twenty-first session (branch `wal-tc11`, 2026-11-14): the growth's pure pieces; `TcKnowsF`; the supplies blocked
on the extension.** Untrusted; `Impl.lean` unchanged. Task 1 done (pure), task 2 done for `fallocDoneH` (the
`ZeroToEnd` post's fact designed, not made), task 3 not started (blocked: I3b, `wal-tc11` entry).
- **`RzGrow.lean`** (new, pure, proved): the growth's first step is `rzSeg g0 tr tg n` with `size ≤ tg ≤ hi` (bytes
  unchanged): `rzMeta_pcG` (`rzMeta_pc` for either kind), **`segBytesX_rzGrow`** (the growth form of
  `segBytesX_rzSeg`: as long, `RzCands`), `fileCrashedR_rzMeta_grow` (`tg ≤ hi`: no longer crash; `OsMeta.TcZ`),
  **`crashOkA_rzGrow`**, **`tailCrashStep_rzGrow`**, `rzGrow_pure` (with `walAbsD_rzStart`: `wr ≤ tg`, `min lo tg ≤ wr`).
  The landing with the size `w` (`size ≤ w ≤ tg`): **`rzLandG g0 tr tg w n zs`** (`OsMeta` `rsPostK true tr … w n []`,
  bytes `g0.bs ++ growBytes n zs`, `rsDoneK`'s), `fileCrashedR_rzLandG`, `pcRunN_add`, **`segBytesX_rzLandG`** (the
  in-flight `segBytesX` is a prefix of the landed one's), **`crashOkA_rzLandG`**, `tailCrashStep_rzLandG`,
  **`walAbsD_rzLandG`** (a window; `hlo : min lo tg ≤ wr`, `hold : w ≤ |old|`), `rzLandG_pure`. The landing takes
  **`hzs`: the bytes grown over have the candidates the `OsMeta` knew** (`m.pc (size + j) = some c → zs[j]? = some c`).
- **`TcKnowsF`** (`FallocateAu.lean`; ledger 2026-11-14): `fallocDoneH` carries `⌜TcKnowsF m tg w tc⌝` (`rsTail
  false`'s domain); `TcKnowsF.rsTail`; `DefsAu.fallocDoneH_preGrownH` repaired. `ZeroToEnd.specAu`'s post fact
  `ZteMeta` (the pc domain past the size kept, `cz` kept, `zf` within `max z0 (pageEnd size)`) proposed in the ledger,
  not made: `preGrownH` must carry the facts through `Preallocate.specAu` first.

**Twentieth session (branch `wal-tc10`, 2026-11-14): `TcKnows`; the truncate supply; `specWalTail` proved.**
Untrusted; `Impl.lean` unchanged. Tasks 1 and 2 done; task 3 (growth, `ZeroToEnd`'s instance) not started (I3b,
`wal-tc10` entry, for what it needs).
- **`TcKnows`** (`LinuxFs/Proof/os/TcKnows.lean`, new, pure): `TcKnows m tg sz' tc := ∀ b, (rsTail true m tg sz' 0 []
  !! b).isSome → (tc !! b).isSome` (the domain of the outcome's `rsTail`; `rsTail_isSome_iff` unfolds it). It takes the
  size the truncate left, `sz'`, against the proposal's three arguments: the not-landed outcome (`rsUnMeta true`, `tc =
  rsTail … m.size n []`) keeps no candidates of the bytes in `[tg, size)`, which are below its size. Laws:
  `TcKnows.rsTail` (the supply's), `TcKnows.mono`, and the retry loop's `TcKnows.of_announce` (an attempt from a
  not-landed state, `(m.announce …).withTc tc0 rz0` with `TcKnows m tg m.size tc0`) and `TcKnows.of_rsPost` (from a
  landed one, `(rsPost true m tg tg).withTc tc0 rz0` with `TcKnows m tg tg tc0`).
- **Spec change (ledger 2026-11-14)**: `os.ftDoneH p m tg zs` carries `⌜TcKnows m tg tg tc⌝`, `os.ftUndoneH p m tg xs'`
  `⌜TcKnows m tg m.size tc⌝`. `File.Truncate.wp_proofAu`: `ftStateH`'s announced state carries `TcKnows m tg m.size tc`;
  `os.ftDoneH_of`/`os.truncOutH_again` take the fact of the state. Repaired: `DefsAu`, `preallocExtendTruncAu`,
  `ZeroToEndAu` (destructuring only). A supply for a file with a sync cut could not prove it (its outcome keeps the
  announcement's `tc`); none exists, and the WAL's segments have no cut (`WalsOk`).
- **`TruncSupPure.lean`** (new, pure): `tailLay_self`, `walsOk_self` (a step that leaves the layout), `rzStart_pure`
  (`walsOk_tailA`/`dirKeysOk_tailA` with `tailCrashStep_rzStart`, `walAbsD_rzStart`), `rzLand_pure` (with
  `tailCrashStep_rzLand`, `walAbsD_rzLand`).
- **`TruncSup.lean`** (new, proved): **`walTail_truncSup`** (`walInv … ⊢ os.truncSup (walTailKey dir γ ∗ tailVar γ (H,
  md, cuts, wr, i, none)) i wr`). The start's update (`truncStartP`: the tie and the caller's halves): `walInvBody_tailW`,
  agreement (`g0.om = m0`, `g0.bs.drop wr = xs0`, `osBytes_takeDrop`), the whole `OsMeta` and bytes cut off lent; the
  commit puts the token in `F` (`⟨t, 0, [], n, g0.om, g0.bs, some (true, wr)⟩`, `rzSeg_ok`), both halves of the record
  to the change in flight, and its update is **`walTail_truncFin`**, whose caller part (`truncFinP`) carries the start's
  `m0.size ≤ m0.hi ∧ wr ≤ m0.size` (the landing's `crashOkA_rzLand` needs `size ≤ hi` of the state before, which the
  in-flight layout does not give when nothing is cut off). The finish: landed, the tail `rzLand g0' wr n` for `g0' := {
  g1 with om := m0, bs := bs0 }` (`rzSeg_of_okR`: `g1 = rzSeg g0' true wr n`), the caller's `ftDoneH` with `tc :=
  (rsPostK true true …).tc` (`TcKnows.rsTail`), `zs = []`; not landed, the in-flight layout kept idle (`segRes g1`: the
  kept take-half joined with half of `rsAnn n xs0`, `osBytes_app0`), the caller's `ftUndoneH` with `tc := rsTail … m0.size
  n []`; the record back to idle. Aborts: **`walInvBody_tailW_same`**. Local copies `tailVar_upd`/`osMeta_agree2`
  (`TailWriter`'s carry its section's `go.Semantics`, `os.Assumptions`).
- **`TruncWalTail.lean`** (new, proved): **`os.File.Truncate.wp_specWalTail`** (`os.File.Truncate.specAu →
  os.File.Truncate.specWalTail Mr`): the handle's bytes split at `wr`, the call with the supply; success: the tail's
  `OsMeta` `(rsPost true m wr wr).withTc tc rz`, bytes `bs.take wr`, `TailMetaW` with **`TailZ.rsPost_tc`** (`TailZ m`,
  `wr ≤ size`, `TcKnows m wr wr tc` give `TailZ` of the landing: zeros from `max z0 (pageEnd size)`, `cz` raised to
  `pageEnd size`). **`WAL.cut.wp_proof` takes `os.File.Truncate.specAu` in place of `specWalTail`.**

**Thirteenth session (branch `wal-path13`, 2026-11-14; G-spine, the claim on each WAL name).** A path to
`dir = r/nm` is a spine through a fraction of a claim on `nm` alone (`osPathS_child`); `nm` sat only in the
area or creating claim. Design (internal invariant, no client-visible ghost state; `Inv.lean`, `Ghost.lean`):
- **`walNamesRes R jr r Ls`**, a framed conjunct appended to `walInvBody` (independent of the claims list,
  so steps changing other claims frame it). Each **registered** WAL name `nm ∈ Wn` has its own claim
  `(jr, .only [nm], hn)`: the invariant's half among `cl` (`osClaims`), and here `nameShare jr Ls nm`, a
  fraction of the program's half with `NameOk nm`, `walNameOk nm` and `hn.cur !! nm = some (.dir lay.j)` for
  the layout named `nm`; plus `∃ q, osPathS R r (own q) jr`, a fraction of the area's spine. Both are **lent
  by halves and never returned**: a registered name's claim never changes again in the generation (no WAL
  function renames onto or away from a registered name; a change needs the whole claim), and the spine lets
  a handle keep a path past the call that opened it (`Open`/`Create` give their caller's spine back whole).
- **Registration pending** (`WalGS.γnm`, `walNamesAuth o`/`walNamesFrag o`, `Option GoString`): every present
  WAL is registered but `o`, the one `Create` committed (`walNamesRes_addWal`, at `CreateAu`'s commit, which
  takes the lock: `walCreateQ (some _)` now carries `walNamesFrag (some dir)`) and has not yet split out
  (until then `Create` holds the whole program half, which its cleanup's rename needs). **`walUnlockedTok`
  gains `walNamesFrag none`**; `walUnlockedTok_lock`/`walLockedTok_unlock`, `walParked_lock`/`_unlock` output/
  take it; `walInvBody_pin`'s post gains `walNamesFrag none`, `walInvBody_unpin` takes it (wal-read's pin and
  error arms thread it); `ExistPin` carries it beside `walTailsFrag ∅`.
- **Split names** (`WalGS.γnw`, `walSplitAuth Wn` here, `walSplitFrag Wn` for `walAreaRes`, not yet added there):
  each `nm ∈ Wn` is a present WAL's; every present WAL but `o` has its name in `Wn`.
- **The law** (`NameClaims.lean`, proved): **`walInvBody_dirPath`** (`walInvBody s -∗ walNamesFrag none -∗
  walDirKey dir j X ==∗ walInvBody s ∗ walNamesFrag none ∗ ∃ q, osPathS R dir (own q) j`) and its program-step
  form **`walInv_dirPath`** (`walInv -∗ notCrashed -∗ walNamesFrag none -∗ walDirKey dir j X ={⊤}=∗ notCrashed ∗
  walNamesFrag none ∗ ∃ q, osPathS R dir (own q) j`). `OpenAtPin.lean`'s `WalDirPathLaw` follows with
  `walNamesFrag none` (from `walParked_lock` at the pin, or inside `walUnlockedTok`) framed in place of the
  area's spine. The path then serves `os.Open(dir)`/`ReadDir(dir)` (or `wal-enoent13`'s child forms).
- `walInv_alloc` (no callers yet): `harea` is now `WalsCreateOk jr cl` (each WAL name in some area claim);
  new premises `hnames` (each boot WAL's name has its own claim `.only [nm]`), `hnok` (`NameOk` of such names)
  and the deposited spine `osPathS R r (own qs) jr`; it registers the boot names (`nameClaimsOf`,
  `names_split_start`) and returns `walSplitFrag (nameClaimsOf …)`; its returned program halves leave out the
  name claims (`NameClaimOf`).
- **Not done** (for the next session): (1) `walAreaRes`'s fact `∀ nm, walNameOk nm → N.Mem nm` must become
  `N.Mem nm ∨ nm ∈ Wn` with `walSplitFrag Wn` added to it (`Create` then gets `N.Mem nm` for an absent WAL from
  `Wn ⊆` present); `Exist`'s present case and `walInvBody_areaAt` must then use the name claim (the law) instead
  of the area claim. (2) `Create`'s registration after the commit: split `.only [nm, nm.tmp]` into `.only [nm]`
  and `.only [nm.tmp]` (both halves, a program step), keep fractions for `renameWAL`'s pipeline/`OpenDir` and the
  handle, put the rest as a `nameShare`, add `nm` to `Wn` (`walSplit_set`), `walNames_set (some dir) → none`;
  `walInvBody_merge2`'s `b1` must then be an unregistered WAL name. (3) `renameWAL.spec`'s caller-supplied path
  law (`RenameWALOk`'s third conjunct) to discharge from (2). (4) The `WalsBounded s Ls` conjunct (metadata
  `< 2^41`, segments' `om.hi ≤ 0xffffffff000`; coordinator's decision) not added.

**Fourteenth session (branch `wal-path14`, 2026-11-14; G-spine continued).**
- **`walAreaRes` with the split names** (`CreateDefs.lean`): `∃ N h cl Wn, osNames jr N ½ h ∗ walSplitFrag Wn ∗
  ⌜∀ nm, walNameOk nm → N.Mem nm ∨ nm ∈ Wn⌝ ∗ …` (`AreaOk N h cl Wn`, `CreateArea.lean`). The predicate's text
  in the specs is unchanged (it is the plan's design: `walInv_alloc` already returns the `walSplitFrag`), but it
  now names `WalGS` (`walAreaRes` elaborates with `W`). `NameSplit.lean` (new): **`split_absent`** (no WAL at
  `r/nm` → `nm ∉ Wn`, so the area claim holds it), `split_present`, **`walNamesRes_splitOk`** (agreement),
  **`walNamesRes_lendAt`** (with `walNamesFrag none`, a present WAL's name claim and a spine fraction lent, kept).
- **Users repaired**: `walInvBody_absent`/`walInv_absent` (take `walSplitFrag Wn` and `N.Mem nm ∨ nm ∈ Wn`, return
  `N.Mem nm ∧ h.cur !! nm = none`); `walInvBody_areaAt` (post only the absent case, `N.Mem nm` included) and
  `walInv_openAt` (thread `walSplitFrag`); `create_abortTmp` (takes `N.Mem nm`, `walSplitFrag`); `Exist`:
  `walInvBody_existPin` reads a present WAL through the lent name claim (`ReadDir.specChildIs` with
  `Np = .only [nm]`) and returns the WAL's key; `walInvBody_existUnpin`/`walInv_existEnd` find the directory's claim
  by the key (`walDirKey`, `DirKeysOk`) instead of the area claim (no `walPast`, `N`, `h` any more).
  `Create`, `Exist`, `openAtIndex`, `Open`, `OpenForRead`, `renameWAL` build.
- **`openAtIndex` without `WalDirPathLaw`**: the pin's `walNamesFrag none` and `walInv_dirPath`. `Open` still
  takes `WalDirPathLaw` (its `OpenDir` step holds the lock inside `walReadH`'s `walReadTie`; the swap needs a
  lemma taking `walNamesFrag none` out of `walReadH` and back, not done).
- **`Create`'s split and registration** (`CreateSplit.lean`, new; proved, not yet used in `Create`'s body):
  **`walInvBody_dropT`** (`walInvBody_drop` with any lock token `T`, `walCreating_empty`; the area claim is no WAL
  directory's by `WalsAt`), **`coverOk_rekey`** + **`walInvBody_rekey`** (a claim of `jr` holding a WAL name
  rekeyed to a set of the same names: both halves, `osNames_rekey`, a covering change), **`walInv_splitNew`**
  (after the commit: the program's half of `.only [nm, nm.tmp]` becomes its half of `.only [nm]` (the invariant
  the other) and the whole `.only [nm.tmp]`, for `walInvBody_mergeIn` back into the area claim),
  **`walInvBody_register`**/**`walInv_register`** (`walNamesFrag (some dir)` → `none`, `Wn` → `nm :: Wn`, a
  fraction of the program's `.only [nm]` deposited as `nameShare`; the WAL present from a `walPast`).
  **Order inside `Create`** (found this session): the split right after the commit (inside `renameWAL`: the
  pipeline and `OpenDir` need paths, built by `osPathS_child` from fractions of the program's `.only [nm]`
  half); the registration only after the parent directory's fsync and close succeed, because the after-rename
  error arm's `cleanupWAL` renames `r/nm` away: `w.Close()` returns the lent fractions, and the rename needs the
  whole claim, i.e. a step taking back the invariant's half of an unregistered (`o = some dir`) name's claim (not
  written). `walInvBody_merge2` is then no longer what `Create` uses after the commit (the `.only [nm.tmp]` claim
  goes back by `mergeIn`).
- **Not done**: (1) `renameWAL.spec`'s law (`RenameWALOk`'s third conjunct) cannot be discharged as stated: it is
  a `={⊤}=∗` without `notCrashed` (so `walInv` cannot be opened to its body) and without the update's result
  `U (some x)` (whose `walLockedTok` is the lock token `walInv_splitNew` needs); proposed restatement (ledger
  first): `∀ x, Sp -∗ notCrashed -∗ U (some x) -∗ renDirOut … (some x) ={⊤}=∗ notCrashed ∗ U (some x) ∗ osPathS R
  dir dq J ∗ osPathS R dir dq J ∗ SpR x`, `dq` fixed by `Create` from a spine fraction it borrows beforehand
  (`os.qp_common` of that fraction and `¼`). (2) `Open`'s swap (above). (3) `WalsBounded` (coordinator,
  2026-11-14: the metadata half as a framed conjunct, the segments' `om.hi ≤ 0xffffffff000` as a named hypothesis
  until `wal-maxb14`'s model lemma lands; no `pipeFile` obligation) not started. (4) nil-receiver `File.Close`,
  `renameWALUnlock`, `renameWAL` not started.

**Fifteenth session (branch `wal-path15`, 2026-11-14; G-spine continued).**
- **`WalsBounded`** (`Inv.lean`): `walInvBody` gains a last framed conjunct `⌜WalsBounded s⌝` (every WAL's metadata
  `< 2^41`; on `s` only, not the layouts). Kept by every step through `walsBounded_upd` (an `absDiskUpd` keeping
  metadata: `setNamed`, `unlSt`), `walsBounded_insSame` (`walAppS`, `walSyncS`) and `walsBounded_ins` (a new WAL with
  a bounded metadata: `createSt`); established by `walCreate_osAUnc` (new premise `hmd : md.length < 2 ^ 41`, `Create`'s
  spec premise) and `walInv_alloc` (new premise `hbd : WalsBounded s`). Read with **`walInvBody_bounded`** (`ReadAll`'s).
  Every destructuring of `walInvBody` threads it (`…, Hnms, %Hbd⟩`; 22 modules, plus `ReadAllLaws`' `walInvBody_readIdle`).
- **The segments' half is not in the invariant** (`SegSize.lean`, new): `wp_segs_size` reads `g.om.size ≤ maxBytes`
  (`= 0xffffffff000`) off a list of `segRes` before a step (`Fs.wp_osMeta_size`, `wal-maxb14`); `openAtIndex` applies it
  right after the pin (`|g.bs| = g.om.size` from `WalAbsD.metas`). The bound on `om.hi` is not kept (a write's
  announcement raises it) and not needed. `walPinOut` drops its size clause; **`walInvBody_pinOut`** proves the pin;
  **`WalPinSized` deleted**, `walInv_openAt` and `openAtIndex.wp_proof` lose the hypothesis (the latter's are now its
  callees' specs and `WalDecEnvSupply`). (A named hypothesis `OsMetaSizeLaw`, the statement of `wp_osMeta_size`, stood in
  until `wal-maxb14` landed the same session.)
- **`Open` without `WalDirPathLaw`** (`Open.lean`): **`walReadH_namesOut`** takes the lock's `walNamesFrag none` (and the
  key) out of `walReadH` with the wand putting it back; `walInv_dirPath` at a step. **`WalDirPathLaw` deleted.**
- **`renameWAL.spec`'s spine law restated** (ledger 2026-11-14): with `notCrashed` and `U (some x)` in and out. Not yet
  discharged by `Create` (needs `walInv_splitNew` in `Create`'s update result) and `renameWAL` not proved.
- `os`'s package fact records `os.ErrInvalid` (`gen-init` `LFS_OS`, `os.errInvalid_of_pkgInit`) for the nil-receiver
  `File.Close` (W7-W12 log).

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
- **`wal-readall17`** (2026-11-14; **adopted provisionally, pending the user's review**; ledger "the readers'
  errors and `errors.Is`"): the `io.ReadFull` axiom's statement carries the reader's error evidence.
  `io.readerStream ri S E` has `E : List w8 → GoInterface → IProp GF` and returns `nil` or an error with
  `□ E (r ++ ys) err` (`io.errAt`); `io.ReadFull.spec` returns `io.readFullRes E eof ueof r0 ys len(buf) err`
  (all came and `nil`; or fewer and the reader's last error `e` with `□ E (r0 ++ ys) e`, `err = e` but
  `io.ErrUnexpectedEOF` for `e = io.EOF` after some bytes: Go's `ReadAtLeast`), the old pure post being
  its shadow (`io.readFullRes_pure`). Why: `errors.Is` of a reader's error is a heap fact (a `*PathError`'s
  `Err`), which the pure `E` could not carry, so the decoder's `isEofOk` had to claim it of every
  `*PathError`, false for `&PathError{Err: io.EOF}`. New hypothesis (true of Go, not an axiom):
  `errors.IsPathErrnoEof.spec`.
- **Corrected (coordinator, 2026-11-14, after the user asked why it is trusted):** only the leaf system call needs a
  model. `io.Copy`/`copyBuffer` (names-only in Perennial's `io`: `io.toml` translates only the types and errors) and
  `(*os.File).ReadFrom`/`WriteTo` (names-only in the part's `os`) are ordinary Go to translate and verify; the one
  kernel call they reach for file-to-file copies on Linux, `copy_file_range(2)` (via `internal/poll`), has no `fsExt`
  step. Plan: translate those (the `io` part a Perennial configuration change, or the part's copy), add an `fsExt`
  `CopyFileRange` step modelled as a `pwrite` of the source's bytes (crash candidates as a write's), with a Go example
  measured on C — that step pending the user's review. The hypothesis below stands until then.
  **Done in part (`wal-copy1`, 2026-11-14, "io.Copy log" at the end):** the part's `os` translates the dispatch
  (`File.ReadFrom`/`WriteTo`, `writeTo`, `generic*`, `getPollFDAndNetwork`, ...) and `poll.handleCopyFileRangeErr`;
  `copy_file_range(2)` is modelled with no new `fsExt` step, as the extension's `PRead` then `PWriteStart`/
  `PWriteFinish` (`model.copyFileRangeRound`, **pending the user's review**, with three Go bodies made trusted because
  they touch `pfd`, absent from the trusted `file` layout; `examples/osfs/semantics/model_os_copy_file_range.go`,
  measured on C). `io.Copy`/`copyBuffer` still have no bodies (Perennial's `io`), so the hypothesis stays until
  Perennial translates them (`notes/perennial-changes.md`, "`io.Copy`/`copyBuffer` without bodies").
- **`io.Copy(bf, f)` of two `*os.File`s** (`wal-repair19`, 2026-11-14; **a missing trusted model, pending the
  user**): `Repair` copies the torn segment into its `.broken` file with `io.Copy`, which on `*os.File` goes through
  `File.ReadFrom` (Linux: `copy_file_range`/`splice`/`sendfile`, then a generic loop) or `File.WriteTo`: neither is
  translated nor modelled (§4.3). `Repair.wp_proof` will take it as a hypothesis: a triple over the destination's whole
  file (`osMeta`/`osBytes` of `bf`'s inode) and the source's stream from its offset (the program's halves of the
  segment, the offset 0 after `Seek`), returning `(n, err)` with the destination's bytes extended by a prefix of the
  source's (any prefix on an error; the whole rest on `nil`) and the source's offset moved by `n`; the source's bytes
  unchanged. Only the `.broken` file's content depends on it, which `Repair`'s spec does not mention (it claims nothing
  past the WAL's state), so a weaker hypothesis (the destination file changed arbitrarily within its claim) also
  suffices. To be replaced by a model of `File.ReadFrom`'s generic path once the user decides.

- **`(*walpb.Record).Reset`** (`wal-leaf2`, 2026-11-14; **a trusted model, decided provisionally by the
  coordinator, pending the user's review**): `Record.Reset.impl`
  (`LinuxFs/TrustedCode/go_etcd_io/etcd/server/v3/storage/wal/walpb.lean`) is Go's `*x = Record{}`; Go's
  `MessageStateOf(x).StoreMessageInfo(mi)` is left out (a protobuf-runtime cache that `ProtoReflect` fills with
  the same `mi` when `nil`). `walpb.Record.Reset.spec` is proved over it (`Record__Reset.lean`). Replaces the
  hypothesis; to be dropped if the user prefers a translation of the protobuf runtime's message state.

- **`(*os.File).Close` of a closed `*File`** (`wal-create18`, 2026-11-14; **a trusted model change, decided
  provisionally by the coordinator, pending the user's review**; merged on `wal-create19`):
  `File.Close.impl` (`LinuxFs/TrustedCode/os.lean`) returns `model.pathError "close" name (load os.ErrClosed)`
  without a system call when the fd field is -1 (only `Close` sets it), as Go's `file.close` does (`pfd.Close`'s
  `increfAndClose` fails, `poll.ErrFileClosing` mapped to `ErrClosed`). Go example
  `examples/osfs/semantics/model_os_close_twice.go`, **measured on configuration C** (`TestCloseTwice`:
  `&PathError{"close", name, ErrClosed}`, and a file opened after the first close, which may reuse the fd number,
  stays open). The WIP also makes the part's `io/fs` and `os` facts record `ErrClosed` as `fmtErrorOk`
  (`etc/gen-init.py`'s `LFS_IOFS`/`LFS_OS`, `errorString_fmtErrorOk` of internal/oserror's error;
  `os.errClosed_of_pkgInit`, `os.errExist_of_pkgInit`). **Was blocked** (unblocked by option (a), `wal-create19`: the
  four predicates are `gFdElem`, carrying `0 ≤ fd.toInt`; `specClosed` proved, its pre with `isPkgInit pkg_id.os`): the four proofs of `Close` on an open fd
  (`File.Close.wp_proof`, `wp_dir`, `wp_dirS`, `wp_outS`) now meet the `fd = -1` test before `FdKind` and must
  refute it, but nothing they hold says an open fd is not -1 (`osFd`/`osDirFd`/`osDirFdS`/`osOutFd` are bare
  ghost elements; the state's `FdFree` has `0 ≤ fd.toInt`, which no ghost fact carries). Options: (a) the four
  extension predicates carry `⌜0 ≤ fd.toInt⌝` (their producers, the extension's `Open` lemmas, already prove it;
  about 60 `unfold` sites in `GooseLang/Ext/Fs` to adjust, and the whole part rebuilt); (b) `os.ownFile` carries
  `⌜0 ≤ fd.toInt⌝` and a closed file gets its own predicate (`os.ownFileClosed f name`; about 80 `unfold
  os.ownFile` sites in `LinuxFs/Proof`, `Close`'s post restated); (c) an `isPkgInit pkg_id.os` premise on the four
  `Close` specs, so their `-1` branch runs (133 call sites; `wp_dir`'s `rdBack` post is not provable there).
  (a) is the most local for callers. The coordinator's call; `os.File.Close.specClosed` stays a hypothesis of
  `Create.wp_proof` meanwhile.

**Pending the user's review (trusted or axiomatic), all off `lean`:** the closed-file `(*os.File).Close` model (2026-11-14, `File.Close.impl`'s fd -1 branch, above; merged on `wal-create19`); the trusted model `walpb.Record.Reset.impl` (2026-11-14, `wal-leaf2`: `*x = Record{}`, the message-state store left out; its docstring, the "Leaf specs log (branch `wal-leaf2`)"); the `io.Copy`-of-`*os.File` hypothesis of
`Repair` (2026-11-14, above); the `io.ReadFull` axiom's restatement
with the reader's error evidence (2026-11-14, `wal-readall17`, above); the file-size bound of `fsExt` (2026-11-14, `Impl.lean`'s
`maxBytes`, ext4's `s_maxbytes` on C: `PWriteFinish`, `FtruncateFinish`, `FallocFinish`, `CrashFile`, `FsInit`;
`examples/osfs/semantics/data_maxbytes.go`, measured on C; W6 log, fourteenth session); the `ENOENT` rule of `fsExt`
(2026-11-14, `Impl.lean`'s `ENOENT`, `Open`/`DirReadNext`; `examples/osfs/semantics/meta_enoent.go`,
measured on C; the W7-W12 log); the fork fixes (§8,
`notes/wal-fsext-fork/`); W1 (the crash premise, `LinuxFs/.../wal/W1.lean`; the open question of torn
non-`Data` bytes, under investigation on `wal-bytemix`; amended 2026-11-14 so a resize's zeros do not
write a frame, restated exactly over the recorded resize stamps by `wal-tc4`, §2.5; it still excludes the rare crash
leaving an intended frame whose zero tail was not yet written, its docstring); the resize-stamp record `OsFile.rzs`
(bookkeeping, `wal-tc4`); the new `os`/`syscall` models and the
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

**Thirteenth session (branch `wal-path13`, 2026-11-14).** G-spine's claim design and path law (W1 log,
thirteenth session); `Create`'s body not advanced. **Correction to the twelfth session's renameWALUnlock
finding (blocker 2):** not real: the trusted model of `(*File).Close` returns `ErrInvalid` on a nil receiver
(`LinuxFs/TrustedCode/os.lean`, Go example `model_os_close_nil.go`), so `WAL.Close` with a nil `dirFile` is not
stuck; a nil-receiver case of `File.Close`'s spec (from the model) is what `renameWALUnlock` needs (not done).

**For `wal-create6` (the invariant's owner, 2026-11-13).** (1) `walAreaRes jr` gains `⌜∀ nm J, walNameOk nm →
h.cur !! tmpName nm = some (.dir J) → ∀ hJ, (J, NameSet.except [], hJ) ∈ cl → FilesOnly hJ.cur⌝` (a leftover
`nm.tmp` holds only files; `CreateDefs.lean`, importing `LinuxFs.Spec.os.RemoveAll`), for `os.RemoveAll.specDirS`
of a leftover `dir.tmp`. (2) The `walCreating` token is `walCreating dir N h J` and the minting must establish
`CreatingNew` (W1 log, seventh session, task 2). (3) `walCreate_osAUnc`'s commit (task 3) needs more of the
program: see the W1 log's task-3 entry.

**Fourteenth session (branch `wal-path14`, 2026-11-14).** `Create`'s area part through the split names
(`walInv_absent` gives `N.Mem nm` from the client's `walAbsent dir`); the post-commit split and the registration
proved as steps (`CreateSplit.lean`; W1 log, fourteenth session, for the order inside `Create` and why the
registration waits for the parent's fsync); the body not advanced (frontier `sorry` unchanged).

**Fifteenth session (branch `wal-path15`, 2026-11-14).** `walCreate_osAUnc` takes `md.length < 2 ^ 41` (the commit
establishes `WalsBounded`); `renameWAL.spec`'s `RenameWALOk` third conjunct restated (ledger) so that `Create` can
discharge it with `walInv_splitNew` (at the step after the rename, with `notCrashed` and the result's lock token);
the nil-receiver `File.Close` spec proved (W7-W12 log). `renameWALUnlock`, `renameWAL` and `Create`'s body not
advanced (frontier `sorry`s unchanged). Note: the stream-end fact `< 2^43` is gone from `walOpenWF`/`walHandleIn`
(`wal-maxb14`): `Create` does not establish it.

**Sixteenth session (branch `wal-create14`, 2026-11-14).**
- *Post-merge build check*: `openAtIndex`, `Open`, `OpenForRead`, `Exist`, `Create` built clean on `wal-int`
  `42d954d80a` (no fix needed).
- **`WAL.renameWAL.wp_proof` proved** (no `sorry`). Hypotheses: `os.RemoveAll.specAbsentN`, `os.Rename.specDirSnc`,
  `newFilePipeline.spec`, `fileutil.OpenDir.spec`, **`errors.AsLinkError.spec`** (new, `LinuxFs/Spec/errors/
  AsLinkError.lean`: `errors.As` of a `*os.LinkError` into a `**os.LinkError` returns `true`; Perennial's `errors.As.spec`
  asks for the whole tree even on a first match, `notes/perennial-changes.md` candidate), `renameWALUnlock.spec`.
  `RemoveAll`'s error exit gives the post's `U none` by committing the update with no effect (**`osAUnc_none`**, in
  the proof file); the spine law runs at the step after a committed rename.
- *Statement changes*: `os.Rename.specDirS`/`specDirSnc` post strengthened with **`os.renameErrOk err`** (nil or a
  `*LinkError`; proved, `Proof/os/Rename.lean`); `RenameWALOk` gains `dir.length < 2 ^ 59` (ledger).
- **Finding (`renameWALUnlock.spec` unprovable as stated; ledger 2026-11-14)**: its `Close` needs the encoder and
  the tail file (the coordinator's decision: the pre carries them; not yet made), its `Open`/`ReadAll` need
  `walAreaRes`, `walUnlockedTok` and an `AU` no generic `U` gives, and after a committed failed rename its second
  `os.Rename` has an absent source (no public spec). (2), (3) await a design.
- **`Create` advanced** past `createNewWALFile`: the success arm's `o = some`, `f.Seek(0, io.SeekEnd)` (the promoted
  method unfolded to the embedded `*os.File`'s, `os.File.Seek.wp_end`; restate `osMeta i` as `osMeta (openFd …).ino`
  before a spec on `d.ino`), its error exit, `fileutil.Preallocate(f.File, 64000000, true)` and its error exit;
  frontier `sorry` now after the preallocation (`preGrown i newMeta 64000000`: the 64 MB of zeros as `osZerosA`).
  Every error exit after the create is the macro **`create_seg_exit`** (`Create.lean`, unhygienic: the deferred
  `f.Close()` via **`wp_lockedClose`**, `CreateLocked.lean`, the segment's claim back, `RemoveAll(nm.tmp)`, the
  abort). New hypotheses of `Create.wp_proof`: `os.File.Close.spec`, `fileutil.Preallocate.spec`, `zap.Int64.spec`.
- *Next*: `w := &WAL{…}`, `newFileEncoder`, `saveCrc`, the metadata record, `SaveSnapshot.specPre`; then the commit
  (`walCreate_osAUnc`, its new `hzf` premise from the synced segment's `TailMeta`, after `SaveSnapshot`'s sync — check
  how its `g.bs` relates to the 64 MB `osZerosA`), the order after it (`walInv_splitNew` for `renameWAL`'s spine law,
  the parent fsync and close, `walInv_register`, `cleanupWAL`'s take-back, `mergeIn` of `.only [nm.tmp]`, the handle).

**Seventeenth session (branch `wal-create15`, 2026-11-14).**
- *Setup*: seeded from `wal-repair18`'s build (the seed named in the brief was older than `wal-int`'s
  `GooseLang/Ext/Fs`); merged `wal-int` `29500dc08c` (`wal-save16`: `TailZ` in `TailMeta`), which rebuilt the part.
  A hard-linked seed can leave a stale `.olean` with a fresh trace (`Proof/io/ReaderStream` lacked `io.errAt`:
  deleting its build files fixed it).
- **`Create` advanced** from `Preallocate` to after `syncDir(nm.tmp)` (frontier `sorry` there; `set_option
  maxHeartbeats 1000000`, as `cut`): `w := &WAL{…}` (fields split, `sync.init_Mutex`), `newFileEncoder(f, 0)`,
  `w.locks = append(nil, f)`, the header stream over the 64 MB of preallocated zeros (`preGrown` unfolded:
  `os.fileW_start` at offset 0, `os.File.writerStreamI` bounded by the stream's length, `os.fileWI`), `saveCrc(0)`,
  `encode(Metadata)`, `SaveSnapshot(&Snapshot{Index: 0, Term: 0})` through `SaveSnapshot.specPre` (the sync inside,
  `os.fileWI_preSyncOk`: success gives `os.fileS`, the segment synced, its bytes the stream then zeros), and
  `syncDir(nm.tmp)` (the spine to `nm.tmp` as for the segment's create; its `osCommitLb hT3.next` kept, `Hcm1`,
  unused so far: `walCreate_osAUnc`'s `hJC` covers every crash of `J`'s claim). Every error exit is
  `create_seg_exit` (the file's `ownFile`/`osFd` taken out of the writer's state, `os.fileW`/`os.fileB`).
- *New pure modules*: `CreateSnap.lean` (`snapC0`, **`WalMarshalCreateOk Mr`**, `walSnapAt_lit`: the literal frozen,
  its hidden fields in the protobuf invariant), `CreateHdr.lean` (`createStream Mr md := segStream … (walDurFresh
  md) [] 0`: `createStream_frames` record by record, `_mod8`, `_fit` (≤ ext4's maximum for `md < 2^41`), `_pos`).
- **Statement change (ledger 2026-11-14)**: `Create.spec` takes `WalMarshalCreateOk Mr` (`Mr.snap0` is protobuf-go's
  encoding of `Create`'s snapshot object and `Mr.encSnap` of its model the same bytes; without it the committed
  `walDurFresh md`'s header disagrees with what `SaveSnapshot` writes). Minor (a pure premise on the client's
  parameter).
- *New hypotheses of `Create.wp_proof`*: `newFileEncoder.spec`, `WAL.saveCrc.spec`, `encoder.encode.specG`,
  `WAL.SaveSnapshot.specPre` (proved, `WAL__SaveSnapshotPre.lean`), `os.File.WriteAt.specLong`,
  `fileutil.Fdatasync.spec`, `wal.syncDir.spec` (proved).
- **`os.Rename.specAbsentSrc`** (task 2c), stated and proved (`LinuxFs/Spec/os/RenameAbsentSrc.lean`,
  `LinuxFs/Proof/os/RenameAbsentSrc.lean`): the source absent in a fraction of a claim holding both names, the
  model returns a `*LinkError` (the target's `LstatDir` a directory, or `rename(2)`'s errno, `EINTR` retried),
  nothing changed. For `renameWALUnlock`'s second rename after a committed first one.
- **Finding (task 2b; ledger 2026-11-14, pending the coordinator)**: a `Create`-specific `renameWALUnlock` can carry
  `walAreaRes` and release the lock token (`walCreateQ (some x)` holds `walOutFrag`/`walTailsFrag ∅`/`walNamesFrag`),
  but **`Open`'s atomic update on `walDirIs dir` cannot be built**: the client's only update (`walAbsent` to
  `walDiskAt … (walDurFresh md)`) is spent at the commit, its `COMM Q` the client's. The retry path needs a second
  client update in `Create.spec` (a change to the client's contract), so (b) was not made; (a) (the pre carries
  the encoder, the tail file and the lock fds) is independent, and so is (c) (done). Also for (a): after a rename
  that took effect and returned an error (the model allows it), `Close`'s fdatasync of the segment runs with only
  half its `OsMeta`/bytes (the invariant holds the other halves after the commit): it needs the invariant-mediated
  fdatasync of an unregistered tail (`TailSyncIdle`'s form), not `Fdatasync.spec`.
- *Next* (in order): the fresh layout's `WalAbsD` as a pure lemma (`lay := ⟨jr, nm, J, [], 0, [g], replicate |g.bs| 0,
  L, L, 0⟩` with `L := |createStream|`, `old` zeros and `z0 = 0` so that `TailLast`'s last clause holds and
  `tailStop` is vacuous; `g := ⟨walFileName 0 0, i, mS.synced, ysS.map durB⟩`, its bytes `(stream ++ zeros).map durB`
  by `streamOk_vals`; `hzf` from `OsMeta.size_le_syncZ`; `hz` by `cutHdrZeros`/`createStream_mod8`; after `wal-readall18`, `WalAbsD.cutPos`
  vacuous (no cuts) and `nameBound`'s `ix < 2^64` with `ix = 0`); the claim split
  of `J` (`.except walTmps` + `walTmpsRes J`), the minting (`walInv_mint`), then the rename (`renameWAL`, whose spec
  awaits the coordinator's decision on the retry), and the post-commit order of the sixteenth session's *Next*. The
  handle must establish `TailZ` (the coordinator, after `wal-save16`): after the fdatasync the segment's `OsMeta` is
  `mS.synced`, whose `TailZ` follows from `TailZ.synced_of` given the page cache zero to the end of the size's page
  (from `Preallocate`'s post once `wal-save17` strengthens it with the `zf`/`cz` facts).

**Eighteenth session (branch `wal-create16`, 2026-11-14).**
- *Setup*: seeded from `agent-a2a9b3c66efdebc6a` (its `GooseLang.Ext.Fs.Impl` trace was of an older source:
  the whole part rebuilt); `Proof/io/ReaderStream`'s stale build deleted (as in the seventeenth session);
  the `.trace` files unshared (the coordinator's fix); merged `wal-int` `fa1f6d8a60` (`wal-repair19`).
- **`Create` advanced** from `syncDir(nm.tmp)` through the call of `renameWAL` (frontier `sorry` right after it,
  `Hpost : renameWALPost …`): `J`'s claims merged and split (`createJ_claims`), the minting (`walInv_mint` with
  `N.diff [nm.tmp]`, `X := walTmps`; `hDe` from `AreaOk`'s `nm ++ "." ++ sfx` names), `J ≠ jr`
  (`create_J_ne`), the log bound (`osLogLb_max` of the creating claim's and `J`'s claim's `next`), `J`'s claim
  halved (half to `walCreateP`, half kept for the handle's `walDirH`), `walCreateP` and the update
  (`createU_none`), the spine fractions (`d` from `os.qp_common` of a quarter of the area's spine and of `¼`),
  `w.dir` loaded through `walPreIn`, and `renameWAL.spec` applied with `RenameWALOk` discharged.
  *Tooling*: `etc/lean-check.py --fast` reported 0 errors on `Create.lean` where `lake build` found two (inside the
  body's `all_goals (…)` block): check `Create` with `lake build`.
- *New modules* (all proved, no `sorry`): **`CreateLay.lean`** (pure: `createLay jr nm J g L`, `createLay_abs`, the
  fresh layout's `WalAbsD`: `cutPos` vacuous, name index 0, `old` zeros, `z0 = 0` so `tailStop` is vacuous;
  `createSeg`, `createSeg_facts`: the segment after the header stream over the preallocated zeros and the
  fdatasync, its size `max 64000000 |stream|`), **`CreateJ.lean`** (pure: `valAfter_restrict_not`, `createJ_val`,
  `createJ_cur`, `createJ_segsNamed`/`_segsNamedC`/`_walInos`: `walCreate_osAUnc`'s `hsn`, `hJC`, `hents`),
  **`CreatePre.lean`** (`createJ_claims`, `osNames_disj` from `NamesCoh.disj`, `create_J_ne`,
  `walNameOk_not_tmps`), **`CreateAuFresh.lean`** (`createFresh_osAUnc`: `walCreate_osAUnc` over the fresh layout,
  every layout premise discharged), **`CreateRename.lean`** (`osAUnc_mono`; `Create`'s `U`/`Sp`/`SpR`:
  `createU` = `walInv ∗ walCreateQ`, `createSp` = the invariants and two spine fractions `d`, `createSpR` = the
  rest of the new name's claim and the whole, now absent, `nm.tmp` claim; `createU_none` and `create_spine`,
  `RenameWALOk`'s two laws: `walInv_splitNew` then `osPathS_child` twice).
- **Statement change (ledger 2026-11-14)**: `fileutil.CreateDirAll.specTmp`'s success post gains
  `∀ K b, hJ.valAfter J K b = none` (the new directory's claim names nothing at any crash). **Obligation**: the
  extension's `mkdir` law must say it (a fresh inode: nothing logged on it before; an allocator fact); the
  existing-`nm.tmp` case of `specTmp` needs an argument or `hJC` weakened to committed crashes (`Hcm1`).
- **Finding (ledger 2026-11-14, pending)**: `renameWALPost`'s error arms are too weak for `Create`'s exits: the
  deferred `f.Close()` needs the lock file's state (open, or closed by `renameWALUnlock`'s `Close`: a second
  close needs an `os.File.Close` spec for a closed file), and arm 4 drops the two spines (the area's spine
  fraction cannot be returned). The proposed restatement (with decision (1)) is in the ledger.
- *Not done*: tasks 2 and 3 (`renameWAL`/`renameWALUnlock`'s restatement and proofs; the retry's reopen over
  `createU (some x)`; `Close` through `wp_idleFsync`), and `Create`'s post-commit order (the parent's
  `OpenDir`/`Fsync`/close, `walInv_register`, `cleanupWAL`, `mergeIn` of `nm.tmp`, the handle with `TailZ`).
  *Next*: restate `renameWALPost` (ledger entry above), re-prove `renameWAL`, then `Create`'s four arms: arm 3
  needs an unminting step (the creating token, the update and both claims back: not written; `walInvBody_merge2`
  is the merge after it), arm 4 returns `Q ∗ osCallPerm ½` after registering (`walInv_register` with
  `createSpR`'s claim fraction and `walCreateQ`'s `walPast`) and giving the area resources back.

**Nineteenth session (branch `wal-create17`, 2026-11-14).**
- *Setup*: `wal-int` `4700d7abe1`, then `c63cf77346` (`wal-repair21`) merged; the seed's traces unshared,
  `GooseLang`/`LinuxFs` builds copied. `Create.lean` builds in about a minute once its imports are built.
- **`renameWALPost` restated** (ledger 2026-11-14, adopted in part): the pre takes `walLockIn` (the empty
  encoder, the segment's `*os.File` `f`, its fd `fd`, descriptor `d`, offset); arm 1 returns it, arms 3
  and 4 `walLockLeft` (open, or closed by `renameWALUnlock`'s `Close`: fd -1). `renameWALUnlock.spec`'s
  pre the same. **`renameWAL` re-proved** (no `sorry`).
- **The spines' area part from the invariant** (`AreaPath.lean`: `walNamesRes_areaPath`,
  `walInvBody_areaPath`, `walInv_areaPath`, proved): `Create`'s `createSp` fractions come from the
  invariant's lend, not from the caller's spine, because one spine stays with the pipeline `renameWAL`
  starts and an error leaves running; the caller's spine now comes back whole on every arm (the
  proposal's "arm 4 returns the two spines" dropped).
- **`os.File.Close.specClosed`** (`LinuxFs/Spec/os/File__CloseClosed.lean`): a closed `*os.File`'s
  `Close` returns an error, changing nothing. **Not provable from the model**: `File.Close.impl` asks
  `FdKind(-1)`, stuck on a closed fd (the model's header leaves a closed file undefined). Reached by Go:
  `renameWALUnlock`'s `w.Close()` closes the locks when its sync succeeds; a failed second rename then
  returns to `Create`, whose deferred `f.Close()` closes `f` again. A hypothesis of `Create.wp_proof`.
  **Proposed trusted change (pending the user)**: `File.Close.impl` returns `&PathError{"close", name,
  ErrClosed}` when the fd field is -1 (Go's `file.close`: `pfd.Close`'s `incref` fails with
  `ErrFileClosing`, mapped to `ErrClosed`), with a Go example in `examples/osfs/semantics/`.
  `wp_lockedCloseLeft` (`CreateLockedLeft.lean`) closes the lock file in either state.
- **`Create`'s four arms after `renameWAL`**: split. **Arm 4 (committed, an error) proved**: the `Warn`,
  the deferred `f.Close()` (`wp_lockedCloseLeft`), the deferred `RemoveAll(nm.tmp)` of the now absent
  name (`os.RemoveAll.specAbsentS` with half the permission; `+noauto` so the ghost steps run before the
  return), the registration (`walInv_register` with `createSpR`'s fraction of `nm`'s claim and
  `walCreateQ`'s `walPast`/`walNamesFrag (some dir)`), and the area back (**`create_areaBack`**,
  `CreateAreaBack.lean`: `walInv_mergeIn` of the whole `nm.tmp` claim into the rest of the area claim
  under the held lock token, `areaOk_reg` (the area less `nm`, `nm` split), `area_give`); post: `Q`, half
  the permission. Arms 1 (the post-commit order), 2 (pending: `renameWALPost`'s arm 2 is unprovable as
  stated, ledger) and 3 (the unminting step, not written) are `sorry`.
- *Statement changes*: `renameWAL.spec`/`renameWALUnlock.spec` (above, internal); `Create.wp_proof` gains
  `os.File.Close.specClosed`. None client-visible.
- *Not done*: task 2 (`hJC` limited to the crashes keeping `J`'s entries; the plan is in the ledger's
  `CreateDirAll.specTmp` entry: `walCreate_osAUnc` takes `osCommitLb m` from `syncDir(nm.tmp)` with `m`
  past `J`'s entries and raises the invariant's bound to `max n m`, then `valAfter = cur`; the `specTmp`
  promise dropped), arm 3's unminting (inverse of `walInv_mint`: the creating entry and its token back to
  `walUnlockedTok`, the creating claim's halves and `J`'s claim back as `nm.tmp`'s `tmpDirH`, then
  `create_abortTmp`), arm 1 (parent `OpenDir`/`Fsync`/close, `walInv_register`, `cleanupWAL`'s take-back,
  the handle with `TailZ`), and `renameWALUnlock` (task 4). *Next*: task 2, arm 3, then the handle before
  naming (arm 1 and the redesigned arm 2 converge on it).

**Twentieth session (branch `wal-create18`, 2026-11-14).**
- *Setup*: `wal-int` `7aba861836`, then `73051f23a6` (`wal-leaf2`) and later `wal-int` merged; seed
  `agent-a0e31bc0a52d6aa5b`, traces unshared, `GooseLang`/`LinuxFs` builds copied.
- **Task 1 (the closed-file `Close`): model change made on `wal-create18-closewip`, not merged** (§10: Go
  example measured on C; the part's `ErrClosed` fact). It breaks the four open-fd `Close` proofs, which cannot
  refute `fd = -1`: options (a)-(c) in §10, pending the coordinator. `specClosed` stays a hypothesis.
- **Task 4 done (the coordinator's direction, and `wal-leaf1`'s `.touch` finding; ledger)**: `specTmp`'s
  `valAfter … = none` clause dropped; `walCreate_osAUnc` takes `osCommitLb m` with `J`'s entries below `m` and
  raises the invariant's commit bound to `max n m` at the commit (`walsOk_mono`, `absentNone_mono`,
  `walsNamed_mono`, new `dirKeysOk_mono`); `hJC` is `SegsNamedC lay.segs hJ.cur`, and `walsNamed_create` gets a
  crash's `J`-names from `ClaimCoh` (every crash at the raised bound keeps `J`'s entries). `createU` carries the
  bound (`∃ m, ⌜J's entries < m⌝ ∗ osCommitLb m`, so `createU_none` stays a closed `⊢`); `Create` passes
  `syncDir(nm.tmp)` the bound `max (J's claim off the segment's name).next (x0 + 1)` (`osNames_next`, new
  `crOut_logLb`) and uses its `osCommitLb` (`Hcm1`); `createJ_claims` returns the entries bound (`ClaimCoh` of the
  merged claim) in place of `createJ_val` (deleted); `createJ_segsNamedC` from the current names. `Create`
  builds. Still open for `specTmp`'s proof: a narrower error post and the existing-directory case (it stays:
  `RemoveAll(nm.tmp)`'s `nil` gives only `tmpDirH`; ledger).
- *Not done*: task 2 (the handle before naming; arms 1 and 2), task 3 (arm 3). Arm 3's plan, from what exists:
  `walInv_unmint` (the creating token back as `walUnlockedTok`), `walInv_merge2` of the area claim less `nm`
  and the program's half of `.only [nm, nm.tmp]` (with `T := walUnlockedTok`, `walUnlockedTok_excl`; `b1` an
  area name `nm ++ ".a"` as `hDe`), `walInv_drop` of `nm.tmp`, `J`'s halves joined and merged with `walTmpsRes
  J` into `tmpDirH`'s subtree, then `wp_lockedCloseLeft`, `wp_removeAllTmp` and `create_abortTmp`. Its one
  missing piece: `create_abortTmp` wants the area claim's history exactly `h.restrict jr (N.diff [nm.tmp])`,
  and the merge/drop give it only up to `restrict` equalities on `N.diff [nm.tmp].diff [nm]` and on `nm`: a
  restriction-union lemma (or `create_abortTmp` over any history agreeing with it) is needed.

**Twenty-first session (branch `wal-create19`, 2026-11-14).**
- *Setup*: `wal-int` `808904a2af` with `wal-create18-closewip` merged, later `wal-int` again; seed
  `agent-a0d5232984f8fe5f2`, traces unshared, `GooseLang`/`LinuxFs` builds copied.
- **Task 1, option (a) (decided), done** (`806d7ac9ce`, pushed): the extension's four fd predicates are
  `gFdElem` (`GooseLang/Ext/Fs/Ghost.lean`: a ghost-map entry with `0 ≤ fd.toInt`; `gFdElem_lookup`/`_update`/
  `_insert`/`_delete`/`_split`/`_nonneg`), so the ~60 sites only swap `gAuth_*` for `gFdElem_*`; the producers
  (`gFdElem_insert`, `osWorld_addFd`/`osWorld_addFd0`'s new `hfd0`) take `FdFree`'s first conjunct.
  `osFd_nonneg`, `osDirFd_nonneg`, `osDirFdS_nonneg`, `osOutFd_nonneg`, and `osFd_fractional` (moved from
  bboltfs's `DB.lean`). The four open-fd `Close` proofs refute `fd = -1` over the closed-file model. No trusted
  change beyond the closed-file model (still pending the user, §10). The extension and all its importers built
  (`nice -n 10`).
- **Task 2 done**: `os.File.Close.specClosed` proved (`LinuxFs/Proof/os/File__CloseClosed.lean`,
  `os.File.Close.wp_proofClosed`); its pre gains `isPkgInit pkg_id.os` (`os.ErrClosed`, ledger), as does
  `wp_lockedCloseLeft`'s. It stays a callee spec of `Create.wp_proof` (as `wp_Close` does, the discipline: a proof
  takes its callees' specs), now a proved one: the link passes `wp_proofClosed`.
- **Task 3, arm 3 done** (`CreateUnmint.lean`, no `sorry`): `create_unmint` (`walInv_unmint`, `walInv_merge2` of
  the area claim less `nm` and the creating claim with `b1` a fresh WAL name, `walName_fresh`, `walInv_drop` of
  `nm.tmp`, `J`'s halves joined and merged with `walTmpsRes J`, `create_Jback`), and `create_abortTmpH`
  (`create_abortTmp` over any history of the area claim less `nm.tmp` agreeing with `h` on its names' current
  entries: the restriction-union lemma was not needed, the abort only reads `cur`). `Create`'s arm 3 proved.
- *Found on `wal-int`* (not this branch's): `ReadAllReg.lean:109` fails after the merge of `wal-save22`
  (`walTailW`'s new `LoWr` conjunct): a semantic merge conflict for the `ReadAll` agent.
- *Not done*: arm 1 (the parent's `OpenDir`/`Fsync`/close, `cleanupWAL` on their errors, `walInv_register`,
  the handle `walOpenWF` with `TailZ`, `walLenLb`/`walSyncedLb`/`walPurgeW`) and arm 2 (`renameWALPost`'s arm 2,
  unprovable as stated: ledger), `renameWALUnlock`. *Next*: arm 1, starting with the handle from
  `renameWALPost`'s arm 1 resources (`walHandleIn`, `Handle.lean`).

**Twenty-second session (branch `wal-create20`, 2026-11-14).**
- *Setup*: `wal-int` `1aaf9f75af`; seed `agent-a0d5232984f8fe5f2`, traces unshared, `GooseLang`/`LinuxFs` builds
  copied (the part rebuilt in minutes). `ReadAllReg.lean:109` still fails on `wal-int` (the `ReadAll` agent's).
- **Task 1 done: the handle before naming** (ledger 2026-11-14, "arm 2 over the handle before naming").
  `walDirH`/`walHandleIn` take the naming fact as a parameter (`nmd`, default `walNamed dir`: every existing
  use and proof unchanged, the importers rebuilt clean); **`walOpenWFU P Mr w dir`** (`Handle.lean`, sealed) is
  `walOpenWF` with `nmd := emp`. Design choice (superseding the earlier suggestion of `walNamesFrag (some dir)`):
  the handle before naming is **registered** (`walNamesFrag none`), since `walInv_register` needs no naming and
  the retry's `Open` needs the lock token back, which needs the registration first; only the parent's fsync
  (`walInv_named`) is left. Laws (`HandleUnnamed.lean`, proved): `walOpenWF_unnamed`, `walOpenWFU_named`,
  `walOpenWFU_dirAcc` (the `dir` field), `walOpenWFU_permAcc` (the handle's call-permission half: `Create`'s
  `OpenDir`/`Fsync` of the parent need a fraction, and `Create.spec`'s success post returns none),
  `walOpenWFU_unlocked_excl`/`walOpenWF_unlocked_excl` (`create_areaBack`'s `T`), `walPurgeW_fresh_lbs`
  (`walLenLb w dir 0`, `walSyncedLb dir 0`).
- **`renameWALPost`'s arm 2 restated**: `∃ x, UH x ∗ walOpenWFU P Mr w' dir ∗ walPurgeW w' dir`, `UH` a new
  parameter (the caller's residue once the reopened handle holds its share) of `renameWALPost`, `renameWAL.spec`,
  `renameWALUnlock.spec`; `renameWAL` re-proved (passes `UH` through). `Create`'s `UH` is **`createUH`**
  (`CreateRename.lean`): `Q`, the fresh past state, a fraction of `nm`'s claim with the rename its last writer
  (`LastWrite`), `osLogLb (x.1 + 1)`, the absent `nm.tmp`'s whole claim, `walSplitFrag (nm :: Wn)`.
  **`createSpR` strengthened** with the last-writer fact and `osLogLb (x.1 + 1)` (from `renDirOut`'s `logOut`;
  `lastWrite_log_restrict`), so arm 1 reaches `createUH` too. `dir_child_model` (`CreatePure.lean`:
  `filepath.Dir(r/nm) = r`).
- *Obligation (ledger)*: `renameWALUnlock`'s proof needs a `RenameWALOk` law from `U (some x) ∗ SpR x` (and the
  split record, which `Create` must then lend through `Sp`) to `UH x` and the reopen's resources.
- *Not done*: tasks 2-4. `Create`'s arms 1 and 2 still `sorry`; arm 2 is now provable. **Plan for both**
  (arm 1 first converts to arm 2's shape, then one continuation, best as an unhygienic macro like
  `create_seg_exit`): arm 1's assembly (an fupd with `notCrashed`): split `createSpR`'s fraction `c` in two
  (`osNames_frac`), `walInv_register` with one half and `Hsf` (`walNamesFrag none`, `walSplitFrag (nm :: Wn)`),
  the tail registered (`walTailsRes_register` inside `walInv`, as `walInvRegisterTailLaw`: `TailZeros`/
  `TailBound` of the fresh layout), the handle minted (`walHandleP_mint`: `walHandleAuth` from `walGhost`,
  `walGhost_handleAuth`; mode `.append`), `walTailW` from the segment's halves (`TailMeta` of `mS.synced`:
  `TailZ.synced_of`, `PastZ.synced`), `walDirH dir J dfd i (child dir (walFileName 0 0)) 0 emp` from
  `walDirKey`, `J`'s kept claim half, `Hsd`, `osDirFdS dfd J .idle`, `walOutFrag (WalOut.empty.create …)`
  (check it is `⟨[i], [(J, .except walTmps)], [dir]⟩`), `walPipeH` (`isFilePipe`, `pipeMain γ 0`,
  `tmpClaim J (pipeTmp 1)`), `w.state`/`decoder`/`readClose` (Create's `w := &WAL{…}` leaves them zero:
  `P.hsIn null` of the zero state is a `WalPbIn` law to take), the encoder's CRC `WalHS.crc` and `Split` of the
  fresh stream; then the continuation: `walOpenWFU_dirAcc`, `filepath.Dir` (`dir_child_model`),
  `fileutil.OpenDir.spec` on `r` (`Hp`, the lent permission), `Fsync.specDirS` with `osLogLb (x.1 + 1)`,
  `walFsyncSec.Observe` (`encEnv`, persistent), `os.File.Close.wp_dirS`, `walInv_named` (`createUH`'s claim
  fraction, `LastWrite`, `x.1 < x.1 + 1`), `walOpenWFU_named`, the deferred `RemoveAll(nm.tmp)`
  (`os.RemoveAll.specAbsentS`), `create_areaBack` (`T := walOpenWF`), `walPurgeW_fresh_lbs`. The error exits
  (`OpenDir`/`Fsync`/`Close` failed) run `cleanupWAL`: a `WAL.Close` spec over `walOpenWFU` (the proof of
  `Close` does not read `walNamed`; restate `WAL.Close.spec`'s pre with `walHandleIn … nmd` generic, or a
  variant) and the rename to `nm.broken.*` (the area's claim on it: `CreateDropStep`'s drop), then the post's
  committed-error arm (`Q ∗ osCallPerm ½`; the pipeline's half: `Close` returns it).

**Twenty-third session (branch `wal-create21`, 2026-11-14).**
- *Setup*: `wal-int` `e9b343bc4e`, later `1766cf7bb9` (`wal-tc17`) and `wal-save24`'s merge; seed
  `agent-a0d5232984f8fe5f2`, traces unshared, `GooseLang`/`LinuxFs` builds copied.
- **The tail registered at the commit** (ledger 2026-11-14, "`walCreateQ` / `walDirH`"): a registration after the
  commit (`walTailsRes_register` inside `walInv`, as the twenty-second session planned) cannot match the
  invariant's history and layout to the handle's encoder CRC and offset (nothing after the commit pins them to the
  fresh WAL's: `walInvBody_readState` gives only `WalAbsD`). So `walCreate_osAUnc`'s commit registers it
  (`walTailsRes_register` on the new layout; new premise `TailBound`, `createLay_tailBound`), and `walCreateQ`'s
  committed arm holds `walTailReg dir t` in place of `walTailsFrag ∅` (`t` a parameter, `createTailG` from
  `createU`). *Obligation*: `renameWALUnlock`'s retry unregisters it (`walTails_unregister`) with the rest of
  `w.Close()`'s parking. *For `wal-tc18`*: `TailIdle`'s new `so = wr ∧ TailMaps` is the fresh layout's (`so = wr =
  |stream|`, no maps) at `walTailsRes_create`.
- **Definition fixes found by the assembly** (internal): `walDirH`'s tail name `∃ pd, name = child pd nm0` (Go's
  `f.Name()` of `Create`'s segment is `dir.tmp/…wal` after the rename; `cut`'s `w.seq()` reads the base only);
  `walHandleIn`'s and `walHandleC`'s `w.decoder` field `↦ GoInterface.nil` (was `↦ null` at type `Loc`: the field is
  an interface, `ReadAll` sets it to `nil`); `renameWALPost`'s arm 1 says `fp ≠ null` (`newFilePipeline`'s);
  `SaveSnapshot.specPre`'s post says the indices (`snapi`/`enti` each kept or the snapshot's index; ledger).
- **`CreateHandle.lean`** (proved, no `sorry`): `createHS` (the fresh handle state), `createHS_split`/`_crc`/`_done`,
  `createSeg_tailMeta` (the synced segment's `TailMeta`, from the preallocation's `ZeroPg`, `metaChain_zeroPg`),
  `createSeg_size`; `walInv_mintAppend` (the append-mode handle from the lock token); `create_ghost` (the name
  registered, `walInv_register` with half of `createSpR`'s fraction, the handle minted; residue `createUH x`);
  `create_handleIn` (the handle `walHandleIn … emp` from arm 1's fields, encoder, tail file, registration, segment
  halves, directory share, pipeline). Laws: `walHandleP_openW` (`HandleAlloc.lean`), `walOpenWFU_intro` and
  `WalPbIn.NilLaw` (`⊢ P.hsIn null hsZero`, a new hypothesis of `Create.wp_proof`, as `ZeroLaw` is `Save`'s)
  (`HandleUnnamed.lean`).
- **`Create`'s arm 1** proved through the handle: `create_ghost`, `walHandleP_openW`, `create_handleIn`,
  `walOpenWFU_intro` (`⧗ 0` by `receipt_zero`); one `sorry` left there, at the convergence point `walOpenWFU P Mr wl
  dir ∗ walPurgeW wl dir ∗ createUH x` (arm 2's resources exactly), with the area spine `Hp`, the absent `nm.tmp`'s
  path, the lock file's struct fields left over. Arm 2 is still its one `sorry` at the same point.
- *Not done*: tasks 2-4. *Next*, the continuation (one unhygienic macro for both arms), in Go's order (the fork's
  `Create`): `perr`'s deferred closure (runs `cleanupWAL` only on `perr ≠ nil`), `w.dir` (`walOpenWFU_dirAcc`),
  `filepath.Dir` (`filepath.Dir.spec`, `dir_child_model`), `fileutil.OpenDir.spec` on `r` (the area's spine `Hp`,
  the handle's call-permission half lent, `walOpenWFU_permAcc`), `time.Now`, `fileutil.Fsync.specDirS` with
  `osLogLb (x.1 + 1)` (`createUH`'s), `walFsyncSec.Observe(time.Since(start))` (specs to find: `walInit`'s
  `Hmet`), `dirCloser()` (`os.File.Close.wp_dirS`), then `walInv_named` (`createUH`'s claim fraction and
  `LastWrite`, `x.1 < x.1 + 1`), `walOpenWFU_named`, the deferred calls in LIFO order (the `perr` closure, `f.Close`
  skipped on `retErr = nil`, `os.RemoveAll.specAbsentS(nm.tmp)` with `createUH`'s whole `nm.tmp` claim),
  `create_areaBack` (`T := walOpenWF`, `walOpenWF_unlocked_excl`), `walPurgeW_fresh_lbs`. The error exits
  (`OpenDir`, `Fsync`, the close) run `cleanupWAL` (task 3: `w.Close()` then the rename to `nm.broken.*`; the
  deferred `f.Close()` then closes a closed file, `specClosed`).

**Twenty-fourth session (branch `wal-create22`, 2026-11-14).**
- *Setup*: `wal-int` `d7d012c53f`, later `7919480144` (`wal-tc19`, `wal-save25`) merged; seed
  `agent-a0d5232984f8fe5f2`, traces unshared, `GooseLang`/`LinuxFs` builds copied.
- **Found: a bug in `Create`** (`nonissues/etcd-wal-create-parent-fsync-nil-nil.md`, blocks-proof; ledger
  2026-11-14): after a failed `Fsync(pdir)` it calls `dirCloser()`, which assigns the close's result to `perr`, so a
  successful close makes `Create` return `(nil, nil)` and skip `cleanupWAL` (upstream too, `d622ec5`; etcd's
  `bootstrapNewWAL` then dereferences the nil WAL). Over `fsExt` the fsync may fail and the close succeed, so
  `Create.spec`'s success arm is false there. Fix proposed as a plain diff, `notes/wal-fsext-fork/0005-...diff`
  (`pdir.Close()` on that path), pending the user with 0001-0004; then retranslate. Until then that path is a
  marked `sorry`.
- **Task 1 done (the continuation)**: `create_named_cont w` (`Create.lean`, an unhygienic macro taking the
  handle's pointer), used by both arms at the same point (`walOpenWFU P Mr w dir ∗ walPurgeW w dir ∗ createUH
  x`): `createUH` opened; `w.dir` (`walOpenWFU_dirAcc`); `filepath.Dir` (`dir_child_model`); `OpenDir(r)` on the
  area spine with the handle's half of the call permission (`walOpenWFU_permAcc`); `time.Now`;
  `Fsync.specDirS` with `osLogLb (x.1 + 1)`; `walInv_named` (`createUH`'s claim fraction, `LastWrite`); the
  `Observe` (as `cut`'s); `dirCloser()` (`Close.wp_dirS`); the deferred calls (the cleanup closure and `f.Close`
  skipped, `RemoveAll.specAbsentS(nm.tmp)` with the lent half); `walOpenWFU_named`; `create_areaBack`
  (`T := walOpenWF`, `walOpenWF_unlocked_excl`); `walPurgeW_fresh_lbs`; the success post. *Statement change*
  (internal): `Create.wp_proof` gains the callee specs `filepath.Dir.spec`, `fileutil.OpenDir.spec`,
  `Fsync.specDirS`, `time.Now`/`Since`/`Duration.Seconds`. Arm 2's `Hsf` (`walSplitFrag Wn`) is left unused
  (the `RenameWALOk` obligation: `Create` must lend it through `Sp`).
- *Left `sorry` in `Create`*: 4 sites in the macro, expanded in both arms: `OpenDir` failed, `Fsync` failed (the bug
  above, and the cleanup when the close also fails), the final close failed: all three run `cleanupWAL`.
- **Task 2 (`cleanupWAL`) designed, not made.** What blocks a simple spec, and the design:
  (a) `WAL.Close.spec` takes an AU on `walDiskAt dir`, which `Create` no longer has after the commit (the client
  holds `walDiskAt`); the AU is used only at `walCloseLaw`'s commit (state unchanged, for `Q` and
  `walSyncedLb`). A variant `WAL.Close.specCleanup` over `walOpenWFU` (`nmd` generic: the proof never reads it),
  no AU, needs `walCloseLaw` without the commit. (b) After `cleanupWAL`, the deferred `RemoveAll(nm.tmp)` needs the
  `nm.tmp` claim and `walAreaRes` needs it merged back (`create_areaBack`), and a merge needs a token excluding a
  free one (`walInv_mergeIn`), a drop the free token (`walInv_drop`). So `Create` keeps `createUH`'s `nm.tmp` claim
  through the cleanup, and the cleanup's post must return such a token in every arm: `walUnlockedTok` when
  `Close` succeeded (`walUnlockedTok_excl`), `walLockedTok` when it failed. The latter is honest (`Close`
  returns before unlocking on a failed sync) but needs `WAL.sync.specC`'s error arm to keep the lock token
  (`wal-save*`'s spec: internal). (c) The rename `nm` -> `nm.broken.<time>`: a new invariant update for
  `os.Rename.specDirSnc` moving a registered WAL whose `named = false` off its name (no abstract change:
  `walDurFresh md`'s crash condition allows `dir` absent), with the claim on the broken name dropped off the
  area under the free token from `Close`, and `nm`'s claim (`createUH`'s fraction and the invariant's). (d)
  The deferred `f.Close()` after a successful cleanup closes a closed file (`specClosed`): `Close`'s variant
  must return the lock files' `os.ownFile f (-1)`. (e) The closure's `fmt.Errorf("%w (after: %v)", ...)`.
  `Create` side once (a)-(e) exist: the cleanup, `f.Close` (`wp_lockedCloseLeft`-like), `RemoveAll(nm.tmp)`,
  `create_areaBack` with `T := walUnlockedTok ∨ walLockedTok`, the post's committed-error arm (`Q ∗ osCallPerm ½`).
- *Not done*: task 2's pieces, task 3 (`renameWALUnlock`'s `RenameWALOk` law and proof).

**Twenty-fifth session (branch `wal-create23`, 2026-11-14).**
- *Setup*: `wal-int` `3875d6f49a` (`wal-fork5` merged: fix 0005 in the translation, `Create.lean` builds with its
  four `sorry` sites), later `b6db856cce` (`wal-leaf5`) merged; seed `agent-aebf4ce5bdcb1461b`, traces unshared,
  `GooseLang`/`LinuxFs` builds copied.
- **`WAL.sync.specC`'s error arm keeps the lock token** (ledger 2026-11-14): `sync.wp_core`'s error arm returns
  `walOpenW w dir` (the flush failure leaves it; the fdatasync returns the pending-cut flag), `specC`'s
  `⌜err ≠ nil⌝ ∗ walLockedTok` (`walOpenW_lockedTok`, `OpenWLocked.lean`); `sync.spec`/`specCut` drop it.
  `walHandleC` takes the naming fact (`nmd`, default `walNamed dir`) and `specC` quantifies it (`Close` passes
  `_`).
- **`WAL.Close.specU` proved** (`Spec/.../WAL__CloseU.lean`, `Proof/.../WAL__CloseU.lean`): `w.Close()` of
  `walOpenWFU` with no update; post `(w.dir ↦ dir ∗ walUnlockedTok ∗ osCallPerm 1) ∨ (⌜err ≠ nil⌝ ∗
  walLockedTok)` (the left arm whatever `err`: the directory's close failed last; the `dir` field because
  `cleanupWAL` reads `w.dir` after `Close`). The proof is `Close`'s with `walOpenWFU` unsealed (`import all
  Handle`) and **`walCloseLawU`** (`CloseLawU.lean`: `walCloseLaw` without the commit). Not linked yet (no
  user until `cleanupWAL`).
- **Found, blocking `cleanupWAL`'s rename** (for the user): `brokenDirName := fmt.Sprintf("%s.broken.%v", w.dir,
  time.Now().Format("20060102.150405.999999"))`. `time.Time.Format.spec` (an axiom, `Proof/time/Time__Format.lean`)
  says nothing of its result, so the target path `r/nm.broken.<s>` may hold `/` or be any length: no `os.Rename`
  spec covers it, and the proof cannot own the target's parent. Needed: a stronger trust-boundary spec of
  `Format` for that layout (the result's characters digits and `.`, length at most 22) -- an axiom change, the
  user's -- or a callee hypothesis `time.Time.Format.specLayoutDigits` of `cleanupWAL`'s proof until then. And
  `nm.broken.<s>` may pass 255 bytes (patch 0002's `TestCleanupWALRenameFails`): an `os.Rename` spec for a target
  name that is not `NameOk` (`ENAMETOOLONG`, nothing changed) over `fsExt`.
- **Found: the deferred `f.Close()` after the cleanup** (ledger obligation): `Create` needs its segment's lock
  file `f`, closed when `Close` succeeded, open when its sync failed. (1) `walOpenWFU` hides the handle's tail
  lock, so `Create` cannot tell that `f` is it (arm 1) -- a parameter `lt` of `walOpenWFU`, from a copy of
  `walHandleIn` with `lt` free (`walHandleIn` itself has 13 destructuring files); (2) on a failed sync the tail
  file is lost: `sync`'s error arms must return `os.ownFile f fd name ∗ osFd fd …` (the fdatasync's does, inside
  `walTailW`; the flush's needs `wp_tailWriteAtW`'s/`wp_tailWriteW`'s error arms to keep `osFd` -- they have it in
  context -- and `wal.tailWriterW`'s `B` to carry it); (3) arm 2: `renameWALPost`'s arm 2 must return `walLockLeft f
  …` (the retry's `w.Close()` closed `f`, or left it open when its sync failed).
- *Not done*: `cleanupWAL` (blocked above), `fmt.Errorf("%w (after: %v)", …)` (`fmt.ErrorfErrs.spec` needs `errOk`
  of both errors; `Create`'s post needs only `err ≠ nil`), `Create`'s four `sorry` sites, task 3.

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

**W6, twelfth session (branch `wal-save12`, 2026-11-14): `Save` and `SaveSnapshot` proved over hypotheses.**
- **`WAL.Save.wp_proof` proved** (`WAL__Save.lean`, no `sorry`), hypotheses: `sync.spec`, `saveEntry.spec`,
  `saveState.spec`, `cut.spec`, `WAL.tail.spec` (proved, `WAL__tail.lean`), and three laws of the client's raft
  messages (the part cannot import the main tree's raft specs, plan §10): `WalPbIn.IsEmptyLaw` (existing),
  **`WalPbIn.MustSyncLaw`** (`MustSync(p1, p2, n) = (n ≠ 0 ∨ vote/term differ)`) and **`WalPbIn.ZeroLaw`** (a nil
  pointer holds only `hsZero`; a fresh `&raftpb.HardState{}` (`p ↦ zero_val HardState`) holds `hsZero`, under an
  update: the client keeps its hidden fields), both new, in `Spec/.../WAL__Save.lean` (to discharge at C6 from raft's
  `hsRO`/`pbMsg` and raft's `MustSync` spec). No statement change. The proof: the commit at the first step
  (`walHandleIn_append`), the lock (Perennial's `Mutex`, the handle's mutex and `sync`'s init by
  `walHandleIn_lockFacts`), the shortcut joined on the `&&` (`wp_join (Q := …) at (if: _ then _ else #false)`, the
  committed handle quiescent already: `SaveSt.finEmpty`), the nil states (`wp_join … at`, `iapply wp_fupd` before
  the case split so `ZeroLaw`'s update can run; `walHandleIn_state` takes `w.state` out and back), `MustSync`, the
  entries loop (invariant `SaveSt h hs es j hc`, `SavePure.lean`: `SaveSt.entryPre` gives `saveEntry`'s three
  premises, `SaveSt.step` the next state), `saveState` (`SaveSt.statePre`; both successes joined into `SaveFin`),
  `Seek` (`walHandleIn_seek`; the promoted method unfolded by `rw [MethodUnfold.method_unfold (t := …) (m := …)]`:
  plain `wp_method_call` rewrote the deferred `Unlock` in the `defer` cell instead), `sync` or `cut` (a step's
  receipt by `wp_take_receipt` before the method resolves, so the `if` is split by `by_cases`, not
  `wp_if_destruct`, whose `wp_auto` resolves it; `save_pc_bound` keeps the receipt), `save_post` for the three
  successes. Gotchas: a multi-line `{ h with … }` with the fields on a continuation line does not parse (keep it
  on one line); `rename_i` to name the shadowed Go variable `i`'s cell (`wp_for`'s invariant names it).
- **`WAL.SaveSnapshot.wp_proof` proved** (`WAL__SaveSnapshot.lean`, no `sorry`), hypotheses: `sync.spec`,
  **`encoder.encode.specTail`** (new, `Spec/.../encoder__encodeTail.lean`: `encode.specG` over the tail's writer
  without `tailOk`'s size clause, the size growing; its post claims the handle's offset bounds), `ValidateSnapshotForWrite.spec`,
  `Snapshot.GetIndex.spec`, `MustMarshalMessage.specWalSnap`. The commit by `walTail_append` on the unsealed
  handle; the handle rebuilt after the encode and the raises (`SnapPure.lean`: `WalHS.split_snap` (split and CRC),
  `snap_guard` (the encode's guard), `snap_idx` (the index facts with `w.snapi`/`w.enti` raised)).
- **Obligation (writes past the size; `saveEntry`/`saveState`/`encode.specTail`)**: the handle's
  `o0 + |out| + |pend| ≤ 0xffffffff000` after an encode has no source (nothing bounds a segment's stream; a real
  write past `s_maxbytes` fails with `EFBIG`, but the page writer's pending bytes are not written). The three
  specs claim it in their posts; whoever proves them must find it (a bound in the guard, or a handle bound on
  `o0 + |out|` only).
- *Not done*: `sync.wp_proof` and `sync.specCut` (both flush pending bytes past the tail's size: blocked on the
  writes past the size, as `saveEntry`/`saveState`; `wal-tc3` landed the truncate's window only).

**W6, thirteenth session (branch `wal-save13`, 2026-11-14): the stream bound; the window form on the save path.**
- *The stream bound (task 2, decided; ledger 2026-11-14, "the batch's size")*: `Save` takes **`walBatchBytes Mr es <
  2 ^ 40`** (`Handle.lean`: each entry's encoding plus 64, summed; replaces the per-entry premise, which follows,
  `walBatchBytes_each`). The handle fact is in the sealed **`walOpenWF`: `o0 + |out| + |pend| < 2 ^ 43`** (the
  stream's *end*, not the offset: a `Save` that syncs flushes its pending bytes after its `Seek`; and `2 ^ 43`,
  not `SegmentSizeBytes`, because a cut's headers hold the metadata, up to `2 ^ 41`). `saveEntry.spec`/
  `saveState.spec` take `(tailStream Mr h.H h.md h.cuts).length ≤ 0xffffffff000` (`Save` has it from the fact
  and the batch, `saveStream_le`); `encoder.encode.specTail` takes `sz ≤ 0xffffffff000` and `o0 + |out| + |pend| +
  |frame| ≤ 0xffffffff000` (its post's bounds follow). Pure (`StreamBound.lean`, no `sorry`): the tight frame
  bound `frame_walRecEnc_tight` (`|d| + 64`), `recFrames_chainRecs_le`, `saveOp_frames_le`, `WalHS.split_end`/
  `end_le`/`end_rest0`, `cutStream_lt` (a cut's headers `< 2 ^ 43`), `saveStream_le`. `HandleLaws.lean`:
  `ioutil_ownPageWriter_pend` (`|pend| ≤ 2 ^ 18`), `walHandleIn_pure` (split, pend, offset bounds).
- **Finding (for the coordinator): `SaveSnapshot` cannot keep any constant stream bound.** It never cuts
  (S/wal.go:1137-1162), so `n` `SaveSnapshot`s in a row grow the tail by `n` records; the model's `pwrite` may
  succeed past ext4's `s_maxbytes` (only `offMax = 2^62` is a hard stop), so nothing bounds the tail at all, and
  `walHandleIn`'s existing `sz ≤ 0xffffffff000` is unmaintainable too. `SaveSnapshot.wp_proof` now has one `sorry`
  (its post's `< 2 ^ 43`). Options: (a) the model's write fails (`EFBIG`) past `s_maxbytes` (a trusted
  restriction [user], measurable on configuration C; then the tail's written bytes stay `≤ 0xffffffff000` by the
  writes' success, the pending ones `≤ 2 ^ 18`, and neither the batch premise nor the handle fact is needed);
  (b) a per-lifetime budget of `SaveSnapshot`s (receipts, as the cuts budget) with a bound on each snapshot record
  (`2 ^ 40` makes the product too large: the record's real size is tens of bytes, so a much smaller premise).
  Recommended (a).
- *The window form on the save path (task 1's handle side)*: a `Save` that writes past the preallocated size and
  does not sync leaves the tail's window open (`pwPost`: `lo` the old size, `hi` the end), so **`walOpenWF` holds
  `walHandleIn … TailMetaW`**, and `saveEntry`/`saveState` (pre and post, `∃ sz'`), `sync.spec` (pre; its post
  exact, `sz := max sz (o0 + |out| + |pend|)`), `cut.spec` (pre), `os.File.Truncate.specWalTail` (pre: **obligation
  for `wal-tc5`**, the truncate from a window) and `encode.specTail` (pre and post) are over `TailMetaW`. Laws:
  `walTailW_mono`, `walHandleIn_mono`, `walHandleIn_win`; `SaveHandle`'s four lemmas, `walHandleIn_append` and
  `walHandleIn_lenLb` take a last `tm` argument (default `TailMeta`). `SaveSt.step`/`finState` take the new size.
  `Save` re-proved (no `sorry`), `Sync`, `cut` and every importer build.
- *Not done*: task 1's writer past the size (below, design for the next session), `sync.wp_proof`, `sync.specCut`,
  `saveEntry`/`saveState`'s proofs (they need three laws of `P` as hypotheses, to state: `MustMarshalMessage` of an
  entry/hard state to `Mr.encEntry e`/`Mr.encState hs` in a fresh non-nil slice, and `GetIndex` over `P.entIn`;
  then `encode.specTail` with `recSize_tight`, the guard from `WalHS.Split` and the next record, as `snap_guard`),
  `encode.specTail`'s proof.
- *Design for task 1 (the writer past the size), checked against the extension's definitions*: (1) **`W1G` over the
  known candidates past the bytes** (the I3b `wal-tc2` proposal, shared with `ZeroToEnd`'s growth, `wal-tc5`):
  `segBytesOf lay i := g.bs ++` the run of `g.om.pc` from `|g.bs|` below `g.om.hi`; `w1G_of_W1`'s premise from
  `MetaOk.tail`/`zf` (idle) and `tok_cand` (in flight); exact segments unchanged (`hi = |bs|`). Without it a short
  write (`EINTR` with `k < n` landed) leaves `hi > size` with the image's frames past the ghost's bytes, where `W1G`
  says nothing. (2) `SegFl.Ok` past the size: the announced layout's `g.om` with `tc` the token's candidates
  (`pwTail`-shaped, `[(0, 0), (d_b, n)]` given `zf = some size`), as `rzMeta` does for resizes; the crash take's
  write case gives it (`TokPast`). (3) `TailMeta(W)` gains `m.zf = some m.hi`-style known zeros (true of every
  tail the WAL builds, I3b W6 entry). (4) The window `CrashOk`: `tail_decode` with the candidate function extended
  past `|bs|`, image length free in `[lo, hi]` (`wal-tc5`'s truncate-window lemma is the same argument with the
  truncate's zeros; one lemma for both).

**W6, fourteenth session (branch `wal-maxb14`, 2026-11-14): ext4's `s_maxbytes` in the model; the stream bounds
withdrawn; `SaveSnapshot` without `sorry`.**
- *The semantics change (task 1; trusted, decided provisionally by the coordinator, **pending the user's review**,
  §10)*: `Impl.lean`'s `maxBytes := 0xffffffff000` (configuration C's `s_maxbytes`: `ext4_max_size` gives
  `(2^32 - 1) << 12` for extent files with 4 KiB blocks). `PWriteFinish` adds `(k = 0 ∨ off + k ≤ maxBytes)` (a
  write starting at or past it lands nothing, one crossing it is cut there: a page cut, since `maxBytes` is
  page-aligned); `FtruncateFinish`/`FallocFinish` land a resize (whole, or `fallocate`'s prefix) only if
  `c.target ≤ maxBytes`, else only the failure with no change; `CrashFile` adds `sz ≤ maxBytes`; `FsInit` adds
  it of every file at the first start. Go example `examples/osfs/semantics/data_maxbytes.go` (indexed in
  `doc.go`), **measured on C** by `models_test.go`'s `TestMaxBytes` (`run-models-on-c.sh -run TestMaxBytes`,
  kernel 7.0.0-38, `check.sh` passed): `pwrite(100 bytes at max-1) = 1` (size `max`), `pwrite` at `max` =
  `EFBIG` with nothing landed, Go's `WriteAt` crossing it `(0, EFBIG)`, `ftruncate(max)` ok, `ftruncate(max+1)` =
  `EFBIG` with the size unchanged, `fallocate(0, max-4096, 8192)` and the same with `KEEP_SIZE` = `EFBIG`
  unchanged, `fallocate(0, max-4096, 4096)` ok.
- *The model invariant*: `OsWf.sizes` is now `sizeLo ≤ size ≤ sizeHi ≤ maxBytes` (kept by every step,
  `osWf_setFile`'s premise has the third clause; the start from `FsInit`, the crash from `CrashFile`).
  **What clients get**: `PwCut` gained its second clause `(k = 0 ∨ off + k ≤ maxBytes)` (`Write.lean`), so every
  `os` writer spec that states `PwCut` (`WriteAt`, `WriteLong`, `OffLong`, the writer streams) carries the bound
  of what a write landed; **`wp_osMeta_size`/`wp_osMeta_sizeU`** (`Specs.lean`): before any step of a non-value
  expression, `m.size ≤ maxBytes` of an `OsMeta` at hand, or of one an update reaches (opening invariants; the
  general form, from Perennial's `wp_ext_acc`); `crashSeen_max` (`CrashFiles.lean`) and `crash_size_max`
  (`Bridge.lean`) for the restarted program. `MetaOk` is unchanged (a law on a bare `osMeta` fragment needs the
  world, so it is a step lemma, not a field). The WP rules' statements are unchanged (a resize past `maxBytes`
  now only fails; their posts still allow that); their proofs pick the failure step when the target is past it.
  `Tests.lean`: `CacheOk`/`CacheCand` carry the bound (`cacheOk_step` re-proved), `pwrite_page_cut` states it.
- *The stream bounds withdrawn (task 2; ledger 2026-11-14, "the batch premise withdrawn")*: `Save`'s premise is
  back to `∀ e ∈ es, (Mr.encEntry e).length < 2 ^ 40` (the frame encoding's, ledger "no bound on the records'
  size"; the batch bound `walBatchBytes < 2 ^ 40` withdrawn); `walHandleIn` lost `o0 + |out| + |pend| ≤
  0xffffffff000` and the sealed `walOpenWF` its `< 2 ^ 43` (the handle keeps `o0 + |out| ≤ sz ≤ 0xffffffff000`,
  which writes that succeed now keep: they land below `maxBytes`; the pending bytes are at most `2 ^ 18`);
  `saveEntry.spec`/`saveState.spec` lost `(tailStream …).length ≤ 0xffffffff000`; `encode.specTail` lost its
  premise `o0 + |out| + |pend| + |frame| ≤ 0xffffffff000` and its post's `o0 + |out'| + |pend'| ≤ …` (it keeps
  `sz' ≤ 0xffffffff000`, now the model's). **`SaveSnapshot.wp_proof` has no `sorry`.** `Save`, `Sync`, `sync`
  (`wp_proofIn`), `cut` repaired. `StreamBound.lean`'s lemmas (`saveStream_le`, `cutStream_lt`, ...) are now
  unused (left for the cleanup).
- *`ReadAll`'s growth across restarts*: resolved by the model: a crash leaves no file past `maxBytes`
  (`crashSeen_max`), and between crashes every size stays below it (`OsWf.sizes`), so a segment's `|g.bs|`
  (its `OsMeta`'s size) is below `0xffffffff000` at any step: `wp_osMeta_sizeU`, opening `walInv` around the
  step, gives the decoder's `|g.bs| + 2^12 < 2^62` without an invariant conjunct. **Not given**: a bound on
  the ghost `om.hi` (`pwPost`'s `hi` is the announced end `max hi (off + n)`, which a write announced past
  `maxBytes` raises past it although nothing lands there); `WalsBounded`'s `g.om.hi ≤ 0xffffffff000` (wal-path14)
  should bound `|g.bs|` through `wp_osMeta_sizeU` instead, or `pwPost` could clip `hi` at `maxBytes` (a change to
  `Write.lean`'s specs, not made).
- *Task 3 (partial)*: the laws of `P` for `saveEntry`/`saveState` stated: `WalPbIn.MarshalEntLaw`
  (`MustMarshalMessage` of an entry: a fresh non-nil slice of `Mr.encEntry e` with its capacity) and
  `WalPbIn.GetIndexLaw` (`GetIndex` returns `e.Index'`), in `Spec/.../WAL__saveEntry.lean`; `saveState` uses the
  existing `WalPbIn.IsEmptyLaw`/`MarshalHsLaw` (`WAL__cutPre.lean`). `saveEntry.wp_proof`/`saveState.wp_proof`
  now take them and `encode.specTail` (still `sorry`; `saveState.wp_proofPre`, over a guarded writer, is the
  model for its proof). *Not done*: the tail writer past the preallocated size (crash side, the design in the
  thirteenth session; `wal-tc5`'s W1G past the ghost bytes), `sync.wp_proof`, `sync.specCut`, `encode.specTail`.
  **Obligation for them**: the posts' `sz' ≤ 0xffffffff000` come from `PwCut`'s second clause of each write
  (`os.File.WriteAt.spec`'s post) with the handle's `sz ≤ 0xffffffff000`; nothing else bounds the stream.
  `sync`'s proof must also give `WAL.sync.specC` (`WAL__syncC.lean`, `wal-close15`: `sync.spec` over `walHandleC`,
  the handle after `Close` closed the pipeline; `sync` never reads `w.fp`): ideally both from one core lemma over
  the handle without the pipeline (coordinator, 2026-11-14). `walHandleC` lost the stream-end fact with
  `walHandleIn` (this session).
  From `wal-tc6` (merged, `W1G` past the ghost's bytes: `segBytesX`, `crashRestAt_take_tok`, `WinCrash.lean`): a
  write in flight past the size stops `segBytesX` at the announced range, because the token's `OsMeta` forgot those
  candidates; the thirteenth session's design item 2 (the announced layout keeping the token's candidates, `pwTail`-
  shaped) fixes that, and is the tail writer's (not started here). `wal-tc7` does the window-to-window `CrashOk`
  and `specWalTail`.

**W6, fifteenth session (branch `wal-save15`, 2026-11-14): the crash side of a write past the size; `saveEntry` and
`saveState` proved; why the writer past the size is not yet provable.**
- *Task 1, the crash side (done; `Inv.lean`, `CrashTakeSeg.lean`, no `sorry`)*: **`wrMeta m off data n`** (the token's
  `cfMeta` with `tc := pwTail m off data n`: each byte announced past the size keeps `m.pc b ++ [(data_b, n)]`, which
  the token's `OsMeta` forgot; `wrMeta_in`: inside the size it is `cfMeta`, so the in-size steps are unchanged).
  **`SegFl.Ok`'s first clause is now `off ≤ size`** (a `pwrite` starts inside the file, `pwTok`'s) and its layout
  `OsMeta` is `wrMeta`. `wrMeta_pc_cand` (what it knows past the size is the file's, from `tok_cand`) and
  `fileCrashedR_wrMeta` (from `TokPast`); `crashRestAt_take_seg`'s write case gives `SegCrashAt` of it, so
  `segBytesX` of a write in flight past the size covers the announced bytes (the gap `wal-tc6` left).
  `runsCover_fl` generalized (`cfHi` may be the size). The in-size step lemmas take their `hin : off + |data| ≤ size`
  explicitly (`segFin_getElem?`, `segFin_length`, `walAbsD_finish`, `segFin_cand`, `wp_tailPWriteFinish`).
- *Task 3 (done)*: **`WAL.saveState.wp_proof`** and **`WAL.saveEntry.wp_proof`** proved (no `sorry`) over
  `encode.specTail` and the laws of `P`. Pure (`SaveNext.lean`): `chainRecs_getElem?`, `allRecs_tail` (the WAL's
  records end with the tail's), `WalHS.next_rec`/`next_guard` (the encode's guard for the next record, `rest > 0`),
  `WalHS.split_next` (the split and CRC after it). The record's size by `recSize_tight` (`StreamBound.lean`: keep
  it and its `wal_varintSize_*` lemmas when cleaning up). **Spec change (ledger 2026-11-14)**: `saveEntry.spec` takes
  `(Mr.encEntry e).length < 2 ^ 40` (`Save` passes its premise).
- **Finding: the writer past the size needs two facts no handle carries yet** (so `wal.tailWriter` past the size,
  `encode.specTail`, `sync.wp_proof`/`specCut`/`specC` are not done; stating them as hypotheses would state false
  ones):
  1. *Known zeros past the size* (design item 3). A write past the size gets, for each new byte, the candidates
     `m.pc b` (`wp_osPWriteFinishK`'s `zs`), unconstrained where `pc` is unknown. A fully landed write past the size
     leaves `zf = some size` (`announce` raises `zf` to the write's end), but **`OsMeta.synced` loses it**: `zf :=
     some syncZ`, `syncZ = pageEnd size` unless `pageEnd size ≤ cz`, and writes do not raise `cz`. Reachable:
     `SaveSnapshot` (never cuts) writes past the preallocated size to an unaligned end and syncs; the next write past
     the size then has unknown candidates on `[size, pageEnd size)`, and the crash condition cannot exclude a stale
     byte inside a frame (the model's state may indeed have one: `MetaOk.zf` constrains candidates, not the page
     cache, which `OsFile.synced` reads). `Save` itself always cuts after crossing (its `cut` truncates first: `cz`
     covers). Fix options (untrusted, `GooseLang/Ext/Fs`): `MetaOk.zf` also says the page cache is zero from `z` on,
     and `OsMeta.synced` keeps `zf = some size` when `m.zf = some m.size` (every step must keep the cache clause: a
     truncate's stale cache past the new size is the case P2's `cz` handles), or a write past the size raises `cz` to
     `pageEnd` of its end when `zf ≤ off + k`. Then `TailMeta(W)` carries `∃ z, m.zf = some z ∧ z ≤ max m.size m.hi`
     (an obligation for `Create`/`ReadAll`/`specWalTail`'s posts).
  2. *A window's size is its stream's end*: a window opens by `cut`'s truncate at the file offset (`specWalTail`'s
     post: `sz = o0 + |out|`) or by a write past the size (size = the write's end), and every later write is past the
     size, so in a window `sz = o0 + |out|`. The window's fdatasync needs it (with `|g.bs| = wr` the synced layout is
     `TailLast` with `so = wr = |S|`; bytes past `wr` in a window are unconstrained, `TailWin`), but `TailMetaW` does
     not say it. Proposal: `walHandleIn`'s pure part gains `h.sz = h.o0 + |h.out| ∨` (the tail exact), or a
     `TailMetaW`-indexed variant.
  3. *The static relation past the size*: `TailWin` needs `|g.bs| ≤ |old|`, false once a write past the size lands;
     the finish should extend `old` with zeros (vacuous for `tailStop`, kept by `TailZeros`), and `TailWin` should say
     what `segBytesX` holds past `|bs|`: `∀ b, |bs| ≤ b < hi → ∃ c, g.om.pc b = some c ∧ ∀ q ∈ c, q = (0, 0) ∨ (q.1 = 0
     ∧ q.2 ∈ g.om.rz) ∨ (q.1 = S b ∧ 0 < q.2)` (`RzCands`-shaped; `wal-tc7`'s window-to-window lemma needs the same
     premise: coordinate in I3b). The finish takes `wp_osPWriteFinishK true` (`pwTail` kept past the new size after
     a short write; with `false` a retry's bytes there would be unknown).
- *For `wal-close17`* (`TailSynced`): the fdatasync's success gives `osMeta m.synced` and `bs.map durB`
  (`wp_tailFsync`), and `OsMeta.synced` is idempotent (`syncZ` reads `size`, `cz` only), so `sync.spec`/`specC`'s
  posts can carry `TailMetaS m bs := TailMeta m bs ∧ m.synced = m ∧ bs = bs.map (durB ·.1)` as the handle's `tm`
  once `sync` is proved (not stated here: the posts are unchanged).
- *Not done*: tasks 1 (the steps past the size), 2 and 4 (`StreamBound.lean`'s cleanup: `recSize_tight` and the
  varint lemmas are used now; `saveStream_le`, `cutStream_lt`, `walBatchBytes_*`, `WalHS.end_*` still look unused).

**W6, sixteenth session (branch `wal-save16`, 2026-11-14): finding 1 in the extension (option (b)); `TailZ` in the
tail's facts; findings 2 and 3 re-examined.**
- *Extension (untrusted ghost, `GooseLang/Ext/Fs`)*: option (b) needs a fact the coordinator's wording left implicit:
  raising `cz` past a write's end needs the page cache past the write to be known zero, and `MetaOk.zf` constrains
  only candidates. So **`MetaOk.zc`** (new field: `∀ z, m.zf = some z → ∀ b, z ≤ b → f.cache b = 0`; every
  `MetaOk` construction repaired: announce, the write's and resize's finish, both syncs, boot's `initMeta`) and
  **`Fs.pwCz m off n k`** (`pwPost`'s `cz`): `max cz (pageEnd (off + n))` when the write wrote **all** of its data
  (`k = n`, `0 < n`) and `zf ≤ off + n`, else `cz`. Raising only on a complete write (not on any `zf ≤ off + k`)
  matters twice: a short write ends on a page boundary (`PwCut`), so it would add nothing; and with it a retry's
  `OsMeta` is still the whole write's (`pwPost_step`, `File__WriteAt.lean`, re-proved with a `cz` case: the
  first form broke it). Lemmas `le_pwCz`, `pwCz_raise`, `pwFinish_cz_raise`. `WReach.cz` (`Spec/os/CrashSt.lean`)
  is now `m.cz ≤ m'.cz`.
- *The tail's facts (`Handle.lean`)*: **`TailZ m`** (`∃ z, zf = some z ∧ size ≤ z ∧ pageEnd z ≤ max size cz ∧`
  the candidates of `[size, z)` known in `tc`) replaces `TailMeta`/`TailMetaW`'s third conjunct (`∀ z, zf = some z →
  size ≤ z`, now `TailZ.ge`). The coordinator's `∃ z, zf = some z ∧ z ≤ max size hi` is false after `cut`'s truncate
  of a tail whose size is not page-aligned (the truncate raises `zf` to `pageEnd` of the old size, above `hi`);
  `TailZ` says what the writer past the size and the sync need: every byte past the size has known candidates
  (`OsMeta.pc`), and a sync keeps that (`TailZ.synced`: `syncZ` is the size). Kept by writes inside the size
  (`TailZ.pwPost_in`), syncs, and full writes (`ZeroPg.write`, `CutHdr.lean`). `ZeroPg` (`TailZ` without the
  candidates) is the pipeline file's (`pipeFile`'s new conjunct): `cut`'s new tail gets `TailZ` after its sync
  from it (`metaChain_zeroPg`). `TailMetaS.of_sync` (`wal-close17`) carries `TailZ.synced`.
- **Obligations** (new or restated statements): `Create`'s and `ReadAll`'s returned handle, and
  `os.File.Truncate.specWalTail`'s post (`TailMetaW`), now carry `TailZ`; ReadAll's tail from disk has `zf =
  pageEnd size`, `cz = 0`, so it gets `TailZ` only after `ZeroToEnd`'s truncate (`cz ≥ pageEnd` of the old end).
  **`filePipeline.alloc`'s `ZeroPg` is a `sorry`** (true of the state, but neither `trFile`, `os.OpenFile.
  specCreateTruncS`'s post, nor `preGrown`, `fileutil.Preallocate`'s, says anything of `zf`/`cz`: both posts must
  carry it).
- **Finding 2 restated**: `sz = o0 + |out|` is false of `ReadAll`'s `ZeroToEnd` window (truncate to `wr`, then
  `fallocate` back to the old size: the size is the old one, above `wr`). What the window's fdatasync needs is
  rather that the bytes of `bs` past the write position are zero-valued (`cut`'s window: none; `ZeroToEnd`'s: the
  growth's zeros); not added.
- **Finding 3 (the `TailWin` past-size clause)**: not added. Its proposed form needs `wal-tc7`'s `walAbsD_rzStart`
  to show the truncate's cut-off candidates `RzCands`-shaped (they are `ByteOk`'s old bytes past `wr`, durable
  zeros when `z0 < |S|`, plus the truncate's `(0, n)`), and `TailLast.win` a `SegExact` premise.
- **Not done**: task 4 (the writer past the size, `encode.specTail`, `sync`); bboltfs's `DB.init`/`DB.initCrash`
  (their posts state the exact `OsMeta` `{m with size := max m.size 16384}.synced`, whose `cz` the first write now
  raises when `zf ≤ 16384`: the posts' `cz` should be `pwCz m 0 16384 16384`, and `initCrash`'s proof needs a
  `WReach` lemma giving a completed write's `cz` exactly).

**W6, seventeenth session (branch `wal-save17`, 2026-11-14): minibolt repaired; `alloc`'s `ZeroPg` needs the
extension; finding 3's clause amended (design).**
- *Task 1 (done, pushed)*: minibolt's `DB.init.spec`/`DB.init.specCrash` (`initDoneMeta`) state `cz := pwCz m 0 16384
  16384` (the first, complete write of four pages raises it; the metas' writes after the sync stay below the zeros the
  sync made known, `pwCz_eq_of_lt`, so they keep it). `os.File.WriteAt.specCrashS`'s success post gains `nn = |data|`
  (its proof had it, `hfk`), and **`WReach.czInv`/`WReach.cz_done`** (`Spec/os/CrashSt.lean`): a completed `WriteAt`
  leaves `cz = pwCz m off |data| |data|` whatever its short writes and retries (each attempt announces up to the same
  end, so its `zf` is the start's raised to it, and the attempt that completes raises `cz` exactly as one complete write
  would). Clients repaired: `Open`, `OpenLemmas.stored_of_init`, `DB.commit.wp_proof_crash`. Ledger 2026-11-14. The
  part's minibolt `Results` builds.
- **Task 2 (not done): `filePipeline.alloc`'s `ZeroPg` does not follow from `trFile`/`preGrown` posts** (the `sorry`
  stays). Two gaps, both of the model, not of the code:
  1. *A `fallocate` growth leaves `cz` where it was* (`rsCz false = cz`) while its announcement raises `zf` to the target
     (`max z tg`). Landed in full at an unaligned `sz`: `pageEnd sz ≤ max sz cz` fails (`ZeroPg`'s last clause); landed in
     part (`sz' < tg`): `zf = tg` above the page of the size. The truncate path (`preallocExtendTrunc`) raises `cz` to
     `pageEnd` of the target and is fine. A partial `fallocate` then the truncate is fine at the end but not in between,
     so no clause of `preGrown` alone composes through `preGrown_trans` (its intermediate state has neither `ZeroPg`
     nor a bound on `zf` by its own size; a bound by the target needs the target, which `preGrown` does not name).
  2. *The leftover `N.tmp`* (`wp_createTmp`'s `os.OpenFile.wp_truncS` arm): truncating an arbitrary `trFile i False`
     gives `zf = max z (pageEnd s)`, `cz = max cz (pageEnd s)`: `ZeroPg` only if the leftover had `pageEnd z ≤ max (pageEnd
     s) cz`; a leftover from `alloc`'s own error path after a partial `fallocate` (`zf` = the target, `cz` behind) has
     not, so `trFile` cannot carry the fact unconditionally either.
  `SegmentSizeBytes` is 64000000 = 4096 x 15625, page-aligned, so with an aligned `sz` gap 1's full landing is fine;
  but gap 1's partial case and gap 2 remain (they would need a bound by the pipeline's `sz` on every leftover, i.e. in
  `tmpClaim`/`walTmpsRes`, in the invariant). **Proposed (untrusted extension change, the coordinator's call)**: a
  `fallocate` landing raises `cz` when the file had `ZeroPg` (`rsCz false m tg sz' := if ZeroPg m then max cz (pageEnd
  (max z tg)) else cz`; sound: `ZeroPg m` with `MetaOk.cz`/`zc` gives the page cache zero from the size on, and
  `fallocate` writes no page cache). Then `ZeroPg` is kept by every resize outcome and by complete writes, so `trFile`
  carries `ZeroPg m` unconditionally (`newMeta`, a truncate, a file from disk with `zf = pageEnd size`, `alloc`'s error
  path, `filePipeline.run`'s `zerosA_trFile` from a `pipeFile`) and `preGrown` carries `ZeroPg m → ZeroPg m'`
  (composes through `preGrown_trans`); `alloc` then needs nothing about `sz`. Not done here: `wal-tc9` edits the
  extension now, and the change is a full rebuild.
- **Task 3 (not done; design)**: finding 3's clause (`q = (0, 0) ∨ (q.1 = 0 ∧ q.2 ∈ rz) ∨ (q.1 = S b ∧ 0 < q.2)` for the
  known candidates past `|bs|`) is false of `ZeroToEnd`'s window: `ReadAll` truncates to `wr = z0 = |S|` (nothing
  appended), and the cut-off bytes past `z0` are `old`'s, durable, with candidates `[(old b, 0)]` (`ByteOk`, `s = false`,
  `ex = []` past `|S|`), nonzero where a torn append left bytes (what `ZeroToEnd` is for; `tailStop` is what makes them
  harmless). `cut`'s window is fine (`z0 < |S|`: `old` is zero from `z0`). Also a window's own bytes in `[wr, |bs|)` are
  unconstrained in `TailWin`, so `walAbsD_rzStart` from a window cannot show the clause for the bytes it cuts off.
  Amended design: **`WinShape S old rz b q := q = (old.getD b 0, 0) ∨ (q.1 = 0 ∧ q.2 ∈ rz) ∨ (q.1 = S.getD b 0 ∧ 0 <
  q.2)`**, and `TailWin` gains `∀ b, lay.wr ≤ b → (∀ x, g.bs[b]? = some x → ∀ q ∈ x.2, WinShape … b q) ∧ (g.bs.length ≤
  b → b < g.om.hi → ∃ c, g.om.pc b = some c ∧ ∀ q ∈ c, WinShape … b q)`. `TailLast.win` gives the bytes part from
  `ByteOk` (`(old b, 0) :: ex`, `ex` stream-valued, positive stamps) and the past-size part needs `SegExact` (`hi =
  |bs|`: empty range). `walAbsD_rzStart` (cut-off bytes: theirs `++ [(0, n)]`, `n ∈ rzMeta`'s `rz`; past the old size:
  `rsTail`'s `m.pc b ++ [(0, n)]` from the old clause), `walAbsD_rzLand` (the same candidates, `segBytesX_rzLand`), a
  growth (its zeros' stamp in `rz` only with `rsPostK true`) and the writer past the size (`m.pc b ++ [(S b, n)]`, `0 <
  n`) each keep it. Users to repair: `Abs`, `RzStepPure`, `RzLand`, `SaveAbs`, `CutTail`, `WinCrashW`, `TailSyncPure`.
- *Task 4*: not started (it waits on task 3's clause and on the window's size fact, finding 2).
- *Seeding note*: Lake did not rebuild `Proof/io/ReaderStream`, `Proof/io/ReadFull`, `Spec/io/ReadFull` (hard-linked
  artifacts from the seed, source changed by `wal-readall17`): unlink a seeded module's artifacts when its source differs
  from the seed's (`cmp` the sources), never overwrite them in place.

**W6, eighteenth session (branch `wal-save18`, 2026-11-14): `alloc`'s `ZeroPg` proved (the extension's `MetaOk.ce`
and `rsCz`); task 2 (the amended `TailWin`) not started.**
- *Extension (untrusted ghost, `GooseLang/Ext/Fs`)*: the coordinator's `rsCz` (a `fallocate` landing raises `cz`
  when the file had `ZeroPg`) is not provable from the in-flight `MetaOk` alone: a partial landing at `w < tg` needs
  the page cache zero on `[w, tg)`, which the in-flight `OsMeta` (`cz` the old one, `zf` raised to `max z tg`) does not
  record. What makes it provable is a true fact of Linux the model kept but the ghost did not state: **`MetaOk.ce`**
  (the page cache is zero past the size's last page: only `OsFile.land`, `synced` and `ofDisk` write it, never there;
  every `MetaOk` construction repaired: announce, both finishes, both syncs, boot). Then **`rsCz tr m tg`** (now over
  the whole `OsMeta`): an `ftruncate` landed raises `cz` to `max (rsHi …) (pageEnd zf)` (the cache is zero from the
  new size on, unconditionally); `fallocate`'s growth landed (in full or in part) raises it to `pageEnd (max zf tg)`
  when `m.size < tg ∧ pageEnd size ≤ max size cz` (the cache zero from the old size on), else keeps it. A resize that
  did not land keeps the announcement's `OsMeta` (raising `cz` there too was possible, but it would change `rsUnMeta`,
  the WAL's `rzMeta`, under `wal-tc10`). `resize_done_worldK` takes `hgrow : tr = false → size ≤ tg` (a `fallocate`
  never shrinks: needed for `ce`). Lemmas: `rsCz_past`, `rsCe_past`, `le_rsCz`; vocabulary **`OsMeta.ZfGe`**,
  **`OsMeta.ZeroPg`** (the WAL's `ZeroPg`, `CutHdr.lean`, is the same body: defeq) with `zfGe_announce`,
  `zfGe_rsPost`, `zeroPg_rsPost_true` (from `ZfGe`), `zeroPg_rsPost_false` (from `ZeroPg`). `os/Base.lean`:
  `rsCz_same`, `rsCz_announce` (the raise does not depend on its own announcement), `rsPost_rsPost` kept.
- *Posts (ledger 2026-11-14)*: **`preGrown i m w Z`** (the grown `OsMeta` has `ZeroPg` if `Z`; `GrowMeta` keeps
  `ZfGe`; `preGrown_mono`, `preGrown_trans` keeps the second's `Z`): `Preallocate`/`preallocExtend` post `Z := err =
  nil ∧ m.ZeroPg`, `preallocExtendTrunc` `Z := err = nil ∧ m.ZfGe` (a landed `ftruncate` makes `ZeroPg`, so the
  `ENOTSUP`/`EINTR` fallback after a `fallocate` that did not land is fine). **`trFile i P`** gains `m.ZfGe ∧ (P →
  m.ZeroPg)`, not an unconditional `ZeroPg` (the proposal): a leftover from `alloc`'s error path after a `fallocate`
  that did not land has none, and needs none (the `O_TRUNC` open makes it, `trFile_of_rsDone` from `ZfGe`).
  `zerosA_trFile` takes `ZfGe` (`filePipeline.run`: from `pipeFile`'s `ZeroPg`). **`filePipeline.alloc`'s `ZeroPg`
  `sorry` discharged** (`#print axioms` of `filePipeline.alloc.wp_proof`: no `sorryAx`). Trust base: no baseline
  changes; `etc/tcb-collections/linuxfs.txt`'s roots (the `osfs` examples) do not reach the WAL (no `Link` yet), and
  `--check` refused to run here (it needs the whole repository built). The extension's importers (80 leaves, 3065
  jobs) build. Also repaired: `alloc`, `WAL.Close`, `WAL.CloseOpening` discharged `zap.Logger.Error`'s premise as `⌜lg
  ≠ null⌝` (a stale `Spec/go_uber_org/zap` artifact's); its spec takes `zapLoggerOk lg` since `173a618ddd`.
- *For other units*: `Create` gets `ZeroPg` of its file from `Preallocate`'s post now if it wants it (`newMeta` has
  it; `Create.lean` only repaired for the pattern). `ZeroToEnd`'s growth by `ftruncate` (and, with `ZeroPg` of the
  truncated meta, by `fallocate`) gives `ZeroPg`: the `TailZ` obligation of `ReadAll`'s handle can use
  `zeroPg_rsPost_true`/`_false`.
- *Not done*: task 2 (the amended `TailWin` shape: `WinShape`, the users `Abs`, `RzStepPure`, `RzLand`, `SaveAbs`,
  `CutTail`, `WinCrashW`, `TailSyncPure`; seventeenth session's design stands) and task 3.
- *Build note*: seeding by `cp -al` shared `.trace` files; unshare them (the coordinator's `find … -links +1`
  command) and delete the artifacts of modules another worktree rebuilt (here `Proof/io/{ReadFull,ReaderStream}`,
  `Spec/io/ReadFull`, `Proof/path/*`, the `zap` specs).

**W6, nineteenth session (branch `wal-save19`, 2026-11-14): the amended `TailWin` in; finding 2 as `WinZero`; the
window's fdatasync, static half.**
- *Task 1 (done, `eb56487843`)*: **`WinShape S old rz b q`** (`q = (old.getD b 0, 0) ∨ (q.1 = 0 ∧ q.2 ∈ rz) ∨ (b < |S| ∧
  q.1 = S.getD b 0 ∧ 0 < q.2)`: the seventeenth session's design with the third disjunct inside the stream, so that a
  `Save`'s commit keeps it, `WinShape.snoc`) and **`WinCands S old wr g`** (`TailWin`'s new last conjunct), stated over
  `segBytesX` rather than as two clauses: `g.om.hi ≤ |segBytesX g|` (every byte the `OsMeta` may leave past the bytes is
  known: `segBytesX` stops at the first unknown one, `segBytesX_length_le_max`) and every candidate of `segBytesX g` from
  `wr` on has `WinShape … g.om.rz`. Equivalent to the design's form, and the resize lemmas already speak `segBytesX`:
  `WinCands.rz` transports it across a first step (`segBytesX_rzSeg`/`_rzGrow`: same length, `RzCands`), `WinCands.same`
  across a landing (`segBytesX_rzLand`'s map equality, `segBytesX_rzLandG`'s prefix), both in `RzW1.lean`.
  **`TailLast.win` takes `SegExact`** (`ByteOk.winShape`: `(old b, 0) :: ex`, `ex` stream-valued inside the stream).
  `pcRunN`/`pcRun`/`segBytesX` and their lemmas moved up in `Abs.lean` (before `TailLast`); `pcRunN_length_le` moved from
  `RzGrow.lean` to `Abs.lean`. **Statement changes (internal lemmas)**: `walAbsD_rzStart` takes `tg ≤ g0.om.hi` and the
  `segBytesX` relation across the step (`hX`, from `segBytesX_rzSeg`/`_rzGrow`); `walAbsD_rzLand` takes `size ≤ hi`;
  `walAbsD_rzLandG` takes `hzf`, `hzs`. Repaired: `RzStepPure`, `RzLand`, `RzGrow`, `SaveAbs`, `TruncSupPure`
  (`CutTail`, `WinCrashW`, `TailSyncPure`, `TruncSup` needed nothing: their patterns end in `-`).
- *Task 2 (finding 2, done)*: **`WinZero lay g`** (the tail's bytes from `wr` on are zero-valued) is a third conjunct of
  `WalAbsD.last`'s window branch (`TailWin ∧ lo ≤ wr ∧ WinZero`; accessors `WalAbsD.winLo` (now `.2.1`),
  `WalAbsD.winZero`; **`WalAbsD.zeroPast`**: of any tail, given F-Z, `TailLast.winZero`). Not in `TailWin` (an exact tail's
  bytes past `wr` are `old`'s, zero only by `TailZeros`, which `WalAbsD` does not carry, and `lastWin` has many users) and
  not a handle fact (`walTailW`'s `tm` does not see `wr`; the invariant does, and every window keeps it: `cut`'s truncate
  and the writes past the size leave nothing past `wr`, a truncate's first step keeps the values, `rzSeg_fst`, a growth's
  bytes are zeros). Kept by `walAbsD_rzStart` (new premise `hz : WinZero lay g0`, from `zeroPast`), `walAbsD_rzLand`
  (vacuous), `walAbsD_rzLandG` (new premise `hZ`: F-Z of the in-flight layout), `walAbsD_snoc`. `rzGrow_pure` and
  `rzLandG_pure` take `hZ : TailZeros lay` (**for `wal-tc12`**: the supplies have it from `walTailsRes`).
- *The window's fdatasync, static half (`TailSyncWin.lean`, no `sorry`)*: **`syncLayW lay pre g`** (`syncLay` with `old`
  zeros past `wr`: `old.take wr ++ replicate (|bs| - wr) 0`; for an exact tail `syncLay` keeps `old`, whose bytes past `wr`
  the fdatasync made durable unchanged), **`walAbsD_syncW`** (the static relation after the fdatasync of a window tail,
  `wr` the stream's end: exact, `TailLast` from `TailWin`'s `ByteOk` below `wr`, `WinZero` past it; `tailStop` from
  `decStep_zeros_any`, moved from `ReadAllFiles.lean` to `Abs.lean`), `tailZeros_syncW`, `tailBound_syncW`.
- *Not done*: the window's fdatasync, crash half (`crashOk_syncW`): as `crashOk_sync` with `fo0`'s tail the image as of
  the last sync of size `f.size = |bs| ∈ [lo, hi]` (`metas`); its byte clause below `wr` from `ByteOk`'s head as now, from
  `wr` on (past `lo`, `winLo`) by the zero arm of `FileCrashedR` or a stamp-0 candidate (needs `valAt c 0 = 0 ∨ ∃ s,
  (valAt c 0, s) ∈ c`); `hw0` by `w1G_sync` with the tail's `segBytesOf` its `segBytesX` (`segBytesX_getD_lt` below
  `|bs|`, the image no longer), the other segments exact (`metas`); then `crashTo_congr_lay` (it does not read `old`) and
  `crashTo_tailM` over `walAbsD_syncW`/`tailZeros_syncW`/`tailBound_syncW`. Then `walsOk_sync`/`dirKeysOk_sync`'s window
  forms and task 3 (the writer past the size, `encode.specTail`, `sync`'s core lemma): not started.

**W6, twentieth session (branch `wal-save20`, 2026-11-14): the window's fdatasync proved through the invariant step;
the writer past the size blocked on two invariant facts (designed).**
- *Task 1 (done, no `sorry`; `TailSyncWin.lean`)*: **`crashOk_syncW`** (the nineteenth session's design: the old
  condition at the tail imaged as of the last sync, `syncImg g0.bs f.size` with `f.size = |bs|` from the synced
  `OsMeta`; below `wr` `ByteOk`'s head, from `wr` on `valAt0_cases` (`valAt c 0` is a candidate's value or zero) with the
  zero arm past `lo` (`winLo`); `zf`/`tc` clauses vacuous (`hzf`, `size = |bs|`); `hw0` by `w1G_sync` over `segBytesX`,
  the other segments exact since their inodes differ from the tail's); **`walsOk_syncW`**, **`dirKeysOk_syncW`**, and
  **`syncLay_any`** (the synced layout, `syncLay` if exact else `syncLayW`, with every pure fact the invariant step needs).
  **`walInvBody_sync`'s success premise drops `SegExact g0`** (it calls `syncLay_any`); so **`wp_tailFsync` and
  `syscall.Fdatasync.wp_tail` take `TailMetaW`** (weaker; `fileutil.Fdatasync.wp_tail` passes `TailMeta.win`), and the new
  **`fileutil.Fdatasync.wp_tailW`** is the fdatasync of a tail in a window (pre `walTailW … (tm := TailMetaW)`, success
  post `walTailW` with `TailMeta`, by **`TailMetaW.synced`**; failure post the window kept). Statement changes: internal
  lemmas only (no spec). Leaves (`WAL__Close`, `__ReadAll`, `__Save`, `__SaveSnapshot`, `__saveEntry`, `__saveState`,
  `__syncIdle`, `openLast`) build.
- **Finding 1 (blocks the writer past the size): `WalAbsD.winLo` (`lo ≤ wr` in a window) is false of a write past the
  size from an exact tail.** The announcement keeps `lo = min lo (max size (off + n)) = size` and raises `hi` past the
  size, so the window opens with `lo = size`, while `wr = off < size` (a `Save` crossing `SegmentSizeBytes` writes from
  inside the file); after a short write (`EINTR`, `k < size - off`) or between `WriteAt`'s attempts, `wr' = off + k <
  size = lo` with the window open. Only a completed write ends at `wr' = off + n > size ≥ lo`. What `winLo` is for
  (`crashOkA_rzStart`, `crashOk_syncW`): a crash's zero at a byte from `wr` on must be allowed by the window's `OsMeta`.
  **Proposed replacement (internal)**: `WinHead lay g := ∀ b, lay.wr ≤ b → b < |segBytesX g| → ((0 : w8), 0) ∈
  ((segBytesX g).getD b (0, [])).2` (each such byte has a zero stamped 0: `ByteOk`'s head `(old b, 0)` with
  `old b = 0` by F-Z since `z0 ≤ wr`; the zeros past `zf`; a truncate's cut-off bytes keep their head; candidates are
  only appended, so every step keeps it; `syncTail`'s `durB` is stamped 0). It makes the zero arm unnecessary
  (`crashOk_syncW` then takes the candidate arm for every byte; `crashOkA_rzStart`'s old-window crash allows the zero as a
  candidate) and holds of exact tails too (`tail_zero_cand`), so `winLo` can go. Repair: `Abs.lean`'s `last`, the
  resize lemmas that construct the window branch (`walAbsD_rzStart`/`rzLand`/`rzLandG`), `walAbsD_snoc`, and the two
  users; coordinate with `wal-tc13` (the same lemmas).
- **Finding 2 (blocks it too): the candidates past `hi` are unconstrained.** A write past the size gives each new byte
  `m.pc b ++ [(S b, n)]` (`pwTail`, `zs`) for `b ∈ [size, off + n)`, and `WinCands` of the new tail needs `WinShape` of
  `m.pc b`'s candidates there; `WinCands` of the old tail covers only `b < hi` (`segBytesX` stops at `hi`; an exact
  tail's covers nothing past its bytes). `TailZ` makes `m.pc b` known for every `b ≥ size` (`tc` in `[size, z)`, zeros
  past `z`), but not shaped. **Proposed**: `PastCands S old g := ∀ b c, g.om.hi ≤ b → g.om.pc b = some c → ∀ q ∈ c,
  WinShape S old g.om.rz b q`, for every tail (both branches), with `|old| ≤ hi` in a window (the `wal-tc12` entry's
  option (b); then a zero `(0, 0)` past `hi` is `(old b, 0)`). True in every run: past `hi` the only candidates known are
  the zeros past `zf` (a sync empties `tc`; a truncate's cut-off bytes and a write's announced bytes are below the `hi`
  they raise). Kept trivially by steps that raise `hi` past what they announce; established by `Create`/`cut` from the
  pipeline file (`tc` past the preallocated size empty: an obligation on `trFile`/`preGrown`, or a sync before the file
  enters the layout).
- *Design of the steps past the size (for the next session, once findings 1 and 2 are in)*: the announced tail
  `segAnnW g0 off data n := { segAnn g0 off data n with om := wrMeta g0.om off data n }` (`segAnn` for in-size writes:
  `wrMeta_in`); its bytes are `|g0.bs|` long (`cfRange` stops at the size); window branch: `TailWin` from the old (bytes
  below `wr` untouched; `WinCands` from the old one below `|bs|` plus `(S b, n)`, `n > 0`, `b < |S|` since `data <+:
  S.drop off`; past `|bs|` from `pwTail` and `PastCands`/`WinCands`), `WinZero` (bytes from `wr` on: unchanged values),
  `hi ≤ |segBytesX|` from `TailZ`'s known candidates. The finish: `wp_osPWriteFinishK true` (`pwPostK true`: `pwTail`
  kept past the new size after a short write), `finBytes`' bytes past the old size `zs` (= `m.pc`, `hpc`), `old` extended
  with zeros only if `|bs|` passes `|old|` (vacuous for `tailStop`, kept by `TailZeros`). Then `wal.tailWriterW`
  (`io.writerStreamP` with guard `tailOk` minus its size clause, the state `walTailW … (max sz (o0 + |out|)) out
  TailMetaW`), `encode.specTail`, and `sync.wp_proof` as `wp_proofIn` with `wal.tailWriterW` and
  `fileutil.Fdatasync.wp_tailW` (its post's `sz := max sz (o0 + |out ++ pend|)`).
- *Not done*: tasks 2 and 3 (blocked on findings 1 and 2: an internal invariant change shared with `wal-tc13`'s
  lemmas, for the coordinator to schedule).

**W6, twenty-first session (branch `wal-save21`, 2026-11-14): `|old| ≤ hi` in a window (`WinLast`); `WinHead`
defined but `winLo` kept (the truncate at `wr` needs it); `PastCands` not an invariant fact (false at a crash's
tail); `wal-tc13`'s old-length map merged, the window's fdatasync taking its element.** Untrusted, internal; no spec
or trusted change.
- *Done (builds)*: **`WinLast`** (`Abs.lean`), `WalAbsD.last`'s window branch as one definition: `TailWin ∧ lo ≤ wr ∧
  WinZero ∧ |old| ≤ hi` (`WalAbsD.oldHi`; **`WalAbsD.oldHi_any`**: `|old| ≤ hi` of any tail, an exact one as long as
  `old`). Constructions repaired: `walAbsD_win` (takes `WinLast`), `walAbsD_rzStart` (`hi' = max hi tg`), `walAbsD_rzLand`,
  `walAbsD_rzLandG` (from the in-flight layout's `oldHi_any`). **`WinHead lay g`** (each byte of `segBytesX g` from `wr` on
  is at or past `lo`, or has a zero candidate `(0, s)`), `WinHead.of_lo`, `WalAbsD.winHead`; `crashOk_syncW` now takes
  its zero arm from `WinHead` (a zero candidate, else the zero arm past `lo`), so it no longer reads `winLo`.
- **Finding A (the coordinator's `WinHead` is false; amended)**: "every byte from `wr` on has `(0, 0)`" fails in
  `ZeroToEnd`'s window on a crash's tail: its bytes past `z0` are the crash image's (torn, not zero: `WalsStart`,
  `TailZeros` does not hold there, `wal-tc13` entry), and the truncate to `z0` gives them `[(old b, 0), (0, n)]`. The
  disjunctive form above holds of every window (`ZeroToEnd`'s and `cut`'s have `lo ≤ wr`; a write past the size from an
  exact tail has `(old b, 0) = (0, 0)` below the size by F-Z, which the writer has from `walTailsRes`, and `lo` = the size
  past it) and is what `crashOk_syncW` and the truncate's crash step need of the bytes.
- **Finding B (blocks replacing `winLo`)**: the truncate at `wr` (`crashOkA_rzStart`'s window case, through
  `walTail_truncSup`) needs `lo ≤ wr` for the *size* a crash may leave, not only the bytes: its announcement lowers `lo`
  to `wr`, so the crashes of size in `[wr, lo)` are new, and `crashOkA_rz` (inclusion of the new crashes in the old) fails
  for them. A write past the size from an exact tail has `lo` = the old size `> wr` from its announcement until it
  completes (and for ever after a failed one, the handle lost), so the invariant cannot keep `winLo`; but a handle at rest
  always has it (a complete write ends at `wr ≥ lo`; `cut`'s and `ZeroToEnd`'s truncates set `lo = wr`). The supply cannot
  see the handle: `os.truncSup` is `∀ m0` and its tie cannot name the `OsMeta`. Options (for the coordinator; none made):
  (A) **a handle-level fact**: `walTailW` gains `(lo = size = hi) ∨ lo ≤ o0 + |out|` (true at rest, every construction
  has it), and `os.truncSup`/`File.Truncate.specAu` a predicate `P` on the `OsMeta` handed to the supply (default `True`;
  `specAu` takes `P m` of its caller's), so `walTail_truncSup` gets `lo ≤ wr` for a window (plumbing: the 19 `walTailW`
  unfoldings, the four fileutil AU specs passing `True`); (B) **the crash step without it**: a window's crash of size `s ∈
  [wr, lo)` is the old window's of size `lo` with zeros in `[s, lo)` (allowed by `WinHead`), then a reader lemma that zeros
  past `wr` read as the end of the file (new `W1G`/`CrashTo` reasoning); (C) an extension law lowering a file's `lo` while
  nothing is in flight (sound: weaker knowledge), used by the writer before a write past the size, the step from an exact
  tail then `crashOkA_win`'s case. Recommended: (A) (mechanical, no new crash reasoning). Until then `winLo` stays in
  `WinLast` beside the derived `WinHead`, and the writer past the size stays blocked on it.
- **Finding C (`PastCands` is not an invariant fact)**: a crash's tail has `om = initMeta f` with `tc = tailMap f` (the
  disk's bytes past the size in its last page, stamp 0, any value), and `ZeroToEnd`'s truncate keeps them past `hi` (the old
  size); so "the candidates known past `hi` are shaped" is false of `ZeroToEnd`'s window (and of the crash's exact tail). No
  write happens there; writes happen only through a handle whose `OsMeta` came through a sync (`tc = ∅`), `Create`'s or
  `cut`'s pipeline file (task 2), and the writer's own steps (which raise `hi` over every candidate they add). So the fact
  belongs to the handle: **`PastZ m := ∀ b c, m.hi ≤ b → m.pc b = some c → ∀ q ∈ c, q = (0, 0)`** in `TailMeta` (exact
  handles; `OsMeta.synced` has it, `tc = ∅`) and in the writer's state in a window (`TailMetaW ∧ PastZ`, kept by writes and
  truncates: both raise `hi` past what they add; not of `ZeroToEnd`'s post, whose fdatasync restores it). With `|old| ≤ hi`
  (in `WinLast`) a zero stamped 0 past `hi` is `(old b, 0)`, the `WinShape` the writer's new bytes need. Not made (task 3).
- **`wal-tc13` merged** (its old-length map `walOldsRes`, `walOldFrag`, `OldStep`), conflict in `walInvBody_sync`
  resolved: the window's fdatasync (`syncLayW`) keeps `|old|` only if the tail is as long as `old`, so
  **`walInvBody_sync` takes `walOldOpt dir cuts ko`** (`walOldFrag dir cuts k` if `ko = some k`; `walTailsRes_oldOpt`
  agrees it) and its success premise `SegExact g0 ∨ ko = some |bs|`; `syncLay_any` takes `¬ SegExact g0 → |bs| = |old|`
  and returns `|L.old| = |old|` (so `OldStep.same`). `wp_tailFsync`/`syscall.Fdatasync.wp_tail` take `ko` with `(lo = size
  = hi) ∨ ko = some size`; `fileutil.Fdatasync.wp_tail` passes `none`; **`fileutil.Fdatasync.wp_tailW` takes
  `walOldFrag dir cuts sz`** (no users yet). This settles `ZeroToEnd`'s fdatasync (regrown to `|old|`, the map's element
  minted at its pre) and leaves `cut`'s (`sync.specCut`: truncated short of `old`) on `wal-tc13`'s item 1, now sharper:
  with the map as is, `cut`'s window fdatasync is not a step. The way out I recommend: (a') limited to the map, i.e. let
  `OldOk` hold only while nothing is appended past `z0` (`lay.wr = lay.z0`, `ZeroToEnd`'s flow; `cut`'s tail has
  appended records or is past them; to check: a `cut` with nothing appended since the generation's start, a tail
  found past the segment size), minting only then; the window fdatasync after appends then changes `old` freely.
- *Task 2, stated (not repaired)*: with finding C the obligation on a file entering the layout (`Create`'s first
  segment, `cut`'s next one, from the pipeline: `filePipeline.alloc`'s `preGrown`/`trFile` posts) is `PastZ` of its
  `OsMeta` in the handle's `TailMeta` (nothing past `hi` but zeros stamped 0: `tc` empty from the preallocated size on,
  or a sync before the file enters the layout); `TailMeta`'s other users (`OsMeta.synced`: `tc = ∅`) have it. Where
  `alloc` gets it: `preGrownH`'s `PcKeep` and `Z → ZeroPg` (the zeros past the grown size) say what `pc` is past the
  size, but not that `tc` holds nothing else (to check when `PastZ` is added, task 3's first step).
- *Not done*: task 3 (blocked on finding B); task 2's repair (waits on `PastZ`, task 3).
- *Build*: seeded from `agent-a0d5232984f8fe5f2`; the 210 importers of `Abs.lean` build (`lake build` of their leaves,
  2837 jobs), and `WAL__ReadAll`/`ReadAllTail` after merging `wal-int` `6330e224cd`.

**W6, twenty-second session (branch `wal-save22`, 2026-11-14): option (A) made (the truncate told the handle's
`lo ≤ wr`), `winLo` replaced by `WinHead` in the invariant; `PastZ` in the handle's tail facts (task 2).**
Untrusted; two Lean-first spec changes (ledger: `os.truncSup`'s `P`, `os.ftDoneH`'s `TcFrom`); no trusted change, no
client-visible ghost state. Merged `wal-int` (`wal-tc14`'s lent tails).
- *Task 1 (done, builds)*: **`os.truncSup K p tg P`** (`P` defaults to `True`) tells the supply `m0.lo ≤ tg ∨ P m0`;
  **`os.File.Truncate.specAu`** takes `P` and `P m` (later attempts start from announced or landed states, `lo ≤
  tg`: `os.announce_lo_le`, `os.rsPost_lo_le`); the fileutil proofs pass `fun _ => True`. **`walTailW`**'s pure facts
  end in **`LoWr m (o0 + |out|)`** (`(lo = size ∧ hi = size) ∨ lo ≤ wr`, `Handle.lean`; `TailMeta.loWr`, `LoWr.mono`);
  the constructions repaired (`TailWriter`'s two, `WAL__cut`'s new handle, `TruncWalTail`'s post: `lo = wr` after the
  landing). **`walTail_truncSup`** takes `P := (LoWr · wr)`; **`tailCrashStep_rzStart`/`rzStart_pure`** take `hlo :
  ¬ SegExact g0 → g0.om.lo ≤ lay.wr` from it instead of the invariant. **`WinLast`'s second conjunct is `WinHead lay
  g`** (was `lo ≤ wr`); `WalAbsD.winLo` deleted, `WalAbsD.winHead` a projection; the window constructions
  (`walAbsD_rzStart`, `walAbsD_rzLand`, `walAbsD_rzLandG`) give `WinHead.of_lo` of what they proved. Not made: the
  coordinator's "19 unfoldings" plumbing was not needed beyond the five constructions (the pattern `⟨…, hfd0⟩` takes
  the new fact as part of its last component where it is not built).
- *For the growth supplies (`ZeroToEnd`'s, not written)*: `rzGrow_pure`'s `hlo : min lo tg ≤ wr` no longer comes from
  the invariant: from the handle's `LoWr` through the supplies' `P` (`fallocSup` has no `P` yet: add one as
  `os.truncSup`'s when the supply is written), or from `lo ≤ wr` of the truncate to `o` before them (its landing).
- *Task 2 (done for the handle's facts, builds)*: **`PastZ m`** (`Handle.lean`): every candidate known at or past
  `hi` is a zero stamped 0 **or by a known resize** (finding: the twenty-first session's `(0, 0)` only is false after
  `cut`'s truncate, which announces its zeros, stamp `n`, up to `pageEnd` of the old size, past `hi`). In
  **`TailMeta`** and **`TailMetaW`** (last conjunct; `TailMeta.pastZ`, `TailMetaW.pastZ`). Laws: `PastZ.of_pc`,
  `PastZ.announce`, `PastZ.pwPost` (any write keeps it: `hi` is raised over what it adds), `PastZ.synced`,
  `PastZ.of_tcFrom` (a resize's outcome). The truncate's post needs the candidates' values, which the caller's half
  did not give: **`os.ftDoneH`/`ftUndoneH` carry `TcFrom m (max m.size tg) tc rz`** (`TcKnows.lean`: `rz ⊇ m.rz`, each
  candidate of `tc` from there on `m.pc`'s or a zero stamped 0 or in `rz`; `TcFrom.rsTail`, `TcFrom.trans`; ledger).
  **The obligation on the pipeline (alloc's `PastZ`) is moot**: no file enters a handle's tail before an fdatasync
  (`Create`'s `TailSynced`, `cut`'s `tailMeta_synced` after its header phase over the whole-resource writer,
  `ReadAll`'s after `ZeroToEnd`), and `PastZ.synced` holds of any synced `OsMeta`.
- *Next (task 3)*: the writer past the size with `PastZ` and `|old| ≤ hi` (`WalAbsD.oldHi_any`): a candidate `q` of
  `m.pc b`, `b ≥ hi`, has `WinShape S old m.rz b q` (`(0, 0) = (old b, 0)` past `|old|`, or `winShape_rz`); then
  `segAnnW`, `pwPostK true`, `wal.tailWriterW`, `encode.specTail`, `sync`, as designed in the twentieth session. The
  window's `WinHead` after a write past the size from an exact tail: bytes in `[wr, size)` have `(old b, 0) = (0, 0)`
  (F-Z), bytes from the size on are at or past `lo` (the announcement keeps `lo` at the size).
- *Build*: the 42 leaves of the changed modules (`etc/importers.py --leaves`), after merging `wal-int` `1948f75dbb`.

**W6, twenty-third session (branch `wal-save23`, 2026-11-14): task 1 done; the crash condition of any tail step in a
window (the writer past the size's hard part) proved; `WinLo` in the invariant; the writer's steps themselves not
started.** Untrusted, internal; no spec, trusted or client-visible change.
- *Task 1 (done)*: **`PastZ.winShape`** (`Handle.lean`): with `PastZ m` and `|old| ≤ m.hi`, every candidate of `m.pc b`
  at `b ≥ m.hi` has `WinShape S old m.rz b q` (`(0, 0) = (old b, 0)` past `|old|`, or a known resize's zero).
- *The decoding, abstracted (`TailCrashPure.lean`)*: `tail_frame_match`/`tail_decode` read the candidates only through
  `TailCands.mem_val` and `TailCands.asOf`; they are now **`tail_frame_matchV`/`tail_decodeV`** over two facts of the
  image, **`TailVals`** (each byte the intended stream's, or a zero past `max so z0`) and **`TailAsOf`** (each accepted
  frame core as of the last sync or all intended bytes); `tail_decode` (same statement) is their corollary.
- *The window's candidates (`TailCrashW.lean`, new)*: **`TailShape X so z0 rz cs`** (below `so` durable; from `so` on
  each candidate the intended byte or a zero past `max so z0`, the stamp-0 ones the byte under the stream, one below `z0`,
  a write's — positive stamp not in `rz` — the intended byte) gives `TailVals` (`TailShape.vals`, image bytes a candidate
  or a zero past `max so z0`) and `TailAsOf` from W1's `AsOfW` (`TailShape.asOf`: a frame as of a change is as of a
  *write*, so a resize's zero never counts: the resize amendment does the work). Sources: `TailCands.shape` (exact),
  **`tailShape_win`** (`ByteOk` below `wr`, `WinShape` from `wr` on), **`WalAbsD.tailShape`** (any last segment, over
  `segBytesX`, with F-Z).
- **`crashTo_tailW`**: `crashTo_tailL` for any tail: the image up to `|segBytesX g|`, its bytes candidates of
  `segBytesX g` or zeros past `max so z0`, over `TailShape` (W1's `rzOf` the tail's `rz`). Same proof, `g.bs` replaced by
  `segBytesX g`, `hex` gone.
- **`crashOkA_tailW`** (the `crashOkA_tail` pattern, no exactness on either side): the old condition at the old tail's
  image as of its last sync of its size (**`fileCrashedR_syncImg`**: below `wr` `ByteOk`'s head, from `wr` on `WinHead`
  or exact `ByteOk`), then `crashTo_tailW` on the new layout (**`crashImg_tail`**: the new crash's bytes from
  `FileCrashedR`, given `lo` and `zf` past `max so z0` and `hi ≤ |segBytesX|`). **`crashOkA_tailAny`** takes the new
  tail's facts from its `WalAbsD` (`tailShape`, `winLo_any`, **`WalAbsD.hiX`**) and only `zf ≥ |bs|` of both tails;
  **`crashOkW_tailW`** is `crashOkW_tail`'s form. So **every tail step whose new static relation is proved keeps the crash
  condition** (writes past the size, writes in `cut`'s or `ZeroToEnd`'s window, their finishes): the writer past the size
  needs only `WalAbsD` of its two layouts.
- **Finding (internal invariant, made): a window's `lo` must be past `max so z0`** (`WinLo`, fifth conjunct of
  `WinLast`; `WalAbsD.winLo`, `WalAbsD.winLo_any`). The window's crash may zero any byte from `lo` on (`FileCrashedR`'s
  zero arm), and the decoding accepts a zero only past the synced bytes and the frames found. True of every window: `cut`'s
  and `ZeroToEnd`'s truncates set `lo = wr ≥ so, z0`; a write past the size from an exact tail keeps `lo` at the size
  (`announce`'s `lo := min lo tg`, `tg ≥ size`: writes never lower `lo`); growths keep it. Repaired:
  `walAbsD_rzStart`, `walAbsD_rzLand`, `walAbsD_rzLandG` (`winLo_any` of the in-flight layout; `WalAbsD.oldHi` is now
  `.2.2.2.1`).
- *Next (task 2, the steps; design unchanged from the twentieth session, simplified by the above)*: `segAnnW g0 off data
  n := { segAnn g0 off data n with om := wrMeta g0.om off data n }` (`SegFl.Ok` holds of it for any `off ≤ size`);
  **`walAbsD_announceW`** (exact in-size: `walAbsD_announce`; else `walAbsD_win` with `WinLast`: `TailWin` from the old
  (`ByteOk.ann` in the range), `WinCands` (below `|bs|` the old candidates plus `(S b, n)`; past `|bs|` `wrMeta`'s `pc` is
  `pwTail`'s: `g0.om.pc b ++ [(S b, n)]` in the range, `g0.om.pc b` past it, all known by `TailZ`; `g0.om.pc b` shaped by
  `WinCands g0` below `hi0`, by `PastZ.winShape` from `hi0` on), `WinHead` (exact: `lo` = size, below it `(old b, 0) = (0,
  0)` by F-Z; window: the old one, candidates only appended), `WinZero` (values unchanged), `|old| ≤ hi'`, `WinLo` (`lo`
  unchanged)); then `walsOk` of the step by `crashOkW_tailW` (`zf' = max z (off + n) ≥ size`); `walAbsD_finishW` likewise
  (`pwPostK true`, `finBytes`' bytes past the old size `zs` = `m.pc`); the Iris steps `wp_tailPWriteStartW`/`FinishW`
  (`TailMetaW` in place of `TailMeta`, `PastZ` kept by `PastZ.pwPost`, `TailZ` by a past-size `TailZ.pwPost`, `LoWr`
  by `LoWr.mono`), the loop `wp_tailWriteAt` over them, `wal.tailWriterW`; then tasks 3-4.
- *Started*: `TailStepW.lean` (the window steps' pure pieces) with **`wrMeta_pc_ge`** (past the size, `wrMeta`'s `pc` is
  `m.pc` with the data's byte appended in the range, `m.pc` past it).
- *Build*: the 38 leaves of `Abs.lean`'s importers (212 modules) and `TailCrashW`, after the `WinLo` change and after
  merging `wal-int` `475414c88c` (2846 jobs).

**W6, twenty-fourth session (branch `wal-save24`, 2026-11-14): task 1 half done (the announce); found: the
window's below-`wr` `ByteOk` is false of `cut`'s flush, the tail outgrows `old`; the invariant amended.** Untrusted,
internal; no spec, trusted or client-visible change. Merged `wal-int` (`wal-tc17`).
- **Finding 1 (internal invariant, made): `TailWin`'s `ByteOk` below `wr` is false after a write in a window past a
  resize.** `cut` truncates the tail to its file position (`= size` when the `Save` wrote past the preallocated size),
  which announces zeros `(0, n_tr)` on `[size, pageEnd size)` (`rzMeta`'s `rsTail`, kept by `rsPostK true`); the
  flush after it writes there, and the written byte's candidates are `[(0,0), (0, n_tr), (S b, n)]`: `ByteOk`'s
  "every later candidate the intended byte, stamped positive" fails. Also a write past the size from an exact tail
  writes bytes in `[wr, size)` it needs `ByteOk` of, which the window's clause (below `wr` only) dropped. Repair
  (`Abs.lean`): **`TailWin`'s `ByteOk` clause is below the least crash size `lo`** (was `wr`; an exact tail's `lo` is
  its length, every window the resizes open has `lo ≤ wr`, a write past the size keeps `lo` at the size, so its next
  bytes keep `ByteOk`); **`WinLow`** (sixth conjunct of `WinLast`): each byte from `lo` to `wr` is **`WinW`** (the
  stream's value, every candidate `WinShape`), with `ByteOk.winW`, `WinW.snoc`/`mono_rz`; accessors
  **`WalAbsD.low`** (below `wr`: `ByteOk` below `lo`, else `lo ≤ b`, `max so z0 ≤ b` and `WinW`) and
  **`WalAbsD.lowW`**, `WalAbsD.winLow`. Consumers repaired: `fileCrashedR_syncImg`, `crashOk_syncW` (a `WinW` byte's
  sync image: its candidate or FileCrashedR's zero arm, `lo ≤ b`), `WalAbsD.tailShape` (`tailShape_win` at threshold
  `min wr lo`), `walAbsD_syncW`, `lastSeg_synced_durable`; constructions `TailLast.win`, `walAbsD_rzStart`,
  `walAbsD_rzLand`, `walAbsD_rzLandG` (their `lo' ≤ wr`: `WinLow` from `lowW`), `walAbsD_snoc`.
- **Finding 2 (made): a write past the preallocated size makes the tail longer than `old`** (`|bs'| = off + k >
  |old|`), so `TailWin`'s `|bs| ≤ |old|` and the derived `wr ≤ |old|` fail; `old`'s bytes past its end read zero
  (`getD`), and `old` cannot be extended (the lent key fixes `|old|`, `walLentRes_insert_same`). **`TailWin`'s third
  conjunct is `z0 ≤ |old|`**; **`syncLayW`'s `old` is `(old ++ 0^wr).take wr ++ 0^(|bs| - wr)`** (length `|bs|` without
  `wr ≤ |old|`; `syncOld_*`, `tailZeros_syncW`/`_syncW0` without `hwo`).
- *Task 1, done*: **`segAnnW`** (`TailStepW.lean`: `segAnn`'s bytes, `wrMeta`), `segAnnW_ok`/`_in`/`_getElem?`/
  `_length`, `wrMeta_lo_eq`/`_hi_eq`/`_rz_eq`/`wrMeta_pc_some`, `TailZ.pc_isSome`, `pcRunN_length_eq`,
  `segBytesX_getD_ge`, and **`walAbsD_announceW`** (any write from inside the file, the tail exact or in a window:
  exact and inside the size `walAbsD_announce`, else `walAbsD_win` with `WinLast`; takes F-Z, `TailZ` and `PastZ` of
  the tail's `OsMeta`, the handle's). **`segFinW`** (`pwPostK true`, `finBytes`), `pwPostK_true_pc` (its `pc` is
  `wrMeta`'s), `pwPostK_true_in`, `SegFl.Ok.eq_ann`, **`segFinW_getElem?`** (written range: the data's value, below
  the old size the announced candidates, past it `zs` then the data's), `segFinW_length`.
- *Next*: **`walAbsD_finishW`** (designed; premises: the announced layout's `WalAbsD`, `fl.Ok g0`, `off ≤ wr`,
  `k ≤ |data|`, `0 < n`, `data <+: S.drop off`, the finish's `zs` (`zs[j] = m.pc (size + j)`, its length)): exact
  announced tail ⇒ inside the size, `segFinW = segFin` (`pwPostK_true_in`), `walAbsD_finish`; else a window with
  `wr' = max wr (off + k)`, `lo`, `hi`, `rz` unchanged; written bytes below `lo` `ByteOk` (written: `walAbsD_finish`'s
  `hrng` argument), from `lo` on `WinW` (below the old size: the announced byte's candidates, `WinLow`/`lowW` below
  `wr`, `WinCands` from `wr`; past it `zs_j = m.pc b` ⊆ the announced `segBytesX`'s candidates, `WinCands`); `WinCands`
  of the new tail from the announced one (`pwPostK_true_pc`: the same `pc`, `|segBytesX| = hi`); `WinHead`/`WinZero`
  unchanged bytes past `wr'`. Then `walsOk` by `crashOkW_tailW` for both steps, the Iris steps, the loop,
  `wal.tailWriterW`, tasks 3-4.
- *Build*: the 37 leaves of `Abs.lean`'s importers (2850 jobs) after the invariant change; after merging `wal-int`
  (`wal-tc17`) the same 37 leaves (2854 jobs), `TailCrashPend`'s `pendVals` repaired (reads below `wr` through `WalAbsD.low`).

**W6, twenty-fifth session (branch `wal-save25`, 2026-11-14): tasks 1-3 done, task 4 half (`sync.wp_proof`).** The
writer past the preallocated size is proved end to end: `walAbsD_finishW`, the two Iris steps, the `WriteAt` loop,
`wal.tailWriterW`, `encoder.encode.wp_proofTail` (`specTail`) and `WAL.sync.wp_proof` (`sync.spec`, its `sorry`
gone). Untrusted, internal; no spec, trusted or client-visible change (no ledger entry). Merged `wal-int`
(`wal-readall26`, `wal-leaf3`, `wal-tc18`).
- *Task 1 (`TailFinW.lean`)*: **`segFinW_candsX`**: the finish changes no candidate `segBytesX` shows
  (`(segBytesX (segFinW fl g0 k zs)).map (·.2) = (segBytesX g0).map (·.2)`, given the announced tail's `segBytesX`
  reaching `hi`: below the old size the announced candidates, past it `zs ++ [(data, n)]` = `wrMeta`'s `pc`, past the
  new bytes the same `pc`). So **`walAbsD_finishW`** (exact announced tail: inside the size, `walAbsD_finish`;
  window: `WinCands`/`WinHead` the announced tail's through the candidate equality, `ByteOk` below `lo` by
  **`ByteOk.fin`**, `WinLow` from the announced tail's `WinLow`/`WinCands` (`hcand0`), `WinZero` the bytes past `wr'`
  unchanged). Premises as designed plus `hpre : data <+: S.drop off` (a window's byte gives no value fact: its
  candidate `(data b, n)` could be a known resize's zero in `WinShape`); `lay.so ≤ off` derived from the written
  byte's positive candidate. Helpers `pcRunN_getElem?_known`, `segBytesX_known`, `segBytesX_getElem?_known`,
  `candsX_getD`, `pwSize_past`.
- *The handle's facts between attempts (`TailMetaPw.lean`)*: **finding (internal, made): `TailZ` fails between the
  attempts of a `WriteAt` past the zeros known** (a short write moves `zf` to its data's end without raising `cz`:
  `pwCz` raises only on a complete write); it holds after the last attempt, which writes all of its data up to the
  `WriteAt`'s end `E`. **`TailZE m E`** (`TailZ` with the page fact `∨ z ≤ E`), **`TailZE.pwK`** (any write from inside
  the file ending at or below `E` keeps it; a complete one to `E` gives `TailZ`), `TailZE.pc_isSome`,
  **`PastZ.pwK`**, **`LoWr.pwK`**, **`TailMetaL`** (`TailMetaW` with `TailZE`), **`TailMetaL.fin`**. `walAbsD_announceW`
  now takes `∀ b ≥ size, (pc b).isSome` (was `TailZ`).
- *Task 2 (`TailWriterW.lean`)*: **`tailCrashStep_any`** (`crashOkA_tailAny` as a `TailCrashStep`), both steps through
  `walInvBody_tailW` (`walsOk_tailA`, `dirKeysOk_tailA`). **`wp_tailPWriteStartW`** (`off ≤ size`; `TailMetaL`;
  `walTailFlW`: the halves around the range at `cfLo`/`cfHi`), **`wp_tailPWriteFinishW`** (`wp_osPWriteFinishK true`;
  post: `PwCut`'s `k = 0 ∨ off + k ≤ maxBytes`, `TailMetaL`, `TailMetaW` after a complete write to `E`, size `pwSize`,
  the write's candidate on every byte of the range below the new size: `segFinW_candW`). **`wp_tailWriteAtW`** (the
  loop keeps `TailMetaL … E ∧ size = max m.size wr ∧ wr ≤ max off maxBytes ∧ LoWr … E`; arithmetic in `twW_*`; post
  `TailMetaW`, size `max m.size (off + |data|)`, the end below `max m.size maxBytes`, `LoWr`), **`wp_tailWriteW`**,
  **`wal.tailWriterW`**: guard **`tailOkW`** (`tailOk` without its size clause, the stream's end below 2^62: the
  model's `Write` reaching `offMax` is not modelled, a panic), state **`walTailWS`** (`walTailW … (max sz (o0 + |out|))
  out TailMetaW ∗ ⌜o0 + |out| ≤ max sz maxBytes⌝`). `TailWriter.lean`'s refusal paragraph points here.
- *Task 3 (`encoder__encodeTail.lean`)*: **`encoder.encode.wp_proofTail`** over `specG` and `wal.tailWriterW`; the
  guard's 2^62 from **`ownEncoder_pend_le`** (`|pend| ≤ 2·wmBytes`, `TailWriterW.lean`) and **`frame_walRecEnc_lt`**
  (`recSize < 2^47` gives a frame below 2^48). Its callers (`saveEntry`, `saveState`, `SaveSnapshot`) still take
  `specTail` as a hypothesis: the part's WAL has no `Link.lean` yet, so nothing discharges it there.
- *Task 4 (`WAL__sync.lean`)*: **`WAL.sync.wp_proof`** = `wp_proofIn` over `wal.tailWriterW` (`walTailWS` from the
  handle's `walTailW … TailMetaW` at `o0 + |out| ≤ sz`) and `fileutil.Fdatasync.wp_tailW` at size `max sz (o0 + |out ++
  pend|)`, the post's `sz ≤ 0xffffffff000` from `walTailWS`'s bound. **Not done**: `specCut`, `specC` (`syncLay_any`,
  posts via `TailMetaS.of_sync`) and dropping the hypotheses from `cut`, `Close`, `Save`, `SaveSnapshot`, `saveEntry`,
  `saveState` (the latter three take `specTail`, now provable: `wp_proofTail`).
- *Build*: seeded from `agent-a0d5232984f8fe5f2`; each new module by `lake build` (`TailMetaPw`, `TailFinW`,
  `TailWriterW`, `encoder__encodeTail`, `WAL__sync`), then the leaves of `TailStepW`'s and `WAL__sync`'s importers
  (`WAL__Close`, `encoder__encodeTail`) after merging `wal-int` `ada9c4d732`.

**W6, twenty-sixth session (branch `wal-save26`, 2026-11-14): `specC`, `specCut`, the WAL's links.** Untrusted; no
spec or trusted change (no ledger entry). Merged `wal-int` `cbd9e25409` (`wal-tc20`).
- *Task 1 (`WAL__sync.lean`)*: **`WAL.sync.wp_core`**: `sync`'s body over exactly what it reads of the handle (`w.lg`,
  `unsafeNoSync`, `w.encoder` and the encoder, the tail's `walTailW … TailMetaW`, `w.locks`, the lock file, `encEnv`,
  the package's init, `walOpenW`), post the tail at size `max sz (o0 + |out| + |pend|)` with **`TailMetaS`** (synced and
  durable) and the size below `maxBytes`. `fileutil.Fdatasync.wp_tailW` now gives `TailMetaS` on success
  (`TailMetaW.syncedS`; `TailFdatasync` imports `CloseHandle`). **`sync.wp_proof`** = `wp_core` over `walHandleIn`
  (`TailMetaS` weakened by `walTailW_mono`), **`wp_proofC`** (`specC`) = `wp_core` over `walHandleC`, **`wp_proofCut`**
  (`specCut`) = `sync.spec` at `h.sz = o0 + |out|` (`cutSynced h` is `sync.spec`'s post handle). The wrappers start with
  `wp_start_folded` (a triple about the call itself is then applied). No `sorry`.
- *Task 2*: the WAL's `Link.lean` (section 8, "Links"). Making it build found **two kinds of import clash** among the
  WAL's own proofs, which no module had imported together before: eight lemma names declared twice in `WalFs`
  (`segsDs_cut` in `ReadAllEnd`/`CutHdrStream`, `chainOk_crcHead` in `ReadAllEnd`/`RepairDecode`, `mem_walNames` and
  `walNames_nodup` in `OpenNames`/`CutCommitPure`, `osMeta_agree'` and `tailVar_upd` in `CutAu`/`TailWriter`/`TruncSup`,
  `crEnt_writes` in `BrokenAu`/`CreateJ`; each copy used in its file only: made `private`), `segHalves` defined
  differently in `OpenFiles` and `ReadAllExit` (the latter renamed `segHalvesL`), and `checkWALNames`/
  `filePipeline.alloc` importing the main tree's `Spec.go_uber_org.zap.{String,Logger__Warn,Error,Int64}` where the rest
  import the part's copies. Also repaired: `ZeroToEndAu`'s success post (`ZteMeta`'s two halves grouped; it failed to
  build on `wal-int` `cbd9e25409`).
- *Build*: seeded from `agent-aa4f2084215d70d50` (partly stale: that worktree was rebuilding after a merge); `WAL__sync`,
  then the leaves `WAL__Close`, `WAL__ReadAll`, then `Link` (3034 jobs) and `BrokenAu`/`RepairDecode`.

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

**For `wal-readall20` (from `wal-tc12`, 2026-11-14).** `ZeroToEnd.specAu`'s success post now carries `ZteMeta m m'`
(`PcKeep m m' ∧ (m.ZfGe → m'.ZeroPg)`, `DefsAu.lean`; ledger). `ZeroToEnd.specWalTail` is still **not written**: the
growth supplies need an invariant fact on the tail's old length (I3b, `wal-tc12` entry). Keep it a hypothesis of
`ReadAll.wp_proof`.

**For `wal-readall20` (from `wal-tc11`, 2026-11-14).** `ReadAll`'s `ZeroToEnd` instance is named
`ZeroToEnd.specWalTail` but **not written**: its supplies wait on three extension facts (I3b, `wal-tc11` entry) and its
`TailZ` post on `ZteMeta` (ledger 2026-11-14, proposed). Keep it a hypothesis of `ReadAll.wp_proof` under that name.

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

**W1 amended; the tail's window in the handle (branch `wal-tc3`, 2026-11-14).** Tasks 1-2 of the coordinator's
decision (option 1); task 3 (the supplies) not done.
- *Task 1* (W1 log, thirteenth session): W1's change disjunct asks that each byte's candidate as of `n` be stamped
  by a change that wrote a nonzero byte of the core (`WroteIn`), so a resize's zeros do not make a frame written;
  `cut`'s truncate inside a frame no longer blocks `CrashOk` in its window. The kind is not recorded (§2.5's
  amendment says why "nonzero" and not "a `pwrite`"). `W1G`'s users take `AsOfW.weak` (the old form).
- *Task 2* (`Handle.lean`, `WAL__cutTail.lean`, built with every importer): **`TailMetaW m bs`** (`TailMeta` with
  `m.lo ≤ m.size ≤ m.hi` for `lo = size = hi`; `TailMeta.win`); `walTailW` and `walHandleIn` take a last optional
  argument **`tm := TailMeta`** (call sites unchanged; a partial application `walTailW … sz` is now a lambda,
  so `TailWriter`'s two re-folds take a `simp only []`). **`os.File.Truncate.specWalTail`'s success post is
  `walTailW … (o0 + |out|) out TailMetaW`**, and **`WAL.sync.specCut`'s pre `walHandleIn P Mr w dir h TailMetaW`**
  (its post the exact `walHandleIn … (cutSynced h)`: the fdatasync closes the window). `WAL.cut.wp_proof`
  unchanged (it passes the post to `specCut`'s pre). The truncate's landed `OsMeta` (`rsPost true m tg tg`,
  `ftDoneH`'s, any `tc`) satisfies `TailMetaW` (`lo = size = tg`, `hi` the old size, `zf ≥` the old size).
- **For `wal-cut10`/`specCut`'s prover**: `specCut` now starts from the window (`TailMetaW`); its proof closes
  it at the fdatasync's commit (`walInvBody_tailW` with the synced layout's `WalsOk`, the W6 entry above).
- **Open (task 3)**: (1) the pure `CrashOk` of `cut`'s window layout (from `walAbsD_rzStart`'s/`fileCrashedR_rsPostK_rz`'s
  state; the reader's argument of `crashTo_tailM` with the image's length free in `[lo, hi]`, each byte from `wr`
  on `0`, the old byte, or the flush's; the accepted frame straddling `wr` is intended by `AsOfW`, W1 log
  thirteenth session); (2) `ReadAll`'s `ZeroToEnd` (`segBytesOf` extended by `g.om.pc` on `[|bs|, hi)`, `SegCrashAt`
  giving those candidates; **done**: `W1G`'s premise is the frame's fit, `p + frameCore ≤ |bs|`, instead of
  `(img i).length ≤ |bs|`, `crashTo_tailM` derives it from the image's length);
  (3) `truncSup`/`fallocSup` from `walInv` via `walInvBody_tailW`, then `specWalTail`'s proof and `ZeroToEnd`'s
  instance.

**W1 restated exactly (branch `wal-tc4`, 2026-11-14).** Task 1 of `wal-tc3`'s list redone exactly (W1 log,
fourteenth session): the state records resize stamps (`OsFile.rzs`, trusted bookkeeping, pending review),
W1's change disjunct asks each byte's candidate as of `n` be a `pwrite`'s (`p.2 ∉ f.rzs`), so the
split-frame crash with a zero share is allowed and `cut`'s truncate window excluded. `W1G` takes the
resize stamps known per file (`rzOf`); `CrashOk` passes none until the ghost link (`OsMeta.rz`, the W1 log's
plan) is in. **Open (task 3, unchanged)**: the ghost link first; then the pure `CrashOk` of `cut`'s window
(with `segRzOf`), `ReadAll`'s `ZeroToEnd` (`segBytesOf` by `pc`, `SegCrashAt`), `truncSup`/`fallocSup` from
`walInv` via `walInvBody_tailW`, `specWalTail`'s proof and the `ZeroToEnd` instance.

**For `wal-tc5`, from `wal-save13` (2026-11-14).** `os.File.Truncate.specWalTail`'s pre is now `walTailW …
TailMetaW` (a `Save`'s writes past the preallocated size leave the window open when `cut` runs), and `cut.spec`'s
pre `walHandleIn … TailMetaW`. Task 1's crash side needs `W1G` over the known candidates past `|g.bs|` (W6 log,
thirteenth session, design item 1), which your `ZeroToEnd` growth needs too: if you make it, I build on it;
`wal-save13` has not touched `Abs.lean`, `CrashTakeSeg.lean` or `Inv.lean`.

**The ghost link in; the window's `CrashOk` plan (branch `wal-tc5`, 2026-11-14).** Task 1 done (W1 log, fifteenth
session): `CrashOk` sees the resize stamps the layout's `OsMeta` halves know (`segRzOf`), including a truncate's in
flight (`rzMeta`) and landed (`rsPostK true`). Task 2 not done; what is in and the plan:
- *In*: `RzW1.lean` (`W1G.drop_rz`: the window's `W1G` gives the exact tail's, the truncate's zeros dropped).
- *Plan for the truncate window's pure `CrashOk`* (one lemma, `crashOkA_win`, the `crashOkA_tail` pattern): from
  `CrashOkA lay0` (exact tail `g0`) to `CrashOkA lay` (tail `g`, same inode, `|g.bs| = |g0.bs|` or with the `pc` run,
  `lay0.wr ≤ g.om.lo`, `g.om.hi ≤ |g0.bs|`, bytes below `wr` unchanged, each byte `RzCands g.om.rz`): images as of
  the last sync for `hok` (`syncImg g0.bs |g0.bs|`, as `crashOkA_tail`), then a generalization of `crashTo_tailM`
  (**`crashTo_tailL`**: in place of `hfc`, for the tail's image `f`, `max so z0 ≤ f.size ≤ |g.bs|` and each byte below
  `f.size` one of `g.bs`'s candidates; its proof is `crashTo_tailM`'s with `himgl` an inequality: `himg`, `hlenI`, the
  `W1G` frame bound and `hcsb` are the only uses) on `lay0` with `W1G.drop_rz` for the hypothesis. The image facts:
  below `wr` the runs (`g0`'s bytes); from `wr` on the value is a candidate of `g0` or 0, and `(0, 0) ∈ g0.bs[b].2` there
  (`TailLast`'s `ByteOk` with `w = s = false` gives `(old b, 0)` first; `old b = 0` by `TailZeros`, `z0 ≤ wr`).
  **Obligation for the supply's prover**: `0 < n` (the truncate's number; `wp_osFtruncateStart_au`'s `hn` gives it when a
  byte is cut off, `wr < size`; nothing changes otherwise).
- **The landed state needs `W1G` over the known candidates past the bytes** (as the tail writer past the size and
  `ZeroToEnd`'s growth: W6 log, thirteenth session, design item 1; mine, `wal-maxb14` builds on it): after the landing
  the layout's `g.bs` is `wr` long, so `W1G`'s `p + frameCore ≤ |bs|` no longer covers the frame straddling `wr`.
  Design (not made): `segBytesOf lay i := g.bs ++ pcRun g.om |g.bs|` (the run of `g.om.pc` from `|g.bs|` below `g.om.hi`,
  stopping at the first unknown); `w1G_of_W1`'s premise and `SegCrashAt` gain `∀ b c, g.om.size ≤ b → g.om.pc b = some c
  → f.cand b = c` — idle and for a write in flight from `MetaOk.pc_cand` (add it to `FileCrashAt`; `cfMeta` is the token's
  `meta`), for a resize in flight from `tok_cand` (`crashRestAt_take_tok` to export `∀ b c, inRange ti.lo ti.hi b →
  ti.m0.size ≤ b → ti.m0.pc b = some c → f.cand b = c ++ [(ti.val b, ti.n)]`: `rzMeta`'s `rsTail` entries; outside the
  range `rzMeta.pc` is the token's). Exact segments are unchanged (`hi = |bs|`: `segBytesX g = g.bs`); the users of
  `segBytesOf_some`/`w1G_sync` then rewrite bytes below `|g.bs|` (`getD` of the prefix). With it, `rsPostK true`'s `tc`
  (`rsTail`: the cut-off bytes' candidates then `(0, n)`) makes the landed window's `segBytesOf` the in-flight one's, so
  `crashOkA_win` covers both.
- *Not started*: `truncSup`/`fallocSup` from `walInv` (`walInvBody_tailW`), `os.File.Truncate.specWalTail`'s proof, the
  `ZeroToEnd` instance (no name yet for `wal-read13` to swap in).

**`W1G` past the ghost's bytes is in (branch `wal-tc6`, commit `e813841e16`, 2026-11-14; for `wal-maxb14`,
`wal-readall15`).** Built on the design above, as designed. Names (all untrusted):
- `Abs.lean`: **`pcRunN m b k`/`pcRun m b`** (the candidates `m.pc` knows from `b` on, below `m.hi`, up to the first
  unknown; ghost value 0), **`segBytesX g := g.bs ++ pcRun g.om |g.bs|`**, **`segBytesOf lay i`** now maps
  `segBytesX` (was `·.bs`). Laws: `pcRunN_getElem?`, `segBytesX_of_hi` (`om.hi ≤ |bs|` → `= g.bs`),
  `segBytesX_getElem?_lt`/`_getD_lt`/`_length_le`, `segBytesX_getElem?_ge` (past `|bs|`: below `om.hi`, `om.pc b =
  some y.2`), **`segBytesX_cand`** (the candidates of `segBytesX g` are a file's from `om.size = |bs|`, the `bs`
  fact and the `pc` fact). `segBytesOf_some` now gives `segBytesX g = bs`; **`segBytesOf_some_ex`** (all segments
  `om.hi ≤ |bs|`) the old form. `w1G_of_W1`'s premise is over `segBytesX g`.
- `GooseLang/Ext/Fs/CrashTakeFiles.lean`: **`FileCrashAt`** gains `∀ b c, m.size ≤ b → m.pc b = some c → f.cand b =
  c` (from `MetaOk.pc_cand`; `crashRestAt_take`, `crashRestAt_take_tok`).
- `CrashTakeSeg.lean`: **`crashRestAt_take_tok`**'s third conjunct is now `∃ f, st.fs.files !! ti.ino = some f ∧
  (ti.kind.isResize → ti.n ∈ f.rzs) ∧ ∀ b c, inRange ti.lo ti.hi b → ti.m0.size ≤ b → ti.m0.pc b = some c → f.cand
  b = c ++ [(ti.val b, ti.n)]` (`tok_cand`); **`rzMeta_pc_cand`** (what `rzMeta` knows past the size is the file's),
  `OsMeta.pc_congr`; **`SegCrashAt`** gains `∀ b c, g.om.size ≤ b → g.om.pc b = some c → f.cand b = c` (idle,
  write and resize cases); `crashGood_exists`/`walCrash_pure`'s `hfiles` likewise.
- `TailCrash.lean`: `segBytesOf_mem` gives `segBytesX g`; **`segBytesOf_mem_ex`** (exact) the old form.
- Not yet: a write in flight past the size (`SegFl.Ok`'s `g.om = cfMeta …`, the token's `OsMeta`, which forgot the
  announced bytes' `tc`): its `segBytesX` stops at the announced range (`pc` none there); `wal-maxb14`'s design
  item 2 (the announced layout's `tc` the token's candidates, as `rzMeta`) extends it, with `TokPast`/`tok_cand`
  (now exported) for the crash side.

**The truncate window's `CrashOk`; what the supplies still need (branch `wal-tc6`, 2026-11-14).** Task 2 done (W1
log, sixteenth session): `crashTo_tailL`, **`crashOkA_win`** (`WinCrash.lean`). Task 3 (the supplies,
`specWalTail`, `ZeroToEnd`'s instance) not started; what it needs, found on the way:
- *The landing step*: the invariant keeps only the current layout's `CrashOkW`, so at the truncate's finish
  `crashOkA_win` (from the exact `lay0`) is not available; the finish needs `crashOkA` from the in-flight layout
  (`rzMeta`, `rsAnn`) to the landed one (`rsPostK true`): `FileCrashedR` of the landed by
  `fileCrashedR_rsPostK_rz`, `W1G` by equal candidates of `segBytesX` (the landed `pcRun` is the in-flight `rsAnn`'s
  candidates, values aside: `rsTail` below the old size), `segRzOf` equal (`n :: m.rz` both). The generic step is
  proved, **`crashOkA_same`** (`WinCrash.lean`: the tail's crashes no more, `segBytesX` no shorter with the same
  candidates, the stamps kept); the instance's facts (`fileCrashedR_rsPostK_rz`, the `pcRun` of `rsTail` equal to
  `rsAnn`'s candidates) are the supply's.
- *The window before the truncate*: `specWalTail`'s pre is `TailMetaW` (a `Save`'s writes past the preallocated
  size), so `lay0` may itself be in a window; `crashOkA_win` and `crashTo_tailL` need `SegExact g0` and `TailLast`
  (`tailCands_of_abs`). The general form is `crashTo_tailL` over `TailWin` with the candidates past `|bs|` from
  `segBytesX` (`wal-maxb14`'s write-past-the-size layout), then `crashOkA_win` window to window. Until then the supply
  can be proved for an exact `lay0` only (a `walTailW … TailMeta` pre, `cut`'s case when no `Save` since the last
  cut wrote past the size).
- *The supply* (`truncSup (walTailKey dir γ ∗ tailVar γ ½ tg) i wr` from `walInv`): at the start's commit,
  `walInvBody_tailW`, the invariant's halves of `g0` (`segResF` with no change) with the caller's for the whole
  `OsMeta`/bytes, then the continuation at `rzSeg g0 true wr n` (`walAbsD_rzStart` for `WalsOk`'s static relation,
  `crashOkA_win` for its `CrashOkW`; `0 < n` from `wp_osFtruncateStart_au`'s `hn` when `wr < size`); at the finish,
  the token back, `rsOutT`'s `rsDoneK true` split (`rsPostK_withTc`), the landing step above. `fallocSup` likewise
  for `ZeroToEnd`'s growth (`RzCands` with a growth's zeros; its `segBytesX` covers the regrown bytes).

**The truncate from a window; what the supplies have now (branch `wal-tc7`, 2026-11-14).** W1 log, seventeenth
session. For the supply (`truncSup (walTailKey dir γ ∗ tailVar γ ½ tg) i wr`, not started):
- *Start's commit* (the in-flight layout `tailLay lay pre (rzSeg g0 true wr n) lay.wr`): static relation
  `walAbsD_rzStart habs hs (le_refl) (min_le_right)`; crash condition `crashOkA_rzStart` (its `0 < n` and the
  window's `g0.om.TcZ` from the commit's `⌜0 < n ∧ m0.TcZ⌝`, `m0 = g0.om` by agreement; `zf ≥ size` from the
  handle's `TailMetaW`, which the supply must carry through `K` or the invariant: **open**, `K` cannot mention
  `m0`; the window's `lo ≤ wr` is `WalAbsD.winLo`); the alternative layout (`halt`) none for a tail with no rename
  pending; `TailZeros`/`TailBound` unchanged (`lay.so`, `z0`, `old` unchanged); `segResF` with `SegFl.OkR`
  (`rzSeg_ok`).
- *Finish's commit* (landed, `rsDoneK true`): the layout's tail `rzLand g0 wr n` (both halves agree on
  `rsPostK true true …`: the caller's `withTc tc rz` existential is the owner's), crash condition `crashOkA_same`
  from the in-flight layout with `fileCrashedR_rsPostK_rz` and `segBytesX_rzLand`; static relation: not yet
  (a window with `|bs| = wr`: `walAbsD_win` with `TailWin` below `wr` from the in-flight one, `lo = wr`).
  Undone (`e ≠ 0`, the in-flight layout stays, or `ftUndoneH`): not yet.
- `fallocSup` for `ZeroToEnd`'s growth: as above with `rzSeg g0 false tg n` (no bytes cut off, the growth's
  bytes past the old size `rzMeta`'s candidates); `segBytesX_rzSeg`/`crashOkA_rzStart` are for `tr = true` only.

**The truncate's start fact and landing (branch `wal-tc8`, 2026-11-14).** W1 log, eighteenth session. For the
supply (`truncSup (walTailKey dir γ ∗ tailVar γ (H, md, cuts, wr, i, none)) i wr`, not started):
- *Start's commit*: `zf ≥ size` and the window's `TcZ` both from the commit's `m0.TcZ` (`OsMeta.TcZ` now carries
  `zf ≥ size`); the crash step `tailCrashStep_rzStart`, the static relation `walAbsD_rzStart (le_refl _)
  (min_le_right _ _)`, then `walsOk_tailA`/`dirKeysOk_tailA` for `walInvBody_tailW`'s continuation; `segResF` of
  `F' = <[g0.ino := ⟨t, 0, [], n, g0.om, g0.bs, some (true, wr)⟩]> F` by `rzSeg_ok` (needs `0 < wr`); both
  halves of the tail record (`walInvBody_tailW` returns both) updated to `some fl`; the finish's update built
  by `osAUnc_coiter` over the key, the record's half at `some fl` and `walInv`.
- *Finish's commit, landed* (`rsDoneK true`, `zs = []`): the tail `rzLand g0 wr n` (the invariant's half of
  `rsPostK true true …`, the caller's `(rsPost true m0 wr wr).withTc …` the other: `os.ftDoneH`), crash step
  `tailCrashStep_rzLand`, static relation `walAbsD_rzLand`, the record back to `none`.
- *Finish's commit, not landed*: blocked on `rsUndoneK` (W1 log, eighteenth session, last item).
- *Abort* (either step): the state unchanged (`tailLay lay pre g0 lay.wr = lay`, `<[dir := lay]> Ls = Ls`).

**`rsUndoneK` (branch `wal-tc9`, 2026-11-14).** W1 log, nineteenth session. For the supply (`truncSup`, not started),
the finish's not-landed arm (`rsOutT`, `e ≠ 0`, `rsUndoneK true true i wr m0 xs0 n` as `m0.cut = none`): the layout
stays the in-flight one (`tailLay lay pre (rzSeg g0 true wr n) lay.wr = lay`), `F` loses the tail's entry; the
invariant's `segRes` of the in-flight tail from its half of `rsUnMeta true true m0 wr n` (`= rzMeta true m0 wr n`) and
of the bytes (the take half it kept, joined with half of `rsAnn n xs0`); the caller's `os.ftUndoneH` with `tc rz :=
rsTail …, n :: m0.rz`. In the finish, the current tail `g1` is `rzSeg g0' true wr n` for `g0' := { g1 with om := fl.m,
bs := fl.bs }` (`SegFl.OkR` and `SegG`'s eta), `fl` pinned by the tail record's agreement. Before `specWalTail`: the
`TailZ` gap (W1 log, nineteenth session, last item; `os.ftDoneH`/`ftUndoneH` need `TcKnows`).

**`MetaOk.ce` and `rsCz` (branch `wal-save18`, 2026-11-14).** W6 log, eighteenth session. The extension's landed
resizes now raise `cz` (`rsCz tr m tg`: an `ftruncate` always, past `pageEnd zf`; `fallocate`'s growth when the old
size's page was known zero), over the new `MetaOk.ce` (the page cache zero past the size's last page). `rsPost`'s `cz`
changed (`rsPost_cz`, `rsCz_same`, `rsCz_announce` in `os/Base.lean`); `rsUnMeta`/`rzMeta` unchanged (a resize that
did not land keeps the announcement's `cz`). For `wal-tc10`: any proof that computed `(rsPost …).cz` as `max cz
(rsHi …)` (or `cz` for a growth) now has `rsCz tr m tg` (`le_rsCz` for the bound).

**The growth's pieces (branch `wal-tc11`, 2026-11-14).** W1 log, twenty-first session. Done: the pure pieces
(`RzGrow.lean`), `TcKnowsF` on `fallocDoneH`. **Not done: `fallocSup`, the growing truncate's supply, `ZeroToEnd`'s
instance.** The instance is named **`ZeroToEnd.specWalTail`** (to write, beside `os.File.Truncate.specWalTail`: the
tail's halves at `o = wr` in, `TailMetaW` with `TailZ` out, proved from `ZeroToEnd.specAu` with the three supplies).
The supplies need, at the commits, facts the extension's specs do not export (all true of its model; untrusted
changes to `GooseLang/Ext/Fs`, which `wal-save18` edits, so not made here):
1. *`fallocate`'s first step*: `0 < n ∧ m.TcZ` (as `wp_osFtruncateStart`'s; `wp_osFallocStart`, then
   `wp_osFallocStart_auW` and `fallocAuW`'s commit carry it, as `os.truncAuW` does). `crashOkA_rzGrow` needs both.
2. *`fallocate`'s not-landed outcome*: `rsUndoneK m.cut.isNone false` in `rsOutF` (`wp_osFallocFinishK`'s undone arm
   by `resize_undone_worldK`, which exists for either kind); `fallocOutH`'s undone arm then up to `tc`/`rz` with
   `TcKnowsF m tg m.size tc`. With the exact announcement the WAL's tail would forget the candidates past the size
   its in-flight layout knows (`rzMeta`'s `rsTail`), and its crash condition fails.
3. *`rsDoneK`'s `zs`*: `∀ j c, m.pc (m.size + j) = some c → j < zs.length → zs[j]? = some c` (`resize_done_worldK`'s
   `zs` are `(f.cand (size + j)).dropLast`, and `RsFacts.hcandP` gives `f.cand b = c ++ [(0, n)]`): `rzLandG`'s
   `hzs`, for both growths (`fallocate`, the fallback's truncate past the size). Subsumes the existing zeros clause
   under `OsMeta.TcZ`.
Also for the supplies: the growth's target must be at most the tail's `hi` (`ZeroToEnd`'s: the truncate to `wr` kept
`hi ≥` the old size; the tie must carry the old size, since the supplies quantify over the state), `min lo tg ≤ wr`
(the truncate's landing has `lo ≤ wr`), and `w ≤ |old|`.

**The extension facts in; the growth supplies need the tail's old length (branch `wal-tc12`, 2026-11-14).** W1 log,
twenty-second session. Done: the three extension facts (`wal-tc11` entry, 1-3; `rsDoneK`'s new conjunct is in addition to
the zeros clause, not in place of it), `PcKeep`, `preGrownH`'s `PcKeep` and condition `Z`, `ZteMeta` on
`ZeroToEnd.specAu` (ledger). **Not done: `fallocSup` and the growing truncate's supply at the tail, `ZeroToEnd.specWalTail`.**
What blocks them (W1 log, twenty-second session, last item): the commits need `tg ≤ |lay.old|` and `tg ≤ g0.om.hi` (and,
for an exact tail found, `min lo tg ≤ wr` fails when `|old| > wr`: an exact tail of size `tg` grown to `tg` announces
nothing and stays exact, so `rzGrow_pure` needs an exact-case form without `hlo`), about the invariant's layout, which the
tie cannot name (`TailG` has no `old`) and the found state does not give. Options (an internal invariant change, for the
coordinator):
- (a) **A persistent agreement on the tail's old length**: a framed conjunct of `walInvBody` with an agree-map
  `(dir, lay.cuts) ↦ |lay.old|` (fixed within a generation for a given cuts list: `old` changes only at `cut`, which
  changes `cuts`, and at a crash, which reallocates), its fragments persistent; the tie then carries `oldFrag dir cuts tg`
  (`specWalTail`'s caller gets it where it learns `|old| = m.size`, e.g. at `ReadAll`'s pin, or by `walInvBody_tailW` at
  any tail step). Every step changing `Ls` re-establishes it (`tailLay` keeps `old`, `cuts`); `cut`, `Create`, the alloc
  insert. With it: `m0.size ≤ |old| = tg` (`TailWin`), so the growing truncate is a growth, `w ≤ tg = |old|`.
- (b) **A window fact `|lay.old| ≤ g.om.hi`** in `WalAbsD.last` (beside `winLo`; true: a window opens from an exact tail,
  `hi = |bs| = |old|`, and no step before the fdatasync lowers `hi`), giving `tg = |old| ≤ hi` with (a); without (a) it
  does not give `tg ≤ |old|`.
- (c) Spec premises instead (`fallocSup`/`os.truncSup` taking `m0.size ≤ tg ≤ m0.hi`, threaded through
  `preallocExtend`/`preallocExtendTrunc`/`Preallocate`/`File.Truncate.specAu`, `GrowMeta` keeping `hi`): gives `tg ≤ hi`
  but still not `tg ≤ |old|`, so (a) or an invariant `hi ≤ |old|` in windows (unclear: writes past `|old|`) is needed
  anyway.
Recommended: (a), plus (b) or an exact-tail precondition on `specWalTail` (`ReadAll`'s tail is exact). The pieces ready
for the supplies: `rzGrow_pure`, `rzLandG_pure` (`hzs` from `rsDoneK`'s new conjunct, `rzLandG`'s `zs`), `0 < n ∧ TcZ`
from the commit, `rsUndoneK` for the not-landed arm (the in-flight layout kept, as `walTail_truncFin`'s), `TcKnowsF.rsTail`
for `fallocDoneH`/`fallocOutH`.

**The amended `TailWin` and `WinZero` (branch `wal-save19`, 2026-11-14).** W6 log, nineteenth session. For the resize
agents: a window's `TailWin` now ends in `WinCands` (its candidates from `wr` on and past the bytes up to `hi` shaped as
`old`'s at stamp 0, a known resize's zero or the stream's byte, over `segBytesX`), and `WalAbsD.last`'s window branch in
`WinZero` (bytes from `wr` on zero-valued). `walAbsD_rzStart` takes `tg ≤ g0.om.hi` (so the growth's `tg ≤ hi` of the
`wal-tc12` entry is needed by the static relation too, not only by the crash step), `hX` (`segBytesX_rzSeg`/`_rzGrow`'s
conclusion) and `hz : WinZero lay g0` (`WalAbsD.zeroPast` with `TailZeros`); `rzGrow_pure`/`rzLandG_pure` take `hZ :
TailZeros lay`, `walAbsD_rzLandG` `hzf`/`hzs`/`hZ`, `walAbsD_rzLand` `size ≤ hi`. `TailLast.win` takes `SegExact`.

**The window's fdatasync; `winLo` and the candidates past `hi` (branch `wal-save20`, 2026-11-14).** W6 log, twentieth
session. For the resize agents: the fdatasync of a window tail is proved through the invariant step (`crashOk_syncW`,
`syncLay_any`; `walInvBody_sync` without `SegExact`), using `winLo`. Two invariant facts block the writer past the size
and touch the resize lemmas: **`winLo` is false of a write past the size from an exact tail** (`lo` stays the size,
`wr` below it; proposed replacement `WinHead`, a zero stamped 0 at each byte from `wr` on, which every step keeps and
which makes the zero arm unnecessary), and **`PastCands`** (the candidates known past `hi` shaped, with `|old| ≤ hi` in a
window: the `wal-tc12` entry's option (b)). Both change `WalAbsD.last`'s window branch, which `walAbsD_rzStart`/
`rzLand`/`rzLandG` construct: to be made in one change with `wal-tc13`'s.


**The old-length map in; it does not survive the window's fdatasync (branch `wal-tc13`, 2026-11-14).** W1 log,
twenty-third session. Done: option (a) as decided (`walOldsRes` in `walTailsRes`, `walOldFrag`, `walInvBody_tailW`
minting it; builds). **Not done: the exact-tail precondition, `fallocSup`/the growing truncate's supply,
`ZeroToEnd.specWalTail`** (no new name for `wal-readall21`; keep the hypothesis). Why, and the options:
1. *`|old|` changes with the cuts unchanged*: `syncLayW` (the window's fdatasync, `wal-save19`) shortens `old` to `|bs|`
   (`TailLast`'s `|bs| = |old|`). So `OldOk`'s "fixed per key" is false once that step exists, and option (a) cannot
   be kept as designed. (The growth flow itself never shortens it: `ZeroToEnd` grows back to `|old|` before `ReadAll`'s
   fdatasync. The other flows do: `cut`'s truncate then fdatasync; a lost handle leaves the shorter `old` for the next
   `ReadAll` of the same cuts.)
2. *`tg ≤ g0.om.hi` at the growth commits*: needed by `rzGrow_pure` and now by `walAbsD_rzStart`; `hi` is not
   persistent (the map cannot hold it). In `ZeroToEnd`'s flow it holds (the truncate to `o` keeps `hi ≥` the old size,
   the growths raise it), but a generic supply quantifies over every state the invariant allows.
3. *An exact tail found at the growth's start of size `tg > wr`* (the generation-start state) needs an exact form of
   `rzGrow_pure`/`rzLandG_pure` (`hlo` fails; the step announces nothing, `walAbsD_tail`-like congruence): small, pure.
Options for 1-2 (coordinator):
- (d) **Lend the tail record to the invariant during `ZeroToEnd`** (recommended): `specWalTail`'s proof moves the program's
  half of `tailVar γ` into `walTailsRes`'s entry for `dir`, in a "lent" mode that records `k` (`= |old| = tg`, minted from
  the exact pre) and asserts `k = |lay.old|`, `k ≤ hi`, `lo ≤ wr ∨ exact at k`; `K` holds the lent mode's token. Any other
  tail step brings the program's half and refutes the lent mode (three halves); only the supplies (owning the token) step
  a lent tail, and they keep the facts (`rzMeta`/`rsPost` raise `hi`, keep `old`). The 18 `walTailsRes` sites gain a
  refutation; the truncate supply needs a lent-mode twin.
- (c) The supplies' premises from the caller (`fallocSup`/`os.truncSup` with `tg ≤ m0.hi`, threaded through
  `preallocExtend`/`preallocExtendTrunc`/`Preallocate`/`File.Truncate.specAu`): settles 2, not 1.
- (a') Keep `old` long at the window's fdatasync (relax `TailLast` to `|bs| ≤ |old|`, bytes past `|bs|` unconstrained),
  so the map is sound again: settles 1, not 2, and touches `wal-save`'s `TailLast` users.
*Update (coordinator, after `wal-save20`)*: `wal-save21` adds option (b), `|old| ≤ hi` in a window (`PastCands`), and `WinHead` in place of `winLo`; with `k = |old|` from the map that settles item 2. Item 1 (the map's soundness across `syncLayW`) stands: with (b) in, (a') (keep `old` long at the window's fdatasync) or (d) remain the ways to keep `k = |old|`.
Pieces ready: `walOldFrag`/`walOldsRes` (reusable as (d)'s record of `k`), `rzGrow_pure`, `rzLandG_pure` (now with
`hZ`), `rsUndoneK`, `TcKnowsF.rsTail`, `TailZ.zte`.

**`WinLast`, `WinHead`, and the old-length map merged (branch `wal-save21`, 2026-11-14).** W6 log, twenty-first
session. **For `wal-tc13` and the resize agents**: `WalAbsD.last`'s window branch is now `WinLast C Mr d lay g` (`TailWin ∧
lo ≤ wr ∧ WinZero ∧ |lay.old| ≤ g.om.hi`); a window's `|old| ≤ hi` is `WalAbsD.oldHi`, any tail's `WalAbsD.oldHi_any` (so
the growth supplies' `tg ≤ hi` follows from `tg ≤ |old|`, i.e. from the map's `k = |old|` with `tg = k`). `walAbsD_win`
takes `WinLast`; `walAbsD_rzStart`/`rzLand`/`rzLandG` prove the new conjunct themselves (no new premise). `winLo` stays
(the truncate at `wr` needs it of the size, finding B: options (A)-(C), (A) recommended); `WinHead` (disjunctive: `lo ≤ b`
or a zero candidate) is derived and used by `crashOk_syncW`. `PastCands` is **not** an invariant fact (finding C: a
crash's tail knows the disk's bytes past its size, kept past `hi` by `ZeroToEnd`'s truncate); it goes on the handle
(`PastZ`, task 3). `wal-tc13`'s map is merged; the window's fdatasync (`walInvBody_sync`) takes the map's element
(`walOldOpt`), which `ZeroToEnd`'s flow has and `cut`'s does not (item 1 stands for `cut`; proposal in the W6 log).

**Option (A), `WinHead` in the invariant, `PastZ` (branch `wal-save22`, 2026-11-14).** W6 log, twenty-second
session. **For the resize agents**: `WinLast`'s second conjunct is `WinHead` (`winLo` gone); a truncate at `wr` gets
`lo ≤ wr` of a window from the handle (`walTailW`'s `LoWr`, `os.truncSup`'s new `P`, `os.File.Truncate.specAu`'s `P m`):
`walTail_truncSup` takes `P := (LoWr · wr)`, `rzStart_pure`/`tailCrashStep_rzStart` take `hlo`. `rzGrow_pure`'s `hlo`
must come the same way (a `P` on `fallocSup`, or the truncate to `o`'s landing). `os.ftDoneH`/`ftUndoneH` carry
`TcFrom` (the candidates' values past the old size; ledger), and `TailMeta`/`TailMetaW` end in `PastZ`: a
`ZeroToEnd.specWalTail` post needs another tail form (its window knows the disk's bytes past its size: finding C).

**Any tail step's crash condition; `WinLo` (branch `wal-save23`, 2026-11-14).** W6 log, twenty-third session. **For
the resize agents**: `WinLast` has a fifth conjunct, `WinLo lay g := max lay.so lay.z0 ≤ g.om.lo` (a window's crash may
zero bytes from `lo` on; the decoding accepts zeros only past the synced bytes and the frames found); a construction of a
window gives it from `winLo_any` of the layout before (a truncate to `tg ≥ wr`: `min lo tg`), as `walAbsD_rzStart`/
`rzLand`/`rzLandG` now do. **`crashOkA_tailAny`/`crashOkW_tailW`** (`TailCrashW.lean`) give the crash condition of any
step on the tail (window or not, before and after) from the two layouts' `WalAbsD` and F-Z of the new one, given `zf ≥ |bs|`
of both tails and that the new crashes are the new candidates' (the old tail's image as of its last sync is an old crash,
`fileCrashedR_syncImg`): no step-specific crash lemma is needed any more for steps that add candidates of the window's
shapes (a growth past `hi` would need `WinCands` past the old `hi`, which `PastZ` does not give: the growths stay
`crashOkA_rz`'s).

**For `wal-readall21`: registration before `ZeroToEnd` (branch `wal-tc13`, 2026-11-14).** `TailZeros lay` does **not**
hold of an idle tail after a crash: `WalsStart` (`CrashPure.lean`) gives `wr = so = z0 = |stream|` and the tail's bytes
`old.map durB`, `old` the crash image (`walCrash_pure`'s `old := imgOf (fo g.ino)`), and nothing about `old` past `z0`
(a torn frame, a write that reached the page cache but not the frame's end, `fallocate`'s zeros: all allowed by W1).
So `walTailsRes_register`'s `TailZeros` premise cannot be met at `ReadAll`'s pin. The registration needed (the
`wal-zte2` design, I3b log, "`ReadAll`'s tie"): `walTailsRes`' per-tail fact `TailZeros lay ∨ lay.wr = lay.z0` (nothing
appended past the start's frames; "zeros past `wr`" is the same set of bytes then, since `wr = z0`), and the window's
fdatasync after `ZeroToEnd` committing `syncLayW` (`old := old.take wr ++ zeros`, of the same length since `ZeroToEnd`
regrew the tail to `|old|`), which gives `TailZeros` back (`tailZeros_syncW`). The users of the per-tail `TailZeros`
(`walsOk_tail`'s appends, `rzGrow_pure`/`rzLandG_pure`'s `hZ`, `walAbsD_rzLandG`) need it only once something is
appended or the bytes past `wr` are read: the appends come after that fdatasync; for the growth supplies, the window
found has `WinZero` (`WalAbsD.zeroPast`) and the exact one is the no-op form (item 3 above), so `hZ` should be replaceable
by the disjunction there (to check when the supplies are written). `ZeroToEnd.specWalTail` is **not written** (blocked by
items 1-2 above); its intended statement: `walAreaOk ∗ walTailW f fd name dir γ i H md cuts o0 sz out TailMeta` with
`o0 + |out| = wr` and the offset there, the post on success `walTailW … sz out TailMetaW` with the bytes from `wr` to
`sz` a zero run (`osZerosA`) and `TailZ` (`TailZ.zte`), on an error the handle lost.

**The pending-form fdatasync (branch `wal-tc20`, 2026-11-14).** W1 log, thirtieth session. Proved, statement
unchanged: **`fileutil.Fdatasync.wp_specWalPend (wp_Fd : os.File.Fd.spec) Mr : Fdatasync.specWalPend Mr`**
(`FdatasyncPend.lean`; pre `walAreaOk ∗ walTailP … o0 sz [] k false (TailMetaZ ∧ bytes from o0 zero) ∗ walCutFrag
none`, `o0 = |tailStream|`; post `walCutFrag none ∗ ((⌜e = 0⌝ ∗ walTailW … o0 sz [] ∗ walSyncedLb dir |H|) ∨ ⌜e ≠
0⌝)`), over `wp_tailFsyncP`/`syscall.Fdatasync.wp_tailP` and the invariant's `walInvBody_syncP`
(`TailSyncPend.lean`: `syncLay_anyP`, `tailZeros_of_pendEx`, `walTailsRes_cutP`). `Fs.wp_osMeta_zfGe` (new,
untrusted) gives the sync step's `zf ≥ size`. For the WAL `Link.lean`: `ReadAll.wp_proof`'s `wp_FdatasyncP :=
Fdatasync.wp_specWalPend wp_Fd Mr`.

**The growth supplies and `ZeroToEnd.specWalTail` (branch `wal-tc19`, 2026-11-14).** W1 log, twenty-ninth
session. Generic: `os.truncSup` told `⌜P m0⌝`, `os.File.Truncate.specAu`'s later-attempt premise `∀ m', m'.lo ≤ min
m.lo sz → m'.size ≤ max m.size sz → P m'`, `fallocSup … P`, `preGrownH`'s `m'.lo ≤ m.lo`, `P` threaded through
`preallocExtend(Trunc)`/`Preallocate`/`ZeroToEnd` `specAu` (`ZeroToEnd`'s `P Q`, post `m'.lo ≤ min m.lo o`; ledger).
WAL: **`walTail_fallocSup`**, **`walTail_truncSupG`** (`GrowSup.lean`, tie `growTie`, told `lo ≤ wr ∧ size ≤ tg`,
premise `tg ≤ k`), **`ZeroToEnd.wp_specWalTail`** (`ZteWalTail.lean`: `walInv_pendStop` first, then `ZeroToEnd.specAu`
with the three supplies). `specWalTail`: pre `walAreaOk ∗ isPkgInit errors ∗ walTailP … o0 sz [] k true (TailMetaR ∧
zero word at o0)`, success `∃ sz', ⌜o0 ≤ sz' ∧ sz' = sz⌝ ∗ walTailP … o0 sz' [] k false (TailMetaZ ∧ bytes from o0
zero)`; `TailMetaZ` is now `|bs| = size ∧ maps = ∅ ∧ pageEnd size ≤ max size cz`. **`ReadAll`'s obligations**:
`o0 = |tailStream|` and `o0 ≤ sz` (as before; `wr = |tailStream|`, `walInvRegisterPendLaw`), `isPkgInit errors`
(`iPkgInit`, done in `WAL__ReadAll`). `Fdatasync.specWalPend` not proved (design in the W1 log).

**Findings C/D and the registration law (branch `wal-tc18`, 2026-11-14; merge first: `TailIdle` changes).**
W1 log, twenty-eighth session. `TailIdle` is **`TailExact ∧ wr = |S| ∧ TailSynced ∧ so = wr ∧ TailMaps`**
(`TailMaps lay`: the last segment's `maps = ∅`); `TailIdle.bound` (its `TailBound`), `TailLast.so_eq` (an exact
durable tail has `so = wr`); `walCreate_osAUnc` takes `hmaps : g.om.maps = ∅`, `createFresh_osAUnc`/`createU_none`
take `hm2m : m2.maps = ∅` (`wal-create21`: an idle fresh tail must supply both new facts). Proved
(`ReadAllRegCommit.lean`): `walInvBody_readReg`, **`walInvRegisterPendLaw_holds`**, **`walInv_readCommitReg`**
(`ReadAll`'s commit and registration at one opening: `walDurLe dc d` with `d` the registered record's; for
`wal-readall26`). Task 4: the truncate at `wr` from a lent tail of kind `false` is in (`rzStart_pureP`, `TruncSupPend.lean`; **`walTail_truncSup`'s `hok : ∀ k, ok ≠ some (k, true)` and `hS : ∀ kp, ok = some kp → wr = |tailStream Mr H md cuts|`**); `fallocSup`'s `P`, the growing truncate's supply, `ZeroToEnd.specWalTail` and the pending-form fdatasync not done.

**Fixes A and B (branch `wal-tc17`, 2026-11-14; merge first, they change `WalAbsD` and `walLentRes`).**
W1 log, twenty-seventh session. All 38 WAL leaves importing `Abs.lean` build (2851 jobs). *Fix A*:
`WinLast`'s third conjunct is `TailZeros lay → WinZero lay g`; `WalAbsD.winZero` takes `TailZeros lay`
(`WalAbsD.zeroPast` unchanged); `walAbsD_rzStart` has **no `WinZero` premise** (it derives it from
`zeroPast`); `walAbsD_rzLandG`, `rzGrow_pure`, `rzLandG_pure` **lose their `TailZeros` premise**;
`walAbsD_syncW` takes **`hwz : WinZero lay g0`**; `crashOk_syncW`, `walsOk_syncW`, `dirKeysOk_syncW` take
**`hZ : TailZ0 lay`** and `hwz` (new `tailZeros_syncW0 : TailZ0 lay → wr ≤ |old| → TailZeros (syncLayW
…)`); `syncLay_any` unchanged (F-Z). `TailZeros` moved to `Abs.lean`, `LenZ`/`TailPend` (from
`TailCrashPend.lean`) too (same names). A window built by hand (`fun b x hb hx => …` in `WinLast`'s
third place) now takes the F-Z hypothesis first (`fun _ b x hb hx`; `RzLand`, `RzGrow` adapted).
*Fix B*: `ZerosOk T Ls M := ∀ dir lay, T !! dir ≠ none → Ls !! dir = some lay → NotPend M dir →
TailZeros lay ∨ (M !! dir ≠ none ∧ TailPend lay)` (`ZerosOk.zeros`: not lent, F-Z; `zerosOr_congr`);
`TailZK (some (_, false)) := TailZeros ∨ TailPend`, `TailZK.zeros` now takes `∀ k p, ok ≠ some (k, p)`
(the key), new `TailZK.zp` (`∀ k, ok ≠ some (k, true)` → F-Z or `TailPend`); **`walLentRes_pendStop`**
`(hp : ∀ lay, Ls !! dir = some lay → TailPend lay) : walPendTok dir γ k -∗ walLentRes T Ls ==∗
walLentTok dir γ k ∗ walLentRes T Ls`; `walLentRes_unlend` takes `hz : ∀ lay, Ls !! dir = some lay →
TailZeros lay`; **`walLentRes_unpend … (p : Bool)`** takes `walLentTokB dir γ k p` (either kind);
`walLentRes_insert_same` gains `hp : TailPend lay → TailZeros lay' ∨ TailPend lay'` (after `hz`),
`walLentRes_mono`'s `hz` the same conjunct; `walLentRes_lookup`'s `p = false` fact is `TailZeros ∨
TailPend`; `walInvBody_unlend`/`walInv_unlend` removed (unused); `walTail_truncSup`'s `hok` is `∀ k p, ok
≠ some (k, p)` (the key) until task 4 generalizes it. *Task 3*: `TailMetaR`, `TailMetaZ`, `walTailP`
(`HandlePend.lean`) and `walInvRegisterPendLaw` (`ReadAllRegPend.lean`) are in; the law's proof is
blocked on findings C and D (an unregistered tail's `maps = ∅` and `TailBound` not in the invariant;
proposed: `TailIdle` gains `so = wr` and `TailMaps`; W1 log, twenty-seventh session). Task 4 not started.

**The pending tail's crash step (branch `wal-tc16`, 2026-11-14).** W1 log, twenty-sixth session. Proved
(`TailCrashPend.lean`): `LenZ`, `TailPend`, `decStep_zeroWord`, `crashTo_tailP`, `WalAbsD.pendVals`,
**`crashOkA_tailPend`** (any tail step of a pending tail keeps `CrashOkA`, from `WalAbsD` before and after,
`TailPend lay`, `|S| = wr`, the zeros past both tails' lengths). For the supplies (`walTail_truncSup` with a
pending token, `fallocSup`, the growing truncate's): their crash step is `crashOkA_tailPend` (with
`crashOkW_tailW`'s alternative handling) when `TailZK` gives `TailPend`, `crashOkA_tailAny` when it gives
F-Z. Blocked on two findings (W1 log, twenty-sixth session): (A) a pending truncate's in-flight layout
falsifies `WinLast`'s `WinZero` (proposed: `TailZeros lay → WinZero lay g`, `walAbsD_syncW` taking
`WinZero` as a premise); (B) `LenZ` must reach the invariant at a program step after the loop (proposed:
`walLentRes_pendStop`, kind `false` meaning F-Z or `TailPend`). Statements proposed for `wal-readall24`
(not in the code): `ZeroToEnd.specWalTail`'s pre `walTailP … TailMetaR` with the zero word `∀ j < 8,
(bs.getD (o0 + j) (0, [])).1 = 0` in its `tm`; its post the bytes from `o0` on zero-valued (for A);
`walInvRegisterTailLaw` as the `wal-tc15` entry proposes.

**Registered, not yet zeroed (branch `wal-tc15`, 2026-11-14).** W1 log, twenty-fifth session. Made:
`walPendTok` (the lent map's kind), `TailZ0` as `walTailsRes`'s per-tail fact, `ZerosOk`/`IdleZ0` in
`walLentRes`, `walTailsRes_registerPend`, `walLentRes_unpend`, `walTailKeyL` over `Option (Nat × Bool)`.
**Not done: task 3 (exact-start `rzGrow_pure`/`rzLandG_pure`), task 4 (`fallocSup`, the growing truncate's
supply, `ZeroToEnd.specWalTail`)**, and the coordinator's two obligations from `wal-save22` (`rzGrow_pure`'s
`min lo tg ≤ wr` from a `P` on `fallocSup`, as `os.truncSup K p tg P`; `ZeroToEnd.specWalTail`'s own tail
form without `PastZ`). Blocked first on the finding (W1 log, twenty-fifth session): `walTail_truncSup` needs
F-Z (`hok`), so a pending tail cannot be truncated until the crash step from a `TailZ0`-only exact tail
exists. Proposed statements (for `wal-readall24`, not yet in the code):
- `walInvRegisterTailLaw`: as now, but its post `walPendTok dir γ |lay.old|` in place of `walTailKey dir γ`,
  `TailMetaR gl.om gl.bs` (`bs.length = size ∧ maps = ∅ ∧ lo = size ∧ hi = size`: `TailMeta` without
  `TailZ`/`PastZ`) in place of `TailMeta`, and `TailZ0 lay ∧ |lay.old| = gl.om.size` (`walAbsD_old_exact`)
  added; proof: `walInv_readFiles`' look, `walTailsRes_none` (`F = ∅`), `walTailsRes_registerPend`.
- `ZeroToEnd.specWalTail`: pre `walTailP f fd name dir γ i H md cuts o0 sz [] TailMetaR` (`walTailW` with
  `walPendTok dir γ sz` for the key; to define in `Handle.lean`), `o0 = |tailStream|`; post on success `∃ sz' ≥
  o0, walTailP … sz' [] TailMetaZ` (`TailMetaW` without `PastZ`; `TailZ` from `TailZ.zte`), on an error the
  handle lost. The fdatasync after it (`fileutil.Fdatasync.wp_tailW`'s pending form) commits `syncLayW` with
  `walLentRes_unpend` and returns `walTailW … TailMeta` (the key, `PastZ` of the synced `OsMeta`).

**The lent tails, option (d) (branch `wal-tc14`, 2026-11-14).** W1 log, twenty-fourth session. The old-length
map is removed (with `wal-save21`'s `walOldOpt` arguments); `walLentRes` (in `walTailsRes`) holds the key of
each lent tail and `|old|`. For the growth supplies and `ZeroToEnd.specWalTail` (not written): lend at
`specWalTail`'s first step (`walInv_lend`, from `walTailW`'s exact `TailMeta`: `k = sz`), make the three
supplies with `K = walLentTok dir γ sz ∗ tailVar γ (H, md, cuts, wr, i, none)` (`walTail_truncSup` with `ok :=
some sz`; `fallocSup` and the growing truncate's supply, to write, over `walInvBody_tailW` with `ok := some sz`,
which gives `|lay.old| = sz` at each commit, hence `tg = sz ≤ |old|` and, with `wal-save21`'s
`WalAbsD.oldHi_any`, `tg ≤ hi`); the post a lent handle (`walTailW` with `walLentTok` for the key), returned by
the caller at its next step (`walInv_unlend`). Blocked first on task 2 (registration, W1 log, twenty-fourth
session): the same lending must cover the window before `TailZeros` holds.

**The truncate supply and `specWalTail` (branch `wal-tc10`, 2026-11-14).** W1 log, twentieth session. Done:
`TcKnows` on `os.ftDoneH`/`ftUndoneH` (ledger), `walTail_truncSup` (`TruncSup.lean`, no `sorry`),
`os.File.Truncate.wp_specWalTail` (`TruncWalTail.lean`), `WAL.cut.wp_proof` without the `specWalTail` hypothesis. The
supply is for a truncate to the record's write position only (`tg = wr`: the tie fixes it). **Not started: growth and
`ZeroToEnd`'s instance** (no name yet; for `wal-readall18`). What `ZeroToEnd.specAu` asks of `ReadAll` at the tail
(`o = wr`): `os.truncSup K i wr` (this supply), and the growth back to the size by two routes, `fallocSup K i m.size`
and the fallback's `os.truncSup K i m.size` (a truncate growing the file, `tg > size` of the state it finds). Both need:
- a supply for a resize to a target at or past the size (`rzSeg g0 tr tg n` with `tr = false`, and `tr = true` at `tg >
  wr`; the tie cannot fix `tg = wr`: the record's `wr` stays `o`): `walAbsD_rzStart` covers both (`lay.wr ≤ tg`, `min lo
  tg ≤ wr`), but `crashOkA_rzStart`/`segBytesX_rzSeg`/`tailCrashStep_rzStart` are for `tr = true` at `tg = wr` only;
  the growth's bytes past the old size (`rzMeta`'s `rsTail` at the old size: those `m.pc` knew, then zero stamped `n`)
  are candidates `RzCands` allows, so the crash step is `crashOkA_rz` with the growth's zeros (to write: the `tr = false`
  and `tg > size` forms of `segBytesX_rzSeg`, then `tailCrashStep_rzGrow`);
- the landing `rsPostK true false m tg w n []` (`fallocate`, any `w ∈ [size, tg]` on an error: `rsOutF`'s prefix arm)
  and `rsPostK true true m tg tg n []` (the fallback): a growth's `rzLand` (bytes `g0.bs ++ zeros`, `walAbsD` with the
  bytes past `wr` the stream's zeros: `TailZeros`), `crashOkA_same` with the regrown bytes in `segBytesX`;
- `TailZ` in `ZeroToEnd`'s post: `ZeroToEnd.specAu`'s success post gives `pageEnd m.size ≤ m'.cz` only; `fallocDoneH`
  (`LinuxFs/Proof/syscall/FallocateAu.lean`) has the same existential `tc` as `ftDoneH` had, so it needs `TcKnows`'s
  growth form (`rsTail false`'s domain) and `ZeroToEnd.specAu`'s post a `TcKnows`-like conjunct (a ledger entry), or a
  WAL-level `ZeroToEnd.specWalTail` stated directly over `walTailW`, proved like `wp_specWalTail` from `ZeroToEnd.specAu`
  with the post's `osMeta` existential strengthened.

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
**From `wal-save15` (2026-11-14), for `wal-tc7`.** A write in flight past the size: the layout's `OsMeta` is `wrMeta`
(`SegFl.Ok`; `pwTail`-shaped candidates past the size), `SegCrashAt` of it from the take (`wrMeta_pc_cand`,
`fileCrashedR_wrMeta`). Proposed `TailWin` clause for what `segBytesX` holds past `|bs|` (the premise your
window-to-window `crashTo_tailL` needs and the write steps past the size establish): `∀ b, |g.bs| ≤ b → b < g.om.hi →
∃ c, g.om.pc b = some c ∧ ∀ q ∈ c, q = (0, 0) ∨ (q.1 = 0 ∧ q.2 ∈ g.om.rz) ∨ (q.1 = S.getD b 0 ∧ 0 < q.2)`, and the
window's size is the stream's end (`sz = o0 + |out|`, W6 log fifteenth session, finding 2). Not added to `Abs.lean`:
if you make it, `wal-save*` builds on it.
**From `wal-save16` (2026-11-14), for the resize agents.** `TailMetaW`/`TailMeta` now carry `TailZ m` (zeros known
from `z ≥ size`, the candidates of `[size, z)` known, `pageEnd z ≤ max size cz`; `Handle.lean`): `specWalTail`'s post and
`ZeroToEnd`'s window must establish it (a truncate to `wr` with `keep = true` does: `rsTail` knows the cut-off bytes and
`[old size, pageEnd old)` through `pc`, `rsCz` raises `cz` to `pageEnd` of the old end). The window's `g.om.lo ≤ lay.wr`
(`WalAbsD.winLo`) for a window opened by writes past the size, and the `TailWin` past-size clause, are still open (W6 log,
sixteenth session).

**`wal-save24` (2026-11-14): `WinLow`, `TailWin`'s `ByteOk` below `lo`, `syncLayW` padded** (W6 log,
twenty-fourth session, findings 1-2). For the window lemmas: a hand-built `WinLast` now has six conjuncts
(`⟨TailWin, WinHead, fun hZ … => WinZero, |old| ≤ hi, WinLo, WinLow⟩`); `TailWin`'s fifth conjunct takes `b < g.om.lo`
(was `b < lay.wr`) and its third is `lay.z0 ≤ lay.old.length` (was `|bs| ≤ |old|`); below `wr` read the bytes through
`WalAbsD.low` (or `lowW` for `WinW`). A resize step with `lo' ≤ wr` gets `WinLow` from `habs.lowW` on the bytes it
keeps below `wr`.

**`wal-save25` (2026-11-14): the writer past the size proved; any tail step's crash step** (W6 log, twenty-fifth
session). For the resize agents: **`tailCrashStep_any`** (`TailWriterW.lean`) turns any tail step whose new
`WalAbsD` is proved (and `zf ≥ |bs|` of both tails) into a `TailCrashStep` (`crashOkA_tailAny`), for
`walsOk_tailA`/`dirKeysOk_tailA`. `walAbsD_announceW` takes `∀ b ≥ size, (pc b).isSome` in place of `TailZ`. Between
the attempts of a `WriteAt`, the handle's tail facts are `TailMetaL m bs E` (`TailZE`: `TailZ` but the page fact may
wait for the write up to `E`); `TailMetaW.tailMetaL` in, `TailMetaL.fin` out. The handle's writer past the size is
`wal.tailWriterW` with `walTailWS` (size `max sz (o0 + |out|)`, end below `max sz maxBytes`).

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

**Twelfth session (branch `wal-read12`, 2026-11-14).** `openAtIndex` and `OpenForRead` proved (no `sorry`,
`lake build` of `openAtIndex`); `Open`, `ReadAll` not started.
- *New modules, proved*: `OpenAtPin.lean` (**`walInv_openAt`**: at `openAtIndex`'s first step, `walInv` opened,
  the area read (`walInvBody_areaAt`), the client's update opened and committed (write mode `walInvBody_unl`), and
  either `Q none` with the token and `h.cur !! nm = none`, or `walPinOut`: the pin's outputs from position
  `walOpenK idx lay` (`walSearch` of the layout's names, which `selectWALFiles` then computes: `walOpenK_eq`));
  `OpenAtSteps.lean` (`walInv_unpin`: the error arms' put-back at a step; `walInv_mintOpening`: write mode's
  `walOpening` from the lock token, at the pipeline's call step); `OpenAtTail.lean` (`os.fileNamed`, `os.File.Name`
  over it, `walOpenedFiles_last`: the tail's name and lock kept before the decoder takes the file's fd).
- **Hypotheses of `openAtIndex.wp_proof`** (besides the callees' specs, listed in its signature; for the coordinator):
  1. `WalPinSized walCodec Mr R jr r` (`OpenAtPin.lean`): `walInvBody_pin` plus **each segment's `|g.bs| + 2^12 <
     2^62`** (`walDecFiles_mk`'s); the invariant does not hold a size bound. Fix: a framed pure conjunct (ext4's
     maximum file size, 16 TiB, on every segment), or in `WalAbsD.metas`; then `WalPinSized` is `walInvBody_pin` with it.
  2. `WalDirPathLaw walCodec Mr R jr r` (`OpenAtPin.lean`; the coordinator's interim law, finding G-spine): a holder
     of `walDirKey dir j X`, at a program step, with the area's spine framed, gets `∃ q, osPathS R dir (own q) j`,
     kept. Applied once (the pin's step); swap for `wal-path13`'s law there.
  3. `WalDecEnvSupply` (`openAtIndex.lean`): `isPkgInit wal -∗ ∃ IoE eof ueof, decEnv IoE eof ueof ∗ ⌜pointer
     errors ∈ IoE⌝` (needs Perennial's `errors.Is` for `isEofOk`; `io`'s variables).
- **Statement changes** (ledger, 2026-11-14): `openAtIndex`/`Open`/`OpenForRead` take `NameOk nm` (an absent WAL:
  `selectWALFiles.specAbsent`) and `dir.length < 2^59` (`openWALFiles`, `newFilePipeline`), as `Create`.
  `OpenForRead.wp_proof` takes `openAtIndex.spec`.
- **For `Open`/`ReadAll` (not done)**: (a) *call permission*: `Open` returns `osCallPerm ½` and its pipeline holds
  the other half, but `walDirH` (the handle `ReadAll` returns) holds another `½`: `Open`'s success should keep its
  half in `walOpeningF` (as `Create`'s post now does, ledger 2026-11-14), a statement change of `Open`; (b) `Open`'s
  `OpenDir` error arm calls `w.Close()`, which has no spec (W10); (c) `ReadAll` gets the directory path from
  `WalDirPathLaw` (its spec has the area spine and `walAreaOk`; the key is in `walReadTie`), the metadata bound
  (`d.metadata.length < 2^41`) is not in `walInvBody` yet (`wal-save11`'s message: a framed conjunct).

**Second session (branch `wal-enoent13`, 2026-11-14).**

- **Trusted semantics change [user], decided provisionally, pending the user's review: `ENOENT`.**
  `GooseLang/Ext/Fs/Impl.lean`: `def ENOENT : w64 := 2`; `IsFsStep "Open"`'s failure disjunct gains
  `(e = ENOENT → st0.lookup p = none)` (a failing `open` of a path of the trees returns `ENOENT` only
  when the path does not resolve at the step); `"DirReadNext"`'s errno disjunct gains
  `(e = ENOENT → ¬ Reach st.fs.roots st.tree df.ino)` (only for a removed directory). Not `Unlink`/
  `Rmdir`/`Rename`/`Mkdir` (`RemoveAll`'s model relies on their free `ENOENT`), not `Open`'s outside
  case. Why the step is right (the model resolves paths at the step): Linux's `ENOENT` is a component's
  lookup finding no entry or a dead directory (`fs/namei.c`); with no directory renamed during the call
  (the stuck clause), the path did not resolve at that instant (or just after the `rmdir` that killed
  the walk's directory), and the call does nothing else before returning, so the step may sit there;
  `iterate_dir` (`fs/readdir.c`) answers `ENOENT` exactly for `IS_DEADDIR`, which is permanent. Go
  example `examples/osfs/semantics/meta_enoent.go` (indexed in `doc.go`); **measured on C**
  (`run-models-on-c.sh`, `check.sh` passed): `TestEnoent`, `ENOENT` for a missing name, under a missing
  and under a removed directory, and from `Readdirnames` of a removed directory; 3000 rounds of `Open`
  of a present directory and of a file in it and `Readdirnames` of a 2000-entry (htree) directory,
  under 8 goroutines creating/renaming/removing siblings, never failed. ext4's own lookup/readdir
  errors not `ENOENT`: kernel source, not exhaustively measured.
- **Extension** (repaired: patterns in `CommitMono`, `Tests`, `TreeSpecs{Open,DirFd}`,
  `TreeShared{OpenDir,Create,Trunc,Read}`, `os/SharedExt`; no statement weakened): `wp_osOpenDirGenS'`
  (generic in what shows the path), `wp_osOpenDirS`'s failure now `e ≠ ENOENT` (stronger),
  **`wp_osOpenDirChildS`** (`d/b` through a fraction of a claim of `d`'s directory holding it: the child
  form `ExistCallees` asked for; no `walDirPath` hypothesis needed); `wp_dirReadS`'s errno arm gains
  `e = ENOENT → WGone`, `wp_osDirReadNextGenS'` (a further resource showing a state property),
  **`wp_osDirReadNextChildS`** (`e ≠ ENOENT`).
- **`os` layer** (`LinuxFs/Proof/os/NsChildS.lean`, no `sorry`): `os.errnoPathErr err e` (a `*PathError`
  of the errno `e`, persistent; `fmtErrorOk` for `e ≠ 0`), `wp_pathError_errno`, `wp_wrapErrno_errno`;
  `os.OpenFile/Open.wp_dirChildS`, `os.File.Readdirnames.wp_dirChildS` (errors `e ≠ 0 ∧ e ≠ ENOENT`),
  `os.OpenFile/Open.wp_absentErrS` (`wp_absentS` with the error explicit).
- **`hErrNotExist` dropped**: the part's `os` package fact records `os.ErrNotExist` (some error;
  `etc/gen-init.py`'s `LFS_OS`, `--check` passes; `os.errNotExist_of_pkgInit`, `PkgInit.lean`).
  `wal.Exist.wp_proof`/`wp_specCreate`/`wp_core` lose the hypothesis (`wal-create12`: pass no
  `hErrNotExist`).
- **`ReadDir.specAbsentIs`/`specChildIs` still hypotheses.** What is left (`ExistCallees.lean`'s header):
  `ReadDir`'s own loops (`applyOpts` over the closures, the extension filter) and a bound on the names
  read, which `sort.Strings.spec` needs (`≤ 2^62`) and nothing gives (`ReadDir.wp_proof` is `sorry` for
  the same reasons: one proof of the loops serves all three); and the new
  `errors.IsPathErrnoNotExist.spec` (`errors.Is(*PathError of e, os.ErrNotExist) = (e = ENOENT)`: needs
  the error tree of the part's `os` errors, `syscall.Errno.Is`, and `os.ErrNotExist = oserror.ErrNotExist`
  distinct from `ErrPermission`/`ErrExist`/`ErrUnsupported` in the package facts).
- *Not started*: `ValidSnapshotEntries` (W8), `ReleaseLockTo` (W9).

**Third session (branch `wal-small14`, 2026-11-14).**

- **Integration build** (after the `rzs` stamps and the `ENOENT` rule): every `LinuxFs` and
  `GooseLang/Ext/Fs` target built, 3115 jobs, no fix needed; `gen-part-copies.py --check`,
  `gen-init.py --check` pass. Rebuilt after this session's model change and the `wal-int` merge
  (`5f004edd54`): 3135 jobs, success.
- **Decision [user], provisional, pending the user's review: `Readdirnames`' model assumes Go's
  `growslice` limit.** `sort.Strings.spec` needs at most `2^62` names, and the bound is real (Go's
  `heapSort` computes `2*i+1`, which overflows past `2^62`). The model cannot give it: `DirReadNext`
  may return a name again after a concurrent change, so a shared-mode read is unbounded, and the
  names outside the caller's claim are unconstrained; a premise on the claim's history would not
  cover `Exist`'s `.except X` claim nor bound the entries. What bounds it in Go is `append`: a
  `[]string` panics ("growslice: len out of range") once its capacity passes `maxAlloc/16 = 2^44`
  (linux/amd64), before its length does; Perennial's `append` models only the `int` overflow as an
  assumption. So `File.Readdirnames.impl` (`LinuxFs/TrustedCode/os.lean`) assumes (`assume`: diverges
  otherwise) that fewer than `2^44` names were read before each append, excluding only executions Go
  ends in that runtime panic. Go example `examples/osfs/semantics/model_os_readdirnames_len.go`,
  **measured** (`TestAppendStringsLenLimit`: `unsafe.Slice` makes a `2^44`-string header without
  allocating; one `append` panics so). Rejected: a hypothesis "Readdirnames returns at most `2^62`
  names" (false in the model, so unsound as an axiom). General fix for Perennial (its `append` should
  assume `newLen ≤ maxAlloc/elemSize`): `notes/perennial-changes.md`.
- **`os` layer**: `errnoPathErr` and its lemmas moved to `LinuxFs/Proof/os/ErrnoPathErr.lean` (imported
  by `NsS`); `File.Readdirnames.wp_dirS` states its error (`errnoPathErr`, nonzero) and both readdir
  specs (`wp_dirS`, `wp_dirChildS`) the bound `names.length ≤ 2^44`; `os.OpenFile/Open.wp_dirErrS` (the
  error explicit; `wp_dirS` unchanged for `OpenDir`); `Ns.lean`'s `wp_dir` steps past the `assume`.
- **Proved (no `sorry`)**: `fileutil.ReadDir.wp_core` (`ReadDirCore.lean`: the options loop over the
  closures, `os.Open`, the deferred `Close`, `Readdirnames(-1)`, `sort.Strings`, the extension filter,
  over abstract triples of the three `os` calls), **`ReadDir.wp_proof`** (its last `sorry`),
  **`ReadDir.wp_specChildIs`** and **`ReadDir.wp_specAbsentIs`**
  (`LinuxFs/Proof/.../wal/ExistCallees.lean`), both over the one remaining hypothesis
  `errors.IsPathErrnoNotExist.spec`. `Exist` now rests on that hypothesis alone (with `WithExt`,
  proved): `wal-create12`/linking pass `ReadDir.wp_specAbsentIs wp_Strings wp_Ext wp_IsNE` and
  `wp_specChildIs …` for `wp_RDabs`/`wp_RDchild`.
- **`ReleaseLockTo` (W9), started**: the spec over `fsExt`
  (`LinuxFs/Spec/.../wal/WAL__ReleaseLockTo.lean`: the main axiom's, with the area, `walOpenWF`, the
  update at `walAuMask`; `unl` bookkeeping per §6 Q1, committed right after `w.mu.Lock()` whatever the
  outcome) and its update's ghost step `walInv_unlAU` (`ReleaseAu.lean`, proved). Not done: the body
  (the lock loop: `Name()` of each lock, `parseWALName`, the `Close` of the earlier locks, the reslice
  `w.locks[smaller:]`, which keeps the tail last: `walLockH` for the dropped ones, `ownSlice_slice_with_cap`).
- *Not started*: `ValidSnapshotEntries` (W8): it needs the read-mode pin (`walInv_openAt`'s), the
  `openWALFiles`/decoder specs `ReadAll` uses (`wal-readall14`), so it belongs after `ReadAll`.

**Fourth session (branch `wal-close15`, 2026-11-14).**

- **`ReleaseLockTo` (W9): proved** (`WAL__ReleaseLockTo.lean`, no `sorry`, `lake build`), over `filepath.Base.spec`,
  `parseWALName.spec`, `os.File.Close.spec` (all proved elsewhere). The update commits right after `w.mu.Lock()`
  (`walInv_unlAU`); the range loop reads each lock's name through `walLockNamed` (persistent: the non-tail
  locks' `walLockH` and the tail writer's `os.ownFile`, `ReleaseLocks.lean`), its exits joined (`wp_join` at the
  `doFor`, the `return err` arm as `returnVal #()`); `smaller ∈ [1, |locks| - 1]` after the `!found` fix-up, so
  the close loop closes only non-tail locks (`walLockH`), and `w.locks[smaller:]` (`ownSlice_slice_with_cap`)
  keeps the tail last (`dropLast_drop`, `getLast?_drop`). Note for loops whose Go index is also `i`: the range's
  counter shadows it; `rename_i`/`irename` recover both.
- **Handle changes (sealed bodies; no client-visible change)**: `walDirH` holds **`∃ γt, walTailsFrag {dir ↦ γt}`**
  and **`walNamesFrag none`** (what `Close` needs to unlock, W1 log eleventh session's obligation); `walPipeH`
  holds **`fp ≠ null`** (`Close` tests `w.fp != nil`; nothing else showed it: `structFieldRef` says nothing of
  `null`), from **`newFilePipeline.spec`'s post** (now `⌜fp ≠ null⌝ ∗ …`, proved). Repaired: `WAL__cut`,
  `CutPipe` (`walPipeH_next` takes `hfp`), `newFilePipeline`, `openAtIndex`. **Obligations**: `Create`'s post and
  `ReadAll`'s write handle must put `walTailsFrag {dir ↦ γ}` (after registering the tail) and `walNamesFrag none`
  into `walDirH`.
- **`WAL.Close` (W10), append mode: stated and proved over hypotheses** (`LinuxFs/Spec/.../wal/WAL__Close.lean`,
  `LinuxFs/Proof/.../wal/WAL__Close.lean`; ledger 2026-11-14). Spec: `walAreaOk`, `walOpenWF`, `walPurgeW`, the
  update at `walAuMask`; post `(∃ d, Q d ∗ walSyncedLb dir |d.H| ∗ walUnlockedTok ∗ osCallPerm 1) ∨ ⌜err ≠ nil⌝`
  (the left disjunct whatever `err`: `dirFile.Close()`'s error comes after everything). Proof: the pipeline's
  `Close` (`pipeLeft`: its call-permission half, its leftover name's claim), `tail()`, `sync` over
  **`walHandleC`** (`CloseHandle.lean`: `walHandleIn` with `w.fp` nil, `j` a parameter), the range loop closing
  the non-tail locks then the tail's file (a failed close logged: `zap.Error`, `zap.Logger.Error`), the put-back
  at the next step, `dirFile.Close()` (`os.File.Close.wp_dirS`), the deferred unlock. **Hypotheses**:
  `WAL.sync.specC` (`LinuxFs/Spec/.../wal/WAL__syncC.lean`: `sync.spec` over `walHandleC`; `sync` never reads
  `w.fp`, so its proof is `sync.spec`'s with the pipeline out of the frame: for `wal-maxb14`/the `sync` owner),
  **`WalCloseLaw`** (`CloseHandle.lean`, for the invariant's owner, W1): at a program step, the tail (key, its
  record `(H, md, cuts, |tailStream|, ino, none)`, halves with `TailMeta`), the directory claim's half and key, both
  pipeline names' claims, the out-record `⟨[ino], [(j, .except X)], [dir]⟩`, `walTailsFrag {dir ↦ γt}`,
  `walNamesFrag none`, `walOpenW`, `walPurgeW`, `walSyncedLb dir |H|` and the update give `Q d`, `walSyncedLb dir
  |d.H|` and `walUnlockedTok`: the update committed unchanged (`walDurLe` keeps `H`), `walTails_unregister` with
  the WAL's **`TailIdle`** established (the record's `wr` and `TailMeta`'s `lo = size = hi`, the coordinator's
  `WalTailIdle` conjunct of `walTailsRes`, `wal-readall15`), `walParked_putSeg`/`_putClaim`/`_putTmps`,
  `walParked_unlock`; the callee specs `filePipeline.Close.spec`, `WAL.tail.spec`, `os.File.Close.spec` (proved),
  `zap.Error.spec`, `zap.Logger.Error.spec`.
- **Not done**: `WAL.Close.specOpening` (`Open`'s hypothesis) is still a hypothesis. Its proof needs (1) the
  decoder's files out of `ownDecoder` (the tail's `os.File`/fd sit in the decoder's `walFileS` streams; `sync`'s
  `Fdatasync(w.tail().File)` and each lock's `Close` need them), (2) an fdatasync step on an **unregistered**
  pinned tail (its other half is the invariant's, out-record `O`; the synced meta must agree with the layout, a
  `walInvBody` step as `TailFsync`'s for a registered tail), (3) `walInvBody_unpin` at a step (exists), (4) the
  nil-receiver `File.Close` spec (`ErrInvalid` from `os`'s package facts). The failed handle (`walReadFailedF`)
  waits for `ReadAll`. `errors.IsPathErrnoNotExist.spec` (task 3) not started.

**Fifth session (branch `wal-close16`, 2026-11-14).**

- **`WalCloseLaw` proved** (`LinuxFs/Proof/.../wal/CloseLaw.lean`, `walCloseLaw`, for `walCodec`; no `sorry`):
  the update committed unchanged (`walDurLe` keeps `H`, so `walSyncedLb dir |H|` is the client's `d.H`'s);
  `walTailsRes_close` removes the tail record (`walTails_unregister`; the holder's half `{dir ↦ γt}` is the whole
  map, so the tail's record agrees with `(H, md, cuts, wr, ino, none)` and `TailsOnly` leaves nothing in flight,
  `F = ∅`); `walInvBody_untail` establishes the WAL's `TailIdle` (`TailExact` from the program's `TailMeta` half
  agreeing with the layout's last segment, `walsOk_segs_size`; `wr` by `tailStream_eq`); then
  `walInvBody_unpin` with the tail's halves as one segment, the directory claim and the pipeline names
  (`tmpClaims_walTmpsRes`: two whole claims of `walTmps`, the same name twice impossible, `osNames_only_excl`), and
  `walOpenW`'s `walLockedTok` (`import all Ghost`). **`WAL.Close.wp_proof` drops the hypothesis**: it rests on
  `WAL.sync.specC` and the proved callee specs only. Rebased on `wal-path15`'s `WalsBounded` conjunct.
- **`WAL.Close.specOpening` (task 2): not proved; three gaps found.** Done: `ownDecoder_streams`
  (`DecStreams.lean`: every file's stream state out of the decoder, through `bufio.ownReader_open`). Gaps:
  1. **The fdatasync of an unregistered tail.** `Close` of an unread handle runs `sync()`: no encoder, so
     `fileutil.Fdatasync(tail.File)`. `wp_osFsync` needs the whole `OsMeta` and bytes, so the invariant's halves
     (the layout's segment, `F = ∅`) must be joined at the step, and `walsOk_sync` (the registered tail's step,
     `TailSync.lean`) needs `TailZeros` and the `zf` bound, which the invariant keeps only for registered tails
     (and which fail after a crash: the bytes past the frames are junk until `ReadAll`'s `ZeroToEnd`).
     **Design** (for the invariant's owner, W1, and touching `CrashStart`, `Create`'s commit and `sync.specC`):
     strengthen `TailIdle` with **`TailSynced`**: the last segment `g` has `g.om.synced = g.om`, its bytes all
     `durB`, `lay.so = lay.wr` and `d.m = |d.H|`. Then the sync of an idle tail is a no-op on the invariant: a
     step joining the halves, `wp_osFsync`, splitting back the same values (`OsMeta.synced` idempotent on a
     synced meta: `syncZ` depends on the size and `cz` only, to check). Established by a crash (`CrashStart`'s
     segments are durable images), by `Create`'s commit (its segment fsynced before the rename) and by `Close`'s
     untail (needs `sync.specC`'s post to say the tail is synced: `TailMeta` says `lo = size = hi` only; carry
     `OsMeta.synced`/`durB` in `walHandleC`'s `tm`).
  2. **The pipeline's directory inode.** `walReadH`'s pipeline is `∃ j, walPipeH fp dir j 0`, independent of the
     tie's claim directory `j`; the put-back (`walInvBody_unpin`) needs `walTmpsRes` at the tie's `j`. Fix:
     `walReadH` takes the pipeline at the tie's `j` (`openAtIndex` has it: `walTmpsRes_split` at the claim's `j`);
     a sealed-body change touching `openAtIndex`/`Open`/`ReadAll` (`wal-readall16`'s unit).
  3. **`gs` may be empty** in `walReadTie` (no nonemptiness fact): then `tail()` is nil and `sync` is skipped; the
     proof splits on it (or the tie records `gs ≠ []`, which `selectWALFiles` gives).
  The nil-receiver `os.File.Close.specNil` (`wal-path15`, merged) covers `w.dirFile.Close()`.
  **For `wal-create14`'s `renameWALUnlock`**: `specOpening` does not cover its first `w.Close()`: that handle is
  `Create`'s, in append mode (encoder set) with `dirFile` nil. Its `Close` is `WAL.Close.wp_proof`'s with the last
  step `os.File.Close.specNil` in place of `wp_dirS`: state it as `WAL.Close.specNoDir` over a `walOpenWF`
  variant without the directory fd (the handle's `walDirH` then holds no `dfd`/`osDirFdS`), a copy of the proof
  with that one step changed. Not made this session. Its `newWAL.Close()` after a failed `ReadAll` is the failed
  handle's (`walReadFailedF`), waiting for `ReadAll`.
- **`wal.Repair` (W7, task 3): stated** (`LinuxFs/Spec/.../wal/Repair.lean`, `wal.Repair.spec Mr`; ledger
  2026-11-14): `Open`'s premises (`InArea`, `NameOk`, `cleanAbsPath r`, `|dir| < 2^59`, `walAreaOk`, the area's
  spine, `walAreaRes`, `osCallPerm 1`), the token framed (Q7), the update at `walAuMask` committed as accessed,
  the boolean unconstrained. **Not proved.** Its callee specs (hypotheses for the proof): `readWALNames.spec`/
  `readWALNamesAbsent.spec`, `filepath.Join`, `fileutil.LockFile.spec`, `os.File.Name`, `zap.NewNop`/`String`/
  `Error`/`Logger.Info`/`Warn`, `fileutil.NewFileReader.spec`, `NewDecoder.spec`, `decoder.LastOffset.spec`,
  `decoder.Decode.spec`, `decoder.LastCRC.spec`, `decoder.UpdateCRC.spec`, `walpb.Record.GetType`/`GetCrc`/
  `Validate`, `errors.Is`, `createNewWALFile.spec`, `os.File.Seek`, `io.Copy` of `*os.File` (no model:
  `File.ReadFrom`/`WriteTo`, §4.3), `os.File.Truncate` (an unregistered tail's), `fileutil.Fsync.spec`,
  `time.Now`/`Since`, prometheus `Observe`, `os.File.Close.spec` (deferred, twice). The invariant laws it needs:
  (L1) the pin of the last segment with the token (as `Open`'s, `walInvBody_pin`, one segment, read-write), with
  a path to `dir` (`WalDirPathLaw`/`wal-path15`'s name claims); (L2) the decoder over the pinned last segment
  accepting exactly its stream's frames then `io.EOF` or `ErrUnexpectedEOF` at `wr` (W1's crash condition, as
  `ReadAll`'s, `ReadAllDecode.lean`); (L3) the `.broken` file's creation in the WAL directory (a new non-`.wal`
  name under the directory's claim `(j, .except X)`: `WalDirClaim`'s coherence must allow it, to check; and
  `createNewWALFile`'s `O_TRUNC` on an existing `.broken`); (L4) the truncation of an unregistered tail at `wr`
  (an invariant step: the bytes past `wr` cut off, `old` shortened; with `TailSynced` (gap 1 above) the segment
  stays synced after the fsync); (L5) the put-back (`walInvBody_unpin`).
**Sixth session (branch `wal-close17`, 2026-11-14).**

- **`TailSynced` (task 1, decided): done** (`Inv.lean`). `TailIdle C Mr d lay := TailExact lay ∧ lay.wr = |stream| ∧
  TailSynced lay`, `TailSynced lay := ∀ g, lay.segs.getLast? = some g → (∀ y ∈ g.bs, y = durB y.1) ∧ ∀ z, g.om.zf =
  some z → |g.bs| ≤ z`. **Deviation from the fifth session's design**: neither `g.om.synced = g.om` (false at boot:
  `initMeta`'s `tc` holds the candidates past the size, which `OsMeta.synced` forgets) nor `so = wr` nor `d.m = |H|`
  (not needed: the sync step's new layout is `syncLay lay pre g0` and the WAL `d` itself, `walAbsD_syncIdle`). Established:
  at boot (`walInv_alloc`, `Crash.lean`: `g.bs = old.map durB`, `g.om = initMeta f`, `zf = pageEnd size`), at `Create`'s
  commit (**`walCreate_osAUnc` takes a new premise `hzf : ∀ z, g.om.zf = some z → |g.bs| ≤ z`**: `wal-create14`, from
  the synced segment's `TailMeta`), at `Close`'s unregistration (`walInvBody_untail` now takes the program's bytes half
  too; **`WalCloseLaw` takes `TailMetaS m bs`** = `TailMeta m bs ∧` every byte durable, `CloseHandle.lean`). **For
  `wal-save15` (W6)**: `WAL.sync.specC`'s success post is now `walHandleC … TailMetaS` (ledger 2026-11-14); from
  `fileutil.Fdatasync.wp_tail`'s post use `TailMetaS.of_sync` (`TailMeta m bs → TailMetaS m.synced (bs.map durB)`).
  `WAL.Close.wp_proof` unchanged (`lake build`).
- **The fdatasync of an idle tail: proved** (`TailSyncIdle.lean`, `TailFsyncIdle.lean`, no `sorry`). Pure:
  `walAbsD_syncIdle`, `fileCrashedR_unsync` (a crash of the synced tail is one of the tail before: bytes durable,
  exact, zeros only past the end), `crashOk_syncIdle` (W1 by `w1G_durable`), `tailIdle_syncIdle`, `walsOk_syncIdle`,
  `dirKeysOk_syncIdle`. Body: **`walInvBody_syncIdle`** (the WAL's key, the program's half of its directory's claim, the
  empty tails' half, `walCutFrag none`: gives the layout `pre ++ [g0]`, `walInvBody`'s `segRes g0`, and
  `walInos hj.cur = lay.segs.map ino` by the claim's agreement (`osClaims_agree`; the key's claim is the `WalsOk`
  claim, `DirKeysOk`'s "no other claim on `j` holds a `.wal` name"); back: `segRes (syncTail g0)` or `segRes g0`, the
  WAL state unchanged). Step: **`wp_idleFsync`** (`Fsync` with the program's halves of the file at the claim's **last
  `.wal` name**: `(walNames hj.cur).getLast? = some b`, `hj.cur !! b = some (.file d.ino)`; post the synced halves).
- **`WAL.Close.specOpening` (task 2): not proved.** Gap 1 is now `wp_idleFsync`, whose premise identifies the tail by
  the claim's names. **Obligation (for `openAtIndex`'s owner, `wal-readall17`)**: `walReadTie` must record, in write
  mode, `∀ g, gs.getLast? = some g → (walNames hj.cur).getLast? = some g.name` (`openAtIndex` opens
  `readWALNames`' sorted names from `nameIndex` on, so its last file is at the last `.wal` name). Without it (or the
  invariant's `WalPinnedSegs`) nothing ties the handle's last file to the layout's tail: `WalReadState`'s layout is
  existential, not the invariant's `Ls !! dir`. Gaps 2/3 are `wal-readall17`'s (`walReadH`'s `j`, `gs ≠ []`, seen in
  its worktree). Left for the proof: the pipeline's `Close`, `tail()`, `sync()` with a nil encoder (`time`, zap `Warn`,
  prometheus `Observe` as in `WAL__sync.lean`) over `wp_idleFsync` (the files out of the decoder: `ownDecoder_streams`),
  the lock loop on the decoder's files, `specNil` for `dirFile`, the put-back (`walInvBody_unpin` at a step, and the
  inverse of `walInv_mintOpening`: `walOpening` carries `walLockedTok`). `Open.wp_proof` keeps the hypothesis.
- **`WAL.Close.specNoDir` (task 3): not made; the fifth session's premise is wrong.** `renameWALUnlock`'s first
  `w.Close()` runs on the **pre-rename handle** (`walPreIn`, `WAL__SaveSnapshotPre.lean`: `fp` and `dirFile` nil,
  one lock), whose WAL is not yet in `walInv` (the rename failed: no layout, no `walOpenW`, no update): not a
  `walOpenWF` variant. Its `Close`: no pipeline, `sync()` as `WAL.sync.specPreL` (the stream `os.fileWI`/`fileS`,
  `walPreSyncOk`), the one lock's file closed, `specNil`. The spec must be stated over the resources
  `renameWALUnlock` holds at that point (in `U o`/`walCreateP`, the encoder and the segment's halves): **for
  `wal-create14`** to state with `renameWALUnlock`'s proof.
- **`wal.Repair` (task 4): not started.** Decided L3 recorded (the WAL directory's claim may hold `*.wal.broken`
  names). With `TailSynced`, L4's truncation keeps the tail synced after its fsync (bytes past `wr` cut, the rest
  durable).
- Merged `origin/wal-int` (`wal-save15`'s W6 changes).

**Seventh session (branch `wal-repair18`, 2026-11-14).** `wal.Repair`'s laws L1, L2 and L5's unchanged case proved
(no `sorry`); `Repair.wp_proof`, `openLast`'s spec, L3, L4 and `WAL.Close.specOpening` (task 2) not made.

- **L2, the reader of the last segment** (`RepairDecode.lean`, pure). `Repair`'s loop is `ReaderRun` on one file
  (`decStep` folds in its `LastCRC`/`Validate`/`UpdateCRC`). `RepairFile C bs rs` (the file starts with the frames of
  `rs`, a chain from CRC 0, nothing accepted at their end at the chain's CRC) and the loop invariant `RepairAt C rs off
  c` (the decoder at the end of a prefix, at the chain's CRC after it): `repairAt_start`, `repairAt_ok` (a record step
  keeps it, the file not dropped), `repairAt_stop` and `repairAt_fail` (a `goDecode` stop and a failed `proto.Unmarshal`,
  `GoFail`, happen only at the end of the frames: the encoder's frames are `UFail`-free, `decFrame_ofFrame`), and
  `walRepairFile`: the last segment of a WAL with `TailExact` and `wr = |stream|` (`TailIdle`) is a `RepairFile` whose
  frames end at `wr`. A fresh decoder (CRC 0) agrees with the chain from the segment's start because every segment's
  first record is a CRC record (`lastRecs_head`, `chainOk_crcHead`). So `LastOffset()` at `Repair`'s truncation is
  `wr`: the truncation removes no record. **What the wp proof still needs for the `errors.Is(err,
  io.ErrUnexpectedEOF)` test**: its answer on the readers' I/O errors must be `false` (else the truncation could be at
  an offset below `wr`); with `wal-readall17`'s error evidence (`os.errnoPathErr`) this should now be provable from
  `Errno.Is`, as `isEofOk`. On every decoder stop the answer may be anything (the stop is at `wr`).
- **L1, the pin of the last segment** (`RepairPin.lean`): `walInvBody_pinIdle` (`walInvBody_pin` in read mode, plus the
  WAL's `TailIdle` from `walTailsRes_idle`: a copy of the pin's proof, since `walInvBody_readIdle`'s layout cannot be
  identified with the pin's from outside), `walInvBody_pinLast` (`k = walLastK`, the one segment `gL`, as
  `walPinLast`), `walInv_openLast` (the update committed unchanged, as `walInv_openAt` with `write = false`), and
  `walInv_unpinLast` (L5 when nothing changed: `walInv_unpin`, one segment, read mode).
- **Name clash fixed**: `TailCrash.lean`'s `WalFs.lastRecs` renamed `lastSegRecs` (it clashed with `ReadAllDecode`'s
  `WalFs.lastRecs`, so no module could import both the invariant's crash lemmas and `ReadAll`'s reader; `ReadAll.wp_proof`
  would have met it too).
- **L3 (the `.broken` file), design found**: the WAL directory's claim `(j, .except X)` already holds `<seg>.wal.broken`
  (not a `.wal` name; `X` is `walTmps` in practice, but the invariant only says `X` holds no `.wal` name: add `∀ b ∈ X,
  ¬ ".wal.broken" <:+ b` to `DirClaimOk`/`WalDirClaim`, or `X ⊆ walTmps`). Two obstacles: (1) the part's
  `os.OpenFile` specs take `.only [b]` claims; the program holds half of a cofinite claim, so the create needs an
  invariant step joining the halves at the open's atomic update (as `walInvBody_syncIdle` for the fsync), or an
  `OpenFile` variant over a claim `N ∋ b`; (2) `O_TRUNC` on an existing `.broken` (a previous `Repair`'s) needs the whole
  file (`trFile`): nobody owns non-segment files of a WAL directory today. **The invariant must own the files at the
  claim's non-`.wal` names** (whole: meta and bytes), established at boot from the crash image and handed to the
  program at the step. That is new invariant state (internal, not client-visible).
- **L4 (truncate the unregistered tail at `wr`)**: not stated. With `TailIdle`, the bytes past `wr` are `old`'s; the
  truncation opens a resize window on an unregistered tail (the invariant's `TailWin` needs `lo ≤ wr`, and `SegFl.OkR`
  is only for registered tails, `TailsOnly`). Reuse of `wal-tc8`'s truncate supplies to check when it lands; else a
  step lemma keeping the segment's halves joined over `Truncate` and `Fsync` (both by the program, the lock held).
- **`io.Copy` of `*os.File`** (no trusted model): to be a hypothesis of the wp proof, §10.
- **Task 2 (`specOpening`) not started**: `wal-readall17`'s three `walReadTie` facts landed during the session (merged).

**Eighth session (branch `wal-repair19`, 2026-11-14).** Task 1 (`specOpening`) proved; task 2 (L3) designed, not
made; task 3 (L4) not started; task 4: `openLast` stated and proved, `Repair.wp_proof` not started (waits for L3/L4),
`io.Copy`'s hypothesis recorded in §10.

- **`WAL.Close.specOpening`: proved** (`WAL.Close.wp_proofOpening`, `LinuxFs/Proof/.../wal/WAL__CloseOpening.lean`, no
  `sorry`, `lake build`). Callee specs: **`WAL.sync.specIdle`** (new, `LinuxFs/Spec/.../wal/WAL__syncIdle.lean`, proved:
  `WAL.sync.wp_proofIdle`, over `WAL.tail`, `os.File.Fd`, `time.Now`/`Since`, `Duration.Seconds_ptr`, zap's `Duration`/
  `Warn`), `filePipeline.Close`, `WAL.tail`, `os.File.Close`, `os.File.Close.specNil`, zap's `Error`/`Logger.Error` (all
  proved or the part's leaf specs). Steps: the pipeline's `Close` (`pipeLeft`: its call-permission half and its leftover
  name; with the handle's `tmpClaim`, `walTmpsRes j` by `tmpClaims_walTmpsRes`); the decoder's files
  (`ownDecoder_streams`, then **`walTie_files`**, `CloseOpeningFiles.lean`: the segments' halves and, per index, the file
  and its fd); `w.sync()` over **`fileutil.Fdatasync.wp_idle`** (`FdatasyncIdle.lean`, `wp_idleFsync` through
  `syscall.Fdatasync`), the tail identified by `walReadTie`'s last-name fact; then, **at the next step, whatever the sync
  answered**, the put-back `walInv_unpin` with the tail's synced or unchanged halves (`syncOut_seg`) and the lock token
  from the ghost handle (**`walOpening_lockedTok`**: `walHandleP` holds it; the handle's ghost names stay behind, as
  `Close` of `walOpenW` leaves them); on success the loop closing every lock's file (`walTie_locks`: the files with the
  locks' `lockedFile` facts are `walLockH`s; a failed close logged), `Close` of the nil `dirFile` (`specNil`), the deferred
  unlock. The Go code returns early on a sync error, its locks left open: the halves are ghost, the token still comes back.
  `Open.wp_proof` keeps `specOpening` as a callee spec (now proved). No statement changed.
- **Build hazard found**: with `.lake` seeded by `cp -al`, Lake rewrites `.trace` files **in place**, so a build in one
  worktree changes the traces of every worktree sharing the inode (oleans are written anew). A trace rewritten by another
  worktree made `Proof.io.ReaderStream` look up to date over an old olean (`Unknown identifier io.errAt` in
  `bufio.Defs`). Fix: after `cp -al`, replace every linked `.trace` by a copy (`find .lake/build -name '*.trace' -links
  +1`, `cp -p` then `mv`), and delete a stale module's trace to force its rebuild.
- **L3 (the `.broken` file), design fixed (not made)**. The brief's decision (the invariant owns the WAL directory's
  non-`.wal` files; `DirClaimOk` says `X` holds no `.wal.broken` name) needs two pieces, each a multi-module change:
  1. *Where the files live*: **parked with the directory's claim**, in `walParked`'s per-claim element: `if ParkedClaim Ls
     o.D c then osNames c ½ ∗ walOthers c.1 c.2.2.cur else emp`, `walOthers j E := [∗map] b ↦ n ∈ E, if walNameP b then emp
     else tmpEnt (some n)` (the files whole, as `tmpClaim`'s `tmpEnt`). Whoever takes the claim's half out (the pins:
     `walInvBody_pin`, `_pinIdle`, `Exist`'s) takes the files with it and brings them back with it (`walInvBody_unpin`,
     `walParked_putClaim`), so no lending record is needed and the holder can `O_TRUNC` a leftover `.broken`. Rejected: an
     always-owned conjunct in `walInvBody` (a file lent across steps needs a record of lent inodes in `walOutFrag`/`o`,
     whose `WalOut` constructor every module builds positionally) and a separate invariant (it must agree with the claim's
     history, which only the invariant's `osClaims` half knows). Ripple: `walParked`'s 11 unfolding modules (`Parked`,
     `ParkedPut`, `Crash`, `CreateDropStep`, `CreateMergeStep`, `CreateKeys`, `CutAuLemmas`, `TailAcc`, `TailAccW`,
     `TailSync`, `Inv`); the holders' sealed bodies (`walReadTie`, `walDirH`, `walPinLast`, `Exist`'s pin) carry
     `walOthers`; `walCloseLaw` and this session's put-back return it; a cut's rename changes the claim's history at a
     `.wal` name only (`walOthers` of the new entries equal, a pure lemma); boot (`walInv_alloc`): the `rest` of
     `walStart`'s start files (the non-segment inodes, discarded today) at the claims' non-`.wal` names; `Create`'s new
     directory has none (`walOthers` of its entries `emp`: only the segment and `walTmps`).
  2. *The create step*: the extension creates a name only with the whole claim, so `createNewWALFile(b)` needs an
     invariant step at the open's atomic update joining the program's half with `osClaims`' half (as
     `walInvBody_syncIdle` joins a file's halves), the history logged with `b ↦ file i` (a non-`.wal` name). Its pure core
     is a family like the cut's (`creatingOk_cut`, `absentNone_cut`, `dirsOk_cut`, `walsNamed_cut`, `dirKeysOk_cut`,
     `crashOkA_cut_other`, `walsOk_dir_ne`): every fact over `cl` kept when one WAL directory claim's history changes at a
     name with `walNameP b = false` (the layout's relation reads only `.wal` entries, `walInos`/`walNames`; the crash
     condition only the `.wal` entries' histories). An `OpenFile` variant over the half claim is not smaller (it still
     needs this step). `DirClaimOk`'s new fact `∀ b ∈ X, ¬ ".wal.broken" <:+ b` (X is `walTmps` at boot and never changes)
     lets `b ∉ X` so that `b` is in the claim.
  Not started this session: the context budget went to task 1. Order for the next session: (2)'s pure family and step
  first (riskiest), then (1).
- **`openLast`: stated and proved** (`LinuxFs/Spec/.../wal/openLast.lean`, `openLast.wp_proof`, no `sorry`, `lake
  build`). Spec: `Repair.spec`'s premises; the update commits unchanged at the first step with the pin of the last
  segment (`walInv_openLast`); post `Q o` and either an error with the token back, or `err = nil`, `o ≠ none` and
  **`walLastOpen`** (`OpenLastDefs.lean`: `walPinLast`'s resources with the segment named, a kept path to the WAL
  directory, the last segment's `*os.File` opened `O_RDWR` and locked, offset 0, fd whole). Callee specs:
  `readWALNames.spec`/`specAbsent`, `filepath.Join`, `fileutil.LockFile` (over `walOpen_triple`). The error arms put the
  pin back (`walInv_unpinLast`); after `LockFile` the put-back needs a step, so its call is `wp_apply +noauto` (the
  stores of its results are the steps). For `Repair.wp_proof`: the decoder over `walLastOpen`'s file (law L2,
  `walRepairFile`, with the `os.File` reader bridge as `ReadAll`'s), the `errors.Is(err, io.ErrUnexpectedEOF)` test over
  the readers' error evidence (`os.errnoPathErr`, as `isEofOk`), then L3, `io.Copy` (§10), L4, `Fsync`, L5.

**Ninth session (branch `wal-repair20`, 2026-11-14).** Task 1 (L3's create step) in part: its pure core
and the `os` open it needs proved (no `sorry`, `lake build`); the invariant step itself not made, blocked
on one invariant fact (below). Tasks 2-4 not started.

- **`brokenHist_pure`** (`BrokenPure.lean`, pure): a keyed WAL directory's claim `(lay.j, .except X, hj)`
  replaced by `hj.log x e c` (`replClaim`), `e` writing only a free name `bt` with `walNameP bt = false`, `c`
  agreeing with `hj.cur` on every `.wal` name: `WalsOk`, `WalsCreateOk`, `CreatingOk`, `AbsentNone`,
  `WalsNamed`, `DirKeysOk … K cp` (any pending cut, the keys unchanged) and `WalsAt` all kept, `Ls`, `s`, `K`
  unchanged. The crash side through **`TreeNearW j m'' m'`** (the trees agree but at `j`'s non-`.wal`
  names): a crash of the new claims is one of the old on such a tree (`regionCrashed_nonwal`, from the cut's
  `regionCrashed_cut`), and every crash condition reads only the WAL directories' `.wal` entries and the
  area's (`crashOkA_nonwal`, `absentOk_nonwal`); `WalAbsD` reads `walInos` only (`walInos_congr`). Its
  premise `hothers`: **no other claim of `lay.j` holds `bt`**.
- **`wp_osOpenCreateSN`** (`GooseLang/Ext/Fs/TreeSharedCreateN.lean`): `wp_osOpenCreateS'` over a claim on
  any names `N ∋ b` (the proof is that one's, `N`'s other names unchanged; a new module, so nothing
  rebuilds; `wp_osOpenCreateS'` could become its corollary in a cleanup). **`os.OpenFile.specCreateTruncSncN`**
  (`LinuxFs/Spec/os/OpenFileTruncSN.lean`, `crOutN`; proved in `LinuxFs/Proof/os/OpenFileTruncSN.lean`, the
  proof of `specCreateTruncSnc` with `N`): what `Repair`'s `createNewWALFile(<seg>.broken, true)` calls in
  the absent-name case, the program passing a quarter of the directory claim and the update the invariant's
  half plus another quarter (as `walCut_osAUnc`, so that the update can identify the history).
- **The blocker: `hothers` is not in the invariant.** `DirClaimOk`'s exclusivity is only on `.wal` names (the
  cut renames onto one), and the claims' disjointness (`NamesCoh.disj`) is the shared invariant's, which an
  `os` call's update cannot open (`osAuMask`). It is needed (not an artefact): with another claim of `j`
  holding `bt`, the kept create has no crash of the old claims. **Design**: strengthen the exclusivity to
  every name of the claim, `∀ c' ∈ cl, c' ≠ (j, .except X, hj) → c'.1 = j → ∀ b, (NameSet.except X).Mem b →
  ¬ c'.2.1.Mem b` (implies the `.wal` one, `hX`). Least ripple: as a second conjunct inside `DirClaimsOk`'s
  `∃ X hj` (keys need nothing: at the step `DirClaimOk.eq_of_mem` identifies the key's claim with the
  `DirClaimsOk` one). Constructions: boot (`dirClaimsOk_start`, `walInv_alloc`'s `hdirs1`: no caller yet; the
  boot's claims of a WAL directory in `cl` are its directory claim only, the pipeline's `walTmpsRes` held
  whole outside `cl`), `Create`'s commit (`CreateKeys`: needs `CreatingNew`'s second conjunct strengthened
  the same way, where the creating token is made with the shared invariant open; the fresh directory's other
  claims are all the program's, outside `cl`), the cut (`dirKeysOk_cut`: unchanged other claims),
  `CreateDropInv`/`CreateMerge` (`mono_cl`: only `jr`'s claims change), `brokenHist_pure`. Destructurings:
  `OpenPinTake` (123), `CreateKeys` (196), `CutCommitLemmas` (307). Plus `DirClaimOk`'s second conjunct
  for `bt ∉ X` (`<seg>.wal.broken`): `∀ b ∈ X, ¬ go!".wal.broken" <:+ b` as the eighth session planned, or
  `X ⊆ walTmps`, in the same change (both are `DirClaimOk`'s, so every `⟨hjr, hX, honce, hcoh, hex⟩` site moves).
- **The step (`walBroken_osAUnc`, next)**: as `walCut_osAUnc` (`CutAu.lean`): the program's `walDirKey dir
  j X`, a quarter of the claim and its `walOutFrag o` (`(j, .except X) ∈ o.D`); open `walInv`, the key gives
  `K !! dir`, `DirKeysOk.1` the claim once (`l1 ++ c :: l2`, `osClaims_split`), `osNames_agree` the history;
  α the invariant's half plus the quarter. Commit `some (x, s0, i)`: `crOutN`'s facts give `hj.next ≤ s0 ≤ x`
  (`claimCoh_log`; `crEnt` writes only `bt`), the new claim's halves split back, `osClaims_split` at `l1 ++
  c' :: l2` (`claimOnce_repl`), `brokenHist_pure`, and `walParked` over the replaced claim unchanged (the
  claim is out by key, its element `emp` either way: a `walParked_cut`-like lemma without the segment part).
  Abort and `none`: the invariant as it was. Then task 2 (the files at the claim's other names, for the
  `O_TRUNC` of a leftover `.broken`: `os.OpenFile.wp_truncS` with `trFile`).

**Tenth session (branch `wal-repair21`, 2026-11-14).** Task 1 (the exclusivity) done and task 2's create
step proved (no `sorry`, `lake build` of every module importing `Inv`); task 2's `O_TRUNC` case, task 3 (L4) and
task 4 (`Repair.wp_proof`) not made: the first needs the multi-module ownership change below, the second a tail
registration for an idle WAL that `ReadAll` needs too.

- **`DirClaimExcl`** (`Inv.lean`, internal): `DirClaimsOk`'s per-WAL `∃ X hj` now carries, next to `DirClaimOk`,
  `DirClaimExcl cl j X hj`: `∀ b ∈ X, ¬ go!".wal.broken" <:+ b`, and no other claim of `j` holds a name of `.except
  X` (exclusivity on every name, not just the `.wal` ones). Placed in `DirClaimsOk` rather than `DirClaimOk` (the
  brief's wording): `DirKeysOk.1` inlines `DirClaimOk`'s facts and every `⟨hjr, hX, honce, hcoh, hex⟩` site would
  have moved; a key's claim is identified with `DirClaimsOk`'s by `DirClaimOk.eq_of_mem`, so the facts reach the key
  holder. Laws: `DirClaimExcl.repl` (a claim replaced by one of the same directory and names), `.mono` (no claim of
  `j` added), `walTmps_not_broken`, `not_walTmps_of_wal`; `DirClaimsOk.mono_cl` takes a second argument (the claims
  of a WAL directory after are claims before).
- **`CreatingNew`'s second conjunct strengthened** to `∀ c ∈ cl, c.1 = J → ∀ b, b ∉ walTmps → ¬ c.2.1.Mem b` (was:
  the `.wal` names). **Statement changes (internal, for `wal-create16`)**: `walInvBody_mint`/`walInv_mint` take
  `hXt : ∀ b ∈ X, b ∈ walTmps` after `hX` (the token's `J`-exclusivity is recorded off the pipeline names, `X`
  being the program's left-out names); `walCreate_osAUnc` and `dirKeysOk_create` take `hXt : X = walTmps` after `hX`
  (the new key's claim exclusive on all its names from `CreatingNew`, and `X` holding no `.wal.broken` name).
  `Create` calls both with `walTmps` (`CreateAuFresh`): pass `fun _ h => h` and `rfl`. Boot: `walInv_alloc`'s and
  `dirClaimsOk_start`'s `hdirs1` give the exclusivity on `(NameSet.except walTmps).Mem b` (was: `.wal` names).
  Repaired: `Crash`, `CreateKeys` (the new directory's `DirClaimExcl`, the others' by `.mono`), `CreateMint`,
  `CreateSteps`, `CreateAu`, `CreateMerge`/`CreateDropInv` (`mono_cl`'s new argument), `CutCommitLemmas`
  (`dirKeysOk_cut`: `.repl` for the cut WAL, `.mono` for the others), `BrokenPure`, `OpenPinTake` (destructuring).
- **`walBroken_osAUnc`** (`BrokenAu.lean`, new, proved): `Repair`'s update for `os.OpenFile.specCreateTruncSncN`
  in the absent-name case (`walBrokenP`: the key, a quarter of the claim, `walOutFrag o` with `(j, .except X) ∈
  o.D`; the call gets the other quarter, the update `½ + ¼`; `walBrokenQ`: the quarter at the logged history). The
  commit: `brokenCommit_pure` (the key's claim, `DirClaimsOk`'s `DirClaimExcl`: `bt ∉ X`, no other claim of `j`
  holds `bt`; `claimCoh_log`; then `brokenHist_pure`), `walParked_replOut` (a claim out replaced by one of the same
  directory and names: its element `emp` either way). Pure: `walNameP_broken` (a `.wal.broken` name is no `.wal`
  name), `crEnt_writes`. Not yet used (`Repair.wp_proof`).
- **The leftover `.broken`'s `O_TRUNC` (not made)**. The eighth session's design (the claim's non-`.wal` files whole,
  `walOthers`, inside `walParked`'s per-claim element next to its half) makes every holder of a WAL directory
  claim's program half carry them: the takers (`OpenPinTake`, `ExistPin`, `RepairPin`), the put-backs
  (`OpenUnpin`, `ExistPin`), and every sealed body holding the half (19 files: `walReadTie`/`walDirH`/`ReadState`/
  `ReadAllInv`/`CloseHandle`/`FdatasyncIdle`/`TailFsyncIdle`/`TailSyncIdle`/`WAL__syncIdle`/`OpenLastDefs`/...), many
  of them `wal-readall20`'s and `wal-save18`'s. Checked again and rejected: leaving the files in the invariant while
  the claim is out (the program writes the `.broken` file across steps after the open, `io.Copy`, so the file is lent
  across steps and needs a lending record); keying them to the pipeline names' parking (`walTmpParked` has no claim
  history to tie `E` to). Left for a session of its own, after `ReadAll` lands (fewest conflicts): add `walOthers`
  to the per-claim element, a `walClaimHalf j X hj := osNames j (.except X) ½ hj ∗ walOthers j hj.cur` used by every
  holder (one definition to thread), boot from `walStart`'s `rest`.
- **L4 (not made), design narrowed**: the truncate's supply `walTail_truncSup` (`TruncSup.lean`) and
  `os.File.Truncate.wp_specWalTail` apply to a *registered* tail (`walTailW`: `walTailKey`, the record `tailVar γ
  (H, md, cuts, wr, i, none)`, the program's halves); an unregistered tail cannot have a change in flight
  (`TailsOnly`). So `Repair` registers its WAL's tail after the pin (`walTailsRes_register`, from `walLastOpen`'s
  `walTailsFrag ∅`), which needs `TailZeros lay` and `TailBound C Mr d lay` of the idle WAL. `TailBound` holds
  where the idle WAL came from a crash (`CrashStart`: `wr = so = z0 = |stream|`, all the records), but **`TailZeros`
  does not**: `old`'s bytes past `z0` are the crash image's, not known zero (W1 only says no frame past the stream
  passes the CRC); `ReadAll` gets it from its `ZeroToEnd` before registering, `Repair` does not zero, it truncates.
  So either the registration happens with `old := old.take wr` (a layout change: `WalAbsD`'s and the crash
  condition's reading of `old` past `wr` to check, legitimate only once the truncate has landed), or L4 is a
  supply of its own for an unregistered tail (the seventh session's alternative: the segment's halves joined over
  `Truncate` and the fdatasync by the program, the lock held, with a change in flight allowed on the pinned last
  segment of a WAL out in read mode, `TailsOnly` extended). To decide with `wal-readall20` (whose registration is
  the other client), then state once. Then
  `specWalTail` at `o0 + |out| = wr` (its `walTailW` carries `ownOff f wr`: `Repair`'s offset after `io.Copy` is the
  file's end, so either a `Seek`-free variant of `specWalTail` framing the offset, or a lemma moving `ownOff`), the
  fdatasync closing the window (`TailSync`'s supply, as `WAL.sync.specCut`'s), the tail unregistered
  (`walTails_unregister`) and the pin put back (`walInv_unpinLast`, with the segment's new halves).
- **`Repair.wp_proof` (not started)**: its order is fixed by the code (`LinuxFs/Code/.../wal.lean`, `Repair.impl`):
  `openLast`; the decoder loop (`ReaderRun`, L2's `repairAt_*`); `errors.Is(err, io.EOF)`; `errors.Is(err,
  io.ErrUnexpectedEOF)`; `createNewWALFile(f.Name() + ".broken", true)` (absent: `walBroken_osAUnc`; present: the
  `O_TRUNC` above); `Seek`; `io.Copy` (hypothesis, §10); `Truncate(lastOffset)` (L4); `fileutil.Fsync`; the put-back
  (L5).

**Eleventh session (branch `wal-repair22`, 2026-11-14).** Task 1 (L3's leftover `.broken`: the WAL directory's
non-`.wal` files owned by the invariant) done (no `sorry`, `lake build` of every leaf importing `Inv`); task 2 (L4)
blocked on a W1-level finding (below); task 3 (`Repair.wp_proof`) not started.

- **Deviation from the eighth/tenth sessions' design (decided here, internal).** Not "parked with the claim's half"
  (`walClaimHalf`, which every holder of the claim's program half would carry: the takers, the put-backs and 19
  sealed handle bodies). Instead the files stay in the invariant **whether the claim is parked or out**, with a
  lending record: `walParked`'s new last conjunct `walOthersL Ls o.D cl` (`Inv.lean`): for every WAL directory claim
  (`WalDirClaimOf`), `walOthers o.D c.1 c.2.2.cur := [∗map] b ↦ n ∈ othersOf o.D j E, tmpEnt (some n)` (the file
  whole, `trFile i False`, as the pipeline names' `tmpEnt` and `wal-leaf5`'s `.touch`; a directory there is `False`),
  `othersOf D j E` the entries at non-`.wal` names **not lent**. A name lent is the pseudo-key `lendKey j b = (j,
  .only [b])` in the record of what is out, `WalOut.D` (whose claim keys are always `.except` ones, so the two never
  meet): no `WalOut` field added (54 positional constructions, in sealed bodies other agents edit), no new ghost name.
  Why the invariant can keep them while the claim is out: the claim's history is the invariant's either way
  (`osClaims`' half), and only `Repair` changes it at a non-`.wal` name (`walBroken_osAUnc`, which now lends the new
  name at the same step). The tenth session's objection to this design (the `WalOut` constructor built positionally
  everywhere) does not apply to a pseudo-key in `D`.
- *Laws* (`Inv.lean`): `othersOf_lookup`, `othersOf_congr` (entries agreeing off `.wal` names), `othersOf_congrD`,
  `lendKey_cons_except`/`lendKey_filter_except` (a claim key moved: nothing lent), `othersOf_lend` (a name created and
  lent at once), `othersOf_lend_ne`, `walOthers_lend` (a leftover file taken: its `tmpEnt`), `walOthers_unlend` (given
  back), `walOthers_none`, `walOthersL_mono`/`_keyD`/`_repl` (one claim replaced), `walDirClaimOf_key`.
- *Threaded* (each destructuring of `walParked` gains `Hw`): `Parked` (`walParkedIn` too; `walParked_takeClaim`/
  `putClaim` move a claim key: `walOthersL_keyD`; **`walParked_putClaim` takes `hcX : ∃ X, c.2.1 = .except X`, an
  auto-param** (`⟨_, rfl⟩`, both callers pass `(j, .except X, h)`)), `ParkedPut`, `TailSync`/`TailAcc`/`TailAccW` (the
  layout replaced, same directory), `CutAuLemmas` (**`walParked_cut` takes `hcur : ∀ b, walNameP b = false →
  c'.2.2.cur !! b = c.2.2.cur !! b`**: the rename writes a `.wal` name; `CutAu` passes it), `CreateKeys`
  (`walDirClaimOf_create`, `walOthersL_create`: **`walParked_create` takes `hJo : ∀ b, walNameP b = false → hJ.cur !!
  b = none`**, the new directory's claim holding no other file), `CreateAu` (**`walCreate_osAUnc` takes `hJo`, its last
  premise; `createFresh_osAUnc` discharges it from its `hcur`**: for `wal-create22`, nothing to do unless a new caller
  appears), `CreateMergeStep` (`others_cover`), `CreateDropStep` (`others_drop`), `BrokenAu`, `Crash`.
- *`BrokenAu`*: `walParked_replOut` replaced by **`walParked_lendNew`** (the claim replaced, the new name `bt` lent: the
  record `o.addClaim (lendKey j bt)`); **`walBrokenQ`'s commit case returns `walOutFrag (o.addClaim (lendKey j bt))`**
  (statement change, not yet used). No other WAL directory claim of `j` (`dirClaim_noOther`: it would hold `.wal`,
  `DirClaimOk`'s exclusivity).
- *`BrokenLend.lean`* (new): `walInvBody_dirClaim` (the invariant's `walParked` at a keyed WAL directory's claim, the
  program's half agreeing, and the way back), `walParked_lendOld`/`walParked_unlend`, **`walInv_lendOther`** (at any
  step: the program's key, claim half at `hj` with `hj.cur !! bt = some n`, `walOutFrag o`, `lendKey j bt ∉ o.D` ⟹
  `tmpEnt (some n)` and `walOutFrag (o.addClaim (lendKey j bt))`: what `os.OpenFile.wp_truncS` takes for the leftover
  `.broken`) and **`walInv_unlendOther`** (the file back, `o.delClaim (lendKey j bt)`). `Repair` returns the file
  (either case) before `walInv_unpinLast`, whose record `⟨[gL.ino], [(lay.j, .except X)], []⟩` is then exact again.
- *Boot*: **`walInv_alloc` takes `(∀ Ls, ⌜WalsStart C Mr R jr s Ls V.now⌝ -∗ walOthersL Ls [] cl)`** (no caller yet,
  as its `walTmpsRes` premise; a caller gets the files from the crash's start files, `osFileStart_trFile` of
  `wal-leaf5`, and must exclude a directory at a non-`.wal` name of a WAL directory).
- **L4, finding (blocks L4 and `Repair`'s `ErrUnexpectedEOF` arm; coordinator's, a trusted-assumption question for the
  user).** `walInvRegisterPendLaw_holds` applies to `Repair`'s pin as is (`gs = [gL]`), giving a lent tail of kind
  `true` (`walPendTok`, `TailZ0` only). `walTail_truncSup` refuses kind `true` (`hok : ∀ k, ok ≠ some (k, true)`); kind
  `false` needs F-Z or `TailPend` (`LenZ`: the length word at `wr` zero), which `ReadAll` gets from `ZeroToEnd`'s
  first step. `Repair` truncates exactly when the decoder found a **torn frame at `wr`** (`io.ErrUnexpectedEOF`): the
  word at `wr` is generally nonzero, so neither holds, and the truncate window's crash step meets `wal-tc15`'s gap: a
  crash leaving the crash image's bytes past `wr` mixed with the truncate's zeros (which the extension's truncate
  model allows) is not covered by W1 (no frame past the stream passes the CRC, for the
  image's bytes only). With `wr` within 8 bytes of a block end, the length word at `wr` mixes zeros and old bytes and
  the frame read there is not one of the image's. Proposals: (a) **W1 extended** (trusted, the user's): no frame past
  the stream passes the CRC in the image's bytes past the stream with any suffix from a block boundary zeroed (the
  shrinking truncate's crash outcomes), then a kind-`true` shrinking supply at `wr` (`rzStart_pureP`'s form with that
  W1); (b) the evidence first: an `examples/osfs/semantics/` case measuring whether ext4 on configuration C can leave
  the zeroed block tail without the size change (if it cannot, the model's truncate outcomes could be narrowed instead). The offset snag is separate and small: `walTailP`/`walTailW` carry
  `ownOff f wr`, `Repair`'s offset after `io.Copy` is the file's end; a `Truncate` spec over the tail with the offset
  framed (`specWalTail`'s proof does not touch the offset) or the predicates' offset as a parameter.
- **`Repair.wp_proof`: not started.** Its order is fixed by the code (tenth session); its new pieces from this session:
  the leftover case `walInv_lendOther` then `os.OpenFile.wp_truncS`, the absent case `walBroken_osAUnc` (lends too),
  then after `bf.Close()` `walInv_unlendOther` with the file's `trFile i False` (`io.CopyFiles.spec` must give it
  back with `cut = none`, `maps = ∅`, `lo ≤ size`, `ZfGe`), then `walInv_unpinLast`. The tail's `Fsync` (`fileutil.Fsync`,
  not `Fdatasync`) needs a WAL-tail form of its own (`Fsync.spec` takes the whole `OsMeta`), as `Fdatasync.specWalPend`.

**Twelfth session (branch `wal-repair23`, 2026-11-14).** Task 1 (L4) in part: the crash step proved, no
trusted change (no `sorry`, `lake build` of `TailCrashRep`); the supply's use of it, the offset snag and the
WAL-tail `Fsync` not made; task 2 (`Repair.wp_proof`) not started (two blockers below).

- **L4's crash step, the coordinator's argument made** (`TailCrashRep.lean`, new, pure; withdraws the eleventh
  session's finding: W1 as it is covers the image). **`RepOld lay`**: `wr = z0`, and every byte the segment may
  leave from `wr` on (`segBytesX g`) lies within `old` and reads `old`'s byte as of the last sync (`valAt
  (cands b) 0 = old.getD b 0`). **`crashTo_tailR`**/**`crashOkA_tailRep`** (`crashTo_tailP`/`crashOkA_tailPend`
  with `RepOld` in place of `TailPend`): a frame the crash image's reader accepts at `wr = |S|` is on the fresh
  reader's path (**`acceptsFrom_frames_sub`**, then the CRC head as in `crashTo_tailL`), so W1G gives
  `AsOfOneG` of its core; as of the sync the core is `old`'s and the image no longer than `old`, so the durable
  image's reader accepts the same frame (**`decStep_congr`**: the step reads only the core and the length),
  against **`WalAbsD.tailStop`** (`z0 = wr = |S|`; no decoder evidence from the program needed); as of a change
  `n > 0` the candidate at `wr` would be stamped by a non-resize, but `WinCands` gives only stamp 0 or a resize
  stamp there (nothing written past the stream). The segment must stay within `old`: a growth's zeros past `old`
  could complete a frame the durable image tears short (case (i) then says nothing). **`TailLast.repOld`**/
  **`WalAbsD.repOld`** (every exact tail with `wr = z0`: `ByteOk`'s unsynced head `(old b, 0)`, later stamps `>
  0`), **`repOld_rzCands`** (a resize's first step: zeros appended with stamps `> 0`, `valAt0_rzCands`),
  **`repOld_rzLand`** (the landing: the same candidates). **`tailCrashStep_rzStartR`**, **`rzStart_pureR`**
  (`rzStart_pureP` with `TailZeros lay ∨ (RepOld lay ∧ |S| = wr)`). The landing and the not-landed outcome
  need nothing (`rzLand_pure`, `walsOk_self`).
- **Not made: `walTail_truncSup` accepting the pending tail (kind `true`)**: the start's update needs `RepOld`
  of the layout at *every* attempt. The first attempt starts from `Repair`'s exact idle tail (`WalAbsD.repOld`
  from `TailIdle` and the registration's `TailZ0`'s `wr = z0`); a later one (`os.File.Truncate.specAu` retries
  after an undone attempt: `ftUndoneH`, `P` monotone) starts from the window `rzSeg … n` of the first, whose
  `RepOld` holds (`repOld_rzCands`) but no fact the supply sees records it (`WinCands` has the candidates'
  shapes, not that each byte keeps `old`'s stamp-0 candidate, nor `0 ∉ rz`). **A channel is needed**
  (coordinator's choice; internal, no client-visible change): (A) the lent registry carries `TailZeros ∨ RepOld`
  for each kind-`true` tail (a conjunct of `walLentRes` next to `ZerosOk`, which exempts kind `true`); its
  maintenance is needed only on kind-`true` steps (`Repair`'s truncate: `repOld_rzCands`/`repOld_rzLand`), but
  `walLentRes_insert_same` and `TailAccW`'s continuation are generic, so their premise must be conditional on
  the token's kind (`TailAccW` has `ok`: `ok = some (_, true) → …`), threaded through every supply over
  `TailAccW` (`truncSup`, `fallocSup`, `truncSupG`, the syncs); `walLentRes_regPend` gets it from `TailIdle`
  (`WalAbsD.repOld`). (B) `os.truncSup`'s `P` over the bytes cut off too (`P m0 xs0`, monotone across
  `rsAnn`): a part-`os` spec change, `Repair` passing "the stamp-0 values of `xs0` are its own" with the
  handle's bytes. (A) recommended (WAL-internal; (B) changes a library spec for one caller). Not
  `RepOld` in `WalAbsD` (true of every reachable window with `wr = z0`, `ZeroToEnd`'s growth included, but
  its maintenance through the growth steps' `pc` candidates is the largest of the three).
- **Finding (blocks `Repair.wp_proof`'s failure arms after the truncate; coordinator's, possibly the user's).**
  `Repair` returns `walUnlockedTok`, whose `walTailsFrag ∅` makes it unregister its tail, which needs
  `TailIdle` (`WalTailIdle`: exact). After a failed `f.Truncate` (`ftUndoneH`: the window open, `lo = wr`) or a
  failed `fileutil.Fsync` (the window open, landed or not) the Go code returns `false` with no sync, and nothing
  can close the window. The crash condition of that state is fine (`crashOkA_tailRep`: the window of a `RepOld`
  tail). Options: (a) `WalTailIdle` admits an unregistered tail in such a window (`RepOld`, the window a truncate
  at `wr`): `ReadAll`'s registration and `Exist`/`Open`/a later `Repair` must take it (a later `Repair`'s
  truncate starts from it: kind `true`, `RepOld` from the idle fact); `ReadAll` would need its tail exact
  (`ZeroToEnd` from a window); (b) `Repair`'s post on `false` weaker (client-visible: the user's). Not decided.
- **Not made (unchanged from the eleventh session)**: the offset after `io.Copy` (`walTailP`/`walTailW` carry
  `ownOff f wr`; a `Truncate` spec over the tail with the offset framed), the WAL-tail `fileutil.Fsync` (as
  `Fdatasync.specWalPend`, the window's sync `walAbsD_syncW` with `WinZero` vacuous after the landing and
  `tailZeros_syncW0` from `wr = z0`), `Repair.wp_proof` (the eleventh session's plan, plus the above).

**W3/W5 log, thirteenth session (branch `wal-read13`, 2026-11-14).** `Open.wp_proof` proved (no `sorry`, `lake build`).
- *Task 1, the call permission* (ledger 2026-11-14, "the call permission counted twice"): the sealed `walOpeningF`
  (`ReadDefs.lean`) holds `osCallPerm ½`; `Open.spec`'s success arm is `walOpeningF w dir s` alone. `ReadAll` must move
  that half into the write handle's `walDirH`. `openAtIndex` and `OpenForRead` keep their posts (read mode returns the
  whole permission: no pipeline).
- *Statement change (internal)*: `openAtIndex.spec`'s error arm adds `∃ e, ⌜err = GoInterface.ok e⌝ ∗ errOk e` (`Open`
  wraps it with `%w`; the proof frames `Errorf`'s `errOk`); `OpenForRead`'s proof drops it.
- *New, proved*: `os.OpenFile.wp_dirSOk`/`os.Open.wp_dirSOk` (`LinuxFs/Proof/os/NsSOk.lean`: `wp_dirS` with the error's
  `fmtErrorOkOrNil`, `os.wp_pathError_ok`), `fileutil.OpenDir.specOk`/`wp_proofOk` (`OpenDirOk.lean`, spec and proof).
- *`Open.wp_proof`* (`Open.lean`): `openAtIndex` in write mode; the WAL's key from `walReadH` (`walReadH_key`), a path to
  the WAL directory from `WalDirPathLaw` at `OpenDir`'s step (**swap for `wal-path13`'s law there**), `OpenDir.wp_proofOk`;
  success: `walOpeningF` (the dir fd at the key's `j`); error: `w.Close()`, then `Errorf`. **Hypotheses**:
  `openAtIndex.spec`, `WalDirPathLaw`, `fmt.ErrorfErrs.spec`, and **`WAL.Close.specOpening`**
  (`LinuxFs/Spec/.../wal/WAL__CloseOpening.lean`, new, for W10): `Close` of a write-mode `openAtIndex` handle with
  `dirFile` nil, from `walAreaOk`, `walOpening`, `walReadH true`, `osCallPerm ½`, gives `walUnlockedTok ∗ osCallPerm 1`
  on any error. Its proof needs: the pipeline's `Close` returning its half and its `walTmpsRes` (`tmpClaim`s), a ghost
  step `walOpening → walLockedTok` (the inverse of `walInv_mintOpening`), `walInvBody_unpin` at a step, and the sync's
  early return (the Go code leaves the locks open: the token still comes back, the halves being ghost).
- *Task 2, `WalPinSized` (designed, not made).* The invariant change is not made this session: it touches every proof
  that destructures `walInvBody` (24 modules) and `wal-path13` adds its metadata conjunct to the same patterns at the same
  time, and its maintenance at the crash needs a bound the invariant does not hold. **Design** (for one session after
  `wal-path13` lands, ideally one conjunct for both bounds, e.g. `⌜WalsBounded s Ls⌝ := (∀ dir d, s.wal !! dir = some d →
  d.metadata.length < 2^41) ∧ ∀ g ∈ segsAll Ls, g.om.hi ≤ 0xffffffff000`): bound **`g.om.hi`**, not `|g.bs|` (with
  `WalAbsD.metas`' `|g.bs| ≤ g.om.hi` it gives the decoder's `|g.bs| + 2^12 < 2^62`); a bound on `|g.bs|` alone is not
  kept by a crash, whose new size is anything in `[m.lo, m.hi]` (`CrashFiles.lean:169`, `initMeta f`: `hi = f.size`).
  Kept by: the tail's writes (`pwPost`/`cfMeta` announce `max size (off + n)`, and `segAnn_ok` has `off + n ≤ size`);
  resizes (`rzMeta`: `hi` raised to `tg`, `tg ≤ size` for `cut`'s truncate and `ZeroToEnd`); `cut` and `Create` (the
  new segment is the pipeline's file: **`pipeFile` must add `m.hi ≤ 0xffffffff000`**, which `filePipeline.alloc`'s
  `O_TRUNC` create and `Preallocate` to `sz ≤ 0xffffffff000` give); the crash (`f.size ≤ m.hi` of the real meta, the
  in-flight segments' through `F`'s `fl.m`); `walInv_alloc` (a premise on the files found). `WalPinSized` is then
  `walInvBody_pin` with the conjunct read off, and `openAtIndex`'s `hpin` goes.
- *Not done*: Task 2's change (above), `ReadAll` (task 4: obligations unchanged from the twelfth session, plus moving
  `walOpeningF`'s call-permission half into `walDirH`; its `Close` on a failure arm is `walReadFailedF`'s).

**W3/W5 log, fourteenth session (branch `wal-readall14`, 2026-11-14).** `ReadAll`'s pure core proved (no `sorry`,
`lean-check`); `WAL.ReadAll.wp_proof` itself still `sorry` (its Goose body is ~40 KB: the loop, eight error arms,
the zeroing, three syncs, the encoder; not started).
- *Proved, the reader on the running files* (`ReadAllDecode.lean`, `ReadAllFiles.lean`): **`walReadFiles_running`**:
  under `WalAbsD C Mr d lay ents`, `TailExact lay` and `lay.wr = |segStream … lay.cuts.length|` (the last segment's
  stream all written), a fresh reader of the page-cache bytes (`segImg g = g.bs.map (·.1)`) of `lay.segs.drop kk`
  reads exactly `(recsOfSegs … (segsOf (histM d) lay.cuts)).drop (recsOfSegs … (take (first + kk))).length`
  (over `walDecodeFiles_core`/`_suffix`: the non-last segments are their frames (`intact`), the last its frames then
  zeros past `z0 < |S|`, or `old` with `tailStop` at `z0 = |S|`: `noCollision_running`). Helpers: `histCut_of_le`,
  `lastRecs`, `chainSegs_appendR` (a copy of `CutHdrStream`'s `chainSegs_append`, renamed: that module imports
  `Handle`), `tailLast_img`, `decStep_zeros_any`.
- *Proved, the fold to the post* (`ReadAllOk.lean`, `ReadAllPos.lean`): **`readAll_ok_pure`** (a successful
  `readAllFold` over those records is `walReadAllOk I cut s σ` with the metadata; from a cut file `s` is newest from
  the read position `k` too, because the fold matched a snapshot record of `s`'s index after `k`:
  `walNewestPair_suffix`, `walValidSnaps_suffix`; `walReadAt_of_from`, the converse of `walReadAt_from_eq`);
  **`readPos_le_openPos`** (`k ≤ walOpenPos I a` from `k`'s name bound, `ix ≤ a`, and that record).
- *Proved, combined* (`ReadAllPure.lean`): **`readAll_success hC hU hab hex hwr hcpos kk g hg s hsel hs stop r hok :
  ∃ σ, walReadAllOk (histM d) d.cut s σ ∧ r = (d.metadata, σ.hs, σ.ents)`**, `hok` the fold over
  `(walDecodeFiles C ((lay.segs.drop kk).map segImg) 0#32).recs` (what `readerRun_start` gives of the Go loop when it
  stops, not `GoFail`). Also `length_flatten_take_segsOf` (`(segsOf I cuts).take p` holds `segStart cuts p` ops),
  `segStart_mono`. The AU's `d` vs the invariant's: `walDurLe` keeps `H`, `cut`, `metadata`.
- **Hypotheses stated for the wp proof** (no `sorry`): `WalReadState` (`ReadAllLaws.lean`, one invariant law: at a
  step, the WAL's key, `walTailsFrag ∅`, the out-record and the pinned halves give the invariant's `d`, layout,
  names with `WalAbsD`, `TailExact`, the stream written (**`WalTailIdle`**: not in `walInvBody`; true after a crash,
  `CrashStart`, and `Create`'s commit; `Close`'s unregistration must establish it, W10), the cuts positive
  (`0 < b`: `walCutPos` allows a cut at 0, which `readAllFold_from` cannot read from; every real cut follows a
  `Save`), and `lay.segs.drop kk = gs` (the pinned segments still the layout's suffix)); `decoder.Decode.specR`
  (`decoder__DecodeR.lean`, ledger 2026-11-14 "the error's identity": `decPost` lets a bad frame return `io.EOF`
  and gives no `errors.Is` answer on the decoder's own errors).
- **Obligations for other units.** (1) `walReadH`/`walReadTie` must record the selection's fact for the first
  pinned segment (`∀ sq ix, g.name = walFileName sq ix → ix ≤ s.1`, `readAll_success`'s `hsel`: `openAtIndex`
  knows it from `searchIndex`, `walOpenK`); a sealed `ReadDefs` change and `openAtIndex`'s proof. (2) The invariant
  owner: `WalReadState` (W1; `WalTailIdle` as a framed conjunct over unregistered WALs, the cuts' positivity in
  `WalAbsD.cuts`). (3) `Decode.spec`'s strengthening (W3a). Unchanged from the thirteenth session: the `ZeroToEnd`
  instance (`wal-tc5`), the tail registration and F-Z commit, the permission half into `walDirH`, the read tail's
  sequence `< 2^63` (`k = h.pc = 0`), the metadata bound (`WalsBounded`, `wal-path13`), `walInvBody_unl`, `walOpenWF`.
- *Plan for the wp proof* (next session): the loop as `ReaderRun` built backwards is awkward in a `for`; carry
  instead `(rdRest C fs₀ 0 0#32).recs = acc ++ (rdRest C fsᵢ offᵢ cᵢ).recs` and `foldlM raStep raInit acc = .ok st`
  (Go's `metadata/state/ents/match` the state's), stepping with `rdRest_ok`; at the exit `rdRest_stop` (or the
  `GoFail`/`IoE` arms: error) gives `walDecodeFiles … = acc` and the stop; the write-mode check then needs
  `specR`. Open `walInv` once at the commit step (the `Fsync(w.dirFile)` or `syncDir`'s step, for `walNamed`),
  read `WalReadState` there and apply `readAll_success`.

**W3/W5 log, fifteenth session (branch `wal-readall15`, 2026-11-14).** The decoder's error identity, `WalTailIdle`
in the invariant, the selection fact; `WAL.ReadAll.wp_proof` still `sorry` (not started). No `sorry` added.
- *Task 1, the decoder* (ledger 2026-11-14, "the error's identity": **adopted**). `decPost` (`DecDefs.lean`) is now
  `decPostB ∗ decAns eof err` (the old body; `errors.Is(err, io.EOF)`'s answer on a non-nil error, `isEofAns`);
  `stopErr`'s catch-all is `e ≠ nil ∧ e ≠ eof`, so `io.EOF` comes only from the `.eof` stop (the `IoE` arm: `isEofOk`'s
  `¬ IoE eof`). `Decode.spec`/`decodeRecord.spec` read the same; **`decoder.Decode.specR` deleted**. Re-proved
  (`decoder__decodeRecord.lean`, `decoder__Decode.lean` unchanged, `lake build`), over two new **hypotheses**:
  `fmt.ErrorfErrsNot.spec` (`LinuxFs/Spec/fmt/ErrorfErrsNot.lean`: `Errorf`'s result is not `t` and `errors.Is(_, t)`
  is false on it when so of every error argument, `t` a package variable's value; `errIsNot`) and
  `proto.UnmarshalWalRecordE.spec` (the error is not `io.EOF`, same answer); `perennial-changes.md` 2026-11-14.
  *Statement changes (internal)*: `walpb.Record.Validate.spec` takes targets `X`/`t` and `errIsNot ErrCRCMismatch t`,
  gives `errIsNot` of its error (re-proved over `ErrorfErrsNot`); `decEnv` holds `errIsNot ErrCRCMismatch io.EOF` (a
  client obligation, as `isEofOk`). New lemmas (`DecLemmas.lean`): `decPost_mk`, `decAns_nil`, `decAns_of_eofOk`,
  `decAns_of_not`, `errIsNot_ueof`, `errIsNot_ne`.
- **Finding (for `openAtIndex`'s owner): `WalDecEnvSupply` is unsatisfiable.** It gives `decEnv IoE eof ueof` with
  `∀ ii, IsPointerError ii → IoE (ok ii)`, but `decEnv`'s `isEofOk` needs `¬ IoE eof`, and `eof` (`io.EOF`, an
  `errors.New` `*errorString`) is a pointer error: the hypothesis proves `False` under `isPkgInit wal`, so
  `openAtIndex`/`Open`/`OpenForRead` are vacuous until it is fixed. Fix: `IoE` the `*PathError`s (`os.File.Read`'s
  error) and `Stat`'s errors with `≠ eof` (`ReadBridge.lean`'s two uses of `hIo`: line 133 a `*PathError`, line 200
  `Stat`'s pointer error, which then needs `Stat`'s spec to say it is not `io.EOF`).
- *Task 2, `WalTailIdle`* (`Inv.lean`). **Deviation from "a separate conjunct of `walInvBody`"**: the condition is on
  the WALs with no registered tail, i.e. on `walTailsRes`'s map `T`, which only `walTailsRes` binds (a separate
  conjunct would need `T`'s authority split three ways). So it is a third pure part of `walTailsRes`, after
  `TailsOnly`: `WalTailIdle C Mr s Ls T := ∀ dir d lay, T !! dir = none → s.wal !! dir = some d → Ls !! dir = some lay
  → TailIdle C Mr d lay`, `TailIdle := TailExact lay ∧ lay.wr = |segStream … lay.cuts.length|` (still framed: no proof
  that does not unfold `walTailsRes` changed). Established by `walInv_alloc` (from `WalsStart`: `wr = z0 = |S|`, the
  last segment exact) and by `Create`'s commit (`walTailsRes_create`'s new premise, `CreateAu`'s `hex`/`htail`); kept by
  the registered WALs' steps (`WalTailIdle.of_reg`: `walTailsRes_cut`, `_append`, `TailAcc`/`TailAccW`), the state-only
  changes (`walTailsRes_mono` takes the reverse lookup too: `OpenUnl`, `TailSync`, `CreateNamed`) and registration.
  **Obligation (W10)**: `Close`'s unregistration must establish `TailIdle` of its WAL (after its sync: the stream
  written; no resize window open).
- *Cut positivity: not done.* It cannot go into the invariant without the cut recording it: `CutLay`'s `hcut` gives
  only `walCutPos` (which allows 0), and the crash must keep it (`WalsStart`). Plumbing (for the cut's owner):
  `0 < h.H.length` through `WAL.cut.spec` (`WAL__Save` knows it: its history is `H ++ [save]`), `CutAu`, and a fourth
  pure part (`∀ dir lay, Ls !! dir = some lay → ∀ b ∈ lay.cuts, 0 < b`, all WALs) with `walTailsRes_cut` taking
  `∀ b ∈ lay'.cuts, b ∈ lay.cuts ∨ 0 < b`; `WalsStart` and `CrashPure` keep it. Not a field of `WalAbsD`: a dozen
  positional constructions (`RzStepPure`, `TailStepPure`, `OpenUnl`, ...) would break.
- *`WalReadState`* (`ReadAllLaws.lean`): **still a hypothesis**, now with its idle part proved: **`walInvBody_readIdle`**
  (the WAL's key and `walTailsFrag ∅` give `d`, the layout with `lay.j = j`, `WalAbsD` and `TailIdle`); helpers
  `walTailsRes_idle`, `walDirKeys_lay`. What `WalReadState` adds and no invariant fact gives yet: (i) the cuts'
  positivity (above); (ii) **`WalPinnedSegs`**: the pinned segments `gs` are `lay.segs.drop kk`. Design (for the
  invariant's owner): a pure part of `walParked` relating the out record to the layout, `∀ dir lay, Ls !! dir =
  some lay → (lay.j, _) ∈ o.D → T !! dir = none → ∃ k, (lay.segs.drop k).map ino = o.O` (one handle at a time: the
  lock token); the pin establishes it (`walInvBody_pin`: `walOpenK`), the put-back and registration drop it, purges
  (W9, `ReleaseLockTo`) keep it (they drop a prefix and the handle's own pins), the contents then follow from the
  halves' agreement (`walTailsRes_none`: no change in flight). Once both are in, `WalReadState` is
  `walInvBody_readIdle` plus them.
- *Task 3, the selection fact*: `walReadTie` takes the start `s` and records `∀ g, gs.head? = some g → ∀ sq ix,
  g.name = walFileName sq ix → ix < 2^64 → ix ≤ uint.nat s.1` (`openAtIndex`: `walSearch_sel`, over
  `walSearchFrom_le`). **The bound `ix < 2^64` is needed**: `walFileName` keeps `ix` modulo `2^64` (`hex16`), so the
  unbounded form is false. Hence `readAll_success` now takes `hsel` in that form and **`hnb`** (the selected segment's
  `nameBound` with `ix < 2^64`) instead of reading `hab.nameBound`: **obligation (invariant's owner)**: `WalAbsD.nameBound`
  should carry `ix < 2^64` (the cut names its file with a `uint64`, `Create` with 0; the copies are unchanged).
- *Not done*: `WAL.ReadAll.wp_proof` (task 4), with the fourteenth session's plan; its hypotheses now: `WalReadState`
  (narrowed as above), `Decode.spec` (strengthened), the `ZeroToEnd` instance (`wal-tc5`), `walInv_dirPath`
  (`NameClaims.lean`, `wal-path13`: use it, not `WalDirPathLaw`), the metadata bound (`WalsBounded`, `wal-path14`).

**W3/W5 log, sixteenth session (branch `wal-readall16`, 2026-11-14).** Task 1 (the vacuity) and task 2 (the audit) done;
tasks 3-4 not started. No `sorry` added or removed.
- *Task 1, `WalDecEnvSupply`* (`openAtIndex.lean`; ledger 2026-11-14, "the readers' errors and `errors.Is`"). `IoE` now
  holds of every `*PathError` (`∀ pe, IoE (mkOk *PathError #pe)`), not of every pointer error. `os.File.Stat.spec`'s error is
  the model's `*PathError` (`∃ pe, ii = ⟨*PathError, #pe⟩`, was `IsPointerError`; the proof already had it; its three other
  users ignore the conjunct); `ReadBridge`/`OpenFiles` take the new `hIo`. **Sanity check** `walDecEnv_eof_not`: by `io`'s
  initialization (`io.eof_of_init`, `errors.newVar`) `io.EOF` is an `*errorString`, so no `*PathError`: `IoE` the
  `*PathError`s meets `¬ IoE eof`. `openAtIndex`, `Open`, `OpenForRead`, the bboltfs/crashlog users of `Stat` build (`lake
  build`). **Not provable, and not true of Go**: `isEofOk` asks `errors.Is(e, io.EOF) = false` of every `IoE` error with no
  precondition, false for a `&PathError{Err: io.EOF}`; no pure `IoE` can single out the model's `*PathError`s (their `Err`
  is heap), and the errors reach the decoder through pure predicates only (`io.readerStream`'s `E`, `bufio.ownReader`,
  `decRdErr`, the trust-boundary axiom `io.ReadFull.wp_proof`). The fix (an Iris error predicate through `readerStream` and
  `ReadFull`'s axiom, then `isEofOk`'s I/O branch from an `errors.Is` fact on `os.errnoPathErr`) changes a trust-boundary
  axiom: **the user's decision** (ledger entry, "Proposed change").
- *Task 2, the audit of the hypotheses of the WAL `wp_proof`s that are not callee specs* (satisfiable = no contradiction
  with another premise or itself; "true" where I could judge it against Go):
  - `WalDecEnvSupply` (`openAtIndex`): was unsatisfiable; now satisfiable, not true (above).
  - `WalReadState` (`ReadAll`, not yet used): **was unsatisfiable** once a segment is pinned: `gs`'s names were constrained
    by nothing (the out record and the halves fix inodes, metadata, bytes), so renaming a pinned segment to a non-WAL name
    contradicted `WalAbsD.nameBound` through `lay.segs.drop kk = gs`. Restated: takes the program's directory half
    `osNames j (.except X) ½ hj0` with `∀ g ∈ gs, hj0.cur !! g.name = some (.file g.ino)` (`walReadTie` has both), and any
    open-WAL record `ws` (read mode records none). Its proof needs the WAL directory's files singly named.
  - `WalPinSized` (`openAtIndex`): satisfiable; true once the invariant bounds `g.om.hi` (`WalsBounded`, `wal-path15`).
  - `WalDirPathLaw` (`Open`): satisfiable (fresh fractions of a path; `walInv_dirPath` proves its like); to be replaced.
  - `WalCloseLaw` (`Close`): satisfiable; no unconstrained data (the tail record, halves, claims and tails' map agree with
    the invariant; `b = b'` makes its premise false, harmless); `wal-close16` proves it.
  - `WAL.sync.specC` (`Close`): a triple of the real `sync` (pre `TailMetaW`, success post `TailMeta`: the fdatasync closes
    the resize window, as `sync.specCut`); plausible.
  - `WAL.Close.specOpening` (`Open`): plausible (`(*os.File)(nil).Close()` returns `ErrInvalid`; `sync` skips a nil
    encoder; an early return keeps the token, the halves being ghost).
  - `WalPbIn.ZeroLaw` (`Save`): satisfiable (e.g. `hsIn _ hs := ⌜hs = hsZero⌝`); the client's instance must meet it.
  - `fmt.ErrorfErrsNot.spec` (decoder): true (`ArgWf` arguments are basic, never wrapped; the result is fresh).
  - `proto.UnmarshalWalRecordE.spec` (decoder): true of protobuf-go (its errors are not `io.EOF`); a hypothesis, the
    trust-boundary axiom unchanged.
  - `errors.IsPathErrnoNotExist.spec` (`Exist`): true (`Errno.Is(ErrNotExist)` is `e == ENOENT`).
- *Merged* `wal-close15` (`6c1d49b154`): `walDirH` holds `∃ γt, walTailsFrag {dir ↦ γt}` and `walNamesFrag none`;
  `ReadAll`'s write handle must put them in after `walTails_register`; `walPipeH` holds `fp ≠ null`.
- *Not done*: task 3 (cut positivity, the pinned-segments law, `nameBound`'s `ix < 2^64`: 15 uses in 11 modules, the
  cut's `hname` premise in `CutLay` and its callers must carry the bound from the cut's `uint64` index), task 4
  (`ReadAll.wp_proof`, the fourteenth session's plan). Build note: a seed `.lake` older than `wal-int` rebuilds
  `GooseLang.Ext.Fs.Impl`; copying `GooseLang`/`LinuxFs`/`Proof/.../storage` from a fresher worktree's build avoided it.

**W7-W12 log, nil-receiver `File.Close` (branch `wal-path15`, 2026-11-14).** **`os.File.Close.specNil`**
(`LinuxFs/Spec/os/File__CloseNil.lean`) / **`os.File.Close.wp_proofNil`** (`LinuxFs/Proof/os/File__CloseNil.lean`, no
`sorry`): `{{ isPkgInit os }} (null : Loc).Close() {{ err, RET #err; True }}` (the model's nil test, then a load of
`os.ErrInvalid`). For `WAL.Close.specOpening` (`wal-close16`) and `renameWALUnlock`'s `w.Close()`. `os`'s fact now
records `ErrInvalid`'s variable (`os.errInvalid_of_pkgInit`; `Create.lean`'s pattern on the fact updated).

**W3/W5 log, `WalsBounded` for `ReadAll` (branch `wal-path15`, 2026-11-14).** The metadata bound: `walInvBody_bounded
: walInvBody s ⊢ ⌜WalsBounded s⌝ ∗ walInvBody s` (`Inv.lean`), with `WalsBounded s := ∀ dir d, s.wal !! dir = some d →
d.metadata.length < 2 ^ 41`; `WalReadState` gives `s.wal !! dir = some d` with the body, so apply it there. The segments'
size: `wp_segs_size` (`SegSize.lean`, `Fs.wp_osMeta_size` over `segRes`s, before any step). `WalPinSized` and
`WalDirPathLaw` are deleted (use `walInv_dirPath`).

**W3/W5 log, seventeenth session (branch `wal-readall17`, 2026-11-14).** Task 1 done (the readers' errors with
their evidence; a trust-boundary axiom restated, **adopted provisionally, pending the user's review**, off
`lean`); the coordinator's two `ReadDefs` additions done; tasks 2-3 not started. No `sorry` added or removed.
- *The axiom* (`Spec/io/ReadFull.lean`; ledger "the readers' errors and `errors.Is`", §10): `io.readerStream ri S E`
  with `E : List w8 → GoInterface → IProp GF`, each `Read` returning `io.errAt E (r ++ ys) err` (`nil`, or
  `□ E (r ++ ys) err`); `io.ReadFull.spec`'s post `∃ ys, ⌜sint.Z n = |ys| ∧ |ys| ≤ |buf|⌝ ∗
  io.readFullRes E eof ueof r0 ys |buf| err ∗ ...`, `io.readFullRes` the old `readFullOk` with the reader's last
  error's evidence `□ E (r0 ++ ys) e` (Go's `ReadAtLeast`: `nil` when all came; else that error, or
  `io.ErrUnexpectedEOF` for `io.EOF` after some bytes). The pure `io.readFullOk` stays as its shadow
  (`io.readFullRes_pure`). Repaired: `bufio.ownReader` (pending error `io.errAt`), `bufio.Reader.Read`,
  `bufio.NewReader`, `FileBufReader.Read`, `NewFileBufReader`'s spec, `readInt64` (post `io.readFullRes ... ∗
  ⌜err = nil → n = ...⌝`). Main tree: no other user (its `readerStreams` is another predicate).
- *The decoder* (`DecDefs.lean`): the readers' errors `decRdE bs eof IoE r e := ⌜decRdErr bs eof IoE r e⌝ ∗
  isEofAns e eof`; `decFile`'s `FileInfo` and `ownFbr`'s stored error carry `decAns eof err`; `isEofOk` asks
  `errors.Is(_, io.EOF)` only on `nil`, `io.EOF`, `io.ErrUnexpectedEOF`. New lemmas: `readFull_ans` (a decoder
  `ReadFull`'s pure shadow and `isEofAns err eof`), `decAns_of_ans` (`DecLemmas.lean`), `isEofOk_eof`,
  `walPathErr_ans` (`ReadBridge.lean`). `decodeRecord`/`NewDecoder` re-proved (`lake build`).
- *The `os` bridge*: `os.File.Read.wp_eof`'s error arm adds `∃ e, ⌜e ≠ 0⌝ ∗ os.errnoPathErr err e`; `os.File.Stat.spec`'s
  last conjunct is now `⌜err = nil⌝ ∨ ∃ e, ⌜e ≠ 0⌝ ∗ os.errnoPathErr err e` (was "a `*PathError`"); bboltfs/crashlog
  unchanged. `walDecFile_ok`/`walDecFiles_mk` take `errors.IsPathErrnoEof.spec` (**new hypothesis**, true of Go:
  `LinuxFs/Spec/errors/IsPathErrnoEof.lean`), `¬ IoE eof`, `isPkgInit os` and `isEofAns eof eof`;
  `openAtIndex.wp_proof` takes `errors.IsPathErrnoEof.spec` (`wal_osInit`: `os`'s initialization from the WAL's).
- *`WalDecEnvSupply`*: unchanged statement, now **true of Go** (the `*PathError` clause is gone from `isEofOk`), but
  **not provable**: `errors.newVar` (Perennial's `io` fact, the part's `walpb` fact) keeps no trace of the
  allocation, so `io.EOF ≠ io.ErrUnexpectedEOF` and `errors.Is(walpb.ErrCRCMismatch, io.EOF) = false` cannot be
  derived (`notes/perennial-changes.md`, 2026-11-14, "`errors.newVar` forgets the allocation"). With that Perennial
  change (and `walpb`'s fact in `newVar` form, `etc/gen-init.py`'s `LFS_SPECIAL`), the proof is three leaf walks of
  `errors.Is.spec` (`errorWalkTree_leaf`).
- *Coordinator's additions* (`ReadDefs.lean`, for `Close.specOpening`): (1) `walReadTie dir write s j fs lfs` takes the
  directory inode `j` (was existential) and `walReadH` binds it once, last of its existentials, for both the tie and
  the pipeline (`walPipeH fp dir j 0`); (2) `walReadTie`'s first pure fact begins with `gs ≠ []` (`openAtIndex`:
  `hgne`, from `kk < |lay.segs|`); (3) and ends with `write = true → ∀ g, gs.getLast? = some g →
  (walNames hj.cur).getLast? = some g.name` (the handle's last file at the claim's last `.wal` name: `wp_idleFsync`'s
  premise; `openAtIndex`: `hlastw`, over **`walNames_segs`**: under `SegsNamed`, `WalAbsD.names` and distinct
  inodes, `walNames hj.cur = lay.segs.map name`). `Open.lean`'s `walReadH_key`/`_namesOut` and `openAtIndex`
  re-proved; all 58 build leaves of `ReadDefs`, `Proof/io/ReaderStream` and `os.File.Stat`'s spec build on `wal-int`
  `ca175563f6` (`lake build`, `556227981d`).
- *TCB*: `etc/tcb-report.py --collection etc/tcb-collections/linuxfs.txt --check` refuses without a full `lake build`
  (it checks every root's freshness); not run. The axiom keeps its name (`io.ReadFull.wp_proof`), and no linked root
  reaches the WAL proofs (the collection's roots are minibolt/crashlog/walfs), so no baseline line changes.
- *Not done*: task 2 (the invariant facts for `WalReadState`: files singly named, cut positivity, the pinned-segments
  law, `nameBound`'s `ix < 2^64`), task 3 (`ReadAll.wp_proof`). Build note: `wal-create14`'s `.lake` (GooseLang,
  LinuxFs, `Proof/*.olean` top level, `Proof/go_etcd_io/etcd/server/v3/storage`) after its build seeded this one.

**W3/W5 log, eighteenth session (branch `wal-readall18`, 2026-11-14).** Task 1 done: **`WalReadState` proved and
deleted** (`walInvBody_readState`, `ReadState.lean`, no `sorry`); task 2 (`ReadAll.wp_proof`) not started beyond the
plan below. No `sorry` added or removed.
- *The cuts' positivity*: a new field **`WalAbsD.cutPos : ∀ b ∈ lay.cuts, 0 < b`** (last, after `nonempty`; the
  positional constructions in `OpenUnl`, `TailSyncIdle`, `RzStepPure`, `TailStepPure`, `SaveAbs`, `CreateNamed`,
  `CreateCommit`, `Crash` take it through). Established by `cutLay_abs` (new premise `hpos : 0 < d.H.length`), kept by
  the crash (`CrashPure`: the cuts unchanged) and every other step (the cuts unchanged). Plumbing: **`WAL.cut.spec`
  takes `0 < h.H.length`** (ledger 2026-11-14, "the history nonempty at a cut"; `WAL.Save.wp_proof` supplies it from
  `H ++ [save]`), `CutAu`'s/`cutCommit_pure`'s `hcpos` is `walCutPos … ∧ 0 < |H|`. Not a part of `walTailsRes`
  (the fifteenth session's plumbing plan): a field reaches every layout, the crash included, with no new framed part.
- *`nameBound`'s `ix < 2^64`*: **`WalAbsD.nameBound`** now reads `∃ sq ix, g.name = walFileName sq ix ∧ ix < 2 ^ 64 ∧
  (…)`; `cutLay_abs` takes `hix : ix < 2 ^ 64`, the cut's `hbt` (`CutAu`, `cutCommit_pure`) ends with `ix < 2 ^ 64`,
  which `WAL.cut.wp_proof` has from the handle (`hmx : max enti snapi + 1 < 2^64`). `readAll_success` drops its
  `hcpos`/`hnb` premises and reads both from `WalAbsD`.
- *The pinned segments, with no invariant law* (**deviation** from the sixteenth session's "files singly named" and
  `WalPinnedSegs` designs): the program's half of the WAL directory's claim agrees with the invariant's
  (`osClaims_agree`), so it suffices that **`walReadTie` records `∃ kk, (walNames hj.cur).drop kk = gs.map name`**
  (`ReadDefs.lean`, a sealed-module change; `openAtIndex` proves it from `walNames_segs` and `gs = lay.segs.drop kk`).
  At any later step, `walNames hj.cur = lay.segs.map name` (`WalAbsD.names`, `SegsNamed`, distinct inodes), so the
  pinned names are the layout's from `kk` on; each name gives the same inode in both (`segs_drop_inos`), and the
  halves of `OsMeta` and bytes agree (`halves_agree`; `walTailsRes_none`: no change in flight), so `lay.segs.drop kk
  = gs` (`segs_drop_eq`). The claim's history cannot change while the program holds its half, which is why no
  invariant law is needed: no purge, cut or rename moves a `.wal` name of a WAL whose claim half is out.
- **`walInvBody_readState hnm hdrop hsz`** (`ReadState.lean`): `walInvBody s`, `walDirKey dir j X`, the program's
  half `osNames j (.except X) ½ hj0`, `walTailsFrag ∅` and the pinned halves give `d`, `lay` with `lay.j = j`,
  `WalAbsD C Mr d lay hj0.cur`, `TailExact`, the stream written and `lay.segs.drop kk = gs`, everything returned.
  Its premises are `walReadTie`'s facts (`hj.cur !! g.name = some (.file g.ino)`, the new `hdrop`, `g.om.size =
  g.bs.length`). `walNames_segs` moved there from `openAtIndex.lean` (which now imports `ReadState`). Statement
  difference from the deleted hypothesis: no `walOutFrag` (unused), no cut-positivity conjunct (in `WalAbsD`).
- *Merged* `wal-int` `29500dc08c` (`wal-save16`: `TailMeta`/`TailMetaW` carry `TailZ m`). **Obligation for
  `ReadAll`**: its write handle (`walOpenWF`) must establish `TailZ` of the tail's meta: a tail read from disk has it
  only after `ZeroToEnd`'s truncate (`ZeroToEnd.specAu`'s `pageEnd m.size ≤ m'.cz`, then the fdatasync), so from
  `wal-tc9`'s `ZeroToEnd` instance or a named hypothesis whose post includes it.
- *Name clashes found*: `ReadAllDecode.lastRecs` vs `TailCrash.lastRecs` (resolved as `wal-repair18`'s
  `038c1103d5` did, the identical rename to `lastSegRecs` in `TailCrash`, so the merge is clean);
  `OpenPinTake.bigSepL_take_drop` (mine renamed `rs_bigSepL_take_drop`).
- *Obligations for other units*: `Create`'s body (`wal-create15`) supplies `CreateAu`'s `habs` with the two new
  fields (`cutPos`: no cuts; `nameBound`: index 0). Any new `WalAbsD` construction adds `cutPos`.
- *Plan for `ReadAll.wp_proof`* (refines the fourteenth session's; one module per phase): (1) `ReadAllLoop`: the
  `for` loop, invariant over the decoder state `(fsᵢ, offᵢ, cᵢ)`: `(rdRest C fs₀ 0 0#32).recs = acc ++ (rdRest C
  fsᵢ offᵢ cᵢ).recs` and `foldlM raStep raInit acc = .ok st` with Go's `metadata`/`state`/`ents`/`match` holding `st`
  (and `w.enti`/`w.snapi`, written only); a record step by `rdRest_ok`, the exit by `rdRest_stop` or `decPostB`'s
  `IoE`/`GoFail` arms (the error post). (2) `ReadAllArms`: each switch arm against `raStep` (callees:
  `MustUnmarshalEntry`/`State`, `pbutil.MustUnmarshalMessage`, `bytes.Equal`, `decoder.LastCRC`/`UpdateCRC`,
  `Record.Validate`, `HardState.Reset`, the Go `append(ents[:offset], e)`). (3) `ReadAllTail`: the mode check
  (`errors.Is` with `decAns`), `Seek(LastOffset)`, `ZeroToEnd.specAu` with the invariant's supplies, the F-Z
  fdatasync, `TailZ`. (4) `ReadAllCommit`: open `walInv` at the directory sync (`walNamed`), `walInvBody_readState`
  with `walReadTie`'s facts, `walInvBody_bounded`, `readAll_success`; the AU's commit; the put-back of all but the
  tail's halves; `walTails_register`, then `walTailsFrag {dir ↦ γt}` and `walNamesFrag none` into `walDirH`;
  `newFileEncoder`; `walOpenWF`.
- Build: seeded from `wal-repair18`'s `.lake` (`GooseLang`, `LinuxFs`, `Proof/io`, `Proof/*.olean` top level,
  `Proof/go_etcd_io/etcd/server/v3/storage`), `GooseLang.Ext.Fs.Zeros` and `Proof.io.ReaderStream` rebuilt; all 32
  build leaves of `Abs`, `WAL__cut`'s spec, `ReadDefs`, `ReadState` and `TailCrash` build (`lake build`).

**W3/W5 log, nineteenth session (branch `wal-readall19`, 2026-11-14).** `ReadAll.wp_proof` still `sorry`; phase 1's
pure part and the pieces every phase needs are in (no `sorry` added; `lean-check` and `lake build`).
- *Phase 1, pure* (`ReadAllLoop.lean`): **`RdLoop C U s R0 acc fs off c st ix`**, the loop's invariant at the
  condition: `R0.recs = acc ++ (rdRest C fs off c).recs`, the same stop, `foldlM raStep raInit acc = .ok st`, and
  `(w.enti, w.snapi) = acc.foldl (raIdx U s) (0, 0)` (**`raIdx`**: an entry sets `enti`, a snapshot raises `snapi`, the
  start's raises `enti`: S/wal.go:543, :569-585). `rdLoop_start` (`R0 = rdRest C fs₀ 0 0` = `walDecodeFiles`,
  `rdRest_start`), **`rdLoop_ok`** (a `goDecode` `.ok r` the reader does not reject as a CRC record, and the arm's
  `raStep … = .ok st'`: `r ∈ R0.recs` and the invariant at the decoder's next state with `rdCrc`), **`rdLoop_stop`**
  (a `.stop s'`: `R0.recs = acc`, `R0.stop = s'`), **`rdLoop_fold_eof`** (at `.eof` with `match`: `readAllFold … = .ok
  (md, hs, ents)`, `readAll_success`'s `hok`). *No arm panics*: **`RecDec U r`** (an entry/state/snapshot record's data
  decodes under `U`); `recsOfSegs_dec` (every record of the segments' encoding, from `U.Ok Mr`), **`readFiles_dec`**
  (what the reader reads from the pinned segments, over `walReadFiles_running`). The fold's error arms
  (`sliceOutOfRange`, …) need no lemma: the error post asks only `walReadFailedF`.
- *Before the loop, no step* (`ReadAllInv.lean`): **`walInv_readFiles`** (`walInv_open` under `notCrashed`, as
  `walInv_dirPath`; `walInvBody_readState`; closed at once: `d`, `lay`, `kk` with `WalAbsD`, `TailExact`, the stream
  written, `lay.segs.drop kk = gs`, the resources back) and **`readFiles_dec'`** (with `walReadTie`'s `F.bs = segImg g`,
  the decoder's files decode: the loop's premise `∀ r ∈ R0.recs, RecDec U r`). Obtain `notCrashed` with
  `wp_notCrashed_acc` (as `Close.specOpening`'s proof). Phase 4 opens the invariant again at the directory sync (the
  AU's commit) and applies `readAll_success` to that `d`: the records are fixed by `gs`, so the two looks agree.
- **Hypotheses (missing callee specs; `ReadAllCallees.lean`, true of Go, to discharge with the client's `P` at C6)**:
  `WalPbIn.UnmarshalEntLaw P U` (`MustUnmarshalEntry` of bytes `U` decodes: `P.entIn`), `WalPbIn.GetTermLaw P`,
  **`WalHsOwn P U HsO`** (the hard state `ReadAll` owns, `HsO`: a fresh zero one, `MustUnmarshalState`, `GetCommit`,
  `Reset` (the error arms write it, so `P.hsIn`, persistent, cannot hold it during the loop), `freeze` into `P.hsIn`
  on success), `WalPbIn.CloneHsLaw P` (`proto.Clone(state).(*HardState)` → `w.state`),
  `pbutil.MustUnmarshalMessage.specWalSnap U` (into a fresh `walpb.Snapshot`: `walSnapIdTerm`),
  `walpb.Snapshot.GetTerm.spec`. The proof also takes `U` and `U.Ok Mr` (no client statement changes: the spec does
  not mention `U`). Existing specs used: `Decode`, `LastCRC`, `UpdateCRC`, `LastOffset`, `Record.GetType`/`GetCrc`/
  `Validate`, `Snapshot.GetIndex`, `GetIndexLaw`, `WAL.tail`, `fmt.ErrorfErrs`, `bytes.Equal`.
- *The wp proof* (`WAL__ReadAll.lean`): through `wp_start`, `walOpeningF`/`walReadH`/`walReadTie` destructured (as
  `Close.specOpening`'s), the defer, `w.mu.Lock()`, the locals, the decoder's nil test, and **the first
  `decoder.Decode(rec)`** (the interface call resolves to `wp_Decode` directly), then `sorry` at the `doFor`.
- *Next (phase 1-2, inline in the wp proof)*: (a) before the `doFor`, `wp_notCrashed_acc` and `walInv_readFiles`
  (the halves from `ownDecoder_streams`/`walTie_files`, as `Close.specOpening`, put back after), giving `hdec`; (b)
  `wp_for` with the invariant `∃ acc fsD off c st ix e mdv stp entsv esL, err_ptr ↦ e ∗ decPost … fsD off c e ∗
  metadata_ptr ↦ mdv ∗ (st.md: nil, or `mdv ↦* d` kept from the record's data, split off `ownRec` before the next
  `Decode`, which takes only `ownRecAny`) ∗ state_ptr ↦ stp ∗ HsO stp st.hs ∗ ents_ptr ↦ entsv ∗ entsv ↦* esL ∗ cap ∗
  walEntsIn P esL st.ents ∗ match_ptr ↦ st.matched ∗ w.enti/snapi ↦ ix ∗ ⌜RdLoop … (fsD.map bs) off c st ix⌝`; the
  `decPostB` arms: `.ok` (with `err = nil`) the body, `.stop`/`IoE`/`GoFail` the exit (`rdLoop_stop`; `IoE`/`GoFail`
  are errors for the mode check through `decAns`); (c) phase 2 per arm against `raStep` (the CRC arm: `LastCRC` is
  `c'`, `Validate` iff `r.crc = c'`, `UpdateCRC r.crc` = `rdCrc c' r`). Phase 3/4 obligations unchanged (eighteenth
  session), plus: `walHandleIn`'s index facts from `raIdx`'s fold (`walMaxSnapIdx H ≤ snapi`, `rest = 0 → walLastIdx H ≤
  max enti snapi`, `max + 1 < 2^64`) need a pure lemma over the records from `kk` (not started), and `w.state`'s
  `h.st = walLastHS H` from the fold's `hs` (`walReadAllOk`'s `σ.hs`).
- Build: seeded from `agent-a073f6c88b2244128`'s `.lake` after `agent-a2a9b3c66efdebc6a`'s was older than `wal-int`
  (`GooseLang.Ext.Fs.Impl` stale); traces unshared (the coordinator's `find … -links +1` fix).


**W3/W5 log, twentieth session (branch `wal-readall20`, 2026-11-14).** `ReadAll.wp_proof` still `sorry`, at three
places: the entry arm, the snapshot and default arms (one `sorry` after the CRC arm), and the loop's exit (phases 3-4).
- *Proved, inline in `WAL__ReadAll.lean`*: the look at the invariant before the first `Decode` (`ownDecoder_halves`
  lends the segments' halves out of the live decoder for `walInv_readFiles` and takes them back; `readFiles_ok'`
  gives `∀ r ∈ R0.recs, RecDec U r ∧ RecMd d0.metadata r`); the loop's invariant as logged (nineteenth session) with
  `mdv ↦* st.md.getD []`, `st.md = none → mdv = nil`, `∀ dd, st.md = some dd → dd = d0.metadata`, `∃ k, fsD = fs.drop
  k`; `wp_for`; at `err == nil` the stops and `GoFail` excluded (`stopErr_nil`: `io.EOF`/`io.ErrUnexpectedEOF` are not
  `nil`, `decEnv_nonnil`) and the I/O arm (`¬ IoE nil`, below); the record arm through `GetType`; **the state arm**
  (`hHs.unmarshal`), **the metadata arm** (both `metadata == nil` and `bytes.Equal`, over `raStep_md`), **the CRC arm**
  (`LastCRC`; at `c' = 0` unchecked, else `Validate`; `GetCrc`, `UpdateCRC`; `rdCrc c' r = r.crc`) **with its mismatch
  exit** (`HardState.Reset`, the error variable from `wal.walInit`, `wp_for_post`'s return, `readAll_failWp`, the
  deferred `Unlock`, the error post). Each arm ends: `wp_for_post`, `Decode` from `(fsD.drop k, off', c'')`, the
  invariant at `acc ++ [r]` by `rdLoop_next` (with `raIdx_other`/`rdCrc_other` for the arms that write neither index).
  Gotchas: `rcases` on `GoInterface` gives `ok` first; `wp_if_destruct`'s first branch substitutes an equality
  condition (`mdv = slice.nil`, `c' = W32 0`); `«rec»` must be renamed before `wp_for` (`iNamed` cannot parse it), and
  the invariant's names avoid `match`; the record variable `r` shadows the area root, so the proof names the root
  `rt`; a persistent `#` name in the invariant fails (`walEntsIn` not seen persistent there): plain `Hein`.
- *New modules and lemmas*: `ReadAllExit.lean`: `walInvBody_failOpening`/`walInv_failOpening` (the ghost handle
  `opening s` to `failed`, `walHandleP_set`), `walAu_same` (the update committed unchanged, at `⊤ \ walN`),
  **`readAll_failWp`** (both, under `wp_notCrashed_acc`, before the code returning the error), `ownFbrs_halves`/
  `ownDecoder_halves`, `decEnv_nonnil`, `decFiles_bs`, `decFiles_names`. `ReadAllLoop.lean`: `RecMd`,
  `recsOfSegs_md`, `readFiles_md` (every metadata record carries the WAL's metadata, so `metadata != nil &&
  !bytes.Equal` never fails and a nil `rec.Data` for empty metadata does not matter). `ReadAllInv.lean`:
  `readFiles_ok'`. In the proof file: `stopErr_nil`, `rdLoop_mem`, `rdLoop_next`, `raIdx_other`, `rdCrc_other`,
  `raStep_md`.
- *Statement changes (ledger 2026-11-14, "no I/O error is `nil`")*: `WalDecEnvSupply`'s pure part `(∀ pe, IoE
  (*PathError pe)) ∧ ¬ IoE nil`; `walReadH`'s `(decEnv IoE eof ueof ∗ ⌜¬ IoE nil⌝)`; `openAtIndex` repaired (two
  `isplitr`s); `Open`, `WAL__CloseOpening` unchanged (checked). Without it `decPostB`'s I/O arm at `err == nil` runs
  the loop's body on a dead decoder.
- *Obligation*: `walReadFailedF`'s body drops the program's halves, the out-record and the pipeline at a failure
  (affine); `Close` of a failed handle (W10) will need them back in `walInv` (put them into the body then).
- *Next*: (1) the snapshot arm (`var snap`, `specWalSnap`, `GetIndex`/`GetTerm`, `w.snapi`/`w.enti` per `raIdx`,
  `match`, `hHs.getCommit`, `ents[:0]` by `ownSlice_slice_with_cap`; its mismatch exit as the CRC's); the default arm
  (types outside 1-5: excluded by a `RecMd`-like fact on `recsOfSegs`, or taken as an exit with `fmt.ErrorfErrs`);
  (2) the entry arm (`ents[:0]`, the `offset > len(ents)` exit with `Errorf` and the `GetTerm`s, `append(ents[:offset],
  e)` by `ownSlice_slice_with_cap` and `wp_slice_append`, `walEntsIn` of `readEnt`); (3) the exit (`errors.Is` through
  `decAns`; the spec is write mode only, so no read-mode return), phases 3-4 as the nineteenth session lists. An error
  exit costs ~20 lines (the CRC's is the template).
- Build: seeded (the coordinator's `agent-a2a9b3c66efdebc6a` was stale: `GooseLang.Ext.Fs.Impl`) from
  `agent-a0e31bc0a52d6aa5b` (`wal-repair20`): `Proof`/`Spec` hard-linked (not rebuilt here), `GooseLang`/`LinuxFs`
  real copies (a real copy of `Proof` is 13 GB; the disk had 6 GB left).

**W3/W5 log, twenty-first session (branch `wal-readall21`, 2026-11-14).** `ReadAll.wp_proof` has one `sorry` left: the
code from `w.tail().Seek(w.decoder.LastOffset(), io.SeekStart)` on (phases 3-4), at the `io.EOF` exit. No statement
changed, no hypothesis added, no ledger entry.
- *Proved (inline in `WAL__ReadAll.lean`; `set_option maxHeartbeats 2000000 in` on the theorem: the proof passed the
  default budget with the snapshot arm)*: **the entry arm** (`MustUnmarshalEntry` by `UnmarshalEntLaw`; at or below the
  start `ents[:0]` by `ownSlice_slice_with_cap`; above it the offset `e.GetIndex() - start - 1` (`entOff_nat`), the
  **`ErrSliceOutOfRange` exit** (`fmt.Errorf` over six arguments: `walInit`'s error variable, the start's and the entry's
  index and term, `len(ents)`; local `raArgWf_uint64`/`raArgWf_int`, as `selectWALFiles`'), else `append(ents[:offset], e)`
  by `ownSlice_slice_with_cap`, `wp_slice_literal` and `wp_slice_append`, the entries' facts by `walEntsIn_take`/
  `walEntsIn_snoc`; `w.enti`; the step against `raStep`/`raIdx` through `readEnt`); **the snapshot arm** (`var snap`,
  `MustUnmarshalMessage.specWalSnap`, the `w.snapi` raise; the start's index: the term check with the
  **`ErrSnapshotMismatch` exit**, `match`, `ents[:0]` above the commit (`hHs.getCommit`), the `w.enti` raise; another
  index: nothing else); **the default arm** (`state.Reset()`, `fmt.Errorf("unexpected block type %d")` over `argWf_int64`,
  an exit: no type fact on the records needed); **the loop's exit** to the mode check: `w.tail()` (`lfs = ls ++ [lt]` from
  `gs ≠ []`, `lt ≠ null` from `lockedFile`'s points-to), `errors.Is(err, io.EOF)` through `decAns`/`isEofAns` (`io.EOF`'s
  global from `decEnv`), **the decoder's error exit** (not `io.EOF`: `Reset`, the error returned, `readAll_failWp`); at
  `io.EOF`: `decPostB`'s I/O arm excluded (`isEofOk`'s `¬ IoE eof`), its `GoFail` arm too (`goFail_badRec`, `eof ≠ ueof`),
  the record arm (`eof ≠ nil`), so the stop is `.eof` (**`stopErr_eof`**) and `rdLoop_stop` gives `R0.recs = acc`,
  `R0.stop = .eof`, the decoder live at the end (`ownDecoder … (fsD.drop k) off' c' true`), `ownRecAny`.
- *Gotchas*: the `if`s whose branches fall through (`w.snapi`, `ents[:0]`, `w.enti` in the snapshot arm) are joined with
  `wp_join R [at next] with [...] as ...` (Perennial's `Join.lean`; the reference's `wp_join`): `R` must carry `w_ptr ↦ w`
  when a branch stores into a field of `w` (the case's context is only the listed hypotheses and the persistent ones),
  the case falling through is left as the goal `R` (no `wp_join_done`), and `at next` when the condition calls a method
  (the calls are made inside the bound case). `wp_if_destruct` on `if !(a == b)` gives the `a = b` case first (the
  snapshot's term check: matched first, mismatch second). A `{ st with f := …,\n g := … }` split over lines needs the
  second field indented past the `{`. The loop's exit condition reduces with `simp only [intoVal_eq_iff,
  Bool.false_eq_true, decide_false, decide_true, ↓reduceIte]`. Persistent hypotheses cannot be listed in an `ihave … $$
  [H]` selector (prove the premise with `isplitr; iexact`). `lean-check`'s "stopped when the edited declaration was done"
  after an edit to a lemma above the proof means the proof was not rechecked: check again with `-a`.
- *Decided, not done*: `walReadFailedF` keeps its draft body (the ghost handle, `lg`, `dir`). Putting the program's file
  halves, the out-record and the pipeline in it costs at every exit: in the loop's I/O and `GoFail` arms the decoder is dead
  (`ownDecoder … false`), and `ownDecoder_halves` lends the halves out of a live decoder only, so the dead decoder needs a
  halves lemma first, then the seven exits supply them through `readAll_failWp`. W10 (`Close` of a failed handle) is the
  user of those resources: add them with it, starting from a `ownDecoder_halves` for `false`.
- *Next (phases 3-4, from the `sorry` at the `io.EOF` exit)*: (a) `decoder.LastOffset()` (`wp_LastOffset`, the end offset
  `off'` in the last file) and `Seek` on `lt.File` (`fls.getD ls.length null`, the last file's `walFileS`): the decoder
  must lend the last file's stream out and keep what `LastOffset`/`LastCRC` read (an `ownDecoder_tail` lemma: the last
  `DecFile`'s `S` out, a residue answering `LastCRC = c'` and `LastOffset = off'` for `newFileEncoder`); `os.File.Seek`'s
  spec over `os.ownOff`. (b) The tail's registration before `ZeroToEnd` (its supplies are for a registered tail,
  `walTail_truncSup`): `walTailsRes_register` asks `TailZeros lay ∧ TailBound` of the pinned layout: check what the crash
  leaves in `z0` (if `z0 = |old|` after a crash, `TailZeros` is vacuous); `ZeroToEnd.specWalTail` as a named hypothesis
  stated over `walTailW` at `o = wr` (`wal-tc12`'s design: `TailMetaW` with `TailZ` out), F-Z's fdatasync by
  `fileutil.Fdatasync`, `fileutil.Fsync(w.dirFile)` and `syncDir(filepath.Dir(dir))` with the AU's commit at the directory
  sync (`walNamed`). (c) **`match`**: `!match` returns `ErrSnapshotNotFound` *after* every side effect (the encoder is made
  first), so the proof either shows `st.matched = true` at `io.EOF` (the start's record is in a file from `kk` on: not in
  `walReadTie`, which records only the first file's index `≤ s.1`; the selection (`selectWALFiles`, `searchIndex`) knows
  the next file's index is `> s.1`, so a `walReadTie` fact of that and a pure lemma over `segsOf` would give it), or
  verifies the `¬ match` path to the end and exits by `readAll_failWp` (the registered tail then stays registered,
  affinely dropped). The first is the better spec (no `ErrSnapshotNotFound` in write mode at the newest pair). (d) Phase 4
  as the nineteenth session lists: `readAll_success` with `rdLoop_fold_eof` (`hR0r`, `hm`), `h.st = walLastHS H`, the
  index facts from `raIdx`'s fold (a pure lemma: not started), `proto.Clone` (`CloneHsLaw`, after `hHs.freeze`),
  `readClose` (nil in write mode), `w.start`, `w.metadata`, `newFileEncoder`, `walOpenWF` with `walDirH`.
- Build: seeded from `agent-a0e31bc0a52d6aa5b` (as the twentieth session); `lake build` of `WAL__ReadAll` after merging
  `wal-int` `65a8fb5429`.

**W3/W5 log, twenty-second session (branch `wal-readall22`, 2026-11-14).** `ReadAll.wp_proof` still one `sorry`, at the
same place (the `io.EOF` exit, before `w.tail().Seek(w.decoder.LastOffset(), io.SeekStart)`), now with every file's
stream in hand. No `sorry` added or removed; one spec defect fixed (ledger 2026-11-14, "the files left behind are lost").
- **Found and fixed (ledger)**: `Decode`'s post dropped the streams of the files the decoder leaves (`d.brs =
  d.brs[1:]`); at `io.EOF` the decoder holds no file at all (`goDecode`'s last-file `.eof` returns `[]`), so phase 3
  had nothing to `Seek`/`ZeroToEnd`/encode on and phase 4 no halves to put back. `decPostB`'s first arm is now `∃ k,
  ([∗list] F ∈ fs.take k, ∃ q, F.S q) ∗ match …` (`DecDefs.lean`); `decPost_cons_eof` takes the left file's stream,
  `decodeRecord`'s two end-of-file arms open the reader (`bufio.ownReader_open`) for it; `Decode`'s proof unchanged.
- *The loop*: the invariant has `kD` (`fsD = fs.drop kD`, was `∃ k`) and `"Hleft" ∷ [∗list] F ∈ fs.take kD, ∃ q,
  F.S q`, merged at each `Decode` (`leftS_merge`). `RdLoop` has `endOff`/`endCrc` (`R0.off`/`R0.crc` are the
  decoder's at the end); **`rdLoop_stop_end`**: at a stop other than a CRC mismatch, `R0.off = off'`, `R0.crc = c'`.
  At the `sorry`: `hR0o : R0.off = off'`, `hR0c : R0.crc = c'`, `Hleft` over `fs.take (kD + k)` (= `fs`: the decoder
  is over `[]`), `Hdec : ownDecoder dec … (fsD.drop k) off' c' true`.
- *`ReadAllTail.lean` (new)*: **`ownDecoder_lend`** (every file's `∃ q, F.S q` out, the residue `decResid d c`: the
  CRC field and digest) and **`decoder.LastCRC.wp_resid`** (over `crc.digest.Sum32.spec`; `ReadAll.wp_proof` takes
  the new hypothesis `wp_Sum32`, proved in the part), `leftS_merge`. With `Hleft` holding all streams, `ownDecoder_lend`
  is needed only for the residue (`LastCRC` after `ZeroToEnd`).
- *Next, in order*: (1) `wp_LastOffset` on `Hdec` (`W64 off'`); split `Hleft` at the last file (`fs = fs.dropLast ++
  [Fl]`, `hfk (gs.length - 1)`: `Fl.S = walFileS f fd (child dir g.name) (openFd g.ino 2|O_CLOEXEC) g`, `fls[_]? =
  some f`, `lockedFile lt f`), `wp_tail`, `MethodUnfold … LockedFile … Seek` as `WAL.Save`, `os.File.Seek.wp_start`
  (needs `off' ≤ 0xffffffff000`: from (2) and the segment's size bound). (2) **pure, not started**: the decoder's end
  is the write position, `(walDecodeFiles C ((lay.segs.drop kk).map segImg) 0#32).off = lay.wr` and `.crc` the chain's
  CRC (`h.crc Mr` for the encoder) — `walDecodeFiles_running`'s `.recs` statement extended to `.off`/`.crc` (its core
  lemmas `walDecodeFiles_core`/`_suffix`, main tree `WalEncSegsImg`/`WalEncSuffix`, state only `.recs`). (3) the
  registration and `ZeroToEnd`, as named hypotheses until `wal-tc14` lands (the coordinator's decision, 2026-11-14:
  `walTailsRes_register`'s per-tail premise `TailZeros lay ∨ lay.wr = lay.z0`; the window's fdatasync restores
  `TailZeros`, `tailZeros_syncW`): intended names `walInv_registerTail` (the invariant-level registration at the pin:
  `walTailKey dir γ`, `walTailsFrag {dir ↦ γ}`, the tail record's half `(H, md, cuts, wr, g.ino, none)` with `d`,
  `lay`, `kk` as `walInv_readFiles`') and `ZeroToEnd.specWalTail` (`wal-tc13`'s intended statement: pre `walAreaOk ∗
  walTailW … TailMeta` at `o0 + |out| = wr`, post `walTailW … TailMetaW` with the bytes from `wr` a zero run and
  `TailZ`; on an error the handle lost); `wal-tc14` logs the real names here. *`wal-tc17` (2026-11-14)*: the registration restated as
**`walInvRegisterPendLaw`** (`ReadAllRegPend.lean`: `walPendTok dir γ |lay.old|` for the key, `TailMetaR
gl.om gl.bs` for `TailMeta`, `TailZ0 lay ∧ |lay.old| = gl.om.size` added), not proved (findings C, D of the
W1 log's twenty-seventh session); the handle's lent tail is **`walTailP … o0 sz out k p tm`**
(`HandlePend.lean`; `ReadAll` builds it as `walTailW_ofRead` does, with the token and `TailMetaR.loWr`);
`ZeroToEnd.specWalTail`'s restatement (pre/post in that session's last item) not made; the old law and
hypothesis stay for `WAL__ReadAll` until it switches; `walInv_unlend` is removed (the key comes back at the
fdatasync, `walLentRes_unpend`, either kind). *`wal-tc16` (2026-11-14)*: the pending tail's crash step is proved (`crashOkA_tailPend`, `TailCrashPend.lean`); for `ReadAll`, the proposed `ZeroToEnd.specWalTail` takes the zero length word at `o0` over the handle's bytes (`∀ j < 8, (bs.getD (o0 + j) (0, [])).1 = 0`, in its `tm`), which `ReadAll` gets from the decoder's `io.EOF` stop at `wr` over `gl.bs`'s values; neither hypothesis is restated yet (I3b, `wal-tc16` entry; W1 log, twenty-sixth session, findings A and B). *`wal-tc15` (2026-11-14)*: the registration is **`walTailsRes_registerPend`** (`TailReg.lean`; the pending token `walPendTok dir γ |lay.old|`, `⌜TailZ0 lay⌝` out, no zero premise) and the token→key step **`walLentRes_unpend`** (`Inv.lean`, for the fdatasync after `ZeroToEnd`); the two hypotheses' proposed restatements are in the I3b log's `wal-tc15` entry (not yet made: `ZeroToEnd`'s truncate from a pending tail is blocked, W1 log, twenty-fifth session). *`wal-tc14` (2026-11-14)*: neither is written yet (keep the hypotheses). What changes for `ReadAll`: the tail is lent while `ZeroToEnd` runs (option (d): `walInv_lend`/`walInv_unlend`, `TailLend.lean`; `walLentTok dir γ k` in place of the key), so `ZeroToEnd.specWalTail`'s post will hold the token, not the key, and `ReadAll` returns it (`walInv_unlend`) at a step after the call; and the registration with `TailZeros lay ∨ lay.wr = lay.z0` will hand out a token of a "registered, not yet zeroed" tail rather than the key (W1 log, twenty-fourth session, task 2), which the fdatasync after `ZeroToEnd` turns into the key. (4) F-Z's `fileutil.Fdatasync`, F-N4's
  `Fsync(w.dirFile)`/`syncDir` (the AU's commit at the directory sync), then **`!match` (decided: verified to the end)**:
  `err = ErrSnapshotNotFound`, `proto.Clone`, `readClose`, `w.start`, `w.metadata`, `newFileEncoder` (its nil error
  overwrites `err`), `w.decoder = nil`, the final `err == nil && !match` re-set, exit by `readAll_failWp` (the registered
  tail and the new encoder dropped affinely). (5) Phase 4 as the nineteenth session lists.
- Build: seeded from `agent-a0d5232984f8fe5f2` (traces unshared, `GooseLang`/`LinuxFs` real copies); `lean-check -a`
  of `DecLemmas`, `ReadAllTail`; `--fast` of `decodeRecord`, `Decode`, `WAL__ReadAll`; `lake build` of the 53 leaves
  importing `DecDefs` (below).

## io.Copy log (branch `wal-copy1`, 2026-11-14)

**The Go path** of `Repair`'s `io.Copy(bf, f)` (`bf` an `*os.File`, `f` a `*fileutil.LockedFile`, whose method set has
`*os.File`'s promoted `WriteTo`), Go 1.27.3 (`GO_TOOLCHAIN`), linux/amd64, file:line of `$GOROOT/src`:

1. `io.Copy` (io.go:387) → `copyBuffer(dst, src, nil)` (io.go:407): `src.(WriterTo)` holds → `f.File.WriteTo(bf)`.
2. `File.WriteTo` (os/file.go:265): `checkValid("read")`, then `f.writeTo(bf)` (zero_copy_linux.go:18):
   `getPollFDAndNetwork(bf)` (:124): `bf.(syscall.Conn)` holds, `bf.SyscallConn()` (file.go:698, `newRawConn`,
   rawconn.go:45) is a `*rawConn`, which has no `PollFD`/`Network` → `nil` → unhandled → `genericWriteTo(f, bf)`
   (file.go:294) → `io.Copy(bf, fileWithoutWriteTo{File: f})`.
3. `copyBuffer`: `fileWithoutWriteTo` has no `WriteTo` (the embedded `noWriteTo`'s and `*File`'s collide at depth 1);
   `bf.(ReaderFrom)` holds → `bf.ReadFrom(src')` (file.go:175): `checkValid("write")`, `bf.readFrom(src')`
   (zero_copy_linux.go:42): `appendMode` false → `bf.copyFileRange(src')` (:89): `tryLimitedReader` (zero_copy_posix.go:26,
   `remain = 2^63-1`), the type switch's `fileWithoutWriteTo` case, `src.checkValid`, `pollCopyFileRange(&bf.pfd,
   &f.pfd, remain)` = `poll.CopyFileRange` (internal/poll/copy_file_range_unix.go:13): `supportCopyFileRange()`
   (copy_file_range_linux.go:15, kernel ≥ 5.3), rounds of `copyFileRange` (:35, fd locks, `ignoringEINTR2`,
   `unix.CopyFileRange(src, nil, dst, nil, min(remain, 0x7ffff000), 0)`) until `n == 0` or an error, each judged by
   `handleCopyFileRangeErr` (copy_file_range_linux.go:95).
4. Handled (the first round copied something): `ReadFrom` returns `(written, f.wrapErr("write", e))` (the error a
   `*os.SyscallError{"copy_file_range", errno}`). Unhandled (the first round returned 0 — an empty rest — or `ENOSYS`,
   `EXDEV`, `EINVAL`, `EIO`, `EOPNOTSUPP`, `EPERM`): `spliceToFile` (:59, unhandled: the source's `rawConn` has no
   `PollFD`) → `genericReadFrom` (file.go:204) → `io.Copy(fileWithoutReadFrom{bf}, src')` → `copyBuffer`'s loop with a
   32 KiB buffer over `File.Read`/`File.Write` (both modelled).

Measured on C (strace, `TestCopyFileRangeIoCopy`): a 9900-byte rest is `copy_file_range(4, NULL, 7, NULL, 2147479552,
0) = 9900` then `= 0`; an empty source `copy_file_range(...) = 0` then `read(8, "", 32768) = 0`. No `sendfile`/`splice`.

**What is translated, what is trusted** (`8b93163b63`): the part's `os.toml` translates `File.ReadFrom`, `File.WriteTo`,
`File.writeTo`, `genericReadFrom`/`genericWriteTo`, `noReadFrom.ReadFrom`/`noWriteTo.WriteTo` (panics),
`getPollFDAndNetwork` (its assertion to an anonymous interface translates), `isUnixOrTCP`, `tryLimitedReader`,
`File.checkValid`, `File.wrapErr`, `File.SyscallConn`, `newRawConn`, `wrapSyscallError`, `NewSyscallError`,
`SyscallError.Error`/`Unwrap`; `internal/poll.toml` translates `handleCopyFileRangeErr` and `maxCopyFileRangeRound`.
Trusted (`LinuxFs/TrustedCode/os.lean`, **pending the user's review**): `File.readFrom`, `File.copyFileRange`,
`File.spliceToFile` (Go's bodies, but they read `f.appendMode` and pass `&f.pfd`, absent from the trusted `file`
layout), `rawConn.Control/Read/Write` (panics: `pfd.RawRead`, never reached here), and the system call
`model.copyFileRangeRound` with `model.pollCopyFileRange` (poll's loop, `supportCopyFileRange()` true on C).
`goose.py --check --project bboltfs` passes; `gen-init --check` unchanged.

**Decision (provisional, coordinator's to confirm, then the user's): no new `fsExt` step.** One `copy_file_range`
round is the existing `PRead` of up to `max` bytes at the source's offset, then `PWriteStart`/`PWriteFinish` of what it
read at the destination's offset, both offsets (the trusted `file.off` cells) moved by the count written; an errno
with nothing written is returned; at the source's end 0. So `Impl.lean` is unchanged and every existing write/read
lemma (page cuts, crash candidates, announce/land, `PwCut`) applies to the copy; no world rebuild of `GooseLang`. Why
it is a superset of Linux on C (the docstring and `model_os_copy_file_range.go`): ext4 has no `remap_file_range`, so
`vfs_copy_file_range` copies by `splice_copy_file_range` → `do_splice_direct`, a page-cache read and a
`generic_perform_write` (pwrite's path); finer interleavings with writers of the source are sequences of rounds
(`PRead`'s short counts); every errno with nothing copied (`EINVAL` on overlapping ranges of one file, measured) is a
`PRead` errno. `TestCopyFileRange` on C: 12388 bytes from offset 100 to offset 50, both offsets advanced by the count,
the bytes the source's; 0 at the end; `EINVAL` with nothing changed on overlapping ranges.

**Finding** (`nonissues/go-os-readfrom-count-after-fallback.md`): after a partial copy, an `EIO`/`EINVAL`/... round
makes `ReadFrom` fall back and return only the fallback's count. `Repair` ignores the count; the triple below claims
nothing of `n`. So the logged statement's "the source's offset moved by `n`" is **dropped** (ledger: not a frozen
spec, the hypothesis's own statement).

**Not done: the triple's proof.** `io.Copy`/`copyBuffer` have no bodies (Perennial's `io.toml`: names-only), and a
part copy of `io` cannot give them (`notes/perennial-changes.md`, the `io.ReadFull` entry: a `FuncUnfold` comes only
from its package's `Assumptions`, and Perennial's `io` is in every closure). Recorded as a Perennial change
("`io.Copy`/`copyBuffer` without bodies"). So `Repair.wp_proof` keeps the hypothesis, restated:
`io.CopyFiles.spec`: for `dst = bf` (an `*os.File` with the whole file's `osMeta`/`osBytes` claim and its offset `o_d`)
and `src = f` (an `*os.File` or a struct embedding one, offset `o_s`, the source's bytes `S`), `io.Copy(dst, src)`
returns `(n, err)`; afterwards the source's bytes are `S`, the destination's are `D[:o_d] ++ S[o_s:o_s+k]` past its
old content for some `k` (with the write's crash candidates) and both offsets moved by `k`, with `k = |S| - o_s` when
`err = nil`; `n` arbitrary. What `Repair.wp_proof` should call: that hypothesis (named `io.CopyFiles.spec`), its
`err` only compared with `nil`.
Proof plan once Perennial translates `io`: the chain above, in `LinuxFs/Proof/os/` (`File__WriteTo`, `File__ReadFrom`,
`copyFileRange` over a round lemma `model.copyFileRangeRound` = `wp_PRead` + `wp_PWrite*`), and the generic loop
of `copyBuffer` (a loop over `File.Read`/`File.Write`'s specs; reached only from an empty rest, so one iteration:
`Read` returns `io.EOF`).

**W3/W5 log, twenty-third session (branch `wal-readall23`, 2026-11-14).** `ReadAll.wp_proof` still one `sorry`, now
after the tail's fdatasync (before `fileutil.Fsync(w.dirFile)`). Steps (1)-(3) of the twenty-second session's list done,
(4) begun. No spec statement changed; two named hypotheses added (the coordinator's forms), one internal definition
strengthened.
- *Pure (`ReadAllEnd.lean`, new, no `sorry`)*: **`walReadFiles_running_end`**: from the `kk`-th named segment on, the
  reader ends at `lay.wr` with CRC `chainEnd 0 (recsOfSegs … (segsOf (histM d) lay.cuts))` (= `tailCrc`, `h.crc Mr` at
  `rest = 0`), under `walReadFiles_running`'s premises. Over `walDecodeFiles_intact_last` (intact files then a last
  one: the last file's decoding at the chain's CRC), `walDecodeFrom_framesEnd` (a file holding the frames of `rs` and
  nothing accepted after them ends at `|recFrames rs|`, CRC `chainEnd c rs`) and, for a start in a cut file at CRC 0,
  `chainOk_crcHead`/`chainEnd_crcHead` (a chain starting with a CRC record does not depend on its start;
  `segsDs_cut`: every file after the first starts with a cut header). The core lemmas of the main tree were not
  touched (the part's copies stay generated). Also `walReadFiles_wr_le` (`lay.wr ≤ |g.bs|` of the last file).
- *Internal definition (no ledger: not client-visible)*: `walFileS` carries `0 ≤ fd.toInt` (`Seek` needs it; `Open`'s
  `walOpenedFile` had it and dropped it); `OpenFiles`, `ReadBridge` repaired, the 8 importer leaves rebuilt.
- *In `WAL__ReadAll.lean`*: at `io.EOF` the decoder holds no file (`goDecode_eof_nil`, `decRecStep_ne_eof`), so
  `Hleft` is every file's stream; the last file split off (`walFileS` of `gl`, `lockedFile lt fl` through
  `fls.getD`); **`LastOffset`** (`off' = lay.wr` by `walReadFiles_running_end`; `c'` the chain's CRC, kept as
  `hcrcw` for `newFileEncoder`); **`Seek`** (`os.File.Seek.wp_start`, the size bound by `Fs.wp_osMeta_size`);
  **`ZeroToEnd`** on the registered tail (`walTailW_ofRead`: the stream state, the key and the tail record as
  `walTailW … lay.wr gl.om.size []`), its error exit; **the fdatasync** (`fileutil.Fdatasync.wp_tailW`, the pending-cut
  flag lent by the opening handle, `walOpening_cutFrag`), its error exit; on success the tail exact again
  (`walTailW … TailMeta`) and `walSyncedLb dir d0.H.length`. Error exits by `readAll_failWp` (the registered tail
  dropped affinely: it stays registered, as decided for `!match`).
- *Named hypotheses (until `wal-tc14` lands; `ReadAll.wp_proof` takes them)*: **`WalFs.walInvRegisterTailLaw`**
  (`ReadAllReg.lean`): the look at the invariant before the loop **with** the registration, in place of
  `walInv_readFiles`: its facts, plus `walTailsFrag {dir ↦ γ}` (for `walTailsFrag ∅`), `walTailKey dir γ`, the
  program's half of `tailG d lay gl.ino none` (`gl` the last segment), and **`TailMeta gl.om gl.bs`** (the pinned
  last segment's `OsMeta` exact: `maps = ∅`, `lo = hi = size`, `TailZ`; an obligation of the registration's proof).
  **`fileutil.ZeroToEnd.specWalTail Mr`** (`Spec/…/wal/ReadAllTailCallees.lean`): pre `walAreaOk ∗ walTailW … o0 sz
  [] TailMeta` with `o0 ≤ sz`, `o0 = |tailStream|`; success `∃ sz' ≥ o0, walTailW … o0 sz' [] TailMetaW`; error: the
  tail lost. (The zeros from `o0` on are the invariant's, not in the triple: `walTailW` hides the bytes.) Also
  `wp_Fd : os.File.Fd.spec` (proved in the part) and the instance binders `[syscall.Assumptions]`,
  `[ioutil.Assumptions]` (`TailFdatasync`'s).
- *Gotchas*: importing `TailFdatasync` makes `decide_true` ambiguous with `BI.decide_true` under `open Iris.BI`: the
  file now says `_root_.decide_true`. `rw [h]` on the proof-mode goal rewrites the Iris context too (used for
  `fs.take (kD + k) = fs` and `fls.getD … = fl`); `subst hoffw` turns the `Seek` offset into `lay.wr`.
- *Next, in order*: (a) `fileutil.Fsync(w.dirFile)` (`Hdf`, `Hdfs : osDirFdS dfd jd .idle`; cut's `os.File.Sync.specDirS`
  is the pattern), then `syncDir(filepath.Dir(dir))` (`syncDir.lean`'s spec; the area, `Hp`) **with the AU's commit**
  there (`walNamed dir`; `walAu_same` for the error exits before it, `readAll_failWp` after only if the commit has not
  happened: split the two). (b) `match`: case on `st.matched` once both syncs succeeded: `!match` to the end through
  `readAll_failWp` (decided); `match`: phase 4 (`readAll_success` with `rdLoop_fold_eof`, `h.st = walLastHS H`, the
  `raIdx` fold lemma, `CloneHsLaw`, `readClose`, `w.start`, `w.metadata`, `newFileEncoder` at `c'` (`hcrcw`, `tailCrc`)
  over `walTailW`, `walOpenWF` with `walDirH` holding `walTailsFrag {dir ↦ γt}` and `walNamesFrag none`).
- Build: seeded from `agent-a0d5232984f8fe5f2` (its `walpb` TrustedCode/ManualProof oleans were missing: rebuilt);
  `lean-check -a` of `ReadAllEnd`, `ReadAllReg`, `ReadAllTailCallees`; `lake build` of `ReadDefs`'s 8 importer leaves;
  `lean-check --fast` then `lake build` of `WAL__ReadAll`.

**W3/W5 log, twenty-fourth session (branch `wal-readall24`, 2026-11-14).** `ReadAll.wp_proof` still one `sorry`, at the
same place (after the tail's fdatasync); the pieces for F-N4 and the commit are proved as lemmas, not yet used past the
`sorry`. No spec statement changed. **Deviation (decided here, internal):** the update commits at the look before the
loop, not at the directory sync.
- *Why the commit moved*: the success post needs `walReadAllOk (histM d) d.cut s σ` of the client's `d`, and the
  client's state equals the invariant's in history, cut and metadata (`walDurLe`) only where both are read in one
  opening. After the registration nothing the program holds pins `d.cut` (the tail record has `H`, `md`, `cuts`, `wr`,
  not `cut`/`first`; only a crash changes `cut`, but no invariant fact says so), so at the directory sync the state's
  `cut` is unknown. **`walInv_readCommit`** (`ReadAllCommit.lean`, new, no `sorry`): just before the registration, one
  opening reads the WAL (`walInvBody_readState`: `d1`, `lay1`, `kk1`, `s1.wal !! dir = some d1`), commits the AU
  unchanged (`Q dc`, `walDurLe dc d1`, the AU's premise at `dc`), takes `walPast s1` and `walLenLb w dir |dc.H|`, and lends
  a fraction of the WAL's registered name claim (**`walInvBody_nameClaim`**, as `walInvBody_dirPath`: `osNames jr (.only
  [nm]) q hn` with `InArea r dir nm`, `NameOk nm`, `hn.cur !! nm = .dir j`), with `osLogLb hn.next` and `ClaimCoh hn`.
  `readAll_success` is to be applied at `d1`/`lay1`/`kk1` (the decode is over the pinned `gs = lay1.segs.drop kk1`); the
  registration's `d0`/`lay` stay for the tail (`hoffw`, `hcrcw`, `walTailW`). Every error exit now uses
  **`readAll_failWpQ`** (the handle `failed`, `Q dc` kept): the seven `readAll_failWp` calls replaced in `WAL__ReadAll`.
- *The synced mark*: the fdatasync gives `walSyncedLb dir |d0.H|` (the tail record's `H`); **`walInv_tailH`**
  (`ReadAllSynced.lean`, new, no `sorry`): at a step, `walTailW … H …` and `walPast s1` give `|d1.H| ≤ |H|` (the tail
  record agrees with the present state, `walInvBody_tailW`/`walInvBody_tailW_same`); `walSyncedLb_le` then gives
  `walSyncedLb dir |dc.H|`.
- *The named step* (F-N4): **`walInvBody_namedBy`/`walInv_namedBy`** (`ReadAllNamed.lean`, new, no `sorry`): `Create`'s
  `walInvBody_named` with the claim's coherence in place of its name's last writer (a registered claim split at the
  generation's start logs nothing, so a last writer need not exist): a program claim fraction on `N ∋ nm`, `ClaimCoh h jr
  N`, `h.cur !! nm = .dir J`, `osCommitLb n` with `h.next ≤ n` give `setNamed` and `walNamed dir`
  (`regionCrashed_coh`; `walsOk_namedBy`/`dirKeysOk_namedBy` are `walsOk_named`/`dirKeysOk_named` over any proof that
  every crash leaves the name a directory; the old ones could become corollaries, a cleanup). Use: `syncDir(filepath.
  Dir(dir))` with `osLogLb hn.next` gives `osCommitLb hn.next`, then `walInv_namedBy` with `walPast s1`.
- *New hypotheses of `ReadAll.wp_proof`* (all proved in the part, none linked yet): `wp_FsyncDir :
  fileutil.Fsync.specDirS`, `wp_syncDir : wal.syncDir.spec`, `wp_Dir : filepath.Dir.spec` (`Dir(r/nm) = r`:
  `filepath.dirModel_name` with `cleanAbs_osPathS` of `Hp` and `cleanSeg_of_nameOk`). `Harea` now also gives `#HosI`,
  `#Hsi`.
- *Fixed*: `walTailW_ofRead` for `wal-save22`'s `LoWr` (`hm.loWr _`; `wal-tc15` made the same fix).
- *Not adapted yet to `wal-tc15`* (merged at the end of the session): `walInvRegisterTailLaw` → `walPendTok`,
  `TailMetaR`, `TailZ0 lay ∧ |lay.old| = gl.om.size`; `ZeroToEnd.specWalTail` over `walTailP` (to define in
  `Handle.lean`) with post `TailMetaZ`, and its decided premise (the 8-byte length word at `wr` zero in the tail's bytes,
  or the file ends before `wr + 8`), to supply from `walReadFiles_running_end` and the `.eof` stop (a pure lemma on
  `decRecStep`'s `.eof`: `l = 0` or EOF in the header); the fdatasync's pending form (`walLentRes_unpend` at its commit,
  `walTailW … TailMeta` out) is not written: a hypothesis until it is.
- *Next, in order*: (1) adapt to `wal-tc15` as above; (2) `Fsync(w.dirFile)` (`wp_FsyncDir df dfd dir _ R jd .idle
  hn.next`, its commit unused) and `syncDir`, error exits by `readAll_failWpQ`; on success `walInv_namedBy`,
  `walInv_tailH`; (3) `match`, `!match` to the end through `readAll_failWpQ`; (4) phase 4 (`readAll_success` at `d1`).
- Build: seeded from `agent-a0d5232984f8fe5f2`; `lean-check -a` of `ReadAllNamed`, `ReadAllCommit`, `ReadAllSynced`;
  `lake build` of `WAL__ReadAll` with the commit move, after merging `wal-int` with `wal-tc15` (unchanged hypotheses still build).

**W3/W5 log, twenty-fifth session (branch `wal-readall25`, 2026-11-14).** `ReadAll.wp_proof` still one `sorry`, now
only the success arm's `walOpenWF P Mr w dir` (every program step of `ReadAll` is proved: both directory syncs, the
`match` split, `!match` to its return, `match` to its return with every other conjunct of the success post). Steps
(2)-(4) of the twenty-fourth session's list done up to `walOpenWF`; step (1) waits on `wal-tc16` (it has not
restated either hypothesis yet: I3b, `wal-tc16` entry). No spec statement changed; one hypothesis added.
- *The syncs* (F-N4): `fileutil.Fsync(w.dirFile)` (`wp_FsyncDir df dfd dir _ R jd .idle hnw.next`, its commit
  unused) and `syncDir(filepath.Dir(w.dir))` (`readAll_dir`: `Dir(dir) = r` from `osPathS_cleanAbs'` of `Hp`,
  `InArea`, `NameOk` of the commit's name; `wp_syncDir rt R jr (own qp) qc hnw.next`), each error exit through
  `readAll_failWpQ`; on success, at one `notCrashed` access, `walInv_namedBy` (the claim `Hnw`, its `ClaimCoh`,
  `osCommitLb hnw.next`, `walPast s1`) gives `walNamed dir`, `walInv_tailH` with `walSyncedLb_le` gives
  `walSyncedLb dir |dc.H|` (`hle1.1 : dc.H = d1.H`).
- *`match`* (`cases hmt : st.matched`): **`!match`** fails the handle at once (`readAll_failWpQ`) and runs the rest on
  what the program holds: `ErrSnapshotNotFound` from `wal.walInit`, `proto.Clone` (`hHs.freeze`, `CloneHsLaw`; the
  `TypeAssert` goes through `wp_auto`), `readClose` nil (`rc = zero_val GoFunc = func.nil`), `w.start`,
  `w.metadata`, `newFileEncoder` over the tail's file and offset (`walTailW` unfolded), `w.decoder = nil`, the
  return. **`match`**: `readAll_success1` (new, pure: `readAll_success` at `d1`/`lay1`/`kk1`, the client's `dc` by
  `walDurLe`; the head segment from `hgs1`) over `rdLoop_fold_eof` gives `σ` with `walReadAllOk (dc.H.map toM)
  dc.cut s σ` and `(st.md.getD [], st.hs, st.ents) = (dc.metadata, σ.hs, σ.ents)`; the same code to the return;
  **`walInv_appendOpening`** (`ReadAllOpen.lean`, new, no `sorry`: the ghost handle `opening s` to `append`,
  split into `walOpenW` and `walPurgeW`); the slices persisted (`ownSlice_persist`); the post framed but for
  `walOpenWF`.
- *The zero length word* (`ReadAllZero.lean`, new, no `sorry`): `decStep_eof_zero`, `walDecodeFrom_eof_zero`
  (by `walDecodeFrom.induct`), `walDecodeFiles_eof_zero`, **`readAll_tailZeroWord`**: the reader of `gs` stopped
  at `.eof` at `wr` gives `∀ j < 8, (gl.bs.getD (wr + j) (0, [])).1 = 0` (`wal-tc16`'s proposed premise form). In
  `WAL__ReadAll` as `_hzw` before `walTailW_ofRead`, unused until `ZeroToEnd.specWalTail` takes it.
- *New hypothesis of `ReadAll.wp_proof`*: `wp_newFileEncoder : newFileEncoder.spec` (proved in the part).
- *`walOpenWF`'s obligations* (the one `sorry`; the goal's context has everything below but the marked ones):
  (a) **the history at the registration is the one at the commit** (`d0.H = d1.H`, `d0.metadata = d1.metadata`):
  `h.H` is the tail record's (`d0`), `h.st = st.hs = σ.hs` is read from `dc.H = d1.H` (`h.Done`), the metadata slice
  holds `dc.metadata`; `walInv_tailH` gives only `|d1.H| ≤ |d0.H|`. Proposed: commit at the registration's look
  (the restated `walInvRegisterTailLaw` also commits the AU, or a commit variant after the registration over the
  tail record, `walInvBody_tailW`'s agreement), for `wal-tc16`/the next session to choose. (b) `σ.hs = walLastHS
  (H.map toM)` (pure: every segment from `kk` on starts with the state, the fork's `saveState` at each cut).
  (c) `st.md = some _` (`recBytes mdv (some md)` needs `mdv ≠ nil`: a metadata record among those read, pure,
  `hmdn`). (d) the index bounds from `raIdx`'s fold (`walMaxSnapIdx ≤ snapi`, `walLastIdx ≤ max enti snapi`, `max +
  1 < 2^64`; pure, not started). (e) `WalHS.Split` at `o0 = wr`, `out = pend = []`, `rest = 0` (`hwrT`) and the
  encoder's CRC `c' = h.crc Mr` (`hcrcw`, `WalHS.crc_done`). (f) `walDirH`: the path `osPathS R dir q j` from
  `walInv_dirPath` (`Hk✝`, `Hnf`; at the same access as `walInv_appendOpening`), **`jd = j`** (`w.dirFile`'s
  inode: `walOpeningF` does not tie its `j` to the read tie's: obligation on `Open`, or an agreement law), and
  **`walOutFrag ⟨[gl.ino], …⟩`** from `⟨gs.map ino, …⟩`: the non-tail segments' halves (`Hleft`'s `walFileS`)
  given back to the invariant (a new law, none exists; their files and fds go to `walLockH`). (g) `walTailW … TailMetaW`
  from `TailMeta` (`Htw` unfolded at the return: re-fold), `⧗ 0`, `walPipeH fp dir j 0` (held), `walNamesFrag none`,
  `walTailsFrag {dir ↦ γt}` (held).
- *Next, in order*: (1) adopt `wal-tc16`'s restatements (`walPendTok`, `TailMetaR`, `walTailP`, `TailMetaZ`, the
  pending fdatasync), passing `_hzw`; (2) decide (a); (3) the pure lemmas (b)-(e); (4) the segments' give-back law
  and `jd = j` for (f); (5) assemble `walOpenWF` (a lemma `readAll_openWF` over the return's context).
- Build: seeded from `agent-a0d5232984f8fe5f2`; merged `wal-int` (with `wal-tc16`'s crash step and `wal-create20`'s
  `walDirH` naming parameter); `lean-check -a` of `ReadAllOpen`, `ReadAllZero`, `--fast -a` of `WAL__ReadAll`;
  `lake build` of the three.
- *Switched to `wal-tc17`'s pending registration* (after merging `wal-int` with `wal-tc17`; step (1) done):
  `wp_register : walInvRegisterPendLaw` (the token `walPendTok dir γt |lay.old|`, `TailMetaR`, `|lay.old| =
  gl.om.size`); **`walTailP_ofRead`** (`ReadAllPend.lean`, new, no `sorry`): the read tail as `walTailP … lay.wr
  gl.om.size [] gl.om.size true (TailMetaR ∧ zero word at wr)`, the zero word `hzw` from `readAll_tailZeroWord`;
  **`ZeroToEnd.specWalTail` restated** (`ReadAllTailCallees.lean`, the W1 log's twenty-seventh session form: pre
  `walTailP … o0 sz [] k true (TailMetaR ∧ ∀ j < 8, (bs.getD (o0+j) (0,[])).1 = 0)`, success `∃ sz' ≥ o0, walTailP
  … o0 sz' [] k false (TailMetaZ ∧ ∀ b x, o0 ≤ b → bs[b]? = some x → x.1 = 0)`); **`Fdatasync.specWalPend`** (new
  named hypothesis, `wal-tc18`'s pending form until it lands: pre that `walTailP … false` and `walCutFrag none`,
  success `walTailW … TailMeta ∗ walSyncedLb dir |H|`, error the tail lost) in place of `Fdatasync.wp_tailW` (and
  `wp_Fd`, now unused, dropped from `ReadAll.wp_proof`). `walInvRegisterTailLaw` deleted (`ReadAllReg.lean`).
  `lake build` of `WAL__ReadAll` and `ReadAllRegPend`.

**W3/W5 log, twenty-sixth session (branch `wal-readall26`, 2026-11-14).** `ReadAll.wp_proof` still one `sorry`,
the success arm's `walOpenWF P Mr w dir`; obligations (a), (b), (c, half), (e) and the `jd = j` half of (f)
done, three found blocked on invariant/spec facts (ledger, three entries, decisions open).
- *(a) done* (`wal-tc18`'s `walInv_readCommitReg`, merged from `wal-int`): one opening commits the update and
  registers the tail, so the commit's state is the registered record's (`d0`, `lay`, `kk`: the old `d1`/`lay1`/
  `kk1` gone, `walDurLe dc d0`). `wp_register` dropped from `ReadAll.wp_proof`'s hypotheses; `ReadAllCommit`
  no longer imported by it.
- *(b), (c), (e)* (`ReadAllWFPure.lean`, new, no `sorry`): `walReadAllOk_hs` (`σ.hs = walLastHS I`, over
  `walFoldChkFrom_hs`/`walHsStep_filter`); `readAll_md_some` (the loop's `st.md = some _`: every segment's
  header has a metadata record, `readFiles_hasMd` over `walReadFiles_running`/`recsOfSegs_drop_map`, and the
  fold keeps it, `foldlM_raStep_mdSome`); `walHS_split_read`/`walHS_crc_read` (the encoder at the tail's end,
  nothing pending). In `WAL__ReadAll` before the `sorry` (`hσhs`, `hmdr`).
- *(f), `jd = j`* (decided): `walOpeningF` now records the WAL's directory key for `w.dirFile`'s inode
  (`∃ df dfd j X, … ∗ osDirFdS dfd j .idle ∗ walDirKey dir j X`; `Open`'s proof frames its `Hkey`), and
  `walDirKey_agree` (`ReadAllWF.lean`, new) gives `jd = j` against the tie's key (done in `WAL__ReadAll`).
- *Blocked, found this session* (ledger 2026-11-14, three entries, the coordinator's call):
  (c') **an empty metadata read back may be `nil`** for all `ownRec` says (protobuf-go gives `[]byte{}`;
  `UnmarshalPb`'s exactness is dropped by `UnmarshalWalRecord`), so `walHandleIn`'s `recBytes mds (some md)`
  fails at `md = []`: (A) carry `Data`'s presence through the decoder, or (B) `Create` takes `md ≠ []` and
  `WalsBounded` keeps `0 < |metadata|`. (d') **`max(enti, snapi) + 1 < 2 ^ 64`**: no invariant fact bounds the
  read-back indices (proposed: `¬ walHasMaxIdx (histM d)` per WAL, from `Save`/`SaveSnapshot`'s premises).
  (f') **`walDirH`'s `sq < 2 ^ 63 + k`**: nothing bounds the tail's sequence across generations.
- *Still to do, not blocked*: (d) the index bounds below the indices (`walMaxSnapIdx ≤ snapi`, `walLastIdx ≤
  max enti snapi`: `nameBound` for the segments before the first read, the matched snapshot's `s.1 ≤ snapi`,
  `raIdx`'s fold over the rest); (f) the give-back law (`walOutFrag ⟨gs.map ino, …⟩` to `⟨[gl.ino], …⟩` with
  the non-tail halves, a `walParked_putSegsRes` over a nonempty `F` whose tail inode is not put back), the
  path (`walInv_dirPath`), `DirKeysOk`'s `walTmps ⊆ X`/no `.wal` in `X` and the largest-name fact (one
  invariant look, say at `walInv_appendOpening`'s access), `|md| < 2 ^ 41` (`walInvBody_bounded` with the tail
  record's agreement); (g) `walTailW … TailMetaW` re-fold (`TailMeta.win`), `⧗ 0`, the locks' `walLockH`
  from `Hleft`'s `walFileS` and `Hlocks`; then `readAll_openWF`.
- Build: reseeded from `agent-ae44fb06ed0e80c7d` (one source file off `wal-int`; the given seed was 124
  off); `lean-check -a` of `ReadAllWFPure`, `ReadAllWF`; `lake build` of `WAL__ReadAll` and `Open`.
- *`wal-tc19` (2026-11-14)*: `ZeroToEnd.specWalTail` is proved (`ZeroToEnd.wp_specWalTail`, `ZteWalTail.lean`); its
  pre gained `isPkgInit errors` (the call in `WAL__ReadAll` frames it, `iPkgInit`), its post `sz' = sz`, and
  `TailMetaZ` is now `|bs| = size ∧ maps = ∅ ∧ pageEnd size ≤ max size cz` (`Fdatasync.specWalPend`'s pre reads it;
  still a hypothesis, I3b `wal-tc19` entry).
- *`wal-tc20` (2026-11-14)*: `Fdatasync.specWalPend` is proved, its statement unchanged
  (`go_etcd_io.etcd.client.pkg.v3.fileutil.Fdatasync.wp_specWalPend (wp_Fd : os.File.Fd.spec) (Mr) :
  Fdatasync.specWalPend Mr`, `FdatasyncPend.lean`): pre `walAreaOk ∗ walTailP … o0 sz [] k false (TailMetaZ ∧ ∀ b
  x, o0 ≤ b → bs[b]? = some x → x.1 = 0) ∗ walCutFrag none`, `o0 = |tailStream Mr H md cuts|`; post `walCutFrag
  none ∗ ((⌜e = 0⌝ ∗ walTailW … o0 sz [] ∗ walSyncedLb dir |H|) ∨ ⌜e ≠ 0⌝)`. `ReadAll.wp_proof` keeps its
  `wp_FdatasyncP` hypothesis; the WAL `Link.lean` passes `Fdatasync.wp_specWalPend wp_Fd Mr` (as
  `ZeroToEnd.wp_specWalTail` for `wp_zte`). No obligation on `ReadAll`.

**W3/W5 log, twenty-seventh session (branch `wal-readall27`, 2026-11-14).** `ReadAll.wp_proof`'s `walOpenWF` is
assembled; one `sorry` left, the tail's sequence bound (`hsq : ∃ sq ix, gl.name = walFileName sq ix ∧ sq < 2 ^ 63 +
0`, task 3, designed, not made). The three ledger entries of the twenty-sixth session are decided (ledger).
- *Task 1, an empty metadata read back `nil`: Fix B* (ledger, decided). The coordinator's first choice (relax
  `walHandleIn` to a `nil` slice at `md = []`) is unsound: `cut` encodes `Record{Data: w.metadata}` as is and
  `record.proto`'s `data` is a proto2 `optional bytes`, so a `nil` slice writes the record without the field (`recEnc`'s
  `optBytesField`, measured by `TestRecordEncoder`), not the model's `walRecEnc (recOf …)` (present, empty), which the
  segments' byte model fixes. Made: **`Create.spec` takes `md ≠ []`** (client premise; `hmdne` threaded through
  `createU_none`, `createFresh_osAUnc`, `walCreate_osAUnc`); **`WalsBounded`** now `|metadata| < 2^41 ∧ metadata ≠ [] ∧
  ¬ walHasMaxIdx (histM d)` (`Inv.lean`; lemmas `walsBounded_ins`/`_insSame` (history kept)/`_upd` (history kept)/
  **`_app`** (an appended operation without a maximal index), `walHasMaxIdx_append`); `ReadAll` gets the slice non-nil
  from `ownSlice_len` of its `↦*□` (`hmdvn`).
- *Task 2, the index bound* (ledger, decided): the `¬ walHasMaxIdx` conjunct is kept by **`walInvBody_append`/
  `walTail_append`/`walHandleIn_append`'s new premise `hox : ¬ walHasMaxIdx [o.toM]`**, which `Save` gives from its
  index premise (`saveOp_noMax`) and `SaveSnapshot` from its (`snapOp_noMax`, `HandleAppend.lean`). **`readAll_idx`**
  (`ReadAllIdx.lean`, new, pure, no `sorry`): from the loop's `RdLoop` (`hL.fold`, `hL.idx`), the matched start
  (`raStep_matched`), the first read segment's name (`hghd`, `WalAbsD.nameBound`): `walLastIdx (histM d0) ≤ max enti
  snapi`, `walMaxSnapIdx ≤ snapi` (obligation (d)), and with `¬ walHasMaxIdx`, `max enti snapi + 1 < 2^64`
  (`readAll_idxD` over `segsDs`: `raIdxT_snap_le`, `entG_le`, `entG_start`, `segsDs_entG`, `snap_mem_segsDs`,
  `segsDs_mem`, `raIdxT_lt`).
- *(f), the give-back and the directory share*: **`walInvBody_readGive`/`walInv_readGive`** (`ReadAllGive.lean`, new, no
  `sorry`): at one look, the non-tail segments' program halves back to the parked state (`walParked_putSegsRes`; nothing
  in flight: `walTailsRes_only` with the holder's `{dir ↦ γt}` and the tail record's `none` give `F = ∅`), the WAL's
  `WalsBounded` facts (the WAL the tail record's), the key's `∀ b ∈ X, walNameP b = false` (`DirKeysOk`);
  `walNames_last_max` (the tail's name the largest `.wal` name). **`readAll_splitLeft`/`filter_out_take`**
  (`ReadAllLocks.lean`, new): the read files before the tail split into segment halves and `walLockH`s; the out record
  becomes `[gl.ino]`. **`walTmps ⊆ X`**: the read tie (`walReadTie`'s write-mode conjunct) now records it; `openAtIndex`
  proves it before the pipeline takes the names (**`walTmpsRes_mem_except`**, over `osNames_disj`); `WAL.CloseOpening`
  repaired (`.1`). The path from `walInv_dirPath`, at the same access as `walInv_appendOpening`.
- *(g)*: `walTailW … TailMetaW` re-folded from `TailMeta.win`; `⧗ 0` (`receipt_zero`); `sz' = |gl|`'s size (`wal-tc19`'s
  `sz' = sz`) below `0xffffffff000`; the encoder's CRC by `walHS_crc_read`; the handle `WalHS.mk d0.H d0.metadata
  lay.cuts gl.ino lay.wr [] [] 0 st.hs γt sz' enti snapi 0`.
- *Task 3, the tail's sequence bound: designed, not made* (`notes/bounds-plan.md`, "The WAL's segment sequence"). The
  coordinator's sketch (a boot premise `sq < 2^63` on `walInv_alloc`, cuts consuming exclusive receipts) does not close
  across generations: a handle's `⧗` vanish at a crash, and the next boot's premise is not implied. The design: the
  global step counter's persistent receipts (`⧖`, crash-stable), `WalAbsD.nameBound` strengthened to sequence `first +
  k` (so the tail's is `|lay.cuts|`), and the invariant holding `⧖ |lay.cuts|` per WAL, deposited by `cut` after one
  `wp_go_step_preceipt` before its rename. An alternative with an easier crash step: `⧖ |d.H|` per WAL (a crash keeps a
  prefix of the history: `preceipt_mono`), `|cuts| ≤ |H| + 1`, deposited at `Save`'s commit, which then needs a counted
  step at its commit and the handle a copy of `⧖ |H|`. Either touches `WalAbsD` or `walHandleIn`/`Save` (100-230
  modules) and the crash path: not attempted this session.
- *Other*: `ReadAllEnd.segsDs_cut` clashed with `CutHdrStream`'s once `ReadAllGive` imported the cut chain; the import
  was dropped instead (`walTailsRes_lookupR`, `mem_walNamesR`: local copies), and `wal-int` made it private.
- *Statement changes*: `Create.spec` (`md ≠ []`); `walInvBody_append`/`walTail_append`/`walHandleIn_append` (`hox`);
  `WalsBounded`; `walReadTie`. No new hypothesis of `ReadAll.wp_proof`.
- Build: reseeded from `agent-a0a10b6d72cb7d34b` (3 source files off; the given seed was 133 off); `lake build` of the 32
  leaves of the changed files (all built), `WAL__ReadAll`; merged `wal-int` (with `wal-tc20`, the WAL `Link.lean`).
