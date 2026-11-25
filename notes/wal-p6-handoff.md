# P6 (etcd_safe #52/#50), phase B: re-prove the WAL over the torn-Save fix — handoff

## START HERE

- **Date**: 2026-11-24. **Branch** `etcd-safe-walfix-p6`, worktree `/shared/etcd-grove-p6`.
- **Done before this session**: the fork fix (`goose-lean-fmt1c-tornsave` @ `2bd3048d7`), the retranslation
  (`Code/.../storage/wal.lean`, `etcdserver.lean`), `examples/` go.mod, `etc/goose.py --check` green.
- **This session**: see "Progress" below (kept current at each milestone).
- **State (2026-11-25, session 5, end)**: `wal.Link` builds (real `lake build`, d6aa9cce3a); `#print axioms`
  of its 254 results = the `wal-fsext.txt` baseline, no `sorry` (`etc/tcb-report.py --check` needs a full
  worktree build: not run). E4's `Repair` done ("Repair with a pending run" below); `WAL__Save` fixed (the
  normalized op `wop`/`saveHS`, `stNil` in the entries loop's invariant). **Next: the WalTester consumers of
  `CloneStLaw` (`Adequacy.lean`: `walRaftP_cloneSt`, regenerate its Link with `etc/gen-link.py --durable`);
  `Unsaved`/`DiscardUnsaved` (new Go functions, unsaved.go, no spec yet: spec first); E5.**
- **Build**: every lake command takes `--packages=/shared/tmp/manifest-fce59af7.json`; builds through
  `/shared/tmp/build-slot.sh`; `export TMPDIR=/shared/tmp`.

## The design (decided in this session; the coordinator's E0-E5 plan)

The fork's Go behavior is `notes/etcd-dist-d6.md` §10. The Lean shape:

1. **Records of a `Save` (E0/E1).** `opDs (.save h es)` = the entry records, then the state record of
   `h` unless `es = [] ∧ hsEmptyP h` (was: unless `hsEmptyP h`). This is what Go writes only when the
   op is *normalized*: `Save(empty, es≠[])` writes `w.state`, the last saved state (`walLastHS` of the
   history before it). `WalNorm.lean`: `normOp p`, `normFrom p`, `normH` rewrite such a `Save` to
   `.save (walLastHS prefix) es`; every reader-side function is invariant (`walRead_normH`,
   `walReadCut_normH`, `walValidSnaps_normH`, `walCutPos_normH`, `walLastIdx_normH`,
   `walFoldChkFrom_normFrom`, ...). The encoding layer's history `histM d` (`wal/Abs.lean`) becomes
   `normH (d.H.map WalOpG.toM)`, so the per-op encoding (`opDs`, `segsDs`, `recsOfSegs`) is untouched in
   shape. `Save`'s append: `normH_snoc` (`histM` grows by `normOp (walLastHS H) o`). The specs of `Save`
   and `ReadAll` (over `d.H`) do not change.
2. **Crash images (E2).** The decoded records of a crash image are no longer the records of a history:
   they are `recsOfSegs` of the segments of `(histM d).take j` *followed by a run of entry records* (a
   prefix of operation `j`'s entries: a torn `Save`, now always followed by a state record that was
   lost). `histCut` (which produced `.save hsZero (es.take k)`) is replaced by "whole ops + trailing
   entry records". The ghost image chosen by the proved crash law is `I = H.take j` (`walImgS`: our own
   definition; `walImgS → walImg`, the trusted `walImg`/`walCrash` vocabulary of
   `GooseLang/Ext/AbsDisk/Impl.lean` untouched). The invariant must then allow, in the last segment, a
   run of entry-record frames after the history's frames (from `lay.z0`): `WalAbsD.tailStop` and
   `CrashTo`'s last clause become "from `z0` the decoder accepts a run of entry records, then stops"
   (`PendStop`), until a write-mode `ReadAll` zeroes from `pendOff = z0` (the old `ZeroToEnd` from
   `LastOffset`, same position).
3. **`ReadAll` (E3).** The Go loop's `pending` buffer: the result is the old fold (`readAllFold`) over
   the decoded records with the trailing run of entry records removed; on the records of a normalized
   history followed by pending entries, that is the old fold over the history's records (a normalized
   history's records never end with an entry record: every `Save` with entries ends with its state
   record). Write mode: the seek offset is `pendOff` (= `z0` when pending is nonempty, else
   `LastOffset`) and the encoder's CRC `pendCRC` (the chain's CRC after the history's records).
4. **E4**: `Repair` keeps the pending frames (it truncates after the last valid record);
   `ValidSnapshotEntries`/`OpenForRead` read past them; `Unsaved`/`DiscardUnsaved` new specs.
5. **E5**: the tester (`WalTester/`) keeps working with `walImgS → walImg`; dropping the torn images
   from Go `walImgs` is a strengthening, optional. `bootstrap.lean` / `MemberGen.lean` as the plan.

## E2 settled (2026-11-24): the crash image with pending entry frames

Checked against the fork's Go (`notes/etcd-dist-d6.md` §10, item 2: write mode zeroes from `pendOff`,
the offset before the first dropped record). No trusted text, no Go change; the shape:

1. **Producer** (`TailCrash.lean`'s `crashTo_tailL`): `tail_decode` gives the decoded `R.take j`, `R` the
   last segment's records `hdr ++ flatMap opDs (lastOps d)`. Split it by `flatMap_histCut`: whole ops
   `histCut Mr (lastOps d) n` and the entry records `histCutRest` (`histCutRest_entry`). The ghost image
   is **`I = d.H.take (segStart + (histCut …).length)`** (not `tailImg`'s `… ++ (histCut …).map toRaw`:
   the normalized ops are not `d.H`'s); `histN_take` gives `histM {d with H := I} = (histM d).take _`,
   and `walImgS_histCut` (compiled) the `walImgS`/`walImg` with `j ≥ d.m`.
2. **`CrashTo`'s last clause and `WalAbsD.tailStop` become `PendStop`**: from `S.length` (`S` the
   image's last-segment stream) the reader accepts the frames of `chainRecs (chainEnd …) ps` for some
   entry-only `ps`, then rejects. `ps = []` is the old clause. Consumers (`CrashPure`, the `ReadAll`
   decode, `Repair`, `ValidSnapshotEntries`) read `ps` as the trailing run that `readAllFoldP_append`
   drops.
3. **`TailPend` (registered tail, not yet zeroed; `TailCrashPend.lean`) and `LenZ`**: with pending frames
   the decoder's zero length word is at the end `e` of the pending run, not at `wr = z0`: `LenZ` moves to
   `e` and `TailPend` says `old` holds the pending frames on `[z0, e)`. A crash in that window, or in
   `ZeroToEnd`'s zeroing (the "zeroing crash"), now needs **W1** (today's `crashTo_tailP` needs none):
   a frame accepted at a pending position is, as of the sync, the pending frame (stamp-0 `old`), or, as
   of the zeroing change, all zeros, whose zero length word the reader rejects. So the accepted frames
   are a prefix of the pending run: `PendStop` again (`ps` a prefix). `W1G` is already a premise of
   `CrashOk`.
4. Appends happen only after a write-mode `ReadAll` zeroed from `pendOff = z0`, so `TailCands`/F-Z
   (`TailZeros` from `z0`) are unchanged for an appending generation.

## Progress

- E0: `Proof/go_etcd_io/etcd/server/v3/storage/WalNorm.lean` (normalization and its invariance lemmas).
- E0/E1 (written, **not yet compiled**; commits `ca99231ff5`, `f9e6cee809` and the stop commit):
  `opDs` (state record after the entries unless `es = [] ∧ hsEmptyP`), `histM d := histN d.H`, the
  scripted `segsOf (histN ·)` rewrite in the handle files, `SaveRecs`/`SaveAbs`/`SavePure`/`HandleAppend`
  over `wop`, `WalEncFold` with the normalization hypotheses (`hNo`; callers in `ReadAllOk` etc. not
  yet updated), `histCut` whole ops + `histCutRest` (`WalEncRecs`, `WalEncSegsImg`, `WalEncSuffix`,
  `ReadAllDecode`), `encodeState.spec`/`specNoErr` and their proofs, `saveState` as a wrapper,
  `walCov_encodeState` (`CalleeCov`). `WAL__Save.lean` not yet changed for the new branch (plan:
  `hs2 := saveHS (walLastHS (h.H.map toM)) hs es`; `hk`/`HI`'s room over `encState hs2`; `hroom1` and
  the `generalize` over `wop h.H`; `finEmpty` takes `⟨rfl, hse⟩`; a `wp_join (Q := executeVal ∗ handle
  at SaveFin ∨ returnVal ∗ err)` `at next` over `if len(ents) > 0 {…encodeState…} else {saveState}`,
  the inner `if IsEmptyHardState(st) { st = w.state }` joined at `∃ hp2, st ↦ hp2 ∗ P.hsIn hp2 hs2`,
  `w.state` from `walHandleIn_state` with `hc.st = walLastHS` by `Hs.st.trans hD.2`).
- E3 started: `Proof/.../storage/WalEncFoldPend.lean` (`raStepP`, `readAllFoldP`, `foldlM_raStepP_eq`,
  `readAllFoldP_append`: over records ending in a non-entry record followed by decodable entry records
  the new read is the old `readAllFold` of the former). Not compiled.

## Session 3 (2026-11-25): E2 done, E3's pure layer

What is proved now (all compile; `wal.Link` build log `/shared/tmp/p6-build4.log`):
- **E2.** `CrashPure`, `CrashStart`, `CutSynced`, `CutLay`, `SaveAbs`, `TailCrash`, `TailCrashW`,
  `TailCrashPend` (its `TailPend` crash is the `es = []` case: `pendStop_nil`), `TailSyncLayP`/`TailSyncWin`,
  `CreateAu`, `CreateHandle`, `CutHdrStream`, `CutAu`, `Append`, `HandleAppend`, `ReleaseTie`.
- **W1 for a pending run** (`TailCrashRep.lean`): `pendStop_transfer` (pure): a pending run of `old` from
  `off` carries over to a crash image that agrees with `old` on the core of every frame its reader accepts
  from `off` (W1) and whose bytes from `off` are `old`'s or zero (the padding: `frame`'s pad is zeros);
  the image's reader accepts a prefix of the run, then stops. `crashTo_tailR` (a repaired tail, `RepOld`)
  uses it: the accepted frame at any `p ≥ wr` is as of the sync (`old`'s) or stamped by a write, which
  `WinCands` excludes past `wr`. `crashTo_tailR`'s `himg` gained the "bytes from `wr` on are `old`'s or
  zero" conjunct (from `crashImg_tail` and `WinCands`, in `crashOkA_tailRep`). Helpers `acceptsFrom_ge`,
  `decStep_core_le`.
- **E3's pure layer.** `walReadFiles_running` (`ReadAllFiles`) and `walReadFiles_running_end`
  (`ReadAllEnd`, now one statement with the records, the end offset `wr + |pending frames|` and the CRC
  `crcAfter … (pendDs es)`), `walDecodeFiles_running_end` and `filesOk_running` (`FilesAtRun`) over a
  trailing run `Y`; `walRepairFile` (`RepairDecode`: the repaired file's records are the last segment's
  then the pending run; its frames end at `wr + |pending frames|`). `readAllFoldP_wal`
  (`WalEncFoldPend`): the new fold (`readAllFoldP`, with `pending`) on the WAL's records from any
  position then a pending run is the old fold on the former (`NoEntLast`, `EntsEnc`). `readAll_success`
  (`ReadAllPure`) now takes the `readAllFoldP` fold. `ReadAllOk` with `hNo`. `ReadAllLoop`'s
  `readFiles_dec`/`readFiles_md`, `ReadAllWFPure`'s `readFiles_hasMd` over the pending run.
- **`VsePure`** (`validSnapshotEntries`): `vseHs_opDs`/`vseHs_ops`/`vseHs_segsDs`/`vseOut_segs` take the
  normalization hypothesis (false otherwise: an op `.save hsZero es` with `es ≠ []` writes a state record
  in the encoding but not in `lhsStep`); `vseOut_pend`: trailing entry records change nothing.
- **Normalization invariance** (`WalNormDisk`): `walReleasePos_normH`, `walOpenPos_normH`,
  `walGuardPos_normH`, `walNameBound_normH`, `walRelGuard_normH`, `walLastSnapPos_normH`.

Left (failing in `wal.Link`'s build, or not yet reached):
1. **`WAL__ReadAll.lean`** (1,901 lines, E3 proper): the retranslated loop has `pending`, `pendOff`,
   `pendCRC` (Code `wal.lean:4927-5740`). The loop invariant `RdLoop` (`ReadAllLoop.lean`) folds `raStep`;
   it must fold `raStepP` (`WalEncFoldPend`) and carry `pendOff`/`pendCRC` (the offset/CRC before the first
   pending record). At the end: success via `readAll_success` (already over `readAllFoldP`); write mode
   seeks to `pendOff` (`= wr` by `walReadFiles_running_end`'s `es ≠ [] → z0 = |S|` and `RepOld`/`TailExact`;
   `LastOffset()` when `pending` is empty) and `ZeroToEnd` from there, and `hzw` (the zero length word) is
   at the decoder's end `wr + |pend|`, not at `pendOff`.
   **Design for `pendOff = wr` (2026-11-25, not started).** Backward reasoning from the end does not
   work (two start offsets can decode `k` records to the same end; decoded frame lengths need not be
   `|recFrames|`: decoding is not canonical). Forward instead: a relation `Reach C s s' n` (`n` accepted
   `goDecode` steps, the CRC through `rdCrc`, no rejected CRC record), deterministic. The loop invariant
   keeps `lastOff, lastCRC = off, c` (Go's `lastOff`/`lastCRC` at the loop head are the decoder's state),
   `Reach (fs₀,0,0) (fs,off,c) |acc|`, and, when `pending ≠ []`, a ghost `fsP` with
   `Reach (fs₀,0,0) (fsP,pendOff,pendCRC) (|acc| - |pending|)`, the last `|pending|` records of `acc`
   entry records decoding to `pending` and the record before them not one. At the end `|acc| - |pending|`
   is the number of the history's records (`readAllFoldP_wal`'s split: the history ends in a non-entry
   record, the pending run is entries), and a new lemma builds `Reach (fs₀,0,0) ([last], wr, tailCrc)`
   over that many records forward from the files' layout (`walDecodeFrom` over known frames, plus the
   step into the next file at a file's end); determinism gives `pendOff = wr`, `pendCRC` the chain's.
   `ReadAllIdx`: `w.enti` is set per applied (flushed) entry, so `raIdx` folds over the applied records.
2. **`TailPend` with a pending run** (`Abs.lean`, `TailCrashPend.lean`): a tail `ReadAll` registers before
   `ZeroToEnd` has `old` = the pending frames on `[z0, e)` and `LenZ` at `e`; its crash needs
   `pendStop_transfer` (the bytes from `z0` are `old`'s or a resize's zero: `WinShape`, writes excluded);
   `walTailsRes_registerPend` and `crashOkA_tailPend` change with it.
3. **E4 `RepairReg.lean`**: `walRepairFile` now gives `∃ rs es` with the frames ending at
   `wr + |pending frames|`; the registration states the tail at the decoder's stop (`(recFrames rs).length`,
   which was `lay'.wr`). Design: `Repair` truncates at `e ≥ wr` and keeps the pending frames; the
   registered layout's `wr`/`z0` stay at the history's stream end, the tail record's offset is `e` (the
   specs `os.File.Truncate.specRepTail`/`fileutil.Fsync.specRepTail` take the stream's length: they need
   the offset `e` with `old`'s bytes on `[wr, e)`). Not started.
4. Failing in the last `wal.Link` build besides `RepairReg`: `ReadAllIdx` (the `raIdx` fold of `w.enti`:
   with `pending`, `enti` counts only applied entries; goes with item 1), `StreamBound.saveStream_le`
   (done 2026-11-25: its bound is on `saveHS (walLastHS …) hs es`, the state written; no users yet), `SavePure.lean:252` (a syntax error in `SaveSt.finState`'s
   record), `WAL__cut.lean:484` (`iframe` of `walStIn … h1.stNil`). Items 1-3 and these are what the
   next session starts on. The spec appliers of `proto.MarshalPb.spec` (`pbutil.MustMarshalMessage*`,
   `encoder__encode`, `RaftModel/*`) build after the non-nil change.
5. Then the `encodeState`/`Save`/`LawsHs*` proofs (edited, unchecked), `ReadAll` provenance and
   `CloneStLaw`, `ValidSnapshotEntries`/`OpenForRead`, `Unsaved`/`DiscardUnsaved`, E5.

## Session 4 (2026-11-25): E3's `ReadAll` loop

- `ReadAllPure.lean`: `walFoldChkFrom_normFrom`, `walReadAt_normH`, `walReadAllOk_normH`/`_histN`
  (`readAll_success1` over `histN`).
- `ReadAllLoopP.lean`: `rdLoopP_flushStep` (one pending entry applied: the folds over `accA ++ accP.take
  (i+1)`), `rdLoopP_flushStart`, `rdLoopP_pend_len`, `rdLoopP_foldP_eof` (success fold `readAllFoldP`
  via `readAllFoldP_append`).
- `ReadAllWFPure.readAll_md_some` takes `recs = acc ++ accP` with `accP` entry records.
- `WAL__ReadAll.lean`: the loop invariant `HI` is `RdLoopP` with `pending`/`pendOff`/`pendCRC`/`lastOff`/
  `lastCRC`; the entry arm appends to `pending` (`rdLoopP_ent`, `pendOff`/`pendCRC` set when `pending` was
  empty); the other arms flush `pending` (an inline `wp_for` over `slice.forRange`, invariant `HF`: the
  index, `ents`, `w.enti`, the folds over `accA ++ accP.take jf`; its body is the old entry arm, the
  `ErrSliceOutOfRange`/reopen returns needing a second `wp_for_post` for the outer loop), then
  `pending = pending[:0]`, `st1`/`ix1` (the flushed state, rewritten into the context), the switch arms on
  `rdLoopP_rec`, `LastOffset`/`LastCRC` after the switch. The write-mode exit: `rdLoopP_eof_wal` gives the
  pending run `es`; `hoffE`/`hcrcE`: `endOff`/`endCRC` (`if pend = [] then LastOffset/LastCRC else
  pendOff/pendCRC`) are `lay.wr` and the chain's CRC in both cases (forward determinism, `DecReach`); the
  two `if len(pending) > 0` joins by `wp_wand`.
- **Item 2 is now the blocker of the write-mode exit**: `walTailP_ofRead` takes the zero length word at
  `wr` (`hzw`), proved only when `pend = []`; with a pending run the bytes at `wr` are its frames
  (`ZeroToEnd` then zeroes them). `hzw`'s `pend ≠ []` case is a `fail` marker in the proof.
- **`w.state`'s provenance** (`iframe … P.hsIn p' st.hs` at the handle, the `walStIn` slot): the
  `CloneStLaw` plan above (Session 3's "Where `walStIn` comes from").

### Item 2 design (session 4, started)

The lent tail (kind `false`) a `ReadAll` with a pending run hands to `ZeroToEnd` has no zero length word at
`wr` (`LenZ` fails: the pending frames are there), so `TailPend` (= `wr = z0 ∧ LenZ`) cannot hold. What the
crash argument needs instead is what a repaired tail already has: `RepOld` (`wr = z0`, the stamp-0
candidates from `wr` on are `old`'s, the segment no longer than `old`), with `crashTo_tailR`/
`crashOkA_tailRep` (W1 + `pendStop_transfer`: every crash image's reader accepts a prefix of the pending
run, then stops). Plan: **`TailPend` becomes `RepOld`** (the registered tail has it: `TailLast.repOld`; the
registered kind-`true` tails already carry `TailZeros ∨ RepOld`), and the `LenZ` uses are replaced:
`crashOkA_tailPend` by `crashOkA_tailRep`, `rzStart_pureP` by `rzStart_pureR` (+ `repOld_rzCands`), the
landing by `repOld_rzLand`, `tailPend_tailLay` (which used that `TailPend` reads only `old`/`z0`/`wr`) by
`RepOld` preservation per step: new lemmas for the growth (`rzGrow`/`rzLandG`: the grown bytes' candidates
are those `pcRun` knew, stamp-0 values kept; size ≤ `k = |old|`), the fdatasync (`syncLayP`: the synced
tail exact, `TailLast.repOld`), and the generic step of `walInvBody_tailW` (`TailAccW.lean:269`: with
`wr' = wr` it kept `TailPend` because `tailLay` keeps `old`; with `RepOld` the caller must supply it: only
resizes and the sync act on a pending lent tail). `ZeroToEnd.specWalTail`/`walTailP_ofRead` then drop the
zero-word premise (`TailLast.repOld` instead of `lenZ_of_tailLast`).

**Refined (same session), being implemented:**
1. `TailPend` := `RepOld`'s formula (done, `Abs.lean`; `tailPend_iff_repOld`). `TailRK (some (_, false))` is
   now `TailZeros ∨ TailPend` (a lent tail's step must keep it; `TailAccW`'s lent `ZerosOk` proof uses it).
   `rzStart_pureK` false case = true case (`rzStart_pureR`). Deleted: `WalAbsD.pendVals`,
   `crashOkA_tailPend` (`TailCrashPend`), `tailPend_tailLay`, `tailCrashStep_rzStartP`, `rzStart_pureP`
   (`TruncSupPend`).
2. The failure path (`ZeroToEnd` fails, `Close` syncs: `syncLayP`, `old` := the synced values from `wr`)
   needs the static `tailStop` of `syncLayP`: a `PendStop` of the handle's values at `wr`. It goes in the
   handle: `TailMetaE` gets `Mr` and the chain CRC (`tailCrc Mr H md cuts`) and its last conjunct becomes
   `PendStop walCodec Mr (bs.map (·.1)) o0 c` (was the zero length word); `walTailPE` gets `Mr`.
   `ZeroToEnd`'s first step derives it from the invariant (exact tail: handle values = `old`; `tailStop`
   with `z0 = wr = |S|`, or F-Z: zero word); its internal states keep it (`pendStop_congr`: values from
   `o0` unchanged, or all zero: `decStep_zeroWord`).
3. `TailSyncLayP`: `hlw` → that `PendStop`; `crashOk_syncP` over `crashTo_tailR` (not `crashTo_tailP`).
4. `GrowSup`: `TailRK (some (k, false))` for the grown layouts: `RepOld` kept by a growth (new lemmas).
5. `specWalTail`'s pre drops the zero word; `walTailP_ofRead` drops `hz`; `WAL__ReadAll`'s marker goes.

## Session 5 (2026-11-25): item 2, `CloneStLaw`, the Link

- **Item 2 done** (`c18dbe98ed`): `TailPend` is `RepOld`'s formula; the failure path's handle carries
  `PendStop` (`TailMetaE Mr c`, `walTailPE Mr`); growth keeps `RepOld` (`repOld_rzGrow`, `repOld_rzLandG`).
  **Removed premise** (ours, proved spec): `ZeroToEnd.specWalTail`'s pre no longer takes the zero length
  word at `wr` (`walTailP … k true TailMetaR`); `walTailP_ofRead` drops `hz`.
- **`CloneStLaw`** (`e1bd2afbaa`): `WalPbIn.CloneStLaw P Mr HsO` (`ReadAllCallees.lean`): `proto.Clone` of
  an owned hard state (`HsO`) gives both pointers frozen at `h`, the clone non-nil and `walStMarsh`. It
  replaces `CloneHsLaw` as `ReadAll`'s hypothesis (`CloneHsLaw` stays, unused by `ReadAll`). Proved for the
  raftpb instance: `walRaftP_cloneSt` (`RaftModel/LawsHsMarshal.lean`) over `proto.ClonePb.spec` and
  `proto.MarshalPb.spec` (the owned source is canonical, `walRaftHsO`). No loop-invariant tracking was
  needed: `HsO` is already canonical. A law hypothesis, no axiom.
- `5054fab591`: `Link.lean` regenerated (`h_WalPbIn_CloneStLaw`, `h_WalPbIn_ZeroStLaw`, `wp_encodeState*`);
  `SavePure:252` was a struct-instance continuation line left of its first field (`checkColGe`);
  `WAL__cut`: `saveState.specPre` takes `P.hsIn` (out of `walStIn`), and `h1.stNil = h.stNil`.

### Repair with a pending run (E4, done 2026-11-25)

`walRepairFile` returns the pending run `es`: `(recFrames rs).length = lay.wr + |pendFrames es|`
(`es ≠ [] → z0 = wr`), and now also the reader's stop at `wr` on the bytes below `LastOffset`
(`PendStop`) and, past `wr`, a nonzero byte of the run's first length word (`frames_nz`). `Repair`
truncates at `tg = |recFrames rs| ∈ [wr, size]` (repair.go:86); the run stays in the file. Done:
1. `repair_register`: the tail record at `lay'.wr` (the stream's end), `wr ≤ tg`, `TailMetaRP Mr (tailCrc …)
   wr tg` (`TailMetaR`, the nonzero byte, the stop) — `RepairTailDefs.lean`.
2. `os.File.Truncate.specRepTail` at target `tg` (pre `TailMetaRP`, post `TailMetaRWP`: `TailMetaRW`,
   `wr ≤ size`, the stop); `walTailPO` no longer carries `LoWr`. Supply `walTail_truncSupR`
   (`TruncSupRep.lean`): the tie `repTie` carries the caller's half of the run's nonzero byte (`repNZ`), which
   with F-Z contradicts `WalAbsD.zeroPast`; `RepOld` starts via `rzStart_pureRT` (`RzRep.lean`); the state
   property `RepP` (size `S0` or `tg`, `LoWr` at `tg = wr`), so `os.File.Truncate.specAu`'s closure was
   widened (`m'.size = m.size ∨ m'.size = sz`, ours, proved).
3. `fileutil.Fsync.specRepTail`: over `wp_tailFsyncPE`/`walInvBody_syncPE` (`syncLay_anyE`: F-Z, or
   `TailPend` = `RepOld` with `syncLayP`), generalized over the token's kind; the post gives the pending token
   back (`∃ k'`), not the key (no F-Z past a run).
4. `walInv_repairPut` (moved to `UnregLent.lean`) unregisters by the token (`walInvBody_untailL`).
   `walInvBody_untailR` (`RepairPut.lean`) and `RepairSync.lean` became unused: both files deleted.

## The hard stop: `DiscardUnsaved` needs two abstract-disk steps (2026-11-25, open)

`wal.DiscardUnsaved` (fork `unsaved.go:97`) renames `dir` to `dir.tmp` and fsyncs the parent, so its spec's
success post must be "no WAL at `dir`" (`walDirIs dir none`, what `wal.bootRes`'s "no WAL, possibly
`wal.tmp`" is built from). The trusted abstract disk (`GooseLang/Ext/AbsDisk/Impl.lean`) cannot reach that
state:
* no `AbsDiskStep` removes an entry of `s.wal` (`"WalCreate"` inserts; every other step goes through
  `absDiskUpd`, which keeps the entry);
* a crash keeps an absent WAL absent (`absDisk_semantics.crash`'s last clause), and `walCrash` lets a WAL
  vanish only when `named = false`, which no step sets (`"WalNamed"` only sets it `true`).
Between the rename and the parent's fsync a crash may keep the WAL at `dir` (the rename lost) or lose it
(the rename durable): the abstract WAL must be one that "may vanish" there, and absent after the fsync.

**Proposed** (trusted text: needs approval): two steps, mirroring `Create`'s rename/fsync pair in reverse:
`"WalUnnamed"` of `dir` (`named := false`, at the rename: `walCrash`'s first disjunct then covers the
rename made durable, its second the rename lost) and `"WalDiscard"` of `dir` (the entry deleted, at the
parent's fsync, after which the rename is durable). No change to `walCrash`, `walImg` or the crash clause.

1. **Minimal program that needs it**:
   ```go
   w, _ := wal.Create(lg, dir, md); w.Close()    // a WAL that holds nothing a Save wrote
   if ok, err := wal.DiscardUnsaved(lg, dir); err == nil && ok && wal.Exist(dir) {
       panic("discarded WAL still there")
   }
   ```
   Its proof needs `walDirIs dir none` after `DiscardUnsaved` (`Exist`'s spec answers from `walDirIs`). With
   the existing steps the abstract entry of `dir` stays `some d` (no step deletes it), while the WAL
   invariant (`WalsOk`) ties every entry to a directory at `dir` holding its segments, which the rename
   removes: no state of the invariant fits after the rename. Searched: `AbsDisk` is this repository's
   extension (Perennial has no WAL model); its `Specs.lean` has no removal lemma, and none can exist since
   the steps are the only transitions.
2. **The real code has it**: etcd fork `goose-lean-fmt1c-tornsave` (`2bd3048d7`),
   `server/storage/wal/unsaved.go:97` `DiscardUnsaved` (`os.Rename(dir, dir+".tmp")`, then
   `syncDir(filepath.Dir(dir))`), called by `server/etcdserver/bootstrap.go:82` `bootstrap` before
   `bootstrapBackend`, `haveWAL = !discarded`.

`Unsaved` (read-only, a decode loop like `validSnapshotEntries`) needs no semantics change. Proposed spec
(not yet written): `ValidSnapshotEntries`'s binders; post `b = true → err = nil ∧ ∃ d, o = some d ∧
∀ op ∈ d.H.map WalOpG.toM, walOpBlank op` (`walOpBlank`: `.save h []` with `hsEmptyP h`, or `.snap m _` with
index 0: what Go accepts), with a pure lemma that every crash image `H.take j` of such a history is blank
(prefix-closed). "Reads `walFresh`" (server level, P5) needs in addition that no `SaveSnapshot` at index 0
carries a nonzero term (raft never saves an empty snapshot: `IsEmptySnap`), a server-side fact.

## The hard stop: `proto.Marshal` of an empty hard state (needs a trusted-spec change)

**Resolved 2026-11-25:** Upamanyu approved the change (#8, 00:38Z). `proto.MarshalPb.spec`'s post now has
`⌜l ≠ null → d ≠ slice.nil⌝` (no new premise); `proto.MarshalPbNonNil.law` is deleted, and
`walRaftP_marshSt`/`walRaftP_zeroSt`/`walSrvP_zeroSt` take `proto.MarshalPb.spec`. The axiom
`proto.MarshalPb.wp_proof` keeps its name (the tcb baseline lists names). What follows is the history.

`Save(st, ents)` with `ents ≠ []` and `st` empty now writes `encodeState(w.state)`, and `w.state` can
be the empty hard state (a WAL with no state record yet: `Save` sets `w.state = &raftpb.HardState{}`,
wal.go:1345-1347). `encodeState` marshals it: `pbutil.MustMarshalMessage(s)` = `proto.Marshal(s)`
(pbutil.go:53-58), and builds `&walpb.Record{Type: …, Data: b}`. `walpb.Record` is proto2 with
`optional bytes data = 3` (record.proto:1,11): a nil `Data` is not encoded, a non-nil empty one is
(field 3, length 0). The frame bytes therefore depend on whether `b` is nil.

1. **Minimal program and the failed proof.**
   ```go
   st := &raftpb.HardState{}
   b, _ := proto.Marshal(st)                         // non-nil empty in protobuf-go
   out, _ := proto.Marshal(&walpb.Record{Type: proto.Int64(3), Data: b})
   if len(out) != 4 { panic("Data's presence") }    // 2 bytes for Type, 2 for an empty Data
   ```
   The `encodeState` proof needs `d ≠ slice.nil` for `recBytes v.Data' (some [])` (`encRecIn`,
   `walpb/PbRecord.lean:97`); for a non-empty state `MarshalHsLaw` gets it from the encoding's length.
   `proto.MarshalPb.spec`'s post is `d ↦* pbEncC I c ∗ ownSliceCap w8 d (DFrac.own 1)`, which a nil
   slice satisfies when the encoding is empty (Perennial's `ownSlice_nil`, `ownSliceCap_nil`,
   `Golang/Theory/Slice.lean:118,326`); no other `proto` spec here says more (`Spec/google_golang_org/
   protobuf/proto/`). Its docstring already claims "an empty encoding is a non-nil empty slice".
2. **The real code.** protobuf-go v1.36.11 `proto/encode.go:119-146`: `Marshal` returns
   `emptyBytesForMessage(m)` for an empty encoding, `emptyBuf[:]` (non-nil) for a valid message, nil
   only for an invalid one (a nil `*T`). etcd: `server/storage/wal/wal.go` `(*WAL).encodeState` called
   from `(*WAL).Save` at fork `2bd3048d7` with `st = w.state` (non-nil pointer, possibly empty).

**Proposed change (for the coordinator / Upamanyu):** `proto.MarshalPb.spec`'s post gains
`⌜l ≠ null → d ≠ slice.nil⌝` (or the premise `l ≠ null` and `⌜d ≠ slice.nil⌝`), axiom
`proto.MarshalPb.wp_proof` in `etc/tcb-baseline.txt`; then `WalPbIn.MarshalHsLaw` drops `¬ hsEmptyP hs`
for `hp ≠ null` (proved in `RaftModel/LawsHsMarshal.lean` from the stronger post). Alternative without
the trusted change: none found (the encoding layer must know whether the empty state's `Data` is
present; a `Save` spec premise excluding an empty `w.state` would add a premise up to the top-level
theorems).

### Coordinator's answer (2026-11-24) and what it implies

(2) approved: keep going with the non-nil fact as an undischarged hypothesis, one `abbrev … .law : Prop`
in a defs module; never edit `proto.MarshalPb.spec` or the tcb baseline. (1) is with Upamanyu (#8).

**Finding while designing it: `MarshalHsLaw` without `¬ hsEmptyP` is false for the instance.**
`walHsIn` (`RaftModel/Pb.lean:106`) admits, for an empty state, any content of that model: raft's
`Ready.HardState` is `⟨some 0, some 0, some 0⟩` when empty (`walHsIn_of_hsOptC`, `RaftModel/Srv.lean`),
whose encoding is not `[]` (explicit zero fields). Such a pointer is never written (`saveState` skips
it, `Save` replaces it by `w.state`), but a law over every `hsIn` pointer would claim its encoding is
`encState hsZero = []`. What is true is narrower: **`w.state`'s content is canonical** (all-absent when
empty): it is assigned only `&HardState{}` (wal.go:1346, :542 then `proto.Clone`, :747), a state decoded
from a record (canonical: our records are canonical encodings or `[]`), or a non-empty `st`
(`encodeState`, canonical by `walHsIn`).

Design (to implement): the handle holds, for `w.state`, `walStIn P Mr sp h.st := P.hsIn sp h.st ∗
walStMarsh Mr sp h.st` in the slot of `P.hsIn sp h.st` (one hypothesis, so `walHandleIn`'s `icases`
patterns do not change), where `walStMarsh Mr sp hs` is the persistent triple "`MustMarshalMessage(sp)`
returns a non-nil slice of `Mr.encState hs`". `encodeState` takes `walStIn` of its argument (no marshal
law); `saveState` builds it from `MarshalHsLaw` (non-empty); `Save`'s fresh `&HardState{}` and
`ReadAll`'s `proto.Clone` of the empty/zero state build it from one new WalPbIn law, proved for the
instance from `proto.MarshalPbNonNil.law` (the strengthened `Marshal` spec as an `abbrev`, the single
place the approval discharges).

**Where `walStIn` comes from (worked out 2026-11-24, partly implemented):**
- `Handle.lean`: `walStMarsh`, `walStIn` (`P.hsIn ∗ (sp ≠ null → walStMarsh)`), `walStIn_null`; the
  handle's `w.state` slot is `walStIn` (`Handle.lean`, `CloseHandle.lean`, `SaveHandle.lean`'s
  `walHandleIn_state`, `CreateHandle.lean`'s premise; `Create.lean` builds it from `NilLaw` with
  `walStIn_null`: `Create` leaves `w.state` nil). Not compiled yet.
- `saveState(s)` (non-empty `s`, also `cut`'s `saveState(w.state)`): `walStMarsh` from `MarshalHsLaw`
  (its post already says non-nil). No new law.
- `Save`'s `w.state = &HardState{}`: a new law `WalPbIn.ZeroStLaw P Mr` (as `ZeroLaw.2` with
  `walStMarsh Mr p hsZero` added), discharged for the instance from `proto.MarshalPb.spec` (non-nil since 2026-11-25).
- `ReadAll`'s `w.state = proto.Clone(state)`: **needs provenance tracking** in the loop. `proto.Clone`
  copies the content with its presence bits, and `walHsIn` admits non-canonical empty contents, so a
  law over any `hsIn` pointer is false. True: `state` is `&HardState{}` or `MustUnmarshalState(d)` of a
  record's data, and on the ok path the last state record's data is `Mr.encState (walLastHS …)`
  (records = the history's). Plan: the loop invariant keeps `bsSt : Option (List w8)` (the data
  `state` was unmarshalled from, `none` = the zero alloc) and the unmarshal law's post adds
  `⌜bs = Mr.encState h⌝ -∗ canonical`; at the end `bsSt` is the last state record's data, which
  the decoding lemmas equate to `Mr.encState`; a `CloneStLaw` carries `walStMarsh` through `Clone`.
  Both laws discharged in `RaftModel/` from `proto.MarshalPb.spec` (and the unmarshal model).

**Second finding: `encodeState(w.state)` needs `w.state ≠ nil`, which the handle forgets.** `Save`
checks `w.state == nil` at its top, but the loop over the entries closes the handle, whose `w.state`
slot is existential: when the entries are done and `Save` loads `w.state` again, nothing says it is
not nil (and `encodeState(nil)` would marshal to a nil slice, a record without `Data`). `Create` leaves
`w.state` nil, so the slot cannot just say non-nil. Planned: the slot becomes `walStIn P Mr sp h.st ∗
⌜sp ≠ null ∨ ∀ o ∈ h.H, o is a snapshot⌝` (one hypothesis, a def `walStH P Mr sp h`); only the proofs
that change `h.H` re-prove it (`walHandleIn_append`: a `Save` needs `sp ≠ null`, which `Save` has from
its nil check; `SaveSnapshot` keeps the disjunct; `Create`: only snapshots; `ReadAll`: `CloneStLaw`
gives a non-nil clone). In progress in `WAL__Save.lean` (the `w.state == nil` join now carries
`walStIn` and `sp' ≠ null`; the `len(ents) > 0` branch not yet written).

**Implemented (2026-11-24, still uncompiled at this point):** `WalHS.stNil : Bool := false` (only `createHS`
sets it); `walStIn P Mr sp hs nil` (`hsIn ∗ (sp ≠ null → walStMarsh) ∗ (nil = false → sp ≠ null)`) in the
handle slot as `walStIn P Mr sp h.st h.stNil`, with `walStIn_null/_intro/_set/_nn`; `walHandleIn_stateNil`
(`SaveHandle.lean`: back with a new flag); `Save` clears it at its nil check and keeps `hc.stNil = false`
in the entries loop (`Hnil` in `HI`); the `len(ents) > 0` branch (`wp_join (Q := …) at next`, the
inner `IsEmptyHardState` join at `walStIn hp2 (saveHS …)`), `saveState` otherwise. New hypotheses of
`Save.wp_proof`: `wp_encodeState`, `wp_encodeStateNE`, `wp_marshal` (`MarshalHsLaw`), `hzst`
(`ZeroStLaw`). Laws: `proto.MarshalPb.spec` (non-nil post, approved 2026-11-25), `walRaftP_zeroC` (`LawsHs`), `walRaftP_marshSt`/`walRaftP_zeroSt`/`walSrvP_zeroSt`
(`LawsHsMarshal`). Still to do there: `ReadAll`'s provenance and `CloneStLaw` (above), the Links.
