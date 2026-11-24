# P6 (etcd_safe #52/#50), phase B: re-prove the WAL over the torn-Save fix — handoff

## START HERE

- **Date**: 2026-11-24. **Branch** `etcd-safe-walfix-p6`, worktree `/shared/etcd-grove-p6`.
- **Done before this session**: the fork fix (`goose-lean-fmt1c-tornsave` @ `2bd3048d7`), the retranslation
  (`Code/.../storage/wal.lean`, `etcdserver.lean`), `examples/` go.mod, `etc/goose.py --check` green.
- **This session**: see "Progress" below (kept current at each milestone).
- **STOPPED at a hard stop (trusted text), 2026-11-24**: "The hard stop: `proto.Marshal` of an empty
  hard state" below. Nothing is compiled yet (the `.lake/build` seed was still building); the next
  session seeds, compiles bottom-up and goes on once the coordinator decides.
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

## The hard stop: `proto.Marshal` of an empty hard state (needs a trusted-spec change)

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
