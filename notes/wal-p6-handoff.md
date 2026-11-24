# P6 (etcd_safe #52/#50), phase B: re-prove the WAL over the torn-Save fix — handoff

## START HERE

- **Date**: 2026-11-24. **Branch** `etcd-safe-walfix-p6`, worktree `/shared/etcd-grove-p6`.
- **Done before this session**: the fork fix (`goose-lean-fmt1c-tornsave` @ `2bd3048d7`), the retranslation
  (`Code/.../storage/wal.lean`, `etcdserver.lean`), `examples/` go.mod, `etc/goose.py --check` green.
- **This session**: see "Progress" below (kept current at each milestone).
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
