/-
`(*wal.WAL).SaveSnapshot` over `fsExt` (W11 of `notes/wal-fsext-plan.md`; the main tree's axiom
`Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__SaveSnapshot.lean` with plan §3's changes, as
`WAL__Save.lean` here). One spec since wal-link L1a (2026-11-17, `notes/wal-link-scope.md` §8: the former
`SaveSnapshot.spec`, `specNoErr` and `specPre` merged), over the handle's state (`WalSnapSt`,
`HandleShared.lean`): a share of the open WAL (`shared`, parameterised by the files with no I/O error `Sio`
as `Save`'s), or `Create`'s `w` before the rename (`pre`). S/ = `server/storage/wal/` at the pin with the
local fork patches. Proved in `Proof/go_etcd_io/etcd/server/v3/storage/wal/WAL__SaveSnapshot.lean`.
Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.HandleShared
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__SaveSnapshotPre
public import GooseLang.Ext.Fs.FilteredSem

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open Fs WalEnc WalFs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]
variable {Sio : IoSet} [FsStepSat (NoIoErr Sio)] [FsStepSat (NoMapLockErr Sio)]

/-- **`w.SaveSnapshot(e)`** (S/wal.go:1148-1184, with the fork's fixes 0007-0008): one snapshot record of
`e`'s index and term (its conf state non-nil unless the index is 0, `ValidateSnapshotForWrite`); `snapi` and
`enti` each raised to the index if below it; then, as `Save`, a `sync` if the tail is below
`SegmentSizeBytes` (or the WAL has no file pipeline yet, `w.fp == nil`: `Create`'s call), else a `cut` (which
syncs).

*`shared γ q`* (an open WAL): the index below `2^64-1`, the encoding below `2^40` bytes (ledger 2026-11-14); the
update commits after `w.mu.Lock()`, before the record is encoded. *Success*: the share, `Q d`, the history
written and synced to its new length. *Error* (only when `Sio` misses an inode, and then the caller holds the
whole share: the encode's write, the flush, a `Seek`, the fdatasync, the cut): committed (`Q d`), the handle
lost, as `Save`'s. When `Sio` covers every inode, the WAL directory fits and its children's paths are in
`Sio` (`cut.spec`'s premise, as `Save`'s).

*`pre …`* (`Create`'s `w` before the rename, `walPreIn`; its encoder writes the first segment in `nm.tmp`, a
file the program owns wholly, whose writer is generic: `W` accepted, `B` broken, `io.writerStream`, and `S`
what an fdatasync of the file makes of `W out`, `walPreSyncOk`): the record encoded after what the encoder
holds, within the encoder's `2^47` bound (`lim < 2^47`, `Create`'s segment size). Success: the encoder empty,
its CRC after the record, everything accepted and synced (`S`). Error: the encoder holds anything, the writer
in some broken or accepted state (`Create` only closes the file then). The tail's offset (`w.tail().Seek`)
is the writer's accepted length (`walPreSeekOk`); `w.fp` is nil (no pipeline yet), so it never cuts. -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.WAL.SaveSnapshot.spec (P : WalPbIn GF) (Mr : WalMarshal) : Prop :=
  ∀ (R : Roots) (jr : Ino) (r : GoString) (w : Loc) (dir : GoString) (st : WalSnapSt GF) (sp : Loc)
    (md : SnapshotMetadataM) (al cs : Bool) (sized : Bool) (Q : WalDur → IProp GF),
  {{ match st with
      | .shared γ q => iprop(WalFs.walAreaOk walCodec Mr R jr r ∗ walOpenWS Sio P Mr w dir γ q ∗
          ⌜walCov Sio ∨ q = 1⌝ ∗ ⌜walCov Sio → DirFits dir ∧ ∀ b, Sio.path (child dir b)⌝ ∗
          walSnapAt Mr sp md al cs ∗
          ⌜md.Index' = W64 0 ∨ cs = true⌝ ∗ ⌜uint.nat md.Index' < 2 ^ 64 - 1⌝ ∗
          ⌜(Mr.encSnap md al).length < 2 ^ 40⌝ ∗
          AU <{ ∃∃ d : WalDur, WalFs.walDiskAtI dir γ.inc d ∗ ⌜d.sized = sized⌝ }> @ walAuMask, ∅
            <{ WalFs.walDiskAtI dir γ.inc { d with H := d.H ++ [WalOpG.snap md al] }, COMM Q d }>)
      | .pre lg mds mdb e lt f snapi enti Wr Br Sr lim out pend c => iprop(
          ⌜md.Index' = W64 0 ∨ cs = true⌝ ∗ ⌜(out ++ pend ++ snapFrame Mr c md al).length ≤ lim⌝ ∗
          ⌜lim < 2 ^ 47⌝ ∗ ⌜walPreSyncOk f Wr Sr⌝ ∗ ⌜walPreSeekOk f Wr lim⌝ ∗
          io.writerStream (wal.fileWi f) lim Wr Br ∗
          globalAddr go_etcd_io.etcd.server.v3.storage.wal.SegmentSizeBytes ↦□ (W64 64000000) ∗
          structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"fp" w ↦ (null : Loc) ∗
          encEnv ∗ isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap ∗
          isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.pbutil ∗
          walPreIn w lg dir mds mdb e lt f snapi enti ∗ ownEncoder e (wal.fileWi f) c pend ∗
          Wr out ∗ walSnapAt Mr sp md al cs) }}
    (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!! go!"SaveSnapshot")) (Val #sp))
  {{ (err : GoInterface), RET #err;
      match st with
      | .shared γ q => iprop(
          (⌜err = GoInterface.nil⌝ ∗ walOpenWS Sio P Mr w dir γ q ∗ ∃ d : WalDur, Q d ∗
              WalFs.walLenLb w dir γ.inc (d.H.length + 1) ∗ WalFs.walSyncedLb dir γ.inc (d.H.length + 1)) ∨
          (⌜err ≠ GoInterface.nil ∧ ¬ walCov Sio⌝ ∗ ∃ d : WalDur, Q d))
      | .pre lg mds mdb e lt f snapi enti Wr Br Sr _ out pend c => iprop(
          ∃ (snapi' enti' : w64), walPreIn w lg dir mds mdb e lt f snapi' enti' ∗
          structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"fp" w ↦ (null : Loc) ∗
          ⌜(snapi' = snapi ∨ snapi' = md.Index') ∧ (enti' = enti ∨ enti' = md.Index')⌝ ∗
          ((⌜err = GoInterface.nil⌝ ∗
              ownEncoder e (wal.fileWi f) (hash.crc32.crc32c c (Mr.encSnap md al)) [] ∗
              Sr (out ++ pend ++ snapFrame Mr c md al)) ∨
           (⌜err ≠ GoInterface.nil⌝ ∗ ∃ (c' : w32) (pend' : List w8),
              ownEncoder e (wal.fileWi f) c' pend' ∗
              ((∃ a b : List w8, Br a b) ∨ (∃ o : List w8, Wr o))))) }}

end spec

end EtcdGrove
end Perennial
