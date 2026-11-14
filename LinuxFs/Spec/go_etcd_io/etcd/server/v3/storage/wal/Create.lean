/-
`wal.Create(lg, dir, md)` over `fsExt` (W4 of `notes/wal-fsext-plan.md`; the main tree's axiom
`Spec/go_etcd_io/etcd/server/v3/storage/wal/Create.lean` restated with the binder changes of plan §3,
its error arms made honest). S/ = `server/storage/wal/` at the pin with the local fork patches
(`notes/wal-fsext-fork/`: F-N1, `dir.tmp` fsynced before the rename; `cleanupWAL` returns its error).
To be proved in `LinuxFs/Proof/go_etcd_io/etcd/server/v3/storage/wal/Create.lean`. Lean-first.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateDefs
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.PkgInit
public import LinuxFs.GeneratedProof.go_etcd_io.etcd.server.v3.storage.wal
public import Spec.go_uber_org.zap.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open Fs WalEnc WalFs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]

/-- **`Create(lg, dir, md)`** (S/wal.go:102-262): a fresh WAL with metadata `md` (a non-nil slice:
its record's `Data`) in `dir = r/nm`, a WAL directory of the area `r` (the directory `jr`, durable).

`nm` is a name (`NameOk`: no NUL byte, beyond `walNameOk`; the system calls on `dir` need it), and
`dir` shorter than `2^59` (`filepath.Join`'s and `CreateDirAll`'s bounds, on `dir.tmp`'s paths).

*Package initialization*: `isPkgInit wal` (`PkgInit.lean`: `SegmentSizeBytes`, the metrics `Create`
observes, the CRC table its encoder takes).

*Resources.* The area's invariants (`walAreaOk`), a fraction of the spine to the area, the program's
part of the area (`walAreaRes`: from it `Create` takes the claims on `nm`, `nm.tmp` and a cleanup's
`nm.broken.*`, all given back), the **whole call permission** (`osCallPerm 1`: `Create` renames a
directory, which `fsExt` allows only with no other call in flight, and `mkdir`s, a directory
operation; I2's deviation 1), the generation's lock token, and the update from `walAbsent dir`.

*The commit* is at the step of the rename of `nm.tmp` onto `nm` (`renameWAL`'s, or the retry in
`renameWALUnlock`), to `walDurFresh md` (`named = false`). Before it, `nm.tmp` holds the first
segment, its records (`saveCrc`, the metadata, the empty snapshot) fdatasynced and `nm.tmp` fsynced
(F-N1), so every crash after the rename decodes to the fresh WAL or (the rename lost) finds `nm`
absent: the fresh WAL's `CrashOk`. The parent's fsync after it commits the rename (`osCommitLb`):
`walNamed dir`.

*Success*: the update's `Q`, the open WAL (`walOpenW`, which takes the lock token), its named entry,
its history's empty prefix written and synced, the purge right, and half of the call permission (the
other half is the file pipeline's, started by `renameWAL`, held in the handle until `Close`).

*An error before the rename* (`Exist` true, `RemoveAll`, `CreateDirAll`, the segment's creation and
writes, `dir.tmp`'s fsync, or a rename that failed with no effect): nothing committed; the token, the
update and the whole permission back.

*An error after the rename* (`renameWAL`'s `OpenDir`, `renameWALUnlock`'s `Open`/`ReadAll`, the
parent's `OpenDir`/fsync/close, then `cleanupWAL`): the update committed (`Q`); the WAL is fresh and
unnamed, its directory at `dir` or moved aside to `dir.broken.*` by the cleanup (whose rename is not
fsynced, so a crash may bring it back: no later state can be promised). The handle, the token and half
of the permission (the pipeline's, perhaps still in flight) are lost. Plan §5 Q4's option (a) (a second,
cleanup update to `walAbsent dir` committed at the cleanup's rename) is not provable: that rename is
never made durable, and a crash keeping `nm` would contradict the committed absence; see the W4
implementation log. -/
abbrev wal.Create.spec (C : WalCodec) (Mr : WalMarshal) : Prop :=
  ∀ (lg : Loc) (R : Roots) (jr : Ino) (r dir nm : GoString) (mp : GoSlice) (md : List w8) (qp : Qp)
    (Q : IProp GF),
  InArea r dir nm → NameOk nm → dir.length < 2 ^ 59 → cleanAbsPath r → mp ≠ slice.nil →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗ zapLoggerOk lg ∗
      mp ↦*□ md ∗ WalFs.walAreaOk C Mr R jr r ∗ WalFs.dirDurable r ∗ osPathS R r (DFrac.own qp) jr ∗
      walAreaRes jr ∗ osCallPerm 1 ∗ WalFs.walUnlockedTok ∗
      AU <{ WalFs.walAbsent dir }> @ walAuMask, ∅ <{ WalFs.walDiskAt dir (walDurFresh md), COMM Q }> }}
    (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.wal.Create)) (Val #lg)) (Val #dir))
      (Val #mp))
  {{ (w : Loc) (err : GoInterface), RET (PairV #w #err);
      osPathS R r (DFrac.own qp) jr ∗ walAreaRes jr ∗
      ((⌜err = interface.nil⌝ ∗ Q ∗ WalFs.walOpenW w dir ∗ WalFs.walNamed dir ∗ WalFs.walLenLb w dir 0 ∗
          WalFs.walSyncedLb dir 0 ∗ WalFs.walPurgeW w dir ∗ osCallPerm (1 : Qp).half) ∨
        (⌜err ≠ interface.nil⌝ ∗ osCallPerm 1 ∗ WalFs.walUnlockedTok ∗
          AU <{ WalFs.walAbsent dir }> @ walAuMask, ∅ <{ WalFs.walDiskAt dir (walDurFresh md), COMM Q }>) ∨
        (⌜err ≠ interface.nil⌝ ∗ Q ∗ osCallPerm (1 : Qp).half)) }}

end spec

end EtcdGrove
end Perennial
