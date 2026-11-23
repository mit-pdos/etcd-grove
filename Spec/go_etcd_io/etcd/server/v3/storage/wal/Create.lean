/-
`wal.Create(lg, dir, md)` over `fsExt` (W4 of `notes/wal-fsext-plan.md`; the main tree's axiom
`Spec/go_etcd_io/etcd/server/v3/storage/wal/Create.lean` restated with the binder changes of plan §3,
its error arms made honest). S/ = `server/storage/wal/` at the pin with the local fork patches
(`notes/wal-fsext-fork/`: F-N1, `dir.tmp` fsynced before the rename; `cleanupWAL` returns its error).
To be proved in `Proof/go_etcd_io/etcd/server/v3/storage/wal/Create.lean`. Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateDefs
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateSnap
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.Handle
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.PkgInit
public import GeneratedProof.go_etcd_io.etcd.server.v3.storage.wal
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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]

/-- **`Create(lg, dir, md)`** (S/wal.go:102-262): a fresh WAL with metadata `md` (a non-nil slice:
its record's `Data`) in `dir = r/nm`, a WAL directory of the area `r` (the directory `jr`, durable).

`nm` is a name (`NameOk`: no NUL byte, beyond `walNameOk`; the system calls on `dir` need it), the
metadata shorter than `2^41` (the handle `walOpenWF` keeps that bound; ledger, 2026-11-14) and not empty
(a handle's metadata slice is then non-nil whatever it is read back as: `cut` writes it as a record's
present data; ledger 2026-11-14, "an empty metadata read back as `nil`"; the server's is a marshalled
`etcdserverpb.Metadata`, never empty), and
`dir` shorter than `2^59` (`filepath.Join`'s and `CreateDirAll`'s bounds, on `dir.tmp`'s paths). The
client's marshaller encodes `Create`'s initial snapshot object as protobuf-go does (`WalMarshalCreateOk`,
`CreateSnap.lean`: the fresh WAL's `Mr.snap0`; ledger, 2026-11-14).

*Package initialization*: `isPkgInit wal` (`PkgInit.lean`: `SegmentSizeBytes`, the metrics `Create`
observes, the CRC table its encoder takes).

*Resources.* The area's invariants (`walAreaOk`), a fraction of the spine to the area, the program's
part of the area (`walAreaRes`: from it `Create` takes the claims on `nm`, `nm.tmp` and a cleanup's
`nm.broken.*`, all given back), the **whole call permission** (`osCallPerm 1`: `Create` renames a
directory, which `fsExt` allows only with no other call in flight, and `mkdir`s, a directory
operation; I2's deviation 1), the generation's lock token, and the update from **any view `o` of
`dir`** the client has (`Pv o`: what it knows of it, given back with the update by the error arms that
commit nothing). `Create` commits only when the real state has no WAL in `dir`, whatever the view: its
`Exist(dir)` answers `false` (the lock token held, every present WAL's name is registered and its
directory there holds a segment, so `Exist` finds a `.wal` name), and the name stays unregistered until the
commit (the program holds its registration half, `walSplitFrag`); the view is below the real state
(`walOptLe`), so it is `none` at the commit. A client after `Exist`'s `false` (`Pv := wal.ExistFalseOk`,
`CreateFresh.lean`) and one that knows `walAbsent dir` (`Pv o := o = none`) are both instances.
(Until 2026-11-15 the update was from `walAbsent dir` only: `notes/specs-only/ledger.md`, "the update
from `walAbsent` only"; `notes/wal-units/fresh.md`.)

*The premise* that the file system does not fail on `dir`, `dir.tmp` and the area `r`, and that `dir`
and `dir.tmp` fit (`FsNoErrOn (fun p => p = dir ∨ p = dir ++ ".tmp" ∨ p = r) ∧ PathFits …`, as `cut`'s
and `Save`'s `walCov Sio → DirFits dir ∧ …`) makes the rename of `nm.tmp` onto `nm` succeed, so
`renameWAL`'s retry (`renameWALUnlock`) is never reached (ledger 2026-11-21: that retry's spec was false as
stated), and makes `Exist(dir.tmp)` and `RemoveAll(dir.tmp)` exact: `CreateDirAll` then only meets an absent
`dir.tmp`, whatever a crash left there (ledger 2026-11-22).

*The commit* is at the step of the rename of `nm.tmp` onto `nm` (`renameWAL`'s), to `walDurFresh md`
(`named = false`). Before it, `nm.tmp` holds the first
segment, its records (`saveCrc`, the metadata, the empty snapshot) fdatasynced and `nm.tmp` fsynced
(F-N1), so every crash after the rename decodes to the fresh WAL or (the rename lost) finds `nm`
absent: the fresh WAL's `CrashOk`. The parent's fsync after it commits the rename (`osCommitLb`):
`walNamed dir`.

*Success*: the update's `Q`, the open WAL (the client handle `walOpenWF P Mr`, as `Save`'s and
`ReadAll`'s: it holds the lock token, the record of what the handle holds out, the tails' authority half,
the metadata, and half the call permission: a quarter its own, a quarter the file pipeline's, started by
`renameWAL`), its named entry, its history's empty prefix written and synced, the purge right, and the
other half of the call permission, the client's while the WAL is open (`Close` returns the handle's).
(Until 2026-11-14 the ghost-only `walOpenW` and half the call permission, then no permission back:
`notes/specs-only/ledger.md`, "the client keeps no call permission while a WAL is open".)

*An error before the rename* (`Exist` true, `RemoveAll`, `CreateDirAll`, the segment's creation and
writes, `dir.tmp`'s fsync, or a rename that failed with no effect): nothing committed; the token, the
update and the whole permission back.

*An error after the rename* (`renameWAL`'s `OpenDir`, the
parent's `OpenDir`/fsync/close, then `cleanupWAL`): the update committed (`Q`); the WAL is fresh and
unnamed, its directory at `dir` or moved aside to `dir.broken.*` by the cleanup (whose rename is not
fsynced, so a crash may bring it back: no later state can be promised). The handle, the token and half
of the permission (the handle's quarter and the pipeline's, perhaps still in flight) are lost. Plan §5 Q4's option (a) (a second,
cleanup update to `walAbsent dir` committed at the cleanup's rename) is not provable: that rename is
never made durable, and a crash keeping `nm` would contradict the committed absence; see the W4
implementation log. -/
abbrev wal.Create.spec (P : WalPbIn GF) (Mr : WalMarshal) : Prop :=
  ∀ (lg : Loc) (R : Roots) (jr : Ino) (r dir nm : GoString) (mp : GoSlice) (md : List w8) (qp : Qp)
    (Q : IProp GF) (Pv : Option WalDur → Prop),
  InArea r dir nm → NameOk nm → dir.length < 2 ^ 59 → cleanAbsPath r → mp ≠ slice.nil →
  md.length < 2 ^ 41 → md ≠ [] → WalMarshalCreateOk Mr →
  FsNoErrOn (fun p => p = dir ∨ p = dir ++ go!".tmp" ∨ p = r) ∧ PathFits (dir ++ go!".tmp") ∧ PathFits dir →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗ zapLoggerOk lg ∗
      mp ↦*□ md ∗ WalFs.walAreaOk walCodec Mr R jr r ∗ WalFs.dirDurable r ∗ osPathS R r (DFrac.own qp) jr ∗
      walAreaRes jr ∗ osCallPerm (callKey R r) 1 ∗ WalFs.walUnlockedTok ∗
      AU <{ ∃∃ o : Option WalDur, WalFs.walDirIs dir o ∗ ⌜Pv o⌝ }> @ walAuMask, ∅
        <{ WalFs.walDiskAt dir (walDurFresh md), COMM Q }> }}
    (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.wal.Create)) (Val #lg)) (Val #dir))
      (Val #mp))
  {{ (w : Loc) (err : GoInterface), RET (PairV #w #err);
      osPathS R r (DFrac.own qp) jr ∗ walAreaRes jr ∗
      ((⌜err = interface.nil⌝ ∗ Q ∗ walOpenWF P Mr w dir ∗ WalFs.walNamed dir ∗ WalFs.walLenLb w dir 0 ∗
          WalFs.walSyncedLb dir 0 ∗ WalFs.walPurgeW w dir ∗ osCallPerm (callKey R r) (1 : Qp).half) ∨
        (⌜err ≠ interface.nil⌝ ∗ osCallPerm (callKey R r) 1 ∗ WalFs.walUnlockedTok ∗
          AU <{ ∃∃ o : Option WalDur, WalFs.walDirIs dir o ∗ ⌜Pv o⌝ }> @ walAuMask, ∅
        <{ WalFs.walDiskAt dir (walDurFresh md), COMM Q }>) ∨
        (⌜err ≠ interface.nil⌝ ∗ Q ∗ osCallPerm (callKey R r) (1 : Qp).half)) }}

end spec

end EtcdGrove
end Perennial
