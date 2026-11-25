/-
`(*wal.WAL).Close()` (S/wal.go:1053-1077) over `fsExt` (W10 of `notes/wal-fsext-plan.md`). One spec since
wal-link L1a (2026-11-17, `notes/wal-link-scope.md` §8: the former `Close.spec`, `specNoErr`, `specFailed`,
`specOpening` and `specU` merged), over the state of the handle it closes (`WalCloseSt`, `HandleShared.lean`),
each state's precondition and result one arm:

* **`shared γ`**, a WAL opened to append, the whole share of its handle (`walOpenWS … 1`): the main tree's
  axiom's first conjunct (`Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__Close.lean`) with plan §3's
  binders (the area `R jr r`, the update at `walAuMask`) and §6 Q6's honest error arm; `SpecPlan/`'s `Close`
  (the purge right consumed, the lock token back) is the same contract. The error arm only when `Sio` does not
  cover every inode (the former `specNoErr`: no error then).
* **`failed`**, the handle a failed `ReadAll` leaves (`walReadFailedF`, `ReadDefs.lean`): the put-back of a
  failed read (the tail unregistered, the segments', the directory claim's and the pipeline's halves back to
  `walInv`'s parked state, the lock token back). On an error the token may be lost (after `ReadAll`'s
  `ZeroToEnd` or its fdatasync failed the tail may be left in a resize window, which only `Close`'s own
  fdatasync closes); the error result then hands back what the handle held of the directory
  (`walCloseLeft dir`, `CloseLeft.lean`), exactly what `wal.Repair.specHeld` takes (`CloseFailedRepair.lean`;
  ledger 2026-11-14 and 2026-11-15).
* **`opening s`**, a handle `openAtIndex` made in write mode before `Open` set its `dirFile` (S/wal.go:391,
  `fileutil.OpenDir` failed): the WAL's halves back to `walInv`'s parked state, the lock token back, whatever
  the result (`Open`'s error arm).
* **`unnamed Rp qp tf`**, `Create`'s handle before naming (`walOpenWFU`, `Create`'s `cleanupWAL`; ledger
  2026-11-14): `shared`'s effects with nothing committed (see the arm).

Proved in `Proof/.../wal/WAL__Close.lean` (the states' proofs its lemmas). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.HandleShared
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadDefs
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.PkgInit
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CloseLeft
public import Proof.go_etcd_io.etcd.server.v3.storage.WalDisk
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
variable {Sio : IoSet} [FsStepSat (NoIoErr Sio)]

/-- **`w.Close()`** (see the file header for each state `m`). *`shared`*: closes the file pipeline, syncs the
tail (every record of the history: `walSyncedLb`), closes every lock's file and the directory's; the purge
right is consumed (`walPurgeW`: `Close` unlocks every file, so the purge must have stopped). The update
commits after the sync, the state unchanged (the synced mark a lower bound); then the WAL's files go back to
the WAL invariant and the generation's lock token comes back (`walUnlockedTok`), with the half of the call
permission the handle held (the client holds the other half while the WAL is open: ledger 2026-11-14).
`nil` when `Sio` covers every inode; otherwise the sync may fail (`Close` returns before it unlocks,
S/wal.go:1064-1066: the handle, its files and the token are lost), or the directory's `Close` may fail after
everything else was done (the success resources come back too). *`failed`*, *`opening`*: the lock token
and the call permission's half back (`failed`: or, on an error, `walCloseLeft dir`). *`unnamed`*: the free
lock token back but for its names fragment (`walUnlockedTokX`), the names fragment `some dir` (`Create`'s
pending registration), the call permission's half, the two pinned paths to `dir` (the handle's and the
pipeline's, at `Rp` and `qp`), the `dir` field (`cleanupWAL` reads it after `Close`) and the tail's
`*os.File` closed, whatever `err`; or, the sync failed, the lock token still held (`walLockedTok`) with the
names fragment and the tail's file open with its fd (`Create`'s deferred `f.Close()` runs on it). -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.WAL.Close.spec (P : WalPbIn GF) (Mr : WalMarshal) : Prop :=
  ∀ (R : Roots) (jr : Ino) (r : GoString) (w : Loc) (dir : GoString) (m : WalCloseSt)
    (Q : WalDur → IProp GF),
  {{ WalFs.walAreaOk walCodec Mr R jr r ∗
      match m with
      | .shared γ => iprop(walOpenWS Sio P Mr w dir γ 1 ∗ WalFs.walPurgeW w dir ∗
          AU <{ ∃∃ d : WalDur, WalFs.walDiskAtI dir γ.inc d }> @ walAuMask, ∅
            <{ WalFs.walDiskAtI dir γ.inc d, COMM Q d }>)
      | .failed => iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗
          walReadFailedF Mr w dir)
      | .opening s => iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗
          WalFs.walOpening w dir s ∗ walReadH true w dir s ∗ osCallPerm (callKey R dir) (1 : Qp).half.half ∗
          structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"dirFile" w ↦ (null : Loc))
      | .unnamed Rp qp tf => iprop(walOpenWFU P Mr w dir Rp qp tf ∗ WalFs.walPurgeW w dir) }}
    (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!! go!"Close"))
      (Val #()))
  {{ (err : GoInterface), RET #err;
      match m with
      | .shared γ => iprop((⌜walCov Sio → err = GoInterface.nil⌝ ∗ ∃ d : WalDur, Q d ∗
            WalFs.walSyncedLb dir γ.inc d.H.length ∗ WalFs.walUnlockedTok ∗ osCallPerm (callKey R dir) (1 : Qp).half) ∨
          ⌜err ≠ GoInterface.nil ∧ ¬ walCov Sio⌝)
      | .failed => iprop((WalFs.walUnlockedTok ∗ osCallPerm (callKey R dir) (1 : Qp).half) ∨
          (⌜err ≠ GoInterface.nil⌝ ∗ WalFs.walCloseLeft dir))
      | .opening _ => iprop(WalFs.walUnlockedTok ∗ osCallPerm (callKey R dir) (1 : Qp).half)
      | .unnamed Rp qp tf => iprop(
          (fmtErrorOkOrNil err ∗ structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"dir" w ↦ dir ∗
            WalFs.walUnlockedTokX ∗ WalFs.walNamesFrag (some dir) ∗ osCallPerm (callKey R dir) (1 : Qp).half ∗
            (∃ j : Ino, osPathS Rp dir (DFrac.own qp) j ∗ osPathS Rp dir (DFrac.own qp) j) ∗
            ∃ nmf : GoString, os.ownFile tf (-1 : w64) nmf (DFrac.own 1)) ∨
          (⌜err ≠ GoInterface.nil⌝ ∗ fmtErrorOk err ∗ WalFs.walLockedTok ∗ WalFs.walNamesFrag (some dir) ∗
            ∃ (fd : w64) (nmf : GoString) (d : OsFd),
              os.ownFile tf fd nmf (DFrac.own 1) ∗ osFd fd (DFrac.own 1) d ∗ fdLocks fd d)) }}

end spec

end EtcdGrove
end Perennial
