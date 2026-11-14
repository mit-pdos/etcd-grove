/-
`(*wal.WAL).Close()` (S/wal.go:1053-1077) of a handle `openAtIndex` made in write mode, before
`Open` set its `dirFile` (S/wal.go:391: `fileutil.OpenDir` failed): the pipeline closed (its half of
the call permission and its pipeline names back), `w.sync()` of the tail (no encoder: an fdatasync),
each lock closed, and `Close` of the nil `*os.File` (`ErrInvalid`). The WAL's halves go back to
`walInv`'s parked state and the lock token comes back (`walInvBody_unpin`); the ghost handle
`walOpening` goes. Any error (the sync's: the Go code then returns early, its locks left open; the
lock token still comes back, the halves being ghost). **A minimal statement for `Open`'s error arm**
(W3/W5 log, thirteenth session), a callee spec of `Open.wp_proof`; proved by
`WAL.Close.wp_proofOpening` (`LinuxFs/Proof/.../wal/WAL__CloseOpening.lean`, the W7-W12 log's eighth
session). Lean-first.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadDefs
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.PkgInit

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

/-- See the file header. -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.WAL.Close.specOpening (Mr : WalMarshal) : Prop :=
  ∀ (R : Roots) (jr : Ino) (r : GoString) (w : Loc) (dir : GoString) (s : w64 × w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗
      WalFs.walAreaOk walCodec Mr R jr r ∗
      WalFs.walOpening w dir s ∗ walReadH true w dir s ∗ osCallPerm (1 : Qp).half ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"dirFile" w ↦ (null : Loc) }}
    (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!! go!"Close"))
      (Val #()))
  {{ (err : GoInterface), RET #err; WalFs.walUnlockedTok ∗ osCallPerm 1 }}

end spec

end EtcdGrove
end Perennial
