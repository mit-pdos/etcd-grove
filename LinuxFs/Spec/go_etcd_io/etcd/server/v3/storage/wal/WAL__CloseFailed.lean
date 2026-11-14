/-
`(*wal.WAL).Close()` (S/wal.go:1053-1077) of the handle a failed `ReadAll` leaves (`walReadFailedF`,
`ReadDefs.lean`): the put-back of a failed read. The pipeline closed (its quarter of the call permission
back), `w.sync()` of the tail, each lock closed, `w.dirFile` closed; the tail unregistered, the segments'
halves, the directory claim's half and the pipeline names back to `walInv`'s parked state, the lock token
back from the ghost handle (`walReadFailed`), with the half of the call permission the handle and its
pipeline held (the client holds the other half since `Open`). Whatever `Close` answers, as
`Close.specOpening` (the sync's error returns before the locks; the token comes back, the halves being
ghost). The tester's `restartRead` (`examples/etcd/wal/wal.go`, `w.Close()` after a failed `ReadAll`, then
`Repair`, which takes the token) is its client.

**Stated, not proved** (W4c U5, fourth session; `notes/wal-fsext-w4c-plan.md`, the U5 log): its proof needs
`walReadFailedF`'s body to keep what every error exit of `ReadAll` holds, and two steps the invariant has no
law for yet: the unregistration of a tail registered, not yet zeroed (the exits before `ZeroToEnd`), and the
put-back of a tail left by a failed `ZeroToEnd` or fdatasync (whose specs lose the tail on an error).
Lean-first.
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
abbrev go_etcd_io.etcd.server.v3.storage.wal.WAL.Close.specFailed (Mr : WalMarshal) : Prop :=
  ∀ (R : Roots) (jr : Ino) (r : GoString) (w : Loc) (dir : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗
      WalFs.walAreaOk walCodec Mr R jr r ∗ walReadFailedF w dir }}
    (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!! go!"Close"))
      (Val #()))
  {{ (err : GoInterface), RET #err; WalFs.walUnlockedTok ∗ osCallPerm (1 : Qp).half }}

end spec

end EtcdGrove
end Perennial
