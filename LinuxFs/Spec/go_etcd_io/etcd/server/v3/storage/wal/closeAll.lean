/-
`closeAll(lg, rcs...)` (S/wal.go:1187-1199): closes each of `rcs`, logging (`lg.Warn`) and
collecting the message of each `Close` error; returns `nil`, or `errors.New` of the messages
joined. Over `wal.rcFile` (`CloseDefs.lean`): each a `*os.File` or a `*fileutil.LockedFile` with
its file and fd whole, which the call consumes (the files are closed). The error, if any, is one
whose `Error()` returns (`errOk`). Proved in
`LinuxFs/Proof/go_etcd_io/etcd/server/v3/storage/wal/closeAll.lean`. W5 of
`notes/wal-fsext-plan.md`; Lean-first.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CloseDefs
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.PkgInit
public import Spec.go_uber_org.zap.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open Fs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]

/-- See the file header. -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.closeAll.spec : Prop :=
  ∀ (lg : Loc) (sl : GoSlice) (rcs : List GoInterface) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗ zapLoggerOk lg ∗
      osInv (GF := GF) ∗ sl ↦*{dq} rcs ∗ [∗list] rc ∈ rcs, wal.rcFile rc }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.wal.closeAll)) (Val #lg)) (Val #sl))
  {{ (err : GoInterface), RET #err; sl ↦*{dq} rcs ∗
      (⌜err = interface.nil⌝ ∨ ∃ e : GoInterfaceOk, ⌜err = GoInterface.ok e⌝ ∗ errOk e) }}

end spec

end EtcdGrove
end Perennial
