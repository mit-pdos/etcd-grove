/-
`validSnapshotEntries(lg, dir)` (S/wal.go:723-791), one attempt of `ValidSnapshotEntries`, over what the
caller's pin holds (W8 of `notes/wal-fsext-plan.md`; `VsePin.lean`): not atomic, since
`ValidSnapshotEntries` commits its update and pins the segments once, before its retry loop.

* `specPinned`: the WAL `d` pinned in the directory `lay.j` (`VsePinOk`: its layout, its tail idle), the
  program's halves of every segment and of the directory's claim, a path to the directory: the names
  read (`readWALNames`), every segment opened read-only and decoded, the snapshot records at or below the
  last state's commit returned (`walValidSnaps` of the history from the read position), or an error; the
  resources back.
* `specAbsent`: no WAL at `r/nm` (the area's claim holds nothing there): `readWALNames` fails.

Both errors come with `errors.Is(err, os.ErrNotExist)`'s termination (`vseErrIs`: the retry test).
Lean-first; proved in `LinuxFs/Proof/go_etcd_io/etcd/server/v3/storage/wal/validSnapshotEntries.lean`.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.VsePin
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.PkgInit
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.WalDisk
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

/-- **`errors.Is(err, os.ErrNotExist)` returns** (persistent): `ValidSnapshotEntries`' retry test on an
error of `validSnapshotEntries`. -/
def wal.vseErrIs (err : GoInterface) : IProp GF :=
  iprop(□ ∀ nx : GoInterface, globalAddr _root_.Perennial.os.ErrNotExist ↦□ nx -∗
    {{ isPkgInit (PROP := IProp GF) pkg_id.errors }}
      (App (App (Val (@! _root_.Perennial.errors.Is)) (Val #err)) (Val #nx))
    {{ (b : Bool), RET #b; True }})

instance wal.vseErrIs_persistent (err : GoInterface) : Persistent (wal.vseErrIs (GF := GF) err) := by
  unfold wal.vseErrIs; infer_instance

/-- See the file header. -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.validSnapshotEntries.specPinned (Mr : WalMarshal) : Prop :=
  ∀ (lg : Loc) (R : Roots) (jr : Ino) (r dir : GoString) (qd : Qp) (d : WalDur) (lay : WalLay)
    (X : List GoString) (hj : NamesH),
  VsePinOk walCodec Mr jr d lay X hj → dir.length < 2 ^ 59 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗ zapLoggerOk lg ∗
      WalFs.walAreaOk walCodec Mr R jr r ∗ osPathS R dir (DFrac.own qd) lay.j ∗ osCallPerm 1 ∗
      ([∗list] g ∈ lay.segs, segRes g) ∗ osNames lay.j (.except X) (DFrac.own (1 : Qp).half) hj }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.wal.validSnapshotEntries)) (Val #lg)) (Val #dir))
  {{ (sl : GoSlice) (err : GoInterface), RET (PairV #sl #err);
      osPathS R dir (DFrac.own qd) lay.j ∗ osCallPerm 1 ∗
      ([∗list] g ∈ lay.segs, segRes g) ∗ osNames lay.j (.except X) (DFrac.own (1 : Qp).half) hj ∗
      ((⌜err ≠ GoInterface.nil⌝ ∗ wal.vseErrIs err) ∨
       (⌜err = GoInterface.nil⌝ ∗ ∃ ps : List Loc, sl ↦*□ ps ∗
          walSnapsAt ps (walValidSnaps (d.H.map WalOpG.toM) d.cut))) }}

/-- See the file header. -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.validSnapshotEntries.specAbsent : Prop :=
  ∀ (lg : Loc) (R : Roots) (r nm : GoString) (j : Ino) (qp : Qp) (N : NameSet) (h : NamesH),
  NameOk nm → N.Mem nm → h.cur !! nm = none →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗ zapLoggerOk lg ∗
      osInv (GF := GF) ∗ osSharedInv (GF := GF) R ∗ osPathS R r (DFrac.own qp) j ∗ osCallPerm 1 ∗
      osNames j N (DFrac.own (1 : Qp).half) h }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.wal.validSnapshotEntries)) (Val #lg))
      (Val #(child r nm)))
  {{ (sl : GoSlice) (err : GoInterface), RET (PairV #sl #err);
      osPathS R r (DFrac.own qp) j ∗ osCallPerm 1 ∗ osNames j N (DFrac.own (1 : Qp).half) h ∗
      ⌜err ≠ GoInterface.nil⌝ ∗ wal.vseErrIs err }}

end spec

end EtcdGrove
end Perennial
