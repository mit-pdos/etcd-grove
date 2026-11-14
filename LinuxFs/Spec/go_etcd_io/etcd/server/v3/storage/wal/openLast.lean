/-
`wal.openLast(lg, dirpath)` (S/repair.go:113-121): `readWALNames(lg, dirpath)`, then
`fileutil.LockFile(filepath.Join(dirpath, names[len(names)-1]), os.O_RDWR, PrivateFileMode)`.
`Repair`'s callee (W7 of `notes/wal-fsext-plan.md`; the W7-W12 log, eighth session). `Repair.spec`'s
premises and resources (the area's, the lock token framed, the client's update): the update commits
unchanged at the first step, with the pin of the WAL's last segment (`walInv_openLast`, law L1). On
success the pin, a path to the WAL directory and the last segment's file opened read-write and locked
(`walLastOpen`); on an error (no WAL: the directory's read fails; the lock's open fails) the pin put back
and the token returned. The update's result `o` is the client's `Q o`; a success had a WAL (`o ≠ none`).
Lean-first.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.OpenLastDefs
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.PkgInit
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateDefs
public import LinuxFs.GeneratedProof.go_etcd_io.etcd.server.v3.storage.wal

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
abbrev go_etcd_io.etcd.server.v3.storage.wal.openLast.spec (Mr : WalMarshal) : Prop :=
  ∀ (lg : Loc) (R : Roots) (jr : Ino) (r dir nm : GoString) (qp : Qp) (Q : Option WalDur → IProp GF),
  InArea r dir nm → NameOk nm → cleanAbsPath r → dir.length < 2 ^ 59 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗ zapLoggerOk lg ∗
      WalFs.walAreaOk walCodec Mr R jr r ∗ osPathS R r (DFrac.own qp) jr ∗ walAreaRes jr ∗
      osCallPerm 1 ∗ WalFs.walUnlockedTok ∗
      AU <{ ∃∃ o : Option WalDur, WalFs.walDirIs dir o }> @ walAuMask, ∅
        <{ WalFs.walDirIs dir o, COMM Q o }> }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.wal.openLast)) (Val #lg)) (Val #dir))
  {{ (lf : Loc) (err : GoInterface), RET (PairV #lf #err); osPathS R r (DFrac.own qp) jr ∗
      walAreaRes jr ∗ osCallPerm 1 ∗ ∃ o : Option WalDur, Q o ∗
      ((⌜err ≠ GoInterface.nil⌝ ∗ WalFs.walUnlockedTok) ∨
       (⌜err = GoInterface.nil ∧ o ≠ none⌝ ∗ walLastOpen walCodec Mr R jr dir lf)) }}

end spec

end EtcdGrove
end Perennial
