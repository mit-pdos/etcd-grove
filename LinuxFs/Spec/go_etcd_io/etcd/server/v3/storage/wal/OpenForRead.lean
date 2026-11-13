/-
`OpenForRead(lg, dirpath, snap)` (S/wal.go:392-397): `openAtIndex(…, false)`, read mode: the files
opened read-only, no locks, no pipeline; `ReadAll` then tolerates a torn last record
(`io.ErrUnexpectedEOF`). Its callers (`Verify`, W8) hold the lock token, as `ValidSnapshotEntries`'s
spec (the main tree's) does; the update commits unchanged where the files are pinned. *Success*: the
read handle (`walReadOnlyF`, with the token) and the whole call permission (no pipeline). *Error*:
the token and the permission back. Lean-first; proof `sorry`
(`LinuxFs/Proof/go_etcd_io/etcd/server/v3/storage/wal/OpenForRead.lean`, from `openAtIndex`'s). W5
of `notes/wal-fsext-plan.md`.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadDefs
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.PkgInit
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

/-- See the file header. -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.OpenForRead.spec (Mr : WalMarshal) : Prop :=
  ∀ (lg : Loc) (R : Roots) (jr : Ino) (r dir nm : GoString) (sp : Loc) (s : w64 × w64) (qp : Qp)
    (Q : Option WalDur → IProp GF),
  InArea r dir nm → cleanAbsPath r →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗ zapLoggerOk lg ∗
      WalFs.walAreaOk walCodec Mr R jr r ∗ osPathS R r (DFrac.own qp) jr ∗ walAreaRes jr ∗
      osCallPerm 1 ∗ walSnapIdTerm sp s ∗ WalFs.walUnlockedTok ∗
      AU <{ ∃∃ o : Option WalDur, WalFs.walDirIs dir o }> @ walAuMask, ∅
        <{ WalFs.walDirIs dir o, COMM Q o }> }}
    (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.wal.OpenForRead)) (Val #lg))
      (Val #dir)) (Val #sp))
  {{ (w : Loc) (err : GoInterface), RET (PairV #w #err);
      osPathS R r (DFrac.own qp) jr ∗ walAreaRes jr ∗ osCallPerm 1 ∗ ∃ o : Option WalDur, Q o ∗
      ((⌜err ≠ GoInterface.nil⌝ ∗ WalFs.walUnlockedTok) ∨
       (⌜err = GoInterface.nil⌝ ∗ ⌜o ≠ none⌝ ∗ walReadOnlyF w dir s)) }}

end spec

end EtcdGrove
end Perennial
