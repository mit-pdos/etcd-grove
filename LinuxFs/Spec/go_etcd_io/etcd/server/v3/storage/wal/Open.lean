/-
`wal.Open` over `fsExt` (W5 of `notes/wal-fsext-plan.md`): the main tree's axiom
`Spec/go_etcd_io/etcd/server/v3/storage/wal/Open.lean` restated with plan §3's binder changes (over
`fsExt`, the WAL layer `walAreaOk`, the area's spine and `walAreaRes` as `Create`'s, the call
permission, the handle `walOpeningF`, the update at `walAuMask`, plan §11). S/ =
`server/storage/wal/` at the pin with the local fork patches. To be proved in
`LinuxFs/Proof/go_etcd_io/etcd/server/v3/storage/wal/Open.lean`. Lean-first.
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

/-- **`Open(lg, dir, snap)`** (S/wal.go:385-397, write mode): `openAtIndex` (`selectWALFiles`:
`readWALNames`, `searchIndex`, `isValidSeq`; `openWALFiles`: `TryLockFile` of each file from the
last one named at most `s.1`, `NewFileReader`; `NewDecoder`; the pipeline), then
`fileutil.OpenDir(dir)`. As the main tree's: the update raises `unl` to `walOpenPos` (bookkeeping
until the lock model, plan §6 Q1: the raise is vacuous), commits on both arms, and fails with no WAL
(`readWALNames`: `ErrFileNotFound`). The `lg.Panic`s of `searchIndex`/`isValidSeq` are
unreachable: every `.wal` name of a WAL directory is a segment's (`walNameStr`, the invariant's
`WalDirClaim`), and `checkWALNames` keeps only names that parse. *Success*: the read handle
(`walOpeningF`, with the lock token) and half the call permission (the other half is the pipeline's,
as `Create`'s, plan §11). *Error*: the token and the whole permission back. -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.Open.spec (Mr : WalMarshal) : Prop :=
  ∀ (lg : Loc) (R : Roots) (jr : Ino) (r dir nm : GoString) (sp : Loc) (s : w64 × w64) (qp : Qp)
    (Q : Option WalDur → IProp GF),
  InArea r dir nm → NameOk nm → cleanAbsPath r → dir.length < 2 ^ 59 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗ zapLoggerOk lg ∗
      WalFs.walAreaOk walCodec Mr R jr r ∗ osPathS R r (DFrac.own qp) jr ∗ walAreaRes jr ∗
      osCallPerm 1 ∗ walSnapIdTerm sp s ∗ WalFs.walUnlockedTok ∗
      AU <{ ∃∃ o : Option WalDur, WalFs.walDirIs dir o }> @ walAuMask, ∅
        <{ WalFs.walDirIs dir (o.map (fun d =>
            { d with unl := max d.unl (walOpenPos (d.H.map WalOpG.toM) s.1) })), COMM Q o }> }}
    (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.wal.Open)) (Val #lg)) (Val #dir))
      (Val #sp))
  {{ (w : Loc) (err : GoInterface), RET (PairV #w #err);
      osPathS R r (DFrac.own qp) jr ∗ walAreaRes jr ∗ ∃ o : Option WalDur, Q o ∗
      ((⌜err ≠ GoInterface.nil⌝ ∗ WalFs.walUnlockedTok ∗ osCallPerm 1) ∨
       (⌜err = GoInterface.nil⌝ ∗ ⌜o ≠ none⌝ ∗ walOpeningF w dir s ∗ osCallPerm (1 : Qp).half)) }}

end spec

end EtcdGrove
end Perennial
