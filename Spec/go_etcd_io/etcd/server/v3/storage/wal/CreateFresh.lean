/-
`wal.Create(lg, dir, md)` from any state `Exist`'s `false` arm allows (`wal.ExistFalseOk`: no WAL, or a
fresh, unnamed one): `Create.lean`'s spec at the client's view predicate `Pv := wal.ExistFalseOk`. The
tester's `Boot` (W4c U5, B3) calls `Create` after `Exist` returned `false`. Until 2026-11-15 a hypothesis
(`Create.spec` then took its update from `walAbsent dir` only); now **proved**, a corollary of
`Create.spec` (`Proof/go_etcd_io/etcd/server/v3/storage/wal/CreateFresh.lean`,
`wal.Create.wp_specFresh`), whose update starts from any view of `dir`: `Create` commits only when the
real state has no WAL there (its own `Exist` check, the lock token held), so the view is `none` at the
commit (`notes/wal-units/fresh.md`). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateDefs
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateSnap
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.Handle
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.PkgInit
public import GeneratedProof.go_etcd_io.etcd.server.v3.storage.wal
public import Spec.go_uber_org.zap.Defs
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.Exist

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

/-- See the file header. -/
abbrev wal.Create.specFresh (P : WalPbIn GF) (Mr : WalMarshal) : Prop :=
  ∀ (lg : Loc) (R : Roots) (jr : Ino) (r dir nm : GoString) (mp : GoSlice) (md : List w8) (qp : Qp)
    (Q : IProp GF),
  InArea r dir nm → NameOk nm → dir.length < 2 ^ 59 → cleanAbsPath r → mp ≠ slice.nil →
  md.length < 2 ^ 41 → md ≠ [] → WalMarshalCreateOk Mr →
  FsNoErrOn (fun p => p = dir ∨ p = dir ++ go!".tmp" ∨ p = r) ∧ PathFits (dir ++ go!".tmp") ∧ PathFits dir →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗ zapLoggerOk lg ∗
      mp ↦*□ md ∗ WalFs.walAreaOk walCodec Mr R jr r ∗ WalFs.dirDurable r ∗ osPathS R r (DFrac.own qp) jr ∗
      walAreaRes jr ∗ osCallPerm (callKey R r) 1 ∗ WalFs.walUnlockedTok ∗
      AU <{ ∃∃ o : Option WalDur, WalFs.walDirIs dir o ∗ ⌜wal.ExistFalseOk o⌝ }> @ walAuMask, ∅
        <{ WalFs.walDiskAt dir (walDurFresh md), COMM Q }> }}
    (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.wal.Create)) (Val #lg)) (Val #dir))
      (Val #mp))
  {{ (w : Loc) (err : GoInterface), RET (PairV #w #err);
      osPathS R r (DFrac.own qp) jr ∗ walAreaRes jr ∗
      ((⌜err = interface.nil⌝ ∗ Q ∗ walOpenWF P Mr w dir ∗ WalFs.walNamed dir ∗ WalFs.walLenLb w dir 0 ∗
          WalFs.walSyncedLb dir 0 ∗ WalFs.walPurgeW w dir ∗ osCallPerm (callKey R r) (1 : Qp).half) ∨
        (⌜err ≠ interface.nil⌝ ∗ osCallPerm (callKey R r) 1 ∗ WalFs.walUnlockedTok ∗
          AU <{ ∃∃ o : Option WalDur, WalFs.walDirIs dir o ∗ ⌜wal.ExistFalseOk o⌝ }> @ walAuMask, ∅
        <{ WalFs.walDiskAt dir (walDurFresh md), COMM Q }>) ∨
        (⌜err ≠ interface.nil⌝ ∗ Q ∗ osCallPerm (callKey R r) (1 : Qp).half)) }}

end spec

end EtcdGrove
end Perennial
