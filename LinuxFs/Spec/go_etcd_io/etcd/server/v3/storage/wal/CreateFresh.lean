/-
**A hypothesis** (not proved, not an axiom): `wal.Create(lg, dir, md)` as `Create.lean`'s spec, its
update taken from any state `Exist`'s `false` arm allows (`wal.ExistFalseOk`: no WAL, or a fresh,
unnamed one), not only from `walAbsent dir`. The tester's `Boot` (W4c U5, B3) needs it: `Boot` calls
`Create` after `Exist` returned `false`, and the WAL may then be a fresh, unnamed one, which a crash
keeps (`AbsDisk/Impl.lean`'s `walCrash` keeps `named = false`: a WAL that survived a kill between
`Create`'s rename and its parent's fsync may survive the next crash too) and `Create`'s cleanup after
a failed fsync may have moved aside (`cleanupWAL`, no fsync).

Why it is true of the Go code: `Create` calls `Exist(dir)` first and returns `os.ErrExist`, before
any effect, when it finds a `.wal` file; a fresh WAL whose directory is at `dir` holds its first
segment (F-N1), so `Create` proceeds only when the unnamed WAL's directory is not at `dir` (moved
aside, or its rename lost), and then `renameWAL`'s `RemoveAll(dir)` and the rename of `dir.tmp` put the
new fresh WAL in place, as from an absent one. Proving it is the WAL layer's (`Create.lean`'s proof
with the creating update generalized to `ExistFalseOk`; the invariant must allow the commit to
replace an unnamed, empty WAL whose directory is not at its name). The stronger `Create.spec`
(`o = none`) is the special case. Lean-first.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateDefs
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateSnap
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Handle
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.PkgInit
public import LinuxFs.GeneratedProof.go_etcd_io.etcd.server.v3.storage.wal
public import Spec.go_uber_org.zap.Defs
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.Exist

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
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗ zapLoggerOk lg ∗
      mp ↦*□ md ∗ WalFs.walAreaOk walCodec Mr R jr r ∗ WalFs.dirDurable r ∗ osPathS R r (DFrac.own qp) jr ∗
      walAreaRes jr ∗ osCallPerm 1 ∗ WalFs.walUnlockedTok ∗
      AU <{ ∃∃ o : Option WalDur, WalFs.walDirIs dir o ∗ ⌜wal.ExistFalseOk o⌝ }> @ walAuMask, ∅
        <{ WalFs.walDiskAt dir (walDurFresh md), COMM Q }> }}
    (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.wal.Create)) (Val #lg)) (Val #dir))
      (Val #mp))
  {{ (w : Loc) (err : GoInterface), RET (PairV #w #err);
      osPathS R r (DFrac.own qp) jr ∗ walAreaRes jr ∗
      ((⌜err = interface.nil⌝ ∗ Q ∗ walOpenWF P Mr w dir ∗ WalFs.walNamed dir ∗ WalFs.walLenLb w dir 0 ∗
          WalFs.walSyncedLb dir 0 ∗ WalFs.walPurgeW w dir ∗ osCallPerm (1 : Qp).half) ∨
        (⌜err ≠ interface.nil⌝ ∗ osCallPerm 1 ∗ WalFs.walUnlockedTok ∗
          AU <{ ∃∃ o : Option WalDur, WalFs.walDirIs dir o ∗ ⌜wal.ExistFalseOk o⌝ }> @ walAuMask, ∅
        <{ WalFs.walDiskAt dir (walDurFresh md), COMM Q }>) ∨
        (⌜err ≠ interface.nil⌝ ∗ Q ∗ osCallPerm (1 : Qp).half)) }}

end spec

end EtcdGrove
end Perennial
