/-
`wal.openLast(lg, dirpath)` (S/repair.go:113-121): `readWALNames(lg, dirpath)`, then
`fileutil.LockFile(filepath.Join(dirpath, names[len(names)-1]), os.O_RDWR, PrivateFileMode)`.
`Repair`'s callee (W7 of `notes/wal-fsext-plan.md`; the W7-W12 log, eighth session). `Repair.spec`'s
premises and resources (the area's, the lock token framed, the client's update): the update commits
unchanged at the first step, with the pin of the WAL's last segment (`walInv_openLast`, law L1). On
success the pin, a path to the WAL directory and the last segment's file opened read-write and locked
(`walLastOpen`); on an error (no WAL: the directory's read fails; the lock's open fails) the pin put back
and the token returned. The update's result `o` is the client's `Q o`; a success had a WAL (`o ≠ none`).

`openLast.specHeld` (2026-11-15, the lock semantics; `notes/wal-units/locks.md`, item 5): the path where
the last segment's lock is still held through another open file description (a WAL handle whose `Close`
failed before its locks were released, `openWALFromSnapshot`'s ignored `w.Close()`): with the directory
claim's share that handle holds (a path to `dir`, `osNames j (.except X)` at the layout's names: the
segments `segs` named in name order, the last `gL`), and the held lock `osLock k gL.ino fd` of
`fileutil`'s kind, `openLast` returns only an error (`LockFile`'s success is excluded,
`fileutil.lockPost_held`; a blocking `LockFile` that never returns satisfies any post); nothing changes,
the held lock is kept. Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.OpenLastDefs
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.PkgInit
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateDefs
public import GeneratedProof.go_etcd_io.etcd.server.v3.storage.wal
public import Proof.go_etcd_io.etcd.client.pkg.v3.fileutil.LockDefs

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
  ∀ (lg : Loc) (R : Roots) (jr : Ino) (r dir nm : GoString) (qp : Qp) (Q : Option WalDur → IProp GF) (ic : Nat),
  InArea r dir nm → NameOk nm → cleanAbsPath r → PathFits dir →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗ zapLoggerOk lg ∗
      WalFs.walAreaOk walCodec Mr R jr r ∗ osPathS R r (DFrac.own qp) jr ∗ walAreaRes jr ∗
      osCallPerm (callKey R r) 1 ∗ WalFs.walUnlockedTok ∗
      AU <{ ∃∃ o : Option WalDur, WalFs.walDirIsI dir ic o }> @ walAuMask, ∅
        <{ WalFs.walDirIsI dir ic o, COMM Q o }> }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.wal.openLast)) (Val #lg)) (Val #dir))
  {{ (lf : Loc) (err : GoInterface), RET (PairV #lf #err); osPathS R r (DFrac.own qp) jr ∗
      walAreaRes jr ∗ osCallPerm (callKey R r) 1 ∗ ∃ o : Option WalDur, Q o ∗
      ((⌜err ≠ GoInterface.nil⌝ ∗ WalFs.walUnlockedTok) ∨
       (⌜err = GoInterface.nil ∧ o ≠ none⌝ ∗ walLastOpen walCodec Mr R jr dir lf)) }}

/-- See the file header (`specHeld`). -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.openLast.specHeld : Prop :=
  ∀ (lg : Loc) (R : Roots) (dir : GoString) (j : Ino) (X : List GoString) (hj : NamesH)
    (segs : List SegG) (gL : SegG) (qd : Qp) (dqn : DFrac) (k : LockKind) (fd : w64),
  (∀ b ∈ X, walNameP b = false) → SegsNamed segs hj.cur → walInos hj.cur = segs.map (·.ino) →
  (segs.map (·.ino)).Nodup → (segs.map (·.name)).Pairwise (fun a b => go.GoStringLt a b) →
  (∀ g ∈ segs, ∃ sq ix : Nat, g.name = walFileName sq ix) → segs.getLast? = some gL →
  PathFits dir →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗ zapLoggerOk lg ∗
      osInv (GF := GF) ∗ osSharedInv (GF := GF) R ∗ osPathS (GF := GF) R dir (DFrac.own qd) j ∗
      osCallPerm (GF := GF) (callKey R dir) 1 ∗ osNames (GF := GF) j (.except X) dqn hj ∗
      osLock (GF := GF) k gL.ino fd ∗ fileutil.lockKind (GF := GF) k }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.wal.openLast)) (Val #lg)) (Val #dir))
  {{ (lf : Loc) (err : GoInterface), RET (PairV #lf #err); ⌜err ≠ GoInterface.nil⌝ ∗
      osPathS R dir (DFrac.own qd) j ∗ osCallPerm (callKey R dir) 1 ∗ osNames j (.except X) dqn hj ∗
      osLock k gL.ino fd }}

end spec

end EtcdGrove
end Perennial
