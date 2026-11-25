/-
`(*wal.WAL).cleanupWAL(lg)` (S/wal.go:300-317, with the fork's fix: it returns its error instead of
panicking; W4 of `notes/wal-fsext-plan.md`, `notes/wal-units/create.md`): `Create`'s deferred cleanup
after its commit, over the handle before naming at its incarnation `i` (`walOpenWFUI`, design P; the
lock token comes back at `i` when no rename was called, for the caller's registration: ledger 2026-11-25). `w.Close()`
(`WAL.Close.spec` (state `unnamed`)), then, if it returned `nil`, `os.Rename(w.dir, w.dir + ".broken." + <time>)`
(`os.Rename.specDirAnySnc`). Internal and `Create`-specific: the rename's claims and atomic update
are the caller's, given by a law at the timestamp (the claim on `nm` and the broken name, which the
caller assembles from what `Close` returned and its own resources, and the update that commits the
rename in the WAL invariant). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.Handle
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.BrokenName
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.PkgInit
public import Spec.os.RenameAny
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
variable [os_sem : os.Assumptions] [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]

/-- **The cleanup's rename, as the caller's law provides it** at the timestamp `ts`: from what a
successful `Close` returned (`walUnlockedTokX`, the names fragment, the two pinned paths, the tail
file closed) and the frame `Fr`, with the generation's `notCrashed` (for steps of the WAL invariant), the precondition of `os.Rename.specDirAnySnc` of `r/nm` onto
`r/nm.broken.<ts>` (the area's path, a claim on both names holding the WAL's directory `J` at `nm`,
the update for the rest of it) and what to do with its outcome (`Fin err`, the call permission and
the area's path given back to it). -/
def cleanupLaw (R : Roots) (jr : Ino) (r nm : GoString) (Rp : Roots) (qp : Qp) (tf : Loc)
    (Fr : IProp GF) (Fin : GoInterface → IProp GF) : IProp GF :=
  iprop(∀ ts : GoString, ⌜timeStampOk ts⌝ -∗ Fr -∗ walUnlockedTokX (W := W) -∗
    walNamesFrag (W := W) (some (child r nm)) -∗
    (∃ j : Ino, osPathS Rp (child r nm) (DFrac.own qp) j ∗ osPathS Rp (child r nm) (DFrac.own qp) j) -∗
    (∃ nmf : GoString, os.ownFile tf (-1 : w64) nmf (DFrac.own 1)) -∗
    notCrashed (hC := hG.goose_localGS.goose_crashGS) ={⊤}=∗
    notCrashed (hC := hG.goose_localGS.goose_crashGS) ∗ ∃ (J : Ino) (N : NameSet) (qd : Qp) (h : NamesH) (q rr : Qp) (lb : Nat)
      (Qr : Option (Nat × Nat) → IProp GF),
      ⌜N.Mem nm ∧ N.Mem (brokenName nm ts) ∧ h.cur !! nm = some (.dir J) ∧ q + rr = 1⌝ ∗
      osPathS R r (DFrac.own qd) jr ∗ osLogLb lb ∗ osNames jr N (DFrac.own q) h ∗
      osAUnc (osNames jr N (DFrac.own rr) h)
        (renDirOutA jr J N nm (brokenName nm ts) h (DFrac.own rr) lb) Qr ∗
      ∀ err : GoInterface, notCrashed (hC := hG.goose_localGS.goose_crashGS) -∗
        osPathS R r (DFrac.own qd) jr -∗ osCallPerm (callKey R r) 1 -∗
        ((⌜err ≠ interface.nil ∧ os.renameErrOk err⌝ ∗ osNames jr N (DFrac.own q) h ∗
            osAUnc (osNames jr N (DFrac.own rr) h)
              (renDirOutA jr J N nm (brokenName nm ts) h (DFrac.own rr) lb) Qr) ∨
          ∃ o, ⌜(err = interface.nil → o.isSome) ∧ os.renameErrOk err⌝ ∗ Qr o ∗
            renDirOutA jr J N nm (brokenName nm ts) h (DFrac.own q) lb o) ={⊤}=∗
        notCrashed (hC := hG.goose_localGS.goose_crashGS) ∗ Fin err)

/-- **`w.cleanupWAL(lg)`** of the handle before naming of the WAL directory `r/nm` (see the file
header), the caller holding the other half of the call permission (the rename needs it whole) and the
frame `Fr`. Three outcomes: `Close` failed in its sync (`WAL.Close.spec` (state `unnamed`)'s error arm: the lock token
still held, the tail lock's file open); `Close` returned everything but an error (no rename); or the
rename was called, the law's `Fin err`, with the rename's error one `fmt` formats by its `Error()`
(`fmtErrorOkOrNil`: fmt soundness, 2026-11-18, for `Create`'s `fmt.Errorf` of it). -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.WAL.cleanupWAL.spec (P : WalPbIn GF) (Mr : WalMarshal) :
    Prop :=
  ∀ (R : Roots) (jr : Ino) (r nm : GoString) (w lg : Loc) (Rp : Roots) (qp : Qp) (tf : Loc) (i : Nat)
    (Fr : IProp GF) (Fin : GoInterface → IProp GF),
  NameOk nm →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗ zapLoggerOk lg ∗
      WalFs.walAreaOk walCodec Mr R jr r ∗ walOpenWFUI P Mr w (child r nm) Rp qp tf i ∗
      WalFs.walPurgeW w (child r nm) ∗ osCallPerm (callKey R r) (1 : Qp).half ∗ Fr ∗
      cleanupLaw (W := W) R jr r nm Rp qp tf Fr Fin }}
    (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!!
      go!"cleanupWAL")) (Val #lg))
  {{ (err : GoInterface), RET #err;
      (⌜err ≠ interface.nil⌝ ∗ fmtErrorOk err ∗ (∃ I, WalFs.walLockedTokI I ∗ ⌜WalFs.incOf I (child r nm) = i⌝) ∗
        WalFs.walNamesFrag (some (child r nm)) ∗
        osCallPerm (callKey R r) (1 : Qp).half ∗ Fr ∗
        ∃ (fd : w64) (nmf : GoString) (d : OsFd),
          os.ownFile tf fd nmf (DFrac.own 1) ∗ osFd fd (DFrac.own 1) d ∗ fdLocks fd d) ∨
      (⌜err ≠ interface.nil⌝ ∗ fmtErrorOk err ∗ (∃ I, WalFs.walUnlockedTokXI I ∗ ⌜WalFs.incOf I (child r nm) = i⌝) ∗
        WalFs.walNamesFrag (some (child r nm)) ∗
        osCallPerm (callKey R r) (1 : Qp).half ∗ Fr ∗
        (∃ j : Ino, osPathS Rp (child r nm) (DFrac.own qp) j ∗ osPathS Rp (child r nm) (DFrac.own qp) j) ∗
        ∃ nmf : GoString, os.ownFile tf (-1 : w64) nmf (DFrac.own 1)) ∨
      (Fin err ∗ fmtErrorOkOrNil err) }}

end spec

end EtcdGrove
end Perennial

end
