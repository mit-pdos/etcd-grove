/-
`(*WAL).renameWAL(tmpdirpath)` over `fsExt` (S/wal.go:321-342; W4 of `notes/wal-fsext-plan.md`,
twelfth session): `Create`'s commit. `os.RemoveAll(w.dir)` (a no-op: `nm` is absent), the rename of
`nm.tmp` onto `nm` (`os.Rename.specDirSnc`, the update given), then `w.fp = newFilePipeline(w.lg, w.dir,
SegmentSizeBytes)` and `w.dirFile, err = fileutil.OpenDir(w.dir)`; a failed rename goes to
`renameWALUnlock` (`os.Rename`'s errors are all `*os.LinkError`).

Generic in the update, as `os.Rename.specDirSnc` is: `Create` builds it (`walCreate_osAUnc`, result
`walCreateQ`); the spec needs of it only that an aborted update's result `U none` rebuilds it (for
`renameWALUnlock`'s retry: `walCreateQ … none` is `walCreateP`, `walCreate_osAUnc`'s input).

**The WAL directory's spine** (`Sp`, `SpR`, `RenameWALOk`'s third conjunct): after the commit the new
directory `dir` needs paths (`osPathS R dir dq J`: one for the pipeline, `pipeRes`, one for
`OpenDir` and the handle's `walDirH`). `osPathS` is made of fractions of `.only [c]` claims, and `nm`
is then in the creating claim `.only [nm, nm.tmp]`, which the program and `walInv` hold half each. So
the spine is a law the caller supplies (`Sp`, with the program's half of the logged claim, gives two
spines and a remainder `SpR`), applied at a program step after the rename, with `notCrashed` and the
update's result `U (some x)` (`Create`'s: the invariant's split of the claim, `walInv_splitNew`, needs
the invariant open and the lock token the result holds; ledger, 2026-11-14).

*Pre*: the call's resources (the whole call permission: the rename), the update `osAUnc` of the
program's half of the creating claim `(jr, N)` (`nm` absent, `nm.tmp` holding `J`), the spine law's
resource `Sp`, `J`'s pipeline names (`walTmpsRes J`: the pipeline takes `0.tmp`, the handle `1.tmp`),
`w`'s pre-rename fields (`walPreIn`) with `fp` and `dirFile` nil.

*Post* (`renameWALPost`): the spine to the area back, and
1. *committed, `w` returned*: the update's result, `SpR`, `w`'s fields, the pipeline in `w.fp`
   (`isFilePipe`, `pipeMain γ 0`, the handle's `1.tmp` claim), the directory open in `w.dirFile`
   (`osDirFdS … .idle`), a spine to `dir`, half the call permission (the pipeline holds the other);
2. *committed, a reopened WAL returned* (`renameWALUnlock`'s retry, then `Open`/`ReadAll`): the result,
   `SpR`, the client handle, its named entry, the purge right;
3. *not committed, an error*: everything back but `w`'s files, which `renameWALUnlock`'s `Close` may
   have closed;
4. *committed, an error* (`OpenDir` failed, or the rename failed after taking effect): the result,
   `SpR`, half the call permission.
Lean-first.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__SaveSnapshotPre
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Handle
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.TmpClaim
public import LinuxFs.Spec.os.Rename

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open Fs WalEnc WalFs

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]

/-- **What `renameWAL` needs of its parameters** (see the file header): `dir = r/nm`; `nm.tmp`
(`tmp`) holding `J` and `nm` absent in the creating claim `(jr, N, h)`, both names of it; the spine
law (`Sp` and the program's half of the claim after the rename give two spines to `dir` and `SpR`); an
aborted update's result rebuilds the update. -/
def RenameWALOk (R : Roots) (jr J : Ino) (r dir nm tmp : GoString) (N : NameSet) (h : NamesH)
    (lb : Nat) (dq : DFrac) (U : Option (Nat × Nat) → IProp GF) (Sp : IProp GF)
    (SpR : Nat × Nat → IProp GF) : Prop :=
  InArea r dir nm ∧ NameOk nm ∧ NameOk tmp ∧ tmp ≠ nm ∧ N.Mem nm ∧ N.Mem tmp ∧
  h.cur !! tmp = some (.dir J) ∧ h.cur !! nm = none ∧
  (⊢ ∀ x : Nat × Nat, Sp -∗ notCrashed (hC := hG.goose_localGS.goose_crashGS) -∗ U (some x) -∗
      renDirOut jr J N tmp nm h (DFrac.own (1 : Qp).half) lb (some x) ={⊤}=∗
      notCrashed (hC := hG.goose_localGS.goose_crashGS) ∗ U (some x) ∗
      osPathS R dir dq J ∗ osPathS R dir dq J ∗ SpR x) ∧
  (⊢ U none -∗ osAUnc (osNames jr N (DFrac.own (1 : Qp).half) h)
      (renDirOut jr J N tmp nm h (DFrac.own (1 : Qp).half) lb) U)

/-- **`renameWAL`'s post** (see the file header). -/
def renameWALPost (P : WalPbIn GF) (Mr : WalMarshal) (R : Roots) (jr J : Ino) (r dir : GoString)
    (N : NameSet) (h : NamesH) (qp : Qp) (dq : DFrac) (w lg : Loc) (mds : GoSlice) (md : List w8)
    (e lt f : Loc) (snapi enti : w64) (U : Option (Nat × Nat) → IProp GF) (Sp : IProp GF)
    (SpR : Nat × Nat → IProp GF) (w' : Loc) (err : GoInterface) : IProp GF :=
  iprop(osPathS R r (DFrac.own qp) jr ∗
    ((⌜err = interface.nil ∧ w' = w⌝ ∗
        ∃ (x : Nat × Nat) (fp : Loc) (γ : PipeNames) (sz : w64) (df : Loc) (dfd : w64),
        U (some x) ∗ SpR x ∗ walPreIn w lg dir mds md e lt f snapi enti ∗
        structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"fp" w ↦ fp ∗
        isFilePipe fp γ R dir dq J sz ∗ pipeMain γ 0 ∗ tmpClaim J (pipeTmp 1) ∗
        structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"dirFile" w ↦ df ∗
        os.ownFile df dfd dir (DFrac.own 1) ∗ osDirFdS dfd J .idle ∗ osPathS R dir dq J ∗
        osCallPerm (1 : Qp).half) ∨
     (⌜err = interface.nil⌝ ∗ ∃ x : Nat × Nat, U (some x) ∗ SpR x ∗ walOpenWF P Mr w' dir ∗
        WalFs.walNamed dir ∗ WalFs.walPurgeW w' dir) ∨
     (⌜err ≠ interface.nil⌝ ∗ U none ∗ osNames jr N (DFrac.own (1 : Qp).half) h ∗ osCallPerm 1 ∗
        Sp ∗ walTmpsRes J ∗ (walPreIn w lg dir mds md e lt f snapi enti ∨ emp)) ∨
     (⌜err ≠ interface.nil⌝ ∗ ∃ x : Nat × Nat, U (some x) ∗ SpR x ∗ osCallPerm (1 : Qp).half)))

end defs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]

/-- See the file header. -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.WAL.renameWAL.spec (P : WalPbIn GF) (Mr : WalMarshal) :
    Prop :=
  ∀ (R : Roots) (jr J : Ino) (r dir nm tmp : GoString) (N : NameSet) (h : NamesH) (lb : Nat)
    (qp : Qp) (dq : DFrac) (w lg : Loc) (mds : GoSlice) (md : List w8) (e lt f : Loc)
    (snapi enti : w64) (U : Option (Nat × Nat) → IProp GF) (Sp : IProp GF)
    (SpR : Nat × Nat → IProp GF),
  RenameWALOk R jr J r dir nm tmp N h lb dq U Sp SpR →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗ osInv ∗
      osSharedInv R ∗ osPathS R r (DFrac.own qp) jr ∗ osCallPerm 1 ∗ osLogLb lb ∗
      osNames jr N (DFrac.own (1 : Qp).half) h ∗
      osAUnc (osNames jr N (DFrac.own (1 : Qp).half) h)
        (renDirOut jr J N tmp nm h (DFrac.own (1 : Qp).half) lb) U ∗
      Sp ∗ walTmpsRes J ∗ walPreIn w lg dir mds md e lt f snapi enti ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"fp" w ↦ (null : Loc) ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"dirFile" w ↦ (null : Loc) }}
    (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!!
      go!"renameWAL")) (Val #(child r tmp)))
  {{ (w' : Loc) (err : GoInterface), RET (PairV #w' #err);
      renameWALPost P Mr R jr J r dir N h qp dq w lg mds md e lt f snapi enti U Sp SpR w' err }}

end spec

end EtcdGrove
end Perennial
