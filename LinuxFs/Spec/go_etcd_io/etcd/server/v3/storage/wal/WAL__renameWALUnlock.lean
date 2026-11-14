/-
`(*WAL).renameWALUnlock(tmpdirpath)` over `fsExt` (S/wal.go:344-368; W4 of `notes/wal-fsext-plan.md`,
twelfth session): `renameWAL`'s retry after a failed rename (`os.Rename`'s errors are all
`*os.LinkError`, so every failure takes it): `w.Close()`, the rename again, `Open(w.lg, w.dir,
&walpb.Snapshot{})` and `ReadAll`. Stated in `renameWAL`'s vocabulary (`WAL__renameWAL.lean`, which says
what each piece is), its post `renameWAL`'s. A hypothesis of `renameWAL`'s proof, not proved: **its
`w.Close()` reaches `w.dirFile.Close()` with a nil `dirFile`** (the pre-rename `w` has none), which
returned `ErrInvalid` in Go but was stuck in the trusted model of `(*os.File).Close` (plan §0, item 6;
the model now returns it, `os.File.Close.specNil`); its `Open`/`ReadAll` need the area's resources
(`walAreaRes`), which `Create` has split up by then, and its success arm (`renameWALPost`'s arm 2, the handle before naming
`walOpenWFU` and the caller's residue `UH`) needs a `RenameWALOk` law producing `UH` (ledger 2026-11-14,
twenty-second W4 session). The pre carries the lock file and the encoder its `Close` consumes
(`walLockIn`; nineteenth W4 session). Lean-first.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__renameWAL

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

/-- See the file header: from the state after the failed first rename (the update's result `U o`, `o`
its outcome, and the program's half of the creating claim after it), `renameWAL`'s post. -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.WAL.renameWALUnlock.spec (P : WalPbIn GF)
    (Mr : WalMarshal) : Prop :=
  ∀ (R : Roots) (jr J : Ino) (r dir nm tmp : GoString) (N : NameSet) (h : NamesH) (lb : Nat)
    (qp : Qp) (dq : DFrac) (w lg : Loc) (mds : GoSlice) (md : List w8) (e lt f : Loc)
    (snapi enti : w64) (fd : w64) (fname : GoString) (d : OsFd) (c : w32) (off : w64)
    (U : Option (Nat × Nat) → IProp GF) (Sp : IProp GF) (SpR UH : Nat × Nat → IProp GF)
    (o : Option (Nat × Nat)),
  RenameWALOk R jr J r dir nm tmp N h lb dq U Sp SpR →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗ osInv ∗
      osSharedInv R ∗ osPathS R r (DFrac.own qp) jr ∗ osCallPerm 1 ∗ osLogLb lb ∗
      U o ∗ renDirOut jr J N tmp nm h (DFrac.own (1 : Qp).half) lb o ∗ Sp ∗ walTmpsRes J ∗
      walPreIn w lg dir mds md e lt f snapi enti ∗ walLockIn e f fd fname d c off ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"fp" w ↦ (null : Loc) ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"dirFile" w ↦ (null : Loc) }}
    (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!!
      go!"renameWALUnlock")) (Val #(child r tmp)))
  {{ (w' : Loc) (err : GoInterface), RET (PairV #w' #err);
      renameWALPost P Mr R jr J r dir N h qp dq w lg mds md e lt f snapi enti fd fname d c off U Sp
        SpR UH w' err }}

end spec

end EtcdGrove
end Perennial
