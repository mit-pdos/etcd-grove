/-
`(*wal.WAL).Sync` with no I/O error (unit `noioerr`, `notes/wal-units/noioerr.md`): `Sync.spec` over a
semantics whose steps satisfy **no I/O error on chosen files** (`FsStepSat (NoIoErr Sio)`), with the
coverage the user chose for now (2026-11-15, coverage (a), `notes/decisions.md`, "fsExt: no I/O errors on
chosen files"): every file of the roots' trees (etcd's data directory), `∀ st i, Sio.ino st i`. Proved in
`LinuxFs/Proof/.../wal/WAL__SyncNoErr.lean`. Lean-first.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__Sync
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.HandleRoom
public import GooseLang.Ext.Fs.Premises
public import GooseLang.Ext.Fs.FilteredSem

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
variable {Sio : IoSet} [FsStepSat (NoIoErr Sio)]

/-- **`w.Sync()` with no I/O error** (see the file header): `Sync.spec`'s success arm, `nil` returned, of
a handle whose tail has room `k` (`walOpenWFR`: the pending bytes end at most at `maxBytes`, where a write
fails with `EFBIG` whatever the premise); the flush moves the pending bytes into the tail, so the room is
kept. -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.WAL.Sync.specNoErr (P : WalPbIn GF) (Mr : WalMarshal) : Prop :=
  (∀ st i, Sio.ino st i) →
  ∀ (R : Roots) (jr : Ino) (r : GoString) (w : Loc) (dir : GoString) (n k : Nat),
  {{ WalFs.walAreaOk walCodec Mr R jr r ∗ WalFs.walOpenWFR P Mr w dir k ∗ WalFs.walLenLb w dir n }}
    (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!! go!"Sync")) (Val #()))
  {{ (err : GoInterface), RET #err;
      ⌜err = GoInterface.nil⌝ ∗ WalFs.walOpenWFR P Mr w dir k ∗ WalFs.walSyncedLb dir n }}

end spec

end EtcdGrove
end Perennial
