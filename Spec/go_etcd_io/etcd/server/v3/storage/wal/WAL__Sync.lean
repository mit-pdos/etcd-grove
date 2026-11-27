/-
`(*wal.WAL).Sync` over `fsExt` (W11 of `notes/wal-fsext-plan.md`; one spec since wal-link L1a, 2026-11-17,
`notes/wal-link-scope.md` §8: the former `Sync.spec` and `Sync.specNoErr` merged). Over a share of the handle
(`walOpenWS`, `HandleShared.lean`: the server's raft loop and apply thread use the WAL at once, serialized by
`w.mu`), parameterised by the files with no I/O error (`Sio`, `FsStepSat (NoIoErr Sio)`): the error arm
only when `Sio` does not cover every inode (`walCov`), and then only for the whole share (the handle is lost
for every holder: `sync` flushes the page writer first, and a failed flush leaves part of the pending bytes
written). Proved in `Proof/.../wal/WAL__Sync.lean`. Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.HandleShared
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

/-- **`w.Sync()`** (S/wal.go:1003-1006, 967-992; the fork's fix 0006 takes `w.mu`): flushes the encoder's page
writer and fdatasyncs the tail: every record `w` has written is synced (`walLenLb n` gives `walSyncedLb n`),
the share kept. *Error* (only when `Sio` misses an inode, and then the caller holds the whole share): the
flush's write or the fdatasync failed; the handle is lost. -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.WAL.Sync.spec (P : WalPbIn GF) (Mr : WalMarshal) : Prop :=
  ∀ (R : Roots) (jr : Ino) (r : GoString) (w : Loc) (dir : GoString) (γ : WalShN) (q : Qp) (n : Nat),
  {{ WalFs.walAreaOk walCodec Mr R jr r ∗ walOpenWS Sio P Mr w dir γ q ∗ ⌜walCov Sio ∨ q = 1⌝ ∗
      WalFs.walLenLb w dir γ.inc n }}
    (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!! go!"Sync")) (Val #()))
  {{ (err : GoInterface), RET #err;
      (⌜err = GoInterface.nil⌝ ∗ walOpenWS Sio P Mr w dir γ q ∗ WalFs.walSyncedLb dir γ.inc n) ∨
      ⌜err ≠ GoInterface.nil ∧ ¬ walCov Sio⌝ }}

end spec

end EtcdGrove
end Perennial
