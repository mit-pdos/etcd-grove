/-
`(*wal.WAL).Sync` over `fsExt` (W11 of `notes/wal-fsext-plan.md`; the main tree's axiom
`Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__Sync.lean` with plan §3's binder changes). Its error
arm changed: the handle is lost (`sync` flushes the page writer first, and a failed flush leaves part
of the pending bytes written). To be proved in `LinuxFs/Proof/.../wal/WAL__Sync.lean`. Lean-first.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Handle

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

/-- **`w.Sync()`** (S/wal.go:994-996, 967-992): flushes the encoder's page writer and fdatasyncs
the tail: every record `w` has written is synced (`walLenLb n` gives `walSyncedLb n`). *Error*: the
flush's write or the fdatasync failed; the handle is lost (the flush may have written part of its
pending bytes, the page writer's buffer is then empty: a later append would not be the stream).
The main tree's spec kept the handle on error. -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.WAL.Sync.spec (P : WalPbIn GF) (Mr : WalMarshal) : Prop :=
  ∀ (R : Roots) (jr : Ino) (r : GoString) (w : Loc) (dir : GoString) (n : Nat),
  {{ WalFs.walAreaOk walCodec Mr R jr r ∗ walOpenWF P Mr w dir ∗ WalFs.walLenLb w dir n }}
    (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!! go!"Sync")) (Val #()))
  {{ (err : GoInterface), RET #err;
      (⌜err = GoInterface.nil⌝ ∗ walOpenWF P Mr w dir ∗ WalFs.walSyncedLb dir n) ∨
      ⌜err ≠ GoInterface.nil⌝ }}

end spec

end EtcdGrove
end Perennial
