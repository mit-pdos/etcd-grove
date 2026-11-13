/-
`(*wal.WAL).SaveSnapshot` over `fsExt` (W11 of `notes/wal-fsext-plan.md`; the main tree's axiom
`Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__SaveSnapshot.lean` with plan §3's changes, as
`WAL__Save.lean` here). To be proved in `LinuxFs/Proof/.../wal/WAL__SaveSnapshot.lean`. Lean-first.
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

/-- **`w.SaveSnapshot(e)`** (S/wal.go:1137-1162): one snapshot record of `e`'s index and term (its
conf state non-nil unless the index is 0, `ValidateSnapshotForWrite`; its index below `2^64-1`),
committed after `w.mu.Lock()`, before the record is encoded; always synced. *Error* (the encode's
write, the flush, the fdatasync): committed (`Q d`), the handle lost, as `Save`'s. -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.WAL.SaveSnapshot.spec (P : WalPbIn GF) (Mr : WalMarshal) : Prop :=
  ∀ (R : Roots) (jr : Ino) (r : GoString) (w : Loc) (dir : GoString) (sp : Loc)
    (md : SnapshotMetadataM) (cs : Bool) (sized : Bool) (Q : WalDur → IProp GF),
  {{ WalFs.walAreaOk walCodec Mr R jr r ∗ walOpenWF P Mr w dir ∗ walSnapAt sp md cs ∗
      ⌜md.Index' = W64 0 ∨ cs = true⌝ ∗ ⌜uint.nat md.Index' < 2 ^ 64 - 1⌝ ∗
      AU <{ ∃∃ d : WalDur, WalFs.walDiskAt dir d ∗ ⌜d.sized = sized⌝ }> @ walAuMask, ∅
        <{ WalFs.walDiskAt dir { d with H := d.H ++ [WalOpG.snap md] }, COMM Q d }> }}
    (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!! go!"SaveSnapshot")) (Val #sp))
  {{ (err : GoInterface), RET #err;
      (⌜err = GoInterface.nil⌝ ∗ walOpenWF P Mr w dir ∗ ∃ d : WalDur, Q d ∗
          WalFs.walLenLb w dir (d.H.length + 1) ∗ WalFs.walSyncedLb dir (d.H.length + 1)) ∨
      (⌜err ≠ GoInterface.nil⌝ ∗ ∃ d : WalDur, Q d) }}

end spec

end EtcdGrove
end Perennial
