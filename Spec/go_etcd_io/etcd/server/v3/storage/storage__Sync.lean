/-
`(*storage.storage).Sync()` (`server/storage/storage.go:96-100`; wal-link L2, 2026-11-17): the WAL's `Sync`
under the storage's read lock. Proved in `Proof/.../storage/storage__Sync.lean`. Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.StorageRep
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__Sync

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI storage go_etcd_io.raft.v3
open Fs WalEnc WalFs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.Assumptions]
variable {Sio : IoSet} [FsStepSat (NoIoErr Sio)]

/-- **`st.Sync()`** of the storage `p` over the WAL `w`, with a reader token (given back): under `st.mux`'s
read lock, `w.Sync()` (`WAL.Sync.spec`). -/
abbrev storage.storage.Sync.spec (P : WalPbIn GF) (Mr : WalMarshal) : Prop :=
  ∀ (p ss : Loc) (R : Roots) (jr : Ino) (r : GoString) (w : Loc) (dir : GoString) (γ : WalShN) (q : Qp)
    (n : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage ∗ storageOver p w ss ∗ storageRd p w ∗
      WalFs.walAreaOk walCodec Mr R jr r ∗ walOpenWS Sio P Mr w dir γ q ∗ ⌜walCov Sio ∨ q = 1⌝ ∗
      WalFs.walLenLb w dir γ.inc n }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.storage.ty @!! go!"Sync")) (Val #()))
  {{ (err : GoInterface), RET #err; storageRd p w ∗
      ((⌜err = GoInterface.nil⌝ ∗ walOpenWS Sio P Mr w dir γ q ∗ WalFs.walSyncedLb dir γ.inc n) ∨
      ⌜err ≠ GoInterface.nil ∧ ¬ walCov Sio⌝) }}

end spec

end EtcdGrove
end Perennial
