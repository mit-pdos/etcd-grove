/-
`(*storage.storage).Close()` (`server/storage/storage.go:90-94`; wal-link L2, 2026-11-17): the WAL's `Close`
under the storage's write lock. Proved in `Proof/.../storage/storage__Close.lean`. Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.StorageRep
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__Close

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

/-- **`st.Close()`** of the storage `p` over the WAL `w`, with the whole share of the WAL's handle: under
`st.mux`'s write lock (its persistent guard is in `storageOver`: no reader token), `w.Close()`
(`WAL.Close.spec`, its `shared` state). -/
abbrev storage.storage.Close.spec (P : WalPbIn GF) (Mr : WalMarshal) : Prop :=
  ∀ (p ss : Loc) (R : Roots) (jr : Ino) (r : GoString) (w : Loc) (dir : GoString) (γ : WalShN)
    (Q : WalDur → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage ∗ storageOver p w ss ∗
      WalFs.walAreaOk walCodec Mr R jr r ∗ walOpenWS Sio P Mr w dir γ 1 ∗ WalFs.walPurgeW w dir ∗
      AU <{ ∃∃ d : WalDur, WalFs.walDiskAtI dir γ.inc d }> @ walAuMask, ∅ <{ WalFs.walDiskAtI dir γ.inc d, COMM Q d }> }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.storage.ty @!! go!"Close")) (Val #()))
  {{ (err : GoInterface), RET #err;
      (⌜walCov Sio → err = GoInterface.nil⌝ ∗ ∃ d : WalDur, Q d ∗
          WalFs.walSyncedLb dir γ.inc d.H.length ∗ WalFs.walUnlockedTok ∗ osCallPerm (callKey R dir) (1 : Qp).half) ∨
      ⌜err ≠ GoInterface.nil ∧ ¬ walCov Sio⌝ }}

end spec

end EtcdGrove
end Perennial
