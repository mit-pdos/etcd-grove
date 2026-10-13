/-
`batchTxBuffered.CommitAndStop` (`batch_tx.go`). `t.CommitAndStop()` (the `run` goroutine's, at the stop): the batch transaction committed and no new one begun, the backend stopped (the whole open token: the clients' half and the `run` goroutine's quarter).
Lean-first (no Rocq counterpart); see `InvBatch.lean` and `InvBackend.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBatch

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.backend backend

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- `t.CommitAndStop()` (the `run` goroutine's, at the stop): the batch transaction committed and no new one begun, the backend stopped (the whole open token: the clients' half and the `run` goroutine's quarter). -/
abbrev backend.batchTxBuffered.CommitAndStop.spec : Prop :=
  ∀ (γ : BNames) (P : BParams) (WR : IProp GF) (b : Loc) (t : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ P WR b ∗ bF go!"batchTx" b ↦□ t ∗
      dghostVar γ.opn (DFrac.own (1 : Qp).half) false ∗
      dghostVar γ.opn (DFrac.own (1 : Qp).half.half) false }}
    (App (Val (t @!! go.GoType.PointerType batchTxBuffered.ty @!! go!"CommitAndStop")) (Val #()))
  {{ RET #(); bStopped γ }}

end spec

end EtcdGrove
end Perennial
