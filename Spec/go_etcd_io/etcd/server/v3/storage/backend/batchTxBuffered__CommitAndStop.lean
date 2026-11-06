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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- `t.CommitAndStop()` (the `run` goroutine's, at the stop): the batch transaction committed and no new one begun, the backend stopped (the whole open token: the clients' half and the `run` goroutine's quarter). -/
abbrev backend.batchTxBuffered.CommitAndStop.spec : Prop :=
  ∀ (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc) (t : Loc) (X Y : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ P W Pk b ∗ bF go!"batchTx" b ↦□ t ∗
      dghostVar γ.opn (DFrac.own (1 : Qp).half) false ∗
      dghostVar γ.opn (DFrac.own (1 : Qp).half.half) false ∗
      -- (2026-11-04, the restart plan's R2b-3d stage 3) the caller's request `X ⇒ Y` (`commitReq`),
      -- served by the stop's commit's hook (`Close`'s caller's, through the stop invariant)
      X ∗ commitReq γ P Pk b X Y }}
    (App (Val (t @!! go.GoType.PointerType batchTxBuffered.ty @!! go!"CommitAndStop")) (Val #()))
  -- (2026-11-04, R2b-3c) and bbolt's database, owned at its committed data, with the lock's ghost
  -- shares there and its client resources `W ∗ Pk` (part 2), for `Close`
  -- (2026-11-06, `notes/begin-tok-plan.md`) and the last rollback goroutine's fork token (no new
  -- read transaction takes it)
  {{ RET #(); bStopped γ ∗ bDBOut γ P W Pk ∗ Y ∗ threadTok }}

end spec

end EtcdGrove
end Perennial
