/-
`batchTx.safePending` (`batch_tx.go`). `t.safePending()`: `pending`, read under the batch lock (the backend open: the `run` goroutine's quarter of the open token); a pending operation means a write-back since the `run` goroutine's last unpaid commit (its half of `γ.used` at `u`: a lower bound `u + 1` of the write-backs).
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

/-- `t.safePending()`: `pending`, read under the batch lock (the backend open: the `run` goroutine's quarter of the open token); a pending operation means a write-back since the `run` goroutine's last unpaid commit (its half of `γ.used` at `u`: a lower bound `u + 1` of the write-backs). -/
abbrev backend.batchTx.safePending.spec : Prop :=
  ∀ (γ : BNames) (P : BParams) (W Pk : IProp GF) (b t : Loc) (u : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ P W Pk b ∗ bF go!"batchTx" b ↦□ t ∗ dghostVar γ.opn (DFrac.own (1 : Qp).half.half) false ∗ ghostVar γ.used (1 : Qp).half u }}
    (App (Val (btOf t @!! go.GoType.PointerType batchTx.ty @!! go!"safePending")) (Val #()))
  {{ (p : w64), RET #p; dghostVar γ.opn (DFrac.own (1 : Qp).half.half) false ∗
      ghostVar γ.used (1 : Qp).half u ∗ (⌜p = W64 0⌝ ∨ monoNatLbOwn γ.wbc (u + 1)) }}

end spec

end EtcdGrove
end Perennial
