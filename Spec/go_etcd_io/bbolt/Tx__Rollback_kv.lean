/-
`Tx.Rollback_kv` (bbolt). `tx.Rollback()` of a read transaction.
A corollary of bbolt's proved `Tx.Rollback` (`Spec/go_etcd_io/bbolt/Tx__Rollback.lean`) over the backend's
vocabulary (`InvBbolt.lean`), proved in `Proof/go_etcd_io/bbolt/Tx__Rollback_kv.lean` (stage S1 of
`notes/bbolt-integration-plan.md`, 2026-11-17; until then an axiom, the backend's trust boundary).
Lean-first (no Rocq counterpart); see `notes/decisions.md`, "The backend: the buffers, bbolt as a
key-value contract, the locks and the views".
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBbolt

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.bbolt backend

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `tx.Rollback()` of a read transaction (all of it): closed, its reader slot's `threadTok` given
back. -/
abbrev bbolt.Tx.Rollback_kv.spec : Prop :=
  ∀ (tx : Loc) (γ : DBNames) (D : backend.Data),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ txLive tx γ 1 (bbolt.TxView.ro D) }}
    (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"Rollback")) (Val #()))
  {{ RET #GoInterface.nil; backend.txDone tx ∗ threadTok }}

end spec

end EtcdGrove
end Perennial
