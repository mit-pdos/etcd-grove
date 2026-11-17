/-
`DB.Begin_kv` (bbolt). `db.Begin(writable)`.
A corollary of bbolt's proved `DB.Begin` (`Spec/go_etcd_io/bbolt/DB__Begin.lean`) over the backend's
vocabulary (`InvBbolt.lean`), proved in `Proof/go_etcd_io/bbolt/DB__Begin_kv.lean` (stage S1 of
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

/-- `db.Begin(writable)`: a read transaction over the committed data (the caller's `threadTok`
held as its reader slot until `Tx.Rollback_kv`), or the write transaction, or an error (the
token given back). -/
abbrev bbolt.DB.Begin_kv.spec : Prop :=
  ∀ (db : Loc) (γ : DBNames) (D : backend.Data) (w : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ ownDB db γ D ∗ (if w then wrTok γ else threadTok) }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"Begin")) (Val #w))
  {{ (tx : Loc) (err : GoInterface), RET (PairV #tx #err); ownDB db γ D ∗ isDB db γ ∗
      ((⌜err ≠ GoInterface.nil⌝ ∗ (if w then wrTok γ else threadTok)) ∨
       (⌜err = GoInterface.nil⌝ ∗ backend.txDB tx γ db ∗
        (if w then ownWTx tx γ D D else txLive tx γ 1 (bbolt.TxView.ro D)))) }}

end spec

end EtcdGrove
end Perennial
