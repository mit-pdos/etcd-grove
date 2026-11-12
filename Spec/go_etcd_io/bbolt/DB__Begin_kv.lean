/-
`DB.Begin_kv` (bbolt). `db.Begin(writable)`: a read transaction over the committed data, or the write transaction
(its token spent), or an error.
The trust boundary: bbolt's key-value contract as the backend uses it (`InvBbolt.lean`), from the
Go documentation; an axiom in `Proof/go_etcd_io/bbolt/DB__Begin_kv.lean`. Lean-first (no Rocq
counterpart); see `notes/decisions.md`, "The backend: the buffers, bbolt as a key-value contract,
the locks and the views".

(2026-11-06, branch `begin-tok`, the user's approval: `notes/begin-tok-plan.md`, Q1/Q3) A read
transaction takes the caller's `threadTok`, held by the transaction as its reader slot of bbolt's
`mmaplock` and given back by `Tx.Rollback_kv` (and by the error branch): the shape of the proved
`DB.Begin.spec`/`Tx.Rollback.spec` (`notes/bbolt-spec-decisions.md`, D1). Until then the read half
took nothing, and a proof could open `2 ^ 30` read transactions and then reach `sync.RWMutex`'s
fatal (`notes/axiom-review/backend-snapshot-begin.md`). The bound that makes the tokens enough is
`Open_kv`'s `[ThreadBoundLe GF (2 ^ 29)]`.
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
held as its reader slot until `Tx.Rollback_kv`), or the write transaction (its token spent), or an
error (the token given back). -/
abbrev bbolt.DB.Begin_kv.spec : Prop :=
  ∀ (db : Loc) (γ : DBNames) (D : Data) (w : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ ownDB db γ D ∗ (if w then wrTok γ else threadTok) }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"Begin")) (Val #w))
  {{ (tx : Loc) (err : GoInterface), RET (PairV #tx #err); ownDB db γ D ∗ isDB db ∗
      ((⌜err ≠ GoInterface.nil⌝ ∗ (if w then wrTok γ else threadTok)) ∨
       (⌜err = GoInterface.nil⌝ ∗ txDB tx db ∗
        (if w then ownWTx tx γ D D else iprop(txLive tx 1 ∗ rtxSnap tx D ∗ rtxStats tx)))) }}

end spec

end EtcdGrove
end Perennial
