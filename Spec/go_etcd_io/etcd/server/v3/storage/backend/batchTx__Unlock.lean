/-
`batchTx.Unlock` (`batch_tx.go`). `t.Unlock()` (the batch transaction's own): the batch lock released with its free resource (nothing to commit: `pending` is below the limit, or the backend stopped).
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

/-- `t.Unlock()` (the batch transaction's own): the batch lock released with its free resource (nothing to commit: `pending` is below the limit, or the backend stopped). -/
abbrev backend.batchTx.Unlock.spec : Prop :=
  ∀ (γ : BNames) (P : BParams) (W Pk : IProp GF) (b t : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ P W Pk b ∗ bF go!"batchTx" b ↦□ t ∗ sync.ownMutex (muOf t) ∗
      ((∃ (st : BSess) (db : Loc), batchPhys γ b t db st ∗ batchGhostAt γ P st true ∗ ⌜freeOk P st⌝ ∗ W ∗ Pk) ∨
       (pendOf t ↦ W64 0 ∗ bStopped γ)) }}
    (App (Val (btOf t @!! go.GoType.PointerType batchTx.ty @!! go!"Unlock")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
