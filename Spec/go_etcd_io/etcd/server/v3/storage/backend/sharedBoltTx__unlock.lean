/-
`sharedBoltTx.unlock` (the backend, `read_tx.go`; added by etcd#22215). `st.unlock()`: `st.txMu.Unlock()`, through its guard.
Lean-first (no Rocq counterpart); see `InvBackend.lean` and `notes/decisions.md`, "The backend:
the buffers, bbolt as a key-value contract, the locks and the views".
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBackend

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

/-- `st.unlock()`: `st.txMu.Unlock()`, through its guard. -/
abbrev backend.sharedBoltTx.unlock.spec : Prop :=
  ∀ (st tm : Loc) (P : Qp → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ rtmuOf st ↦□ tm ∗ sync.ownRWMutexWLocked tm P ∗ ▷ P 1 }}
    (App (Val (st @!! go.GoType.PointerType sharedBoltTx.ty @!! go!"unlock")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
