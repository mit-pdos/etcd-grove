/-
`readTx.Unlock` (the backend, `read_tx.go`). `rt.Unlock()`: `readTx.mu`'s whole resource given back.
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

/-- `rt.Unlock()`: `readTx.mu`'s whole resource given back. -/
abbrev backend.readTx.Unlock.spec : Prop :=
  ∀ (γ : BNames) (P : BParams) (rt : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      sync.ownRWMutexWLocked (rmuOf (baseOf rt)) (rtRes γ P rt) ∗ rtRes γ P rt 1 }}
    (App (Val (rt @!! go.GoType.PointerType readTx.ty @!! go!"Unlock")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
