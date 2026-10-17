/-
`sharedBoltTx.clone` (the backend, `read_tx.go`; added by etcd#22215). `st.clone()`: a new `sharedBoltTx` with the same fields (its `txMu`, bbolt transaction, buckets map and `WaitGroup`).
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

/-- `st.clone()`: a new `sharedBoltTx` with the same fields (its `txMu`, bbolt transaction, buckets map and `WaitGroup`). -/
abbrev backend.sharedBoltTx.clone.spec : Prop :=
  ∀ (st : Loc) (dq : DFrac) (tm tx : Loc) (cm : GoMap) (wg : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ rtmuOf st ↦□ tm ∗ rtxOf st ↦{dq} tx ∗ rbktOf st ↦{dq} cm ∗ rwgOf st ↦{dq} wg }}
    (App (Val (st @!! go.GoType.PointerType sharedBoltTx.ty @!! go!"clone")) (Val #()))
  {{ (st' : Loc), RET #(stIf st'); rtxOf st ↦{dq} tx ∗ rbktOf st ↦{dq} cm ∗ rwgOf st ↦{dq} wg ∗
      rtmuOf st' ↦ tm ∗ rtxOf st' ↦ tx ∗ rbktOf st' ↦ cm ∗ rwgOf st' ↦ wg }}

end spec

end EtcdGrove
end Perennial
