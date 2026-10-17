/-
`newSharedTx` (the backend, `read_tx.go`; added by etcd#22215). `newSharedTx()`: a new `sharedBoltTx`: a new `RWMutex`, no bbolt transaction, a new empty buckets map, a new `WaitGroup`.
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

/-- `newSharedTx()`: a new `sharedBoltTx`: a new `RWMutex`, no bbolt transaction, a new empty buckets map, a new `WaitGroup`. -/
abbrev backend.newSharedTx.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend }}
    (App (Val (@! newSharedTx)) (Val #()))
  {{ (st tm : Loc) (cm : GoMap) (wg : Loc), RET #(stIf st); rtmuOf st ↦ tm ∗
      tm ↦ (zero_val sync.RWMutex) ∗ rtxOf st ↦ Loc.null ∗ rbktOf st ↦ cm ∗
      cm ↦$ (∅ : GMap w64 Loc) ∗ rwgOf st ↦ wg ∗ wg ↦ (zero_val sync.WaitGroup) }}

end spec

end EtcdGrove
end Perennial
