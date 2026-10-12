/-
`txBuffer.reset` (`tx_buffer.go`). `txb.reset()`: the buckets with no entries dropped, the others emptied (`bksReset`).
Lean-first (no Rocq counterpart); see `InvBuffer.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBuffer

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

/-- `txb.reset()`: the buckets with no entries dropped, the others emptied (`bksReset`). -/
abbrev backend.txBuffer.reset.spec : Prop :=
  ∀ (txb : Loc) (m : GoMap) (B : GMap w64 (List Ent)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ txb ↦ ({ buckets' := m } : txBuffer) ∗ ownBks m B }}
    (App (Val (txb @!! go.GoType.PointerType txBuffer.ty @!! go!"reset")) (Val #()))
  {{ RET #(); txb ↦ ({ buckets' := m } : txBuffer) ∗ ownBks m (bksReset B) }}

end spec

end EtcdGrove
end Perennial
