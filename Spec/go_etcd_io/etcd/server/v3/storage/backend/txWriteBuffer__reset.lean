/-
`txWriteBuffer.reset` (`tx_buffer.go`). `txw.reset()`: the buckets reset; a bucket that stays is flagged sequential again.
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

/-- `txw.reset()`: the buckets reset; a bucket that stays is flagged sequential again. -/
abbrev backend.txWriteBuffer.reset.spec : Prop :=
  ∀ (txw : Loc) (W : WBuf),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ ownWB txw W }}
    (App (Val (txw @!! go.GoType.PointerType txWriteBuffer.ty @!! go!"reset")) (Val #()))
  {{ RET #(); ownWB txw W.reset }}

end spec

end EtcdGrove
end Perennial
