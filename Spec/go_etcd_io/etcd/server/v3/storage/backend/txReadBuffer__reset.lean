/-
`txReadBuffer.reset` (`tx_buffer.go`). `txr.reset()` (`txBuffer.reset`, promoted): the buckets reset, the version unchanged.
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

/-- `txr.reset()` (`txBuffer.reset`, promoted): the buckets reset, the version unchanged. -/
abbrev backend.txReadBuffer.reset.spec : Prop :=
  ∀ (txr : Loc) (R : RBuf),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ ownRB txr R }}
    (App (Val (txr @!! go.GoType.PointerType txReadBuffer.ty @!! go!"reset")) (Val #()))
  {{ RET #(); ownRB txr R.reset }}

end spec

end EtcdGrove
end Perennial
