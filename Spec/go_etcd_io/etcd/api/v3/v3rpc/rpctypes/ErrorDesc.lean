/-
`rpctypes.ErrorDesc(err)` (`api/v3rpc/rpctypes/error.go`): the gRPC status message of `err`, or
its `Error()`. Called by `rpctypes.Error` (unit P3a, 2026-10-14). Lean-first (no Rocq
counterpart).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]

/-- `rpctypes.ErrorDesc(err)` of an error grpc's `status` accepts (`statusErrOk`; `nil` included:
`status.FromError(nil)` succeeds, so `Error()` is not called) returns some string. -/
abbrev rpctypes.ErrorDesc.spec : Prop :=
  ∀ (err : GoError),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.v3rpc.rpctypes ∗ statusErrOk err }}
    (App (Val (@! go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrorDesc)) (Val #err))
  {{ (d : GoString), RET #d; True }}

end spec

end EtcdGrove
end Perennial
