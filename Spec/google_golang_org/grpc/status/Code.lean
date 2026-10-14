/-
`status.Code(err)` (grpc, names only; unit P3a): the retry interceptor's `isContextError`.
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

/-- `status.Code(err)` of an error grpc's `status` accepts (`statusErrOk`: it calls
`errors.As` and the error's `GRPCStatus()`) returns some code. -/
abbrev status.Code.spec : Prop :=
  ∀ (err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.status ∗ statusErrOk err }}
    (App (Val (@! google_golang_org.grpc.status.Code)) (Val #err))
  {{ (c : w32), RET #c; True }}

end spec

end EtcdGrove
end Perennial
