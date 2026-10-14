/-
`clientv3.withRepeatablePolicy()` (`client/v3/retry_interceptor.go`, translated for unit C1, the client meets the server). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvKVConn

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `withRepeatablePolicy()`: a `retryOption` whose closure sets the interceptor's options'
`retryPolicy` (`retryApplyOk`). -/
abbrev withRepeatablePolicy.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 }}
    (App (Val (@! go_etcd_io.etcd.client.v3.withRepeatablePolicy)) (Val #()))
  {{ (ro : go_etcd_io.etcd.client.v3.retryOption), RET #ro; retryApplyOk ro.applyFunc' }}

end spec

end EtcdGrove
end Perennial
