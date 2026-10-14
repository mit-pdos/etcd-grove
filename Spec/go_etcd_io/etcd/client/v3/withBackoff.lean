/-
`withBackoff(bf)` (`client/v3/retry_interceptor.go`; unit P3a). Lean-first (no Rocq
counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvRetry

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3
open go_etcd_io.etcd.cache.v3 (statusErrOk backoffOk)

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `withBackoff(bf)` of a backoff function that returns (`backoffOk`) returns a `retryOption`
whose closure writes `backoffFunc` (`optApplyOk`). -/
abbrev withBackoff.spec : Prop :=
  ∀ (bf : GoFunc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ backoffOk bf }}
    (App (Val (@! go_etcd_io.etcd.client.v3.withBackoff)) (Val #bf))
  {{ (ro : go_etcd_io.etcd.client.v3.retryOption), RET #ro; optApplyOk ro.applyFunc' }}

end spec

end EtcdGrove
end Perennial
