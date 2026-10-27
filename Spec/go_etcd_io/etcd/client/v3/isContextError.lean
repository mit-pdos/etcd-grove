/-
`isContextError(err)` (`client/v3/retry_interceptor.go`; unit P3a). Lean-first (no Rocq
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `isContextError(err)` of an error grpc's `status` accepts returns some boolean
(`status.Code(err)` is `DeadlineExceeded` or `Canceled`). -/
abbrev isContextError.spec : Prop :=
  ∀ (err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ statusErrOk err }}
    (App (Val (@! go_etcd_io.etcd.client.v3.isContextError)) (Val #err))
  {{ (b : Bool), RET #b; True }}

end spec

end EtcdGrove
end Perennial
