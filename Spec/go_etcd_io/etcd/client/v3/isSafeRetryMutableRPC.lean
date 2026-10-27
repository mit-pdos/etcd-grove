/-
`isSafeRetryMutableRPC(err)` (`client/v3/retry.go`; unit P3a). Lean-first (no Rocq
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

/-- `isSafeRetryMutableRPC(err)` of an error grpc's `status` accepts returns some boolean
(`true` only for "there is no address/connection available"). -/
abbrev isSafeRetryMutableRPC.spec : Prop :=
  ∀ (err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ statusErrOk err }}
    (App (Val (@! go_etcd_io.etcd.client.v3.isSafeRetryMutableRPC)) (Val #err))
  {{ (b : Bool), RET #b;
      -- (2026-10-21, D29) `true` only for grpc's old balancer's "no address"/"no connection"
      ⌜b = true → go_etcd_io.etcd.cache.v3.errDesc err ∈ go_etcd_io.etcd.cache.v3.refusalDescs⌝ }}

end spec

end EtcdGrove
end Perennial
