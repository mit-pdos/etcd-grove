/-
`isSafeRetry(c, err, callOpts)` (`client/v3/retry_interceptor.go`; unit P3a). Lean-first (no Rocq
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

/-- `isSafeRetry(c, err, callOpts)` on the retry interceptor's client and a call's options, of a
non-nil client error grpc's `status` accepts, returns some boolean. -/
abbrev isSafeRetry.spec : Prop :=
  ∀ (c : Loc) (err : GoInterface) (o : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ retryClientOk c ∗ retryOptsAt o ∗ ⌜err ≠ GoInterface.nil ∧ clientErr err⌝ ∗
      statusErrOk err }}
    (App (App (App (Val (@! go_etcd_io.etcd.client.v3.isSafeRetry)) (Val #c)) (Val #err)) (Val #o))
  {{ (b : Bool), RET #b; True }}

end spec

end EtcdGrove
end Perennial
