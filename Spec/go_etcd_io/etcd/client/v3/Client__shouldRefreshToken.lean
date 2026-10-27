/-
`c.shouldRefreshToken(err, callOpts)` (`client/v3/retry_interceptor.go`; unit P3a). Lean-first
(no Rocq counterpart).
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

/-- `c.shouldRefreshToken(err, callOpts)` on the retry interceptor's client and a call's options,
of a non-nil client error grpc's `status` accepts, returns some boolean. -/
abbrev Client.shouldRefreshToken.spec : Prop :=
  ∀ (c : Loc) (err : GoInterface) (o : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ retryClientOk c ∗ retryOptsAt o ∗ ⌜err ≠ GoInterface.nil ∧ clientErr err⌝ ∗
      statusErrOk err }}
    (App (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
      go!"shouldRefreshToken")) (Val #err)) (Val #o))
  {{ (b : Bool), RET #b;
      -- (2026-10-21, D29) `true` only for an auth refusal
      ⌜b = true → go_etcd_io.etcd.cache.v3.errDesc err ∈ go_etcd_io.etcd.cache.v3.refusalDescs⌝ }}

end spec

end EtcdGrove
end Perennial
