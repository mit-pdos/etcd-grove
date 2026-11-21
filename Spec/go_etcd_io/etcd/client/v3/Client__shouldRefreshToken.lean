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
of a non-nil client error grpc's `status` accepts, returns some boolean (`true` only for an auth refusal:
of its description `m`, `descIs err m`, errdesc stage 2b, 2026-11-21). -/
abbrev Client.shouldRefreshToken.spec : Prop :=
  ∀ (c : Loc) (err : GoInterface) (o : Loc) (m : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ retryClientOk c ∗ retryOptsAt o ∗ ⌜err ≠ GoInterface.nil ∧ clientErr err⌝ ∗
      statusErrOk err ∗ go_etcd_io.etcd.cache.v3.descIs err m }}
    (App (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
      go!"shouldRefreshToken")) (Val #err)) (Val #o))
  {{ (b : Bool), RET #b;
      -- (2026-10-21, D29) `true` only for an auth refusal
      ⌜b = true → m ∈ go_etcd_io.etcd.cache.v3.refusalDescs⌝ }}

end spec

end EtcdGrove
end Perennial
