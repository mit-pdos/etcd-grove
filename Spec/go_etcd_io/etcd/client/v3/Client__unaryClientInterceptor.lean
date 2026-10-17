/-
`c.unaryClientInterceptor(optFuncs...)` (`client/v3/retry_interceptor.go`; unit P3a): the
client's retry interceptor, installed at dial (`client.go`'s `dialSetupOpts`:
`unaryClientInterceptor(withMax(unaryMaxRetries), rrBackoff)`). Lean-first (no Rocq
counterpart); the design: `notes/decisions.md`, "The retry interceptor proved: the gRPC boundary
below it".
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvRetryQuiet

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

/-- `c.unaryClientInterceptor(optFuncs...)` on a client `clientv3.New` built
(`retryClientOk`), with options each building the interceptor's options (`optApplyOk`: the dial's
`withMax`, `withBackoff`), returns an interceptor meeting the retry interceptor's contract
(`etcdInterceptorOk`, `InvKVConn.lean`). -/
abbrev Client.unaryClientInterceptor.spec : Prop :=
  ∀ (c : Loc) (sl : GoSlice) (ros : List go_etcd_io.etcd.client.v3.retryOption),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ retryClientOk c ∗ sl ↦*□ ros ∗ [∗list] ro ∈ ros, optApplyOk ro.applyFunc' }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
      go!"unaryClientInterceptor")) (Val #sl))
  {{ (f : GoFunc), RET #f; etcdInterceptorOk f }}

/-- (etcd-io/etcd#21739, pr-verify) **No warning on context errors**: on the same premises, the
interceptor returned meets the quiet contract (`etcdInterceptorQuiet`, `InvRetryQuiet.lean`):
over an invoker failing only with `Canceled`/`DeadlineExceeded` statuses, a call returns as
`etcdInterceptorOk`'s does. Its proof (`wp_proof_quiet`) is given no spec of `zap.Logger.Warn`:
such a call logs no "retrying of unary invoker failed" (nor any other warning). Not true of the
code before the PR, which logged the warning before testing `isContextError`. -/
abbrev Client.unaryClientInterceptor.spec_quiet : Prop :=
  ∀ (c : Loc) (sl : GoSlice) (ros : List go_etcd_io.etcd.client.v3.retryOption),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ retryClientOk c ∗ sl ↦*□ ros ∗ [∗list] ro ∈ ros, optApplyOk ro.applyFunc' }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
      go!"unaryClientInterceptor")) (Val #sl))
  {{ (f : GoFunc), RET #f; etcdInterceptorQuiet f }}

end spec

end EtcdGrove
end Perennial
