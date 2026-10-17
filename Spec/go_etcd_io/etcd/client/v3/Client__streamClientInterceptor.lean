/-
`c.streamClientInterceptor(optFuncs...)` (`client/v3/retry_interceptor.go`; etcd-io/etcd#21739,
pr-verify, 2026-10-17): the client's retry stream interceptor, installed at dial (`client.go`'s
`dialSetupOpts`: `streamClientInterceptor(withMax(0), rrBackoff)`). Lean-first (no Rocq
counterpart); the contracts are in `InvRetryQuiet.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvRetryQuiet

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

/-- `c.streamClientInterceptor(optFuncs...)` on a client `clientv3.New` built (`retryClientOk`),
with options each building the interceptor's options (`optApplyOk`), returns an interceptor
meeting the stream interceptor's contract (`etcdStreamInterceptorOk`: it returns). -/
abbrev Client.streamClientInterceptor.spec : Prop :=
  ∀ (c : Loc) (sl : GoSlice) (ros : List go_etcd_io.etcd.client.v3.retryOption),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ retryClientOk c ∗ sl ↦*□ ros ∗ [∗list] ro ∈ ros, optApplyOk ro.applyFunc' }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
      go!"streamClientInterceptor")) (Val #sl))
  {{ (f : GoFunc), RET #f; etcdStreamInterceptorOk f }}

/-- (etcd-io/etcd#21739) **No error log on a done context**: on the same premises, the interceptor
returned meets the quiet contract (`etcdStreamInterceptorQuiet`): on a done context over a streamer
failing only with context statuses, a call returns. Its proof (`wp_proof_quiet`) is given no spec
of `zap.Logger.Error`, but takes `Client.getToken.spec_ctx`, which is false: the PR's guard holds
back "streamer failed to create ClientStream" but not "getToken failed". -/
abbrev Client.streamClientInterceptor.spec_quiet : Prop :=
  ∀ (c : Loc) (sl : GoSlice) (ros : List go_etcd_io.etcd.client.v3.retryOption),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ retryClientOk c ∗ sl ↦*□ ros ∗ [∗list] ro ∈ ros, optApplyOk ro.applyFunc' }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
      go!"streamClientInterceptor")) (Val #sl))
  {{ (f : GoFunc), RET #f; etcdStreamInterceptorQuiet f }}

end spec

end EtcdGrove
end Perennial
