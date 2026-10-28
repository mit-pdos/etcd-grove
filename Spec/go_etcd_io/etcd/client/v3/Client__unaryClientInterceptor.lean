/-
`c.unaryClientInterceptor(optFuncs...)` (`client/v3/retry_interceptor.go`; unit P3a): the
client's retry interceptor, installed at dial (`client.go`'s `dialSetupOpts`:
`unaryClientInterceptor(withMax(unaryMaxRetries), rrBackoff)`). Lean-first (no Rocq
counterpart); the design: `notes/decisions.md`, "The retry interceptor proved: the gRPC boundary
below it".
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvRetry
public import Proof.go_etcd_io.etcd.client.v3.InvClientAuth

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

/-- `c.unaryClientInterceptor(optFuncs...)` on a client `clientv3.New` built
(`retryClientOk`), with options each building the interceptor's options (`optApplyOk`: the dial's
`withMax`, `withBackoff`), returns an interceptor meeting the retry interceptor's contract
(`etcdInterceptorOk`, `InvKVConn.lean`). -/
abbrev Client.unaryClientInterceptor.spec : Prop :=
  ∀ (c : Loc) (sl : GoSlice) (ros : List go_etcd_io.etcd.client.v3.retryOption),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ retryClientOk c ∗ sl ↦*□ ros ∗
      -- (2026-10-21, D29) keeping the retry policy
      [∗list] ro ∈ ros, optApplyKeep ro.applyFunc' true }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
      go!"unaryClientInterceptor")) (Val #sl))
  {{ (f : GoFunc), RET #f;
      -- (the auth plan's C1, 2026-10-28) once the client is ready (its `Auth` set: the refresh
      -- path's `getToken` calls it), on a connection whose interceptor `f` is, both modes (D29: a
      -- write on a refusal-free connection, whatever the bound)
      etcdInterceptorOkG c f }}

end spec

end EtcdGrove
end Perennial
