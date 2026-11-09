/-
`(*clientv3.Client).unaryClientInterceptor` (`client/v3/retry_interceptor.go`).

Users: `dialSetupOpts` (the client's connection: every unary RPC of every client call goes through it).

Proof sketch: `reuseOrNewWithCallOptions(defaultOptions, optFuncs)` (`optionsAt`); the closure, for
`uiOk_call`: `withVersion(ctx)` (W0: `ctxOk`, `ctxPrin` kept); `filterCallOptions(opts)` (the gRPC
options and the per-call retry options: the policy repeatable iff `callOptsOk`'s `rep`), a `peer`
option; the per-call options. Limit `0`: one attempt (`AttemptTriple`): a token refusal or a
learner's refusal is fired by the interceptor as a refusal at the return (a ghost step: every such
error is `EtcdErr.refusal`), a not-sent error is indefinite. Otherwise the loop, carrying the
caller's update (exclusive or persistent, `callAU`) while the last attempt gave it back, or nothing
once an attempt fired or lost it (then the loop returns): `waitRetryBackoff` (an error: indefinite,
returned); an attempt; `nil`: return (fired). A context error (`isContextError`): the caller's
context done or a non-repeatable call: returned (indefinite); a repeatable call: resend (the update
persistent). `shouldRefreshToken` (a token refusal: the update was given back): `refreshToken`
(`clientCore`, see the margin): an error is returned after firing the update with it if it is a
refusal, else as indefinite; `nil`: resend. `isSafeRetry`: false: return the error (fired: a
definite answer; given back: a refusal fired by the interceptor; lost: indefinite); true (the policy
repeatable, or not sent, or a learner's refusal): resend. After the last attempt: as `false`.
This is the retry interceptor's discipline (`uiOk`: a non-repeatable call resent only after an
attempt that applied nothing).

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/Client__unaryClientInterceptor.lean` (over a
fixed set of servers' registrations): over the attempt contract, any principal, auth on.

Margin: the refresh needs the `Auth` field (`clientCore`); the interceptor is built before it is
set (open question 1 of the report).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.ApiLease

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ClientV3

open Iris Iris.BI EtcdModel EtcdWire
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `c.unaryClientInterceptor(optFuncs...)`: the client's unary interceptor (`uiOk`). -/
def Client.unaryClientInterceptor.spec : Prop :=
  ∀ (c : Loc) (γ : Cluster) (who : Principal) (sl : GoSlice) (fs : List (RetryOptsM → RetryOptsM)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ clientPre c γ who ∗ retryOptsAt sl fs }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!! go!"unaryClientInterceptor")) (Val #sl))
  {{ (ui : val), RET ui; uiOk ui c γ who }}

end spec

end ClientV3
end EtcdGrove
end Perennial
