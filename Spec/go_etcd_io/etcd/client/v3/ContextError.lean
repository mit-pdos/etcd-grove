/-
`clientv3.ContextError` (`client/v3/client.go`).

Users: every method of the client after a gRPC call (`kv.go`, `txn.go`, `lease.go`, `auth.go`, `cluster.go`, `maintenance.go`, `watch.go`); users that convert their own errors (none in scope).

Proof sketch: `rpctypes.Error.spec` (2a, over `callErr`: `.etcd e` gives `errVal e`; the other kinds are left as
they are), `errors.As` into an `EtcdError` (true exactly for `errVal`s: `errVal_ty`), else
`status.FromError` (2a) and, for `Canceled`/`DeadlineExceeded`, `Context.Err.spec`/`ErrDone.spec`
(a context's error is `.other`: `callErr_ctxErr`).

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/ContextError.lean`: over `callErr` (was the client's `kvErr` and `ctxErrClient`); the context any `ctxOk`.

Margin: the code returns the context's own error for a gRPC `Canceled`/`DeadlineExceeded` once the context is done; the spec says only that the result is indefinite.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Api

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

/-- `ContextError(ctx, err)` of a call's error: `nil` stays `nil`; an etcd error of kind `e`
becomes `errVal e`; an indefinite one stays indefinite. -/
def ContextError.spec : Prop :=
  ∀ (ctx err : GoInterface) (k : CallErr),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ Context.ctxOk ctx ∗ (⌜err = GoInterface.nil⌝ ∨ callErr err k) }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.ContextError)) (Val #ctx)) (Val #err))
  {{ (err' : GoInterface), RET #err';
      (⌜err = GoInterface.nil ∧ err' = GoInterface.nil⌝) ∨
      (callErr err k ∗
        (match k with
         | .etcd e => if e.indefinite then indefCall err' else iprop(⌜err' = errVal e⌝)
         | _ => indefCall err')) }}

end spec

end ClientV3
end EtcdGrove
end Perennial
