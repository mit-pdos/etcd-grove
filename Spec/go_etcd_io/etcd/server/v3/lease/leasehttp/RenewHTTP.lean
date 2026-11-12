/-
`leasehttp.RenewHTTP(ctx, id, url, rt)` (`server/lease/leasehttp/http.go`), names only: a
trust-boundary contract. Lean-first (no Rocq counterpart); the lease-renew plan
(`notes/lease-renew-plan.md`, 2026-11-01).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.LeaseRead
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.SrvCtxWeak
public import Code.net.http
public import Proof.go_etcd_io.etcd.server.v3.lease.leasehttp.Base
public import GeneratedProof.go_etcd_io.etcd.server.v3.lease.leasehttp

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.lease.leasehttp

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.leasehttp.Assumptions]

/-- **`RenewHTTP(ctx, id, url, rt)`** (names-only, a contract; the lease-renew plan's C5), any
goroutine, at a context, over a standard library HTTP transport (`rt` a `*http.Transport`: what
`rafthttp.NewRoundTripper` builds, `transport.NewTimeoutTransport`): a TTL and `nil`, or an error
the gRPC layer can take (`applyErrIs`). Nothing is stated of the TTL.

**Why it is faithful.** It marshals a `LeaseKeepAliveRequest` (`proto.Marshal`), builds a POST
request to `url` with the context (`http.NewRequest`, `WithContext`), sends it with an
`http.Client` over `rt` (`Do`: the standard library's transport, whatever the URL or the peer
answers), reads the reply (`readResponse`: the body, which `http.Client` never leaves `nil`,
closed) and decodes a `LeaseKeepAliveResponse` (`proto.Unmarshal`) into a fresh message whose TTL
it returns; its errors are the marshal's, the request's, the client's (a `*url.Error`),
`ErrLeaseHTTPTimeout` (a 408), `lease.ErrLeaseNotFound` (a 404), an `fmt.Errorf` value (another
status, or a reply whose ID is not `id`) or the decode's, each an error value with an `Error()`.
**Its assumption on the cluster**, as `leaseTimeToLive.spec`'s: a peer's reply is small enough to
buffer (`readResponse` reads up to `maxLeaseHTTPResponseSize`, 100 MiB, per call); the model has no
memory bound to state it with.
(k8s 7f-4, T-f) The context is a stream handler's weak one (`srvCtxWeak`, which every `isContext`
is: `srvCtxWeak_of_isContext`): `req.WithContext(ctx)`; net/http's transport works on its own
`context.WithCancelCause(req.Context())` (go1.27 `net/http/transport.go:675`), whose `Err`/`Cause`
are its own `*cancelCtx`'s, and HTTP/2's (`net/http/internal/http2`) reads `ctx.Err()` only once
`ctx.Done()` is closed, but for `shouldRetryDial`'s nil test (`client_conn_pool.go:284`), which
only decides whether to dial again. An `Err()` of `ErrGRPCNoLeader`, or a non-nil one before
`Done`, at most changes which error is returned, and the post accepts every error here
(`examples/premisefix/streamctx`, `TestRenewHTTPErrTiming`: a context whose `Err()` panics before
`Done` and is `ErrGRPCNoLeader` after; it is not called during a live call, nor when the context is
cancelled in flight, and the cancelled call returns a `*url.Error` of `context.Canceled`; on a
context already done when `RenewHTTP` is called, the transport's `WithCancelCause` calls it twice,
synchronously on the caller's goroutine, in `propagateCancel` and `Cause`, go1.27.3
`context.go:487, 290`, and a `*url.Error` is returned). (k8s 7f-4, T-f') `srvCtxWeak`'s `Err` clauses take a level
token (`levelTok v3rpc.ctxErrLvl`, the reader slot of the wrapper's `RWMutex`), which the premise
does not hand over: net/http calls `ctx.Err()` only from live goroutines (the caller's and the
transport's own), each a thread, so the read locks it holds at one time are bounded by the threads,
which is what the token accounts for in the logic (the Freeze addendum T-f'). -/
abbrev leasehttp.RenewHTTP.spec : Prop :=
  ∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (id : w64) (url : GoString)
    (rt : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease.leasehttp ∗
      srvCtxWeak ctx cd ∗
      ⌜∃ t : Loc, rt = GoInterface.ok ⟨go.GoType.PointerType _root_.Perennial.net.http.Transport.ty, #t⟩⌝ }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.lease.leasehttp.RenewHTTP))
      (Val #(GoInterface.ok ctx))) (Val #id)) (Val #url)) (Val #rt))
  {{ (ttl : w64) (err : GoInterface), RET (PairV #ttl #err);
      ⌜err = GoInterface.nil⌝ ∨ (⌜err ≠ GoInterface.nil⌝ ∗ applyErrIs err) }}

end spec

end EtcdGrove
end Perennial
