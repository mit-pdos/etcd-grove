/-
`s.LeaseGrant(ctx, r)` (`v3_server.go:434-456` at the pin): the lease-grant plan's D4
(`notes/lease-grant-plan.md`, 2026-11-02). Lean-first (no Rocq counterpart); vocabulary
`Proof/go_etcd_io/etcd/server/v3/etcdserver/LeaseGrant.lean`.
-/
module

public import Proof.go_opentelemetry_io.otel.trace.Defs
public import Proof.context.ReqKeys
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.LeaseGrant
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.LeaseReqOn
public import Proof.context.LibKeys

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`s.LeaseGrant(ctx, r)`**, any goroutine, in a cluster that grants leases
(`srvGrantsLeases`), **in the environment's auth mode** (`E.authOn`; auth-lease S3b, 2026-11-15:
until then auth off), at a context, with the request path's resources (`Put`'s: the server's
request-side facts, the auth store's contract (`srvAuthAt`, for `requireAuthInfo`; the plan's
amendment (G), 2026-11-03), the leader-timeout reader, the backend reader `E.RD`, the id generator's
credits, freely minted), the decoded request (its `ID` owned) and the grant's permit
(`leaseGrantPermitM`: off nothing; on, the client's update at whichever id the member fixes, told its
grant under the binding of the header to the context): on `nil`, the server's response
(`leaseGrantedResp`: a lease id not `0`, its header with a revision the store has reached, and the
lease granted at an index of the lessor's history, its TTL at least the request's `ttl`: 2026-11-05,
the lease-expiry plan's E3/R5, the granted TTL), the caller authenticated (`authedOutB`, nothing with
auth off) and, with auth on, the client's result at the state before the grant's entry, for the id
the response names (`leaseGrantResM`); on an error, no response and an error the gRPC layer can take.

Why it is true of the Go code: while `r.ID` is `0` it writes `s.reqIDGen.Next() & (2^63-1)` there
(the owned field); `requireAuthInfo` returns `nil` with auth off and, with auth on, the context's
auth info or an error, which is returned; `raftRequest` proposes `{LeaseGrant: r}` and returns the
apply thread's result: the backend applier's `LeaseGrant` (`lessor.Grant` of `r.ID`, `r.TTL`)
answers a fresh response whose `ID` is the granted lease's, the lessor having appended the snapshot
with it (`lessor.Grant.spec`'s `leaseLiveFrom`, monotone: `leaseGrantedAt_of_live`); an id already
granted (`ErrLeaseExists`), a TTL above the maximum or a timeout are errors. With auth on the grant
has no permission and no lease check at apply (the model always grants it, `grantedAt_grant`), so
the client's update fires at its commit. The type assertion `resp.(*pb.LeaseGrantResponse)` does
not panic: the apply of a `LeaseGrant` request answers that type.

The margin (the review's M4): the request's `ID` is not given back (the post drops it); Go's unary
interceptors read no field of a `LeaseGrantRequest` after the handler (`v3rpc/interceptor.go`), so no
caller needs it. Conditional, through `NewServer`, on the deployment premise
`lease.leasesNoExpiry` (`srvGrantsLeases`). (Auth-lease S3b D5) The margin: the success does not say
the lease was added at the state the update fired at (the client's `Q id σ` can only condition on
it); no error branch carries a client result (D4).

(The lease-expiry plan's E3, 2026-11-04, the user's: generated ids only.) In the revocable lease mode
the request's `ID` is `0` (clientv3's `Grant` always sends `0`), so the lease id is always the
member's generator's: a revoked lease's id is never granted again (the plan's "absent stays absent").
A weaker spec (a premise more); the other modes as before. -/
abbrev EtcdServer.LeaseGrant.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (r : Loc) (ttl id0 : w64) (Q : w64 → KVState → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      ⌜srvGrantsLeases E ρ ∧ (ρ.rd.kv.lm = .revocable → id0 = W64 0)⌝ ∗
      isServerReqM E.authOn s E ρ ∗ srvAuthAt s E ∗ srvLeadTimeReader s ∗ E.RD ∗ □ (|==> idCred ρ.ids 1) ∗
      context.isContext ctx cd ∗ context.libCtxOk ctx ∗ trace.spanCtxOk ctx ∗ context.startTimeOk ctx ∗
      leaseGrantReqOwn r ttl id0 ∗
      leaseGrantPermitM E.authOn ρ.raft ρ.kv (hdrBoundM true s E (GoInterface.ok ctx)) ttl Q }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"LeaseGrant"))
      (Val #(GoInterface.ok ctx))) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); srvLeadTimeReader s ∗ E.RD ∗
      ((⌜err = GoInterface.nil ∧ resp ≠ null⌝ ∗ leaseGrantedResp E resp ttl ∗
          authedOutB s E.authMode (GoInterface.ok ctx) GoInterface.nil ∗
          leaseGrantResM E.authOn s E ρ ctx ttl resp Q) ∨
       (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ applyErrIs err)) }}

end spec

end EtcdGrove
end Perennial
