/-
`s.LeaseGrant(ctx, r)` (`v3_server.go:434-456` at the pin): the lease-grant plan's D4
(`notes/lease-grant-plan.md`, 2026-11-02). Lean-first (no Rocq counterpart); vocabulary
`Proof/go_etcd_io/etcd/server/v3/etcdserver/LeaseGrant.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.LeaseGrant

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
(`srvGrantsLeases`), at a context, with the request path's resources (`Put`'s: the server's
request-side facts, the leader-timeout reader, the backend reader `E.RD`, the id generator's
credits, freely minted) and the decoded request (its `ID` owned): on `nil`, the server's response
(`leaseGrantedResp`: a lease id not `0`, its header with a revision the store has reached, and the
lease granted at an index of the lessor's history); on an error, no response and an error the gRPC layer can take.

Why it is true of the Go code: while `r.ID` is `0` it writes `s.reqIDGen.Next() & (2^63-1)` there
(the owned field); `requireAuthInfo` returns `nil` with auth off; `raftRequest` proposes
`{LeaseGrant: r}` and returns the apply thread's result: the backend applier's `LeaseGrant`
(`lessor.Grant` of `r.ID`, `r.TTL`) answers a fresh response whose `ID` is the granted lease's,
the lessor having appended the snapshot with it (`lessor.Grant.spec`'s `leaseLiveFrom`, monotone:
`leaseGrantedAt_of_live`); an id already granted (`ErrLeaseExists`), a TTL above the maximum or a
timeout are errors. The type assertion `resp.(*pb.LeaseGrantResponse)` does not panic: the apply
of a `LeaseGrant` request answers that type.

The margin (the review's M4): the request's `ID` is not given back (the post drops it); Go's unary
interceptors read no field of a `LeaseGrantRequest` after the handler (`v3rpc/interceptor.go`), so no
caller needs it. Conditional, through `NewServer`, on the deployment premise
`lease.leasesNoExpiry` (`srvGrantsLeases`). -/
abbrev EtcdServer.LeaseGrant.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (r : Loc) (ttl id0 : w64),
  srvGrantsLeases E ρ →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReq s E ρ ∗ srvLeadTimeReader s ∗ E.RD ∗ □ (|==> idCred ρ.ids 1) ∗
      context.isContext ctx cd ∗ leaseGrantReqOwn r ttl id0 }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"LeaseGrant"))
      (Val #(GoInterface.ok ctx))) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); srvLeadTimeReader s ∗ E.RD ∗
      ((⌜err = GoInterface.nil ∧ resp ≠ null⌝ ∗ leaseGrantedResp E resp) ∨
       (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ applyErrIs err)) }}

end spec

end EtcdGrove
end Perennial
