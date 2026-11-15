/-
`s.LeaseRevoke(ctx, r)` (`v3_server.go:470-486` at the pin): the lease-expiry plan's X6
(`notes/lease-expiry-plan.md`, 2026-11-04). Lean-first (no Rocq counterpart); vocabulary
`Proof/go_etcd_io/etcd/server/v3/etcdserver/LeaseRevoke.lean`.
-/
module

public import Proof.go_opentelemetry_io.otel.trace.Defs
public import Proof.context.ReqKeys
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.LeaseRevoke
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.RevokeCtx
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

/-- **`s.LeaseRevoke(ctx, r)`**, any goroutine, in a cluster that revokes leases
(`srvRevokesLeases`: the lease mode `revocable`), **in the environment's auth mode** (`E.authOn`;
auth-lease S3b, 2026-11-15: until then auth off), at a context, with the request path's resources
(`LeaseGrant`'s: the server's request-side facts, the auth store's contract `srvAuthAt` for
`requireAuthInfo`, the leader-timeout reader, the backend reader `E.RD`, the id generator's
credits), the decoded request (`leaseRevokeReqRO`: not `null`, its `ID` read-only) and the
revocation's permit (`leaseRevokePermitM`: off nothing; on, the client's update, told its grant under
the binding of the header to the context): on `nil`, the server's response (`leaseRevokedResp`: its
header at a revision the store has reached, the revocation's commit applied), the caller
authenticated (`authedOutB`) and, with auth on, the revocation granted at the committed prefix before
its entry and the client's result at its state (`leaseRevokeResM`); on an error, no response and an
error the gRPC layer can take.

Why it is true of the Go code: the span reads `r.GetID()`; `requireAuthInfo` returns `nil` with auth
off and, with auth on, the context's auth info or an error, which is returned; `raftRequest` proposes
`{LeaseRevoke: r}` (`reqPropOk`'s revocation form, at the revocable mode; with auth on,
`reqPropOkOn`'s write form) and returns the apply thread's result: the backend applier's
`LeaseRevoke` (`lessor.Revoke` of `r.ID`, then `newHeader()`) answers a fresh
`*pb.LeaseRevokeResponse` whose header is the store's at the log after the revocation; a lease not
found (`ErrLeaseNotFound`), the auth layer's refusal (`checkLeasePuts`' permission check of the
lease's keys) or a timeout is an error. With auth on a success is not the auth layer's refusal, so
the model's auth state grants it (`authTie`). The type assertion `resp.(*pb.LeaseRevokeResponse)`
does not panic: the apply of a `LeaseRevoke` request answers that type (`apply.revokeAnswer`).

The margin (auth-lease S3b D5, review r1 S6): the success does not say the lease was live at the
state the update fired at (Go's success implies the lessor found it; the model's revocation of an id
not live commits nothing); no error branch carries a client result (D4). -/
abbrev EtcdServer.LeaseRevoke.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (r : Loc) (id : w64) (Q : KVState → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ ⌜srvRevokesLeases E ρ⌝ ∗
      isServerReqM E.authOn s E ρ ∗ srvAuthAt s E ∗ srvLeadTimeReader s ∗ E.RD ∗ □ (|==> idCred ρ.ids 1) ∗
      context.isContext ctx cd ∗ context.libCtxOk ctx ∗ trace.spanCtxOk ctx ∗ context.startTimeOk ctx ∗
      leaseRevokeReqRO r id ∗
      leaseRevokePermitM E.authOn ρ.raft ρ.kv (hdrBoundM true s E (GoInterface.ok ctx)) id Q }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"LeaseRevoke"))
      (Val #(GoInterface.ok ctx))) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); srvLeadTimeReader s ∗ E.RD ∗
      ((⌜err = GoInterface.nil ∧ resp ≠ null⌝ ∗ leaseRevokedResp E resp ∗
          authedOutB s E.authMode (GoInterface.ok ctx) GoInterface.nil ∗
          leaseRevokeResM E.authOn s E ρ ctx id Q) ∨
       (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ applyErrIs err)) }}

end spec

end EtcdGrove
end Perennial
