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
(`srvRevokesLeases`: the lease mode `revocable`, auth off), at a context, with the request path's
resources (`LeaseGrant`'s: the server's request-side facts, the auth store's contract `srvAuthAt`
for `requireAuthInfo`, the leader-timeout reader, the backend reader `E.RD`, the id generator's
credits) and the decoded request (`leaseRevokeReqRO`: not `null`, its `ID` read-only): on `nil`, the
server's response (`leaseRevokedResp`: its header at a revision the store has reached, the
revocation's commit applied); on an error, no response and an error the gRPC layer can take.

Why it is true of the Go code: the span reads `r.GetID()`; `requireAuthInfo` returns `nil` with auth
off; `raftRequest` proposes `{LeaseRevoke: r}` (`reqPropOk`'s revocation form, at the revocable
mode) and returns the apply thread's result: the backend applier's `LeaseRevoke` (`lessor.Revoke`
of `r.ID`, then `newHeader()`) answers a fresh `*pb.LeaseRevokeResponse` whose header is the store's
at the log after the revocation; a lease not found (`ErrLeaseNotFound`) or a timeout is an error. The
type assertion `resp.(*pb.LeaseRevokeResponse)` does not panic: the apply of a `LeaseRevoke` request
answers that type (`apply.revokeAnswer`). -/
abbrev EtcdServer.LeaseRevoke.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (r : Loc) (id : w64),
  srvRevokesLeases E ρ →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReq s E ρ ∗ srvAuthAt s E ∗ srvLeadTimeReader s ∗ E.RD ∗ □ (|==> idCred ρ.ids 1) ∗
      context.isContext ctx cd ∗ context.libCtxOk ctx ∗ trace.spanCtxOk ctx ∗ context.startTimeOk ctx ∗ leaseRevokeReqRO r id }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"LeaseRevoke"))
      (Val #(GoInterface.ok ctx))) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); srvLeadTimeReader s ∗ E.RD ∗
      ((⌜err = GoInterface.nil ∧ resp ≠ null⌝ ∗ leaseRevokedResp E resp) ∨
       (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ applyErrIs err)) }}

end spec

end EtcdGrove
end Perennial
