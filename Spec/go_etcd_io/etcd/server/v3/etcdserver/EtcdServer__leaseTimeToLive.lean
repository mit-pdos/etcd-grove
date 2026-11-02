/-
`s.leaseTimeToLive(ctx, r)` (`v3_server.go`), names only: a trust-boundary contract. Lean-first (no Rocq counterpart); the lease-read plan
(`notes/lease-read-plan.md`, 2026-10-31), vocabulary `LeaseRead.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.LeaseRead

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

/-- **`s.leaseTimeToLive(ctx, r)`** (names-only, a contract; the lease-read plan's S1, the user's
choice), any goroutine, at a context, with the request side's and the read side's server facts, its
lessor (`srvLessorRd`), the lessor's reader pool (`lessorRdPool`; a reader slot of the lessor's
lock until the lease-src plan, 2026-11-02: on the leader the slot is borrowed for `Lookup` and given
back before `Remaining()`, `Keys()` and `Demoted()`, which take the token one after another, each
releasing its lock on return, `v3_server.go:636-675`; a follower takes no lessor lock) and a thread
token, reading `r`: on
`nil`, a fresh response (owned) with a fresh header (owned, not nil: the leader's
`&pb.ResponseHeader{}`, under `// TODO: fill out ResponseHeader`; a follower's decoded by
`proto.Unmarshal` from the leader's reply, whose header etcd's lease handler sets, empty too;
stated 2026-11-01 for the gRPC handler's `fill`, `notes/lease-grpc-plan.md`; a reply whose
response has no header panics that `fill`, `issues/etcd-leasehttp-timetolive-nil-header-panic.md`); on an error, no response and one of the
server's or the lessor's package errors (`applyErrIs`: `ErrStopped`, `ErrTimeoutWaitAppliedIndex`,
`ErrLeaseNotFound`, `ErrLeaderChanged`, `ErrNoLeader`, `ErrTimeout`, `ErrCanceled`). The response
is about the asked lease (`ID`; stated 2026-11-02 for the closed lease example,
`notes/lease-ex-plan.md`): the leader's literal has `ID: r.ID`, and a follower's
`leasehttp.TimeToLiveHTTP` returns only a reply whose `LeaseTimeToLiveResponse.ID` is the asked ID
(`lease: TTL id mismatch` otherwise, `http.go:274`). Nothing is stated of its TTL or keys: on the leader it looks the lease up again (`Lookup`,
`Remaining`, `TTL`, `Keys`, `Demoted`, after `waitAppliedIndex`), on a follower it asks the leader
(`waitLeader`, `leasehttp.TimeToLiveHTTP` to each of its peer URLs, until the request's timeout),
so the keys are another lessor's or another lookup's (`issues/etcd-lease-timetolive-keys-toctou.md`).
**Its assumption on the cluster**: whatever serves `/leases/internal` at the leader's peer URLs
answers 200 only with a `LeaseTimeToLiveResponse` and its header set, as etcd's lease handler
(`leasehttp.NewHandler`) does; a 200 reply without the former panics
(`issues/etcd-leasehttp-timetolive-nil-response-panic.md`). A peer listener that does not serve
that path (the examples' members serve only the raft handler, `examples/common`'s `NewMember`)
answers 404, which `TimeToLiveHTTP` reads as `ErrLeaseNotFound`: an error the triple allows,
though the lease may exist (seen 2026-11-02, `examples/leasekv/leasekv_cluster_test.go`). -/
abbrev EtcdServer.leaseTimeToLive.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (γl : GName)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (r : Loc) (dq : DFrac)
    (v : etcdserverpb.LeaseTimeToLiveRequest),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReqM E.authOn s E ρ ∗ isServerReadM E.authOn s E γr ∗ srvLessorRd s γl ∗
      context.isContext ctx cd ∗ lease.lessorRdPool γl ∗ threadTok ∗ ⌜threadBound GF ≤ 2 ^ 30 - 1⌝ ∗
      r ↦{dq} v }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"leaseTimeToLive"))
      (Val #(GoInterface.ok ctx))) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); threadTok ∗
      r ↦{dq} v ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ w : etcdserverpb.LeaseTimeToLiveResponse, resp ↦ w ∗
          ⌜w.Header' ≠ null⌝ ∗ ⌜w.ID' = v.ID'⌝ ∗ ∃ hv : etcdserverpb.ResponseHeader, w.Header' ↦ hv) ∨
       (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ applyErrIs err)) }}

end spec

end EtcdGrove
end Perennial
