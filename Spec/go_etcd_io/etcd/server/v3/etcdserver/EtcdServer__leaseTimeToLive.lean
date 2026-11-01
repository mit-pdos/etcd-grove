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
lessor (`srvLessorRd`), a reader slot of the lessor's lock and a thread token, reading `r`: on
`nil`, a fresh response (owned) with a header (not nil); on an error, no response and one of the
server's or the lessor's package errors (`applyErrIs`: `ErrStopped`, `ErrTimeoutWaitAppliedIndex`,
`ErrLeaseNotFound`, `ErrLeaderChanged`, `ErrNoLeader`, `ErrTimeout`, `ErrCanceled`). Nothing is
stated of the response's lease, TTL or keys: on the leader it looks the lease up again (`Lookup`,
`Remaining`, `TTL`, `Keys`, `Demoted`, after `waitAppliedIndex`), on a follower it asks the leader
(`waitLeader`, `leasehttp.TimeToLiveHTTP` to each of its peer URLs, until the request's timeout),
so the keys are another lessor's or another lookup's (`issues/etcd-lease-timetolive-keys-toctou.md`).
**Its assumption on the cluster**: the leader's peer URLs are served by etcd's lease handler
(`leasehttp.NewHandler`), which always sets the reply's `LeaseTimeToLiveResponse` and its header; a
200 reply without the former panics (`issues/etcd-leasehttp-timetolive-nil-response-panic.md`). -/
abbrev EtcdServer.leaseTimeToLive.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (γl : GName)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (r : Loc) (dq : DFrac)
    (v : etcdserverpb.LeaseTimeToLiveRequest),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReqM E.authOn s E ρ ∗ isServerReadM E.authOn s E γr ∗ srvLessorRd s γl ∗
      context.isContext ctx cd ∗ lease.lessorRdOf γl ∗ threadTok ∗ ⌜threadBound GF ≤ 2 ^ 30 - 1⌝ ∗
      r ↦{dq} v }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"leaseTimeToLive"))
      (Val #(GoInterface.ok ctx))) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); lease.lessorRdOf γl ∗ threadTok ∗
      r ↦{dq} v ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ w : etcdserverpb.LeaseTimeToLiveResponse, resp ↦ w ∗
          ⌜w.Header' ≠ null⌝) ∨
       (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ applyErrIs err)) }}

end spec

end EtcdGrove
end Perennial
