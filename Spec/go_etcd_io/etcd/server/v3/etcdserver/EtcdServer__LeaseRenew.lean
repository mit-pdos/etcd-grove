/-
`s.LeaseRenew(ctx, id)` (`v3_server.go`): the lease keep-alive row's entry point. Lean-first (no
Rocq counterpart); the lease-renew plan (`notes/lease-renew-plan.md`, 2026-11-01), vocabulary
`LeaseRead.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.LeaseRead
public import Code.net.http

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

/-- **`s.LeaseRenew(ctx, id)`**, any goroutine, at a context, with the server's facts and the key
check's resources (`LeaseTimeToLive.spec`'s), reader slots of the logger's lock and of the read
loop's (`srvLgReader`, `srvReadReader`: `ensureLeadership`'s, and an unexpected error of the
forwarding's context is logged), and the server's peer round tripper (`peerRt`, a
`*http.Transport`: `NewServer` stores the bootstrap's `rafthttp.NewRoundTripper` one; a premise,
as no construction spec states the field yet): on `nil`, a TTL and the renewal's key check passed
(the last `checkLeaseRenew`'s: auth disabled at a state no older than `n`, or the principal an
admin at one or allowed to write every key of the lease `id` at a lessor index no older than `m`,
`leaseKeysVerdictFrom .write`); on an error, an error the gRPC layer can take. Nothing is stated
of the TTL.

**The margin**: the keys it checked, not the keys of the lease it renews. On the leader the check
reads the lessor and `Renew` looks the lease up again, so a key attached in between is renewed
unchecked (as `LeaseTimeToLive`'s, `issues/etcd-lease-timetolive-keys-toctou.md`); the check reads
the local lessor, which may lag the lessor that renews: a follower's, the leader's
(`issues/etcd-lease-renew-keys-follower-lag.md`), and the leader's own with `FastLeaseKeepAlive`
and the lease found, which skips `waitAppliedIndex` (entries committed but not yet applied). The
revision re-check is not stated (`checkLeaseRenew.spec`'s margin). -/
abbrev EtcdServer.LeaseRenew.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (γl : GName)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (id : w64) (n m : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReqM E.authOn s E ρ ∗ isServerReadM E.authOn s E γr ∗
      srvAuthAt s E ∗ srvAuthLeaseLb s E ∗ srvLessorRd s γl ∗ auth.authPubLbM E.authMode n ∗
      lease.lessorLb γl m ∗ context.isContext ctx cd ∗ E.RD ∗ lease.lessorRdOf γl ∗ threadTok ∗
      srvLgReader s ∗ srvReadReader s γr ∗ ⌜threadBound GF ≤ 2 ^ 30 - 1⌝ ∗
      (∃ (rt : GoInterface), structFieldRef EtcdServer go!"peerRt" s ↦□ rt ∗
        ⌜∃ t : Loc,
          rt = GoInterface.ok ⟨go.GoType.PointerType _root_.Perennial.net.http.Transport.ty, #t⟩⌝) }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"LeaseRenew"))
      (Val #(GoInterface.ok ctx))) (Val #id))
  {{ (ttl : w64) (err : GoInterface), RET (PairV #ttl #err); E.RD ∗ lease.lessorRdOf γl ∗
      threadTok ∗ srvLgReader s ∗ srvReadReader s γr ∗
      ((⌜err = GoInterface.nil⌝ ∗ leaseCheckFrom s E (GoInterface.ok ctx) n
          (fun info => leaseKeysVerdictFrom E.authMode n info γl m id .write)) ∨
       (⌜err ≠ GoInterface.nil⌝ ∗ applyErrIs err)) }}

end spec

end EtcdGrove
end Perennial
