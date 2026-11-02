/-
`s.LeaseTimeToLive(ctx, r)` (`v3_server.go`): the lease `TimeToLive` row. Lean-first (no Rocq counterpart); the lease-read plan
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

/-- **`s.LeaseTimeToLive(ctx, r)`**, any goroutine, at a context, with the server's facts
(`leaseTimeToLive`'s), the key check's resources (`checkLeaseTimeToLive.spec`'s: the auth store and
lessor at lower bounds `n`, `m`, their readers, a thread token), reading `r`: on `nil`,
`leaseTimeToLive`'s response (owned, with its header owned), the request authenticated (`authedOutB`:
`requireAuthInfo`'s) and, if it asks for the keys (`r.Keys`), auth disabled at a state no older than
`n`, or its principal an admin at one or allowed to read every key of the lease `r.ID` at a lessor
index no older than `m` (`leaseKeysVerdictFrom`; none if the lease was not live there); on an error,
no response and an error the gRPC layer can take. **The margin**: the keys it checked, not the keys
it returns. The response is `leaseTimeToLive`'s, which looks the lease up again, on the leader or
through it (its contract states nothing of the keys), so a key attached in between is returned
unchecked (`issues/etcd-lease-timetolive-keys-toctou.md`). The revision re-check
(`ErrAuthOldRevision` unless the auth revision is still the check's) is not stated
(`checkLeaseRenew.spec`'s margin). -/
abbrev EtcdServer.LeaseTimeToLive.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (γl : GName)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (r : Loc) (dq : DFrac)
    (v : etcdserverpb.LeaseTimeToLiveRequest) (n m : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReqM E.authOn s E ρ ∗ isServerReadM E.authOn s E γr ∗
      srvAuthAt s E ∗ srvAuthLeaseLb s E ∗ srvLessorRd s γl ∗ auth.authPubLbM E.authMode n ∗
      lease.lessorLb γl m ∗ context.isContext ctx cd ∗ E.RD ∗ lease.lessorRdPool γl ∗ threadTok ∗
      ⌜threadBound GF ≤ 2 ^ 30 - 1⌝ ∗ r ↦{dq} v }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"LeaseTimeToLive"))
      (Val #(GoInterface.ok ctx))) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); E.RD ∗
      threadTok ∗ r ↦{dq} v ∗
      ((⌜err = GoInterface.nil⌝ ∗
          (∃ w : etcdserverpb.LeaseTimeToLiveResponse, resp ↦ w ∗ ⌜w.Header' ≠ null⌝ ∗
            ⌜w.ID' = v.ID'⌝ ∗ ∃ hv : etcdserverpb.ResponseHeader, w.Header' ↦ hv) ∗
          authedOutB s E.authMode (GoInterface.ok ctx) GoInterface.nil ∗
          (if v.Keys' then leaseCheckFrom s E (GoInterface.ok ctx) n
              (fun info => leaseKeysVerdictFrom E.authMode n info γl m v.ID' .read)
            else iprop(True))) ∨
       (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ applyErrIs err)) }}

end spec

end EtcdGrove
end Perennial
