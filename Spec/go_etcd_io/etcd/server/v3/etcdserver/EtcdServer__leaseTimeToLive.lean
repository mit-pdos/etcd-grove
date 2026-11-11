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
releasing its lock on return, `v3_server.go:636-675`; a follower takes no lessor lock) and the
level-0 token of the lessor's and the leases' leveled pools (`levelTok lease.lessorLvl`), which it
returns, reading `r`: on
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
**Its assumption on the cluster**, the premise `leasePeersOk` (`LeaseRead.lean`; until the axiom
review of 2026-11-02, `notes/axiom-review/lease-ttl-id.md`, it was only this docstring's, and a
program serving a peer address with an empty `200` got a proof of a panicking call): whatever
serves `/leases/internal` at the leader's peer URLs answers 200 only with a `LeaseTimeToLiveResponse`
and its header set, as etcd's lease handler (`leasehttp.NewHandler`) does; a 200 reply without the
former panics (`issues/etcd-leasehttp-timetolive-nil-response-panic.md`). A peer listener that does
not serve that path (the examples' members serve only the raft handler, `examples/lib/etcdstart`'s
`NewMember`) answers 404, which `TimeToLiveHTTP` reads as `ErrLeaseNotFound`: an error the triple
allows, though the lease may exist (seen 2026-11-02, `examples/etcd/lease/leasekv_cluster_test.go`).

**What the answer says of the lessor `γl`** (the lease-expiry plan's E2, revision 5, the user's,
2026-11-05), at the caller's lower bound `m` of its history (`lessorLb γl m`), under the lease-TTL
row (`leaseTTLRow s γl`: `s` is its cluster's only member, no membership change is admitted, in its
first start): a found lease's `GrantedTTL` is its TTL at an index `≥ m`, or the lease is absent from
`m` on; `ErrLeaseNotFound` (`errIsTrue` against it) means it is absent from `m` on. Why it is true of
Go (`v3_server.go:636-696`): *the leader path* (`isLeader()` true at the check), without the row:
`Lookup` runs after the check, at an index `≥ m` (the caller's `lessorLb γl m` and the history's
monotonicity); found, `GrantedTTL` is `le.TTL()`, the lease's `ttl` field, written only by `Grant`
before the lease enters the map (`lessor.go:301-302`; `ttlTie`); not found, `Lookup` returned `nil`.
*The forwarded path* (`isLeader()` false), under the row: `s`'s first start (its node made by
`StartNode`, `nodeStartedFresh`, so its log began as the bootstrap's configuration changes, and its
lessor's history begins empty) applies no lease before raft stores its leadership (`r.lead` is
stored from the `Ready` before its committed entries are sent to the apply loop,
`raft.go:190-202,237`), and a sole voter (every committed configuration `{mid}`, `confAt`) keeps
it once it has it: CheckQuorum counts the leader itself active (raft `raft.go:967-969,1299-1310`),
the shutdown's leadership transfer is skipped for a single voter (`server.go:1258,1316`),
`MoveLeader` rejects a transferee that is not a member (`server.go:1268-1271`) and raft ignores a
transfer to itself (`raft.go:1667-1669`), no other member exists to send a higher term or a
snapshot, and the trusted transport contract (decisions.md D21b (A)) delivers only the cluster's
members' messages; so at the check's index (`≥ m`) the lessor had no lease at all, whatever the
forwarded reply (`404`, which the examples' raft-only peer listeners answer,
`etcdstart/common.go:172`, or another answer). Hence the found arm's disjunction and the not-found
arm (Go's returned errors are leaves: `errIsTrue` with `ErrLeaseNotFound` means `err` is it).
Without the row both are false (a follower forwards to another member's lessor; a restarted member
applies replayed grants before its election and forwards: review round 3, R7). A change admitting
configuration changes or restarts with leases must revisit this spec. -/
abbrev EtcdServer.leaseTimeToLive.spec : Prop :=
  leasePeersOk →
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (γl : GName)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (r : Loc) (dq : DFrac)
    (v : etcdserverpb.LeaseTimeToLiveRequest) (m : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReqM E.authOn s E ρ ∗ isServerReadM E.authOn s E γr ∗ srvLessorRd s γl ∗
      context.isContext ctx cd ∗ lease.lessorRdPool γl ∗ levelTok lease.lessorLvl ∗ ⌜threadBound GF ≤ 2 ^ 30 - 1⌝ ∗
      lease.lessorLb γl m ∗ r ↦{dq} v }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"leaseTimeToLive"))
      (Val #(GoInterface.ok ctx))) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok lease.lessorLvl ∗
      r ↦{dq} v ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ w : etcdserverpb.LeaseTimeToLiveResponse, resp ↦ w ∗
          ⌜w.Header' ≠ null⌝ ∗ ⌜w.ID' = v.ID'⌝ ∗ (∃ hv : etcdserverpb.ResponseHeader, w.Header' ↦ hv) ∗
          □ (leaseTTLRow s γl -∗
              (∃ i : Nat, ⌜m ≤ i⌝ ∗ lease.leaseTTLAt γl i v.ID' w.GrantedTTL') ∨
              lease.leaseAbsentFrom γl m v.ID')) ∨
       (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ applyErrIs err ∗
          □ (∀ e : GoInterfaceOk,
              globalAddr go_etcd_io.etcd.server.v3.lease.ErrLeaseNotFound ↦□ GoInterface.ok e -∗
              errIsTrue err (GoInterface.ok e) -∗ leaseTTLRow s γl -∗
              lease.leaseAbsentFrom γl m v.ID'))) }}

end spec

end EtcdGrove
end Perennial
