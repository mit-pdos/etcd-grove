/-
`s.waitLeader(ctx)` (`v3_server.go`), names only: a trust-boundary contract. Lean-first (no Rocq counterpart); the
lease-renew plan (`notes/lease-renew-plan.md`, 2026-11-01), vocabulary `LeaseRead.lean`.
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

/-- **`s.waitLeader(ctx)`** (names-only, a contract; the lease-renew plan's C4), any goroutine, at a
context, with the request side's and the read side's server facts: a member `m` (read-only) and
its peer URLs `urls` (read-only) and `nil`; or `nil` and `ErrStopped` or `ErrNoLeader`
(`applyErrIs`).

**Why it is faithful.** `s.cluster.Member(s.Leader())` returns a clone of the cluster's member
(`RaftCluster.Member`: `m.Clone()`, a fresh copy, its `PeerURLs` slice copied too) or `nil`; while
`nil` it waits an election on `time.After`, `s.stopping` (`ErrStopped`) or `ctx.Done()`
(`ErrNoLeader`), then asks again; a member with no peer URL gives `ErrNoLeader`. The member is
fresh and nothing writes it after, so it may be shared read-only. -/
abbrev EtcdServer.waitLeader.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReqM E.authOn s E ρ ∗ isServerReadM E.authOn s E γr ∗ context.isContext ctx cd }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"waitLeader"))
      (Val #(GoInterface.ok ctx)))
  {{ (m : Loc) (err : GoInterface), RET (PairV #m #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ (v : go_etcd_io.etcd.server.v3.etcdserver.api.membership.Member)
          (urls : List GoString), m ↦□ v ∗ v.RaftAttributes'.PeerURLs' ↦*□ urls) ∨
      (⌜m = null ∧ err ≠ GoInterface.nil⌝ ∗ applyErrIs err) }}

end spec

end EtcdGrove
end Perennial
