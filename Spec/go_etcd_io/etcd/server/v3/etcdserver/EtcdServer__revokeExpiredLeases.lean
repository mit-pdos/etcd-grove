/-
`(*EtcdServer).revokeExpiredLeases(leases)` (`server.go`). Lean-first (no Rocq counterpart); the
lease-expiry plan's X5 (`notes/lease-expiry-plan.md`, Part X and "Plumbing: Part X-a"). Names-only
for now: `run` takes it through the sealed open premise `srvRevokeOpen` (`LeaseRun.lean`), which
only a revocable-lease cluster's results discharge.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRunRes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`s.revokeExpiredLeases(leases)`**, `run`'s expiry arm (the lease-expiry plan's X5; 2026-11-04,
X-a: the call's statement, its proof a later step): with the server's persistent facts at that
point of `run` (its fields with auth off, `srvFieldsAt`, and its run fields, `srvRunFieldsAt`:
the stop channel, the server context, `GoAttach`'s protocol) and a slice `ls` of expired leases
as the lessor's `expiredC` delivers it (`lease.expiredLeases`: read-only, non-empty, each lease's
`ID` read-only, each id meeting the server's grant guard, which says the cluster grants leases and
auth is off), it returns (Go: `s.GoAttach` of the round, which checks leadership and proposes one
`LeaseRevoke` per lease, each in a goroutine of its own; the caller waits for none).

What the proof will add to the precondition (the plan's P1, thread tokens by level, and X6, the
revocation's request): the thread resources `GoAttach` takes and lends to the round's goroutines,
and what `ensureLeadership` and `LeaseRevoke` take. -/
abbrev EtcdServer.revokeExpiredLeases.spec : Prop :=
  ∀ (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF)
    (ρ : ReqNames) (v : SrvFields) (γr : ReadNames) (γg : GoNames)
    (γcx : context.ContextNames) (rv : RunFields) (SP : IProp GF) (ls : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvFieldsAt s γ ci TM E ρ v ∗ srvRunFieldsAt s γr γg γcx rv SP ∗
      lease.expiredLeases (srvGrantGuard E.lg E.authMode.isOn) ls }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"revokeExpiredLeases")) (Val #ls))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
