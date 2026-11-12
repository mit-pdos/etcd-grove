/-
`(*EtcdServer).revokeExpiredLeases(leases)` (`server.go`). Lean-first (no Rocq counterpart); the
lease-expiry plan's X5 (`notes/lease-expiry-plan.md`, Part X and "Plumbing: Part X-a"). Translated
and proved (revoke-open pass 2, 2026-11-06; until then names-only): `run` takes it through the
sealed premise `srvRevokeOpen` (`LeaseRun.lean`), which only a revocable-lease cluster's results
discharge, with the linked proof (`srvRevokeOpen_intro`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.RevokeCtx

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

(revoke-open, 2026-11-06, Q8; `notes/revoke-open-plan.md`, "Draft pass 1", I.1) In a cluster that
revokes leases (the KV names' lease mode `revocable`; auth off follows from the slice's grant guard,
`srvGrantGuard_expired`, and with it `srvRevokesLeases`), with levels `0 … srvRevokeK - 1` of a
thread token (`srvRevokeLevels`), the revocation's persistent bundle (`srvRevokeCtx`: the pools its
goroutines borrow from, the request side's views, the server context) and the caller's thread
token, which it returns (its goroutines' reader slots come from pools backed by it). (Review round 1,
NIT 1.1–1.2, 2026-11-06: the premises a `⌜…⌝` conjunct, until then Lean implications, and the lease
mode alone, until then `srvRevokesLeases E ρ`.) -/
abbrev EtcdServer.revokeExpiredLeases.spec : Prop :=
  ∀ (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF)
    (ρ : ReqNames) (v : SrvFields) (γr : ReadNames) (γg : GoNames)
    (γcx : context.ContextNames) (rv : RunFields) (SP : IProp GF) (ls : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvFieldsAt s γ ci TM E ρ v ∗ srvRunFieldsAt s γr γg γcx rv SP ∗
      lease.expiredLeases (srvGrantGuard E.lg E.authMode.isOn) ls ∗
      srvRevokeCtx s E ρ γr γg ∗ ⌜ρ.rd.kv.lm = .revocable ∧ srvRevokeLevels (GF := GF)⌝ ∗
      threadTok }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"revokeExpiredLeases")) (Val #ls))
  {{ RET #(); threadTok }}

end spec

end EtcdGrove
end Perennial
