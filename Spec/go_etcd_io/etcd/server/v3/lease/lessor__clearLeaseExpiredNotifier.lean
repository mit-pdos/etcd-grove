/-
`lessor.clearLeaseExpiredNotifier` (`server/lease/lessor.go`). Lean-first (no Rocq counterpart; prove-ps2-lease, 2026-11-21, for
`lessor.Demote`); see `Proof/go_etcd_io/etcd/server/v3/lease/InvLessor.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.InvLessor

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.lease lease

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

/-- `le.clearLeaseExpiredNotifier()`: `le.leaseExpiredNotifier` set to a fresh, empty notifier. -/
abbrev lease.lessor.clearLeaseExpiredNotifier.spec : Prop :=
  ∀ (lp np : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗
      lF go!"leaseExpiredNotifier" lp ↦ np }}
    (App (Val (lp @!! go.GoType.PointerType lessor.ty @!! go!"clearLeaseExpiredNotifier")) (Val #()))
  {{ RET #(); ∃ np' : Loc, lF go!"leaseExpiredNotifier" lp ↦ np' ∗ notifierAt np' 1 }}

end spec

end EtcdGrove
end Perennial
