/-
`(*lessor).expireExists()` (`server/lease/lessor.go:697-726`), the expiry loop's step. Lean-first (no
Rocq counterpart); prove-ps2-newlessor3, 2026-11-21.
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

/-- `le.expireExists()` under the read lock, with the notifier the field points to (the expiry
loop took it from its cell, `notif_ropen`): `(nil, false)` with no item, or with the first item not
yet due; `(nil, true)` when the first item's lease is gone (the item unregistered); else the first
item's lease `l` of the lease map, its item re-registered at a later time. -/
abbrev lease.lessor.expireExists.spec : Prop :=
  ∀ (lp lm np : Loc) (dm dn : DFrac) (M : GMap w64 Loc) (ri : _root_.Perennial.time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗
      lF go!"leaseMap" lp ↦{dm} lm ∗ lm ↦${dm} M ∗ lF go!"leaseExpiredNotifier" lp ↦{dn} np ∗
      notifierAt np 1 ∗ lF go!"expiredLeaseRetryInterval" lp ↦□ ri }}
    (App (Val (lp @!! go.GoType.PointerType lessor.ty @!! go!"expireExists")) (Val #()))
  {{ (l : Loc) (next : Bool), RET (PairV #l #next);
      lF go!"leaseMap" lp ↦{dm} lm ∗ lm ↦${dm} M ∗ lF go!"leaseExpiredNotifier" lp ↦{dn} np ∗
      notifierAt np 1 ∗ (⌜l = null⌝ ∨ ⌜∃ id, M.lookup id = some l⌝) }}

end spec

end EtcdGrove
end Perennial
