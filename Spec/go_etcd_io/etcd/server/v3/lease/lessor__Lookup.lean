/-
`(*lessor).Lookup` (`server/lease/lessor.go`). Lean-first (no Rocq counterpart); see
`Proof/go_etcd_io/etcd/server/v3/lease/InvLessor.lean`.
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

/-- `le.Lookup(id)` (read-locked), by the lease owner or by a reader (the lease-keys plan, item 3
and Part B, 2026-10-31), with a lower bound `m` of the lessor's history: the lease map of an index
no earlier than `m` (the one the read lock found): `nil` and no lease of `id` there, or a lease `l`
of `id` there. For the owner (`U = some (L, I)`, `leaseOwn γl L I`; until item 3 any share of the
live set), moreover `nil` exactly when `id` is not live, and its resource as it was or opened at
`l` (`leaseOwnOpen`: its item set, which `Keys()` reads); the owner holds a lower bound itself
(`leaseOwn_lb`).
(auth-lease S4 item 7b, 2026-11-17) The owner's view in any window `w` (`lookupViewW`), passed through. -/
abbrev lease.lessor.Lookup.spec : Prop :=
  ∀ (lp : Loc) (γl : GName) (id : w64) (m : Nat) (U : Option (List w64 × GMap LeaseItem w64))
    (w : Option LWin),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ lessorInv lp γl ∗
      lessorRd lp γl ∗ lessorLb γl m ∗ lookupViewW γl w U }}
    (App (Val (lp @!! go.GoType.PointerType lessor.ty @!! go!"Lookup")) (Val #id))
  {{ (l : Loc), RET #l; lessorRd lp γl ∗
      ((⌜l = null⌝ ∗ leaseAbsentFrom γl m id) ∨ (isLeaseObj γl l ∗ leaseLiveFrom γl m id l)) ∗
      lookupViewAfterW γl id l w U }}

end spec

end EtcdGrove
end Perennial
