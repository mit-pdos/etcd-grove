/-
`(*LeaseExpiredNotifier).Init` (`server/lease/lease_queue.go`). Lean-first (no Rocq counterpart);
see `Proof/go_etcd_io/etcd/server/v3/lease/InvLessor.lean`.
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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

/-- `mq.Init()` (`lessor.initAndRecover`'s, at `Recover`): the notifier stays a notifier. Go
heapifies the queue (`heap.Init`) and rebuilds the map from it: the queue's items stay, **not
emptied** (the lease-expiry plan, S1 (i)), so after `Recover` the notifier may hold items of leases
no longer in the lessor's map, which `notifierAt` admits (it ties the map to the queue, not to the
lessor's leases; Go's `findExpiredLeases` drops such an item). -/
abbrev lease.LeaseExpiredNotifier.Init.spec : Prop :=
  ∀ (np : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ notifierAt np 1 }}
    (App (Val (np @!! go.GoType.PointerType LeaseExpiredNotifier.ty @!! go!"Init")) (Val #()))
  {{ RET #(); notifierAt np 1 }}

end spec

end EtcdGrove
end Perennial
