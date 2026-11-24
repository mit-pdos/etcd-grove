/-
`(*LeaseExpiredNotifier).Len` (`server/lease/lease_queue.go`). Lean-first (no Rocq counterpart); see
`Proof/go_etcd_io/etcd/server/v3/lease/InvLessor.lean`. (prove-ps2-newlessor3, 2026-11-21: for the
expiry loop's `expireExists`.)
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

/-- `mq.Len()`, `len(mq.m)`: the number of leases registered (at any share). -/
abbrev lease.LeaseExpiredNotifier.Len.spec : Prop :=
  ∀ (np : Loc) (q : Qp) (M : GMap w64 Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ notifierAtM np q M }}
    (App (Val (np @!! go.GoType.PointerType LeaseExpiredNotifier.ty @!! go!"Len")) (Val #()))
  {{ RET #(W64 (GMap.size M)); notifierAtM np q M ∗ ⌜GMap.size M < 2 ^ 63⌝ }}

end spec

end EtcdGrove
end Perennial
