/-
`(*LeaseExpiredNotifier).Unregister` (`server/lease/lease_queue.go`). Lean-first (no Rocq counterpart); see
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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

/-- `mq.Unregister()`, with a lease registered (`heap.Pop` of an empty queue panics): pops the
queue's first item and unregisters its id, returning the item (the caller's). -/
abbrev lease.LeaseExpiredNotifier.Unregister.spec : Prop :=
  ∀ (np : Loc) (M : GMap w64 Loc),
  M ≠ ∅ →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ notifierAtM np 1 M }}
    (App (Val (np @!! go.GoType.PointerType LeaseExpiredNotifier.ty @!! go!"Unregister"))
      (Val #()))
  {{ (p : Loc), RET #p; ∃ (id k : w64), ⌜M.lookup id = some p⌝ ∗ notifierAtM np 1 (M.delete id) ∗
      lwtAt p id k 1 }}

end spec

end EtcdGrove
end Perennial
