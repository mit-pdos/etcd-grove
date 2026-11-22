/-
`LeaseQueue.Pop` (`server/lease/lease_queue.go`). Lean-first (no Rocq counterpart); see
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

/-- `pq.Pop()` on a queue holding `xs ++ [a]` (`heap.Pop`'s last step): removes the last item and
returns it, its `index` set to `-1`, the caller's. -/
abbrev lease.LeaseQueue.Pop.spec : Prop :=
  ∀ (qf : Loc) (s : GoSlice) (xs : List (Loc × w64)) (a : Loc × w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ qf ↦ s ∗
      queueAt s (xs ++ [a]) 1 }}
    (App (Val (qf @!! go.GoType.PointerType LeaseQueue.ty @!! go!"Pop")) (Val #()))
  {{ RET #(interface.mkOk (go.GoType.PointerType LeaseWithTime.ty) #a.1 : GoInterface);
      (∃ s' : GoSlice, qf ↦ s' ∗ queueAt s' xs 1) ∗ lwtAt a.1 a.2 (W64 (-1)) 1 }}

end spec

end EtcdGrove
end Perennial
