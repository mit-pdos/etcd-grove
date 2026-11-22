/-
The lessor's queues' `Pop` as `container/heap`'s (prove-ps2-newlessor3, 2026-11-21; for the expiry
notifier's `Unregister`). Lean-first (no Rocq counterpart); see `QueueLemmas.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.QueueLemmas
public import Spec.go_etcd_io.etcd.server.v3.lease.LeaseQueue__Pop
public import Spec.container.heap.Pop

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lease

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.lease

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

/-- **`&q`'s `Pop`** over `queueHeap qf`. -/
theorem queue_heapPopIface
    (hPop : lease.LeaseQueue.Pop.spec (GF := GF) (hG := hG))
    (qf : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ⊢
      heap.heapPopIface (interface.mk (go.GoType.PointerType LeaseQueue.ty) #qf) (queueHeap qf)
        queueElem := by
  iintro #Hpkg
  iunfold heap.heapPopIface
  iintro !> %xs %a %Φ !> Hq HΦ
  iunfold queueHeap at Hq
  icases Hq with ⟨%s, Hqf, Hq⟩
  wp_apply (hPop qf s xs a) $$ [$Hqf $Hq] as ⟨⟨%s', Hqf, Hq⟩, Ha⟩
  iapply HΦ
  isplitl [Hqf Hq]
  · iunfold queueHeap; iexists s'; iframe
  iunfold queueElem
  isplitr
  · ipureintro; rfl
  iexists _; iexact Ha

end lemmas

end lease
end EtcdGrove
end Perennial
