/-
Proof of `Spec/k8s_io/client_go/util/workqueue/queue__Len.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.util.workqueue.queue__Len

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace workqueue

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.util.workqueue

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.util.workqueue.Assumptions]

theorem queue.Len.wp_proof : queue.Len.spec (GF := GF) (hG := hG) := by
  intro K T _ l xs
  wp_start as Hq
  iunfold ownFifo at Hq
  icases Hq with ⟨%s, Hl, Hs, Hcap⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  wp_auto
  rw [show (W64 (xs.length : Int)) = s.len by rw [Hlen.1]; word]
  iapply HΦ
  iunfold ownFifo
  iexists s
  iframe

end proof

end workqueue
end EtcdGrove
end Perennial
