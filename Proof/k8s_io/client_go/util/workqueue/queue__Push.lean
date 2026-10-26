/-
Proof of `Spec/k8s_io/client_go/util/workqueue/queue__Push.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.util.workqueue.queue__Push

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace workqueue

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.util.workqueue

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.util.workqueue.Assumptions]

theorem queue.Push.wp_proof : queue.Push.spec (GF := GF) (hG := hG) := by
  intro K T _ l xs k
  wp_start as Hq
  iunfold ownFifo at Hq
  icases Hq with ⟨%s, Hl, Hs, Hcap⟩
  wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %l1 ⟨Hl1, _⟩
  simp only [go.arrayLiteralSize, List.foldl]
  (try wp_auto)
  wp_apply wp_slice_append $$ [$Hs $Hcap $Hl1] as %s' ⟨Hs, Hcap, -⟩
  iapply HΦ
  iunfold ownFifo
  iexists s'
  iframe

end proof

end workqueue
end EtcdGrove
end Perennial
