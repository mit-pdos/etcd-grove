/-
`(*Typed[T]).Get()` (`queue.go`): blocks until the FIFO is non-empty or the queue is shutting
down; hands out the front item, which leaves the dirty set and joins the processing set
(`QState.get`), or reports the shutdown once the FIFO is empty. Lean-first.
-/
module

public import Proof.k8s_io.client_go.util.workqueue.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace workqueue

open Iris Iris.BI k8s_io.client_go.util.workqueue

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.util.workqueue.Assumptions]

/-- `q.Get()`: either an item `k` with its token (`keyTok γ k`: no other `Get` returns `k`
until `Done(k)`), or the zero item and `true` once the queue is shutting down and drained. -/
abbrev Typed.Get.spec : Prop :=
  ∀ {K : Type} {T : go.GoType} [QItem (GF := GF) K T] (q : Loc) (γ : QNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.util.workqueue ∗ isTyped (K := K) q γ }}
    (App (Val (q @!! go.GoType.PointerType (Typed.ty T) @!! go!"Get")) (Val #()))
  {{ (k : K) (sd : Bool), RET (PairV #k #sd);
      if sd then ⌜k = zero_val K⌝ ∗ shutdownLb γ else keyTok γ k }}

end spec

end workqueue
end EtcdGrove
end Perennial
