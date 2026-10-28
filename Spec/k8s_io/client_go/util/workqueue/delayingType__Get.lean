/-
`(*delayingType[T]).Get` (`delaying_queue.go`): promoted from the embedded
`TypedInterface[T]` field (Go's method set of `*delayingType[T]`, a wrapper
that calls `q.TypedInterface.Get`). Lean-first.

**Not translated (gap C2, `notes/k8s-clientgo-goose.md`)**: the pinned Goose writes the
pointer receiver's unfolding of a promoted method of a generic struct ill-typed, so the
translation's configuration excludes it (`Code/k8s_io/client_go/util/workqueue.toml`): there is no
`MethodUnfold` for it, and its proof is `sorry` until the Perennial fix and a pin bump. The spec
is what follows from the embedded `Typed.Get`'s.
-/
module

public import Proof.k8s_io.client_go.util.workqueue.DelayingDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace workqueue

open Iris Iris.BI k8s_io.client_go.util.workqueue

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.util.workqueue.Assumptions]

/-- `(*delayingType[T]).Get`, the method `delayingType` promotes from its embedded `TypedInterface`: `Get()`, as `Typed.Get`
on the embedded queue. -/
abbrev delayingType.Get.spec : Prop :=
  ∀ {K : Type} {T : go.GoType} [QItem (GF := GF) K T] (q : Loc) (γ : DNames) ,
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.util.workqueue ∗ isDelaying (K := K) q γ }}
    (App (Val (q @!! go.GoType.PointerType (delayingType.ty T) @!! go!"Get")) (Val #()))
  {{ (k : K) (sd : Bool), RET (PairV #k #sd);
      if sd then ⌜k = zero_val K⌝ ∗ shutdownLb γ.tq else keyTok γ.tq k }}

end spec

end workqueue
end EtcdGrove
end Perennial
