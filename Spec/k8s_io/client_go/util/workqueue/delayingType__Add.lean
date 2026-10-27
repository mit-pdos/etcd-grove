/-
`(*delayingType[T]).Add` (`delaying_queue.go`): promoted from the embedded
`TypedInterface[T]` field (Go's method set of `*delayingType[T]`, a wrapper
that calls `q.TypedInterface.Add`). Lean-first.

**Not translated (gap C2, `notes/k8s-clientgo-goose.md`)**: the pinned Goose writes the
pointer receiver's unfolding of a promoted method of a generic struct ill-typed, so the
translation's configuration excludes it (`Code/k8s_io/client_go/util/workqueue.toml`): there is no
`MethodUnfold` for it, and its proof is `sorry` until the Perennial fix and a pin bump. The spec
is what follows from the embedded `Typed.Add`'s.
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.util.workqueue.Assumptions]

/-- `(*delayingType[T]).Add`, the method `delayingType` promotes from its embedded `TypedInterface`: `Add(item)`, as `Typed.Add`
on the embedded queue. -/
abbrev delayingType.Add.spec : Prop :=
  ∀ {K : Type} {T : go.GoType} [QItem (GF := GF) K T] (q : Loc) (γ : DNames) (k : K),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.util.workqueue ∗ isDelaying (K := K) q γ }}
    (App (Val (q @!! go.GoType.PointerType (delayingType.ty T) @!! go!"Add")) (Val #k))
  {{ RET #(); True }}

end spec

end workqueue
end EtcdGrove
end Perennial
