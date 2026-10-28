/-
`(&n).GroupVersionResource()` (`identity.go`): its resource (the value method through the pointer's method set). Lean-first; phase 4 of `notes/k8s-daemonset-plan.md` (the informers' FIFO).
-/
module

public import Proof.k8s_io.client_go.tools.cache.FIFODefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI k8s_io.client_go.tools.cache

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- **`(&n).GroupVersionResource()`** of a variable `l ↦{dq} n`: its resource. -/
abbrev InformerNameAndResource.GroupVersionResource_ptr.spec : Prop :=
  ∀ (l : Loc) (dq : DFrac) (n : InformerNameAndResource),
  {{ (l ↦{dq} n : IProp GF) }}
    (App (Val (l @!! go.GoType.PointerType InformerNameAndResource.ty @!! go!"GroupVersionResource")) (Val #()))
  {{ RET #n.gvr'; l ↦{dq} n }}

end spec

end cache
end EtcdGrove
end Perennial
