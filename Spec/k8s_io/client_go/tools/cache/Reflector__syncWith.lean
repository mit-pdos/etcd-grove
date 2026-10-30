/-
`(*Reflector).syncWith(items, resourceVersion)` (`reflector.go:911`): the list's objects copied into
a fresh slice, then the store's `Replace` (the informers' `RealFIFO`). Lean-first; phase 4 of
`notes/k8s-daemonset-plan.md` (fourth round, the reflector).
-/
module

public import Spec.k8s_io.client_go.tools.cache.RealFIFO__Replace
public import Proof.k8s_io.client_go.tools.cache.RefDefs

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

/-- **`r.syncWith(items, rv)`**, logically atomic, for a reflector whose store is the FIFO `f`, and
the list's objects `objs` (meeting the FIFO's contract `OK`): the FIFO's `Replace`, `FQ.replace objs
rv`, at its linearization point. -/
abbrev Reflector.syncWith.spec : Prop :=
  ∀ (r f : Loc) (γ : FifoNames) (OK : GoInterface → IProp GF) (isl : GoSlice) (dq : DFrac)
    (objs : List GoInterface) (rv : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗
      r.[Reflector, go!"store"] ↦□ interface.mkOk (go.GoType.PointerType RealFIFO.ty) #f ∗
      isFIFO f γ OK ∗ isl ↦*{dq} objs ∗ □ ([∗list] o ∈ objs, OK o) }}
  <<{ ∀∀ q, fifoSt γ q }>>
    (App (App (Val (r @!! go.GoType.PointerType Reflector.ty @!! go!"syncWith")) (Val #isl))
      (Val #rv))
    @@ ∅
  <<{ fifoSt γ (q.replace objs rv) }>>
  {{ RET #interface.nil; isl ↦*{dq} objs }}

end spec

end cache
end EtcdGrove
end Perennial
