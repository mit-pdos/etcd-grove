/-
`(*RealFIFO).Replace(objs, rv)` (`the_real_fifo.go:640`): with atomic events, the relist's `ReplacedAll` delta queued; the first time, populated. Lean-first; phase 4 of `notes/k8s-daemonset-plan.md` (the informers' FIFO).
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

/-- **`f.Replace(objs, rv)`**, logically atomic (atomic events): `FQ.replace`; the list's
slice, with its objects' contracts, moves into the queue. -/
abbrev RealFIFO.Replace.spec : Prop :=
  ∀ (f : Loc) (γ : FifoNames) (OK : GoInterface → IProp GF)
    (osl : GoSlice) (objs : List GoInterface) (rv : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ isFIFO f γ OK ∗
      osl ↦* objs ∗ □ ([∗list] o ∈ objs, OK o) }}
  <<{ ∀∀ q, fifoSt γ q }>>
    (App (App (Val (f @!! go.GoType.PointerType RealFIFO.ty @!! go!"Replace")) (Val #osl))
      (Val #rv))
    @@ ∅
  <<{ fifoSt γ (q.replace objs rv) }>>
  {{ RET #interface.nil; True }}

end spec

end cache
end EtcdGrove
end Perennial
