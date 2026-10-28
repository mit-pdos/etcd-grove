/-
`(*RealFIFO).Close()` (`the_real_fifo.go:188`): the queue closed, its waiters woken. Lean-first; phase 4 of `notes/k8s-daemonset-plan.md` (the informers' FIFO).
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

/-- **`f.Close()`**, logically atomic: the queue closed. -/
abbrev RealFIFO.Close.spec : Prop :=
  ∀ (f : Loc) (γ : FifoNames) (OK : GoInterface → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ isFIFO f γ OK }}
  <<{ ∀∀ q, fifoSt γ q }>>
    (App (Val (f @!! go.GoType.PointerType RealFIFO.ty @!! go!"Close")) (Val #()))
    @@ ∅
  <<{ fifoSt γ { q with closed := true } }>>
  {{ RET #(); True }}

end spec

end cache
end EtcdGrove
end Perennial
