/-
`(*RealFIFO).Update(obj)` (`the_real_fifo.go:338`): populated, synced if no initial item is left, the delta `{Updated, obj}` queued. Lean-first; phase 4 of `notes/k8s-daemonset-plan.md` (the informers' FIFO).
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

/-- **`f.Update(obj)`**, logically atomic, for an object meeting the client's contract whose
dynamic type is a pointer type (the watch's objects): `FQ.addObj "Updated" obj`. -/
abbrev RealFIFO.Update.spec : Prop :=
  ∀ (f : Loc) (γ : FifoNames) (OK : GoInterface → IProp GF)
    (obj : GoInterface) (ty : go.GoType) (v : val),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ isFIFO f γ OK ∗
      □ OK obj ∗ ⌜obj = interface.mkOk (go.GoType.PointerType ty) v⌝ }}
  <<{ ∀∀ q, fifoSt γ q }>>
    (App (Val (f @!! go.GoType.PointerType RealFIFO.ty @!! go!"Update")) (Val #obj))
    @@ ∅
  <<{ fifoSt γ (q.addObj go!"Updated" obj) }>>
  {{ RET #interface.nil; True }}

end spec

end cache
end EtcdGrove
end Perennial
