/-
`(*RealFIFO).Delete(obj)` (`the_real_fifo.go:349`): populated, synced if no initial item is left, the delta `{Deleted, obj}` queued. Lean-first; phase 4 of `notes/k8s-daemonset-plan.md` (the informers' FIFO).
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- **`f.Delete(obj)`**, logically atomic, for an object meeting the client's contract whose
dynamic type is a pointer type (the watch's objects): `FQ.addObj "Deleted" obj`. -/
abbrev RealFIFO.Delete.spec : Prop :=
  ∀ (f : Loc) (γ : FifoNames) (OK : GoInterface → IProp GF) (KF : GoInterface → GoString)
    (obj : GoInterface) (ty : go.GoType) (v : val),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ isFIFO f γ OK KF ∗
      □ OK obj ∗ ⌜obj = interface.mkOk (go.GoType.PointerType ty) v⌝ }}
  <<{ ∀∀ q, fifoSt γ q }>>
    (App (Val (f @!! go.GoType.PointerType RealFIFO.ty @!! go!"Delete")) (Val #obj))
    @@ ∅
  <<{ fifoSt γ (q.addObj go!"Deleted" obj) }>>
  {{ RET #interface.nil; True }}

end spec

end cache
end EtcdGrove
end Perennial
