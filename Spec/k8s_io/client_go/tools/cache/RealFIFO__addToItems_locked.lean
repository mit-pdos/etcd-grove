/-
`(*RealFIFO).addToItems_locked(t, skip, obj)` (`the_real_fifo.go:255`): the delta `{t, obj}` appended, the waiters woken. Lean-first; phase 4 of `notes/k8s-daemonset-plan.md` (the informers' FIFO).
-/
module

public import Proof.k8s_io.client_go.tools.cache.FIFODefs
public import Spec.k8s_io.client_go.tools.cache.RealFIFO__keyOf

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

/-- **`f.addToItems_locked(t, skip, obj)`** (the caller holds the items; no transformer), for an
object meeting the key function's contract whose dynamic type is a pointer type: the delta
`{t, obj}` appended, the waiters woken, no error. -/
abbrev RealFIFO.addToItems_locked.spec : Prop :=
  ∀ (f : Loc) (OK : GoInterface → IProp GF) (KF : GoInterface → GoString) (kf : GoFunc)
    (mp : Loc) (g : GaugeMetric) (lk : GoInterfaceOk) (t : GoString) (skip : Bool)
    (obj : GoInterface) (ty : go.GoType) (v : val) (sl : GoSlice) (vs : List Delta),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗
      f.[RealFIFO, go!"keyFunc"] ↦□ kf ∗ keyOk OK kf KF ∗ keyAny kf ∗
      f.[RealFIFO, go!"transformer"] ↦□ func.nil ∗
      f.[RealFIFO, go!"metrics"] ↦□ mp ∗ mp.[fifoMetrics, go!"numberOfQueuedItem"] ↦□ g ∗ gaugeOk g ∗
      sync.isCond (f.[RealFIFO, go!"cond"]) lk ∗
      □ OK obj ∗ ⌜obj = interface.mkOk (go.GoType.PointerType ty) v⌝ ∗
      f.[RealFIFO, go!"items"] ↦ sl ∗ sl ↦* vs ∗ ownSliceCap Delta sl (DFrac.own 1) }}
    (App (App (App (Val (f @!! go.GoType.PointerType RealFIFO.ty @!! go!"addToItems_locked"))
      (Val #t)) (Val #skip)) (Val #obj))
  {{ RET #interface.nil; ∃ sl' : GoSlice, f.[RealFIFO, go!"items"] ↦ sl' ∗
      sl' ↦* (vs ++ [Delta.mk t obj]) ∗ ownSliceCap Delta sl' (DFrac.own 1) }}

end spec

end cache
end EtcdGrove
end Perennial
