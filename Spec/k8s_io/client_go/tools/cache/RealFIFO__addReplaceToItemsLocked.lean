/-
`(*RealFIFO).addReplaceToItemsLocked(objs, rv)` (`the_real_fifo.go:283`): the `ReplacedAll` delta appended, the waiters woken. Lean-first; phase 4 of `notes/k8s-daemonset-plan.md` (the informers' FIFO).
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

/-- **`f.addReplaceToItemsLocked(objs, rv)`** (the caller holds the items; no transformer): the
delta `{ReplacedAll, ReplacedAllInfo{rv, objs}}` appended, the waiters woken, no error. -/
abbrev RealFIFO.addReplaceToItemsLocked.spec : Prop :=
  ∀ (f : Loc) (mp : Loc) (g : GaugeMetric) (lk : GoInterfaceOk) (osl : GoSlice) (rv : GoString)
    (sl : GoSlice) (vs : List Delta),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗
      f.[RealFIFO, go!"transformer"] ↦□ func.nil ∗
      f.[RealFIFO, go!"metrics"] ↦□ mp ∗ mp.[fifoMetrics, go!"numberOfQueuedItem"] ↦□ g ∗ gaugeOk g ∗
      sync.isCond (f.[RealFIFO, go!"cond"]) lk ∗
      f.[RealFIFO, go!"items"] ↦ sl ∗ sl ↦* vs ∗ ownSliceCap Delta sl (DFrac.own 1) }}
    (App (App (Val (f @!! go.GoType.PointerType RealFIFO.ty @!! go!"addReplaceToItemsLocked"))
      (Val #osl)) (Val #rv))
  {{ RET #interface.nil; ∃ sl' : GoSlice, f.[RealFIFO, go!"items"] ↦ sl' ∗
      sl' ↦* (vs ++ [Delta.mk go!"ReplacedAll"
        (interface.mkOk ReplacedAllInfo.ty #(ReplacedAllInfo.mk rv osl))]) ∗
      ownSliceCap Delta sl' (DFrac.own 1) }}

end spec

end cache
end EtcdGrove
end Perennial
