/-
`(*RealFIFO).keyOf(obj)` (`the_real_fifo.go:197`): the key function's key of an object (not a `Deltas`, `Delta` or tombstone). Lean-first; phase 4 of `notes/k8s-daemonset-plan.md` (the informers' FIFO).
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

/-- **`f.keyOf(obj)`** for an object meeting the key function's contract whose dynamic type is
a pointer type (so none of `Deltas`, `Delta`, `DeletedFinalStateUnknown`): its key, no error. -/
abbrev RealFIFO.keyOf.spec : Prop :=
  ∀ (f : Loc) (OK : GoInterface → IProp GF) (KF : GoInterface → GoString) (kf : GoFunc)
    (obj : GoInterface) (t : go.GoType) (v : val),
  {{ f.[RealFIFO, go!"keyFunc"] ↦□ kf ∗ keyOk OK kf KF ∗ □ OK obj ∗
      ⌜obj = interface.mkOk (go.GoType.PointerType t) v⌝ }}
    (App (Val (f @!! go.GoType.PointerType RealFIFO.ty @!! go!"keyOf")) (Val #obj))
  {{ RET (PairV #(KF obj) #interface.nil); True }}

end spec

end cache
end EtcdGrove
end Perennial
