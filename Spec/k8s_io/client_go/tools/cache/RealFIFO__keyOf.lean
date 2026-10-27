/-
`(*RealFIFO).keyOf(obj)` (`the_real_fifo.go:197`): the key function's key of an object, or of a delta's object. Lean-first; phase 4 of `notes/k8s-daemonset-plan.md` (the informers' FIFO).
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

/-- `keyOf`'s argument: an object of a pointer type (none of `Deltas`, `Delta`, a tombstone),
or a `Delta` whose object is not a tombstone (the slow-queue trace keys a popped delta). -/
def keyOfArg (obj : GoInterface) : Prop :=
  (∃ (t : go.GoType) (v : val), obj = interface.mkOk (go.GoType.PointerType t) v) ∨
  (∃ (d : Delta) (t : go.GoType) (w : val), obj = interface.mkOk Delta.ty #d ∧
    d.Object' = interface.mkOk t w ∧ t ≠ DeletedFinalStateUnknown.ty)

/-- **`f.keyOf(obj)`**: for an object of a pointer type meeting the key function's contract, its
key and no error; for a delta, some key and error (the key function returns on anything). -/
abbrev RealFIFO.keyOf.spec : Prop :=
  ∀ (f : Loc) (OK : GoInterface → IProp GF) (KF : GoInterface → GoString) (kf : GoFunc)
    (obj : GoInterface),
  {{ f.[RealFIFO, go!"keyFunc"] ↦□ kf ∗ keyOk OK kf KF ∗ keyAny kf ∗ ⌜keyOfArg obj⌝ ∗
      (⌜∃ (t : go.GoType) (v : val), obj = interface.mkOk (go.GoType.PointerType t) v⌝ -∗ □ OK obj) }}
    (App (Val (f @!! go.GoType.PointerType RealFIFO.ty @!! go!"keyOf")) (Val #obj))
  {{ (k : GoString) (err : GoInterface), RET (PairV #k #err);
      ⌜(∃ (t : go.GoType) (v : val), obj = interface.mkOk (go.GoType.PointerType t) v) →
        k = KF obj ∧ err = interface.nil⌝ }}

end spec

end cache
end EtcdGrove
end Perennial
