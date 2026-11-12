/-
`(*RealFIFO).hasSynced_locked()` (`the_real_fifo.go:238`): the `syncedClosed` field. Lean-first; phase 4 of `notes/k8s-daemonset-plan.md` (the informers' FIFO).
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

/-- **`f.hasSynced_locked()`**: the `syncedClosed` field (the caller holds it). -/
abbrev RealFIFO.hasSynced_locked.spec : Prop :=
  ∀ (f : Loc) (b : Bool),
  {{ (f.[RealFIFO, go!"syncedClosed"] ↦ b : IProp GF) }}
    (App (Val (f @!! go.GoType.PointerType RealFIFO.ty @!! go!"hasSynced_locked")) (Val #()))
  {{ RET #b; f.[RealFIFO, go!"syncedClosed"] ↦ b }}

end spec

end cache
end EtcdGrove
end Perennial
