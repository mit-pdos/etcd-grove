/-
`(*RealFIFO).checkSynced_locked()` (`the_real_fifo.go:246`): close `synced` once populated with no initial item left. Lean-first; phase 4 of `notes/k8s-daemonset-plan.md` (the informers' FIFO).
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

/-- Whether `checkSynced_locked` closes `synced`. -/
def syncsNow (p : Bool) (n : Nat) (b : Bool) : Bool := p && n == 0 && !b

/-- **`f.checkSynced_locked()`** (the caller holds the fields): `syncedClosed` set, and `synced`
closed (broadcasting `Q`, which the caller then gives), if the queue is populated with no initial
item left and not yet synced. -/
abbrev RealFIFO.checkSynced_locked.spec : Prop :=
  ∀ (f : Loc) (ch : GoChan) (γch : ChanNames) (Q : IProp GF) (p : Bool) (n : Nat) (b : Bool),
  {{ f.[RealFIFO, go!"populated"] ↦ p ∗ f.[RealFIFO, go!"initialPopulationCount"] ↦ (W64 n) ∗
      ⌜n < 2 ^ 63⌝ ∗ f.[RealFIFO, go!"syncedClosed"] ↦ b ∗ f.[RealFIFO, go!"synced"] ↦□ ch ∗
      ownBroadcastChan ch γch Q (if b then .Done else .Pending) ∗
      (⌜syncsNow p n b = true⌝ -∗ □ Q) }}
    (App (Val (f @!! go.GoType.PointerType RealFIFO.ty @!! go!"checkSynced_locked")) (Val #()))
  {{ RET #(); f.[RealFIFO, go!"populated"] ↦ p ∗ f.[RealFIFO, go!"initialPopulationCount"] ↦ (W64 n) ∗
      f.[RealFIFO, go!"syncedClosed"] ↦ (b || syncsNow p n b) ∗
      ownBroadcastChan ch γch Q (if b || syncsNow p n b then .Done else .Pending) }}

end spec

end cache
end EtcdGrove
end Perennial
