/-
`(*controller).processLoop(ctx)` (`controller.go:238`): the informer controller's loop popping the
FIFO, on the single-delta path. Lean-first.

**Which path.** The loop takes the batch path (`PopBatch` with `ProcessBatch`) when the queue is a
`QueueWithBatch` (the `RealFIFO` is), `ProcessBatch` is not `nil` (the shared informer sets it) and
client-go's feature gate `InOrderInformersBatchProcess` is enabled; otherwise the single-delta path
(`Pop` with `Process`). The spec is the single-delta path's: its premise `gateOff` is that the gate
reads `false`. `Main` leaves the gate at its default, **enabled** (beta since 1.35), so `Main` runs
the batch path, whose `PopBatch` and `Transaction` are not translated (gaps D3, C4): open.
-/
module

public import Spec.k8s_io.client_go.tools.cache.RealFIFO__Pop
public import Perennial.Proof.context.Base

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

/-- **The gate `InOrderInformersBatchProcess` reads `false`** (the single-delta path; a premise,
`features.FeatureGates()` returning a gate set whose `Enabled` says so). -/
def gateOff : IProp GF :=
  iprop({{ True }} (App (Val (@! k8s_io.client_go.features.FeatureGates)) (Val #()))
    {{ (g : GoInterface), RET #g; ∃ gi : GoInterfaceOk, ⌜g = interface.ok gi⌝ ∗
      {{ True }} (App (Val #(methods gi.ty go!"Enabled" gi.v))
        (Val k8s_io.client_go.features.InOrderInformersBatchProcess))
      {{ RET #false; True }} }})

instance gateOff_persistent : Persistent (gateOff (GF := GF)) := by
  unfold gateOff; infer_instance

/-- **`errors.Is(err, ErrFIFOClosed)` returns** for every error `err` the loop sees and the value
`e` of `ErrFIFOClosed` (a premise: the package's fact says only that `ErrFIFOClosed` holds some
error, `k8sCacheInit`, and `Pop`'s spec does not say which error it returns once closed). -/
def errIsOk : IProp GF :=
  iprop(∀ (err e : GoInterface), {{ True }}
    (App (App (Val (@! _root_.Perennial.errors.Is)) (Val #err)) (Val #e)) {{ (b : Bool), RET #b; True }})

instance errIsOk_persistent : Persistent (errIsOk (GF := GF)) := by
  unfold errIsOk; infer_instance

/-- **Back to the loop's invariant `I`** after a `Pop`, which returns a pair (an item and an
error). -/
def popDone (I : IProp GF) : val → IProp GF :=
  fun v => iprop(∃ x e : GoInterface, ⌜v = PairV #x #e⌝ ∗ I)

/-- **`c.processLoop(ctx)`** for a controller `c` whose queue is the FIFO `f` and whose processing
function `pf` meets `processOk` for `Ψ`/`Ψ'`, with the gate off and `errors.Is` returning
(`errIsOk`): it pops the FIFO until it is
closed or `ctx` is done, each pop with the two linearization points the client's invariant `I`
gives (`popAU`/`doneAU`, back to `I`). -/
abbrev controller.processLoop.spec : Prop :=
  ∀ (c : Loc) (ctx : GoInterfaceOk) (cs : context.ContextDesc (IProp GF)) (f : Loc)
    (γ : FifoNames) (OK : GoInterface → IProp GF) (pf pbf : GoFunc) (Ψ : FD → Bool → IProp GF)
    (Ψ' : FD → GoInterface → IProp GF) (I : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ context.isContext ctx cs ∗
      (c.[controller, go!"config"]).[Config, go!"Queue"] ↦□
        interface.mkOk (go.GoType.PointerType RealFIFO.ty) #f ∗
      (c.[controller, go!"config"]).[Config, go!"Process"] ↦□ pf ∗
      (c.[controller, go!"config"]).[Config, go!"ProcessBatch"] ↦□ pbf ∗
      isFIFO f γ OK ∗ □ processOk OK pf Ψ Ψ' ∗ gateOff ∗ errIsOk ∗ I ∗
      □ (I -∗ popAU γ Ψ (popDone I) ∗ doneAU γ Ψ' (popDone I)) }}
    (App (Val (c @!! go.GoType.PointerType controller.ty @!! go!"processLoop"))
      (Val #(GoInterface.ok ctx)))
  {{ RET #(); True }}

end spec

end cache
end EtcdGrove
end Perennial
