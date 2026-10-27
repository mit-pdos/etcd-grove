/-
`(*controller).processLoop(ctx)` (`controller.go:238`): the informer controller's loop popping the
FIFO, on either path. Lean-first.

**Which path.** The loop takes the batch path (`PopBatch` with `ProcessBatch`) when the queue is a
`QueueWithBatch` (the `RealFIFO` is), `ProcessBatch` is not `nil` (the shared informer sets it) and
client-go's feature gate `InOrderInformersBatchProcess` is enabled; otherwise the single-delta path
(`Pop` with `Process`). The spec covers both (the gate returns some boolean, `gateOk`): `Main` leaves
the gate at its default, **enabled** (beta since 1.35), so `Main` runs the batch path, over
`PopBatch`'s spec (a named hypothesis, gap D3). (Until the fourth round the spec was the
single-delta path's only, under the premise `gateOff`.) The processing's contracts are one family
over batches: a lone delta's `Pop` (or `PopBatch` of one) at `[d]`.
-/
module

public import Spec.k8s_io.client_go.tools.cache.RealFIFO__Pop
public import Spec.k8s_io.client_go.tools.cache.RealFIFO__PopBatch
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

/-- **The gate `InOrderInformersBatchProcess` reads** (a premise: `features.FeatureGates()` returns
a gate set whose `Enabled` returns some boolean; the loop takes the batch path iff it is `true`, as
it is in `Main`). -/
def gateOk : IProp GF :=
  iprop({{ True }} (App (Val (@! k8s_io.client_go.features.FeatureGates)) (Val #()))
    {{ (g : GoInterface), RET #g; ∃ gi : GoInterfaceOk, ⌜g = interface.ok gi⌝ ∗
      {{ True }} (App (Val #(methods gi.ty go!"Enabled" gi.v))
        (Val k8s_io.client_go.features.InOrderInformersBatchProcess))
      {{ (b : Bool), RET #b; True }} }})

instance gateOk_persistent : Persistent (gateOk (GF := GF)) := by
  unfold gateOk; infer_instance

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

/-- **Back to `I`** after a `PopBatch`, which returns an error. -/
def popBatchDone (I : IProp GF) : val → IProp GF :=
  fun v => iprop(∃ e : GoInterface, ⌜v = #e⌝ ∗ I)

/-- **`c.processLoop(ctx)`** for a controller `c` whose queue is the FIFO `f`, whose processing
functions `pf` (one delta) and `pbf` (a batch) meet `processOk`/`processBatchOk` for the batch
contracts `Ψ`/`Ψ'` (a lone delta at `[d]`), with the gate returning (`gateOk`) and `errors.Is`
returning (`errIsOk`): it pops the FIFO until it is closed or `ctx` is done, each pop (`Pop`, or
`PopBatch` on the batch path) with the two linearization points the client's invariant `I` gives
(back to `I`). -/
abbrev controller.processLoop.spec : Prop :=
  ∀ (c : Loc) (ctx : GoInterfaceOk) (cs : context.ContextDesc (IProp GF)) (f : Loc)
    (γ : FifoNames) (OK : GoInterface → IProp GF) (pf pbf : GoFunc)
    (Ψ : List FD → Bool → IProp GF) (Ψ' : List FD → GoInterface → IProp GF) (I : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ context.isContext ctx cs ∗
      (c.[controller, go!"config"]).[Config, go!"Queue"] ↦□
        interface.mkOk (go.GoType.PointerType RealFIFO.ty) #f ∗
      (c.[controller, go!"config"]).[Config, go!"Process"] ↦□ pf ∗
      (c.[controller, go!"config"]).[Config, go!"ProcessBatch"] ↦□ pbf ∗
      isFIFO f γ OK ∗ □ processOk OK pf (fun d b => Ψ [d] b) (fun d e => Ψ' [d] e) ∗
      □ processBatchOk OK pbf Ψ Ψ' ∗ gateOk ∗ errIsOk ∗ I ∗
      □ (I -∗ popAU γ (fun d b => Ψ [d] b) (popDone I) ∗ doneAU γ (fun d e => Ψ' [d] e) (popDone I)) ∗
      □ (I -∗ popBatchAU γ Ψ (popBatchDone I) ∗ doneBatchAU γ Ψ' (popBatchDone I)) }}
    (App (Val (c @!! go.GoType.PointerType controller.ty @!! go!"processLoop"))
      (Val #(GoInterface.ok ctx)))
  {{ RET #(); True }}

end spec

end cache
end EtcdGrove
end Perennial
