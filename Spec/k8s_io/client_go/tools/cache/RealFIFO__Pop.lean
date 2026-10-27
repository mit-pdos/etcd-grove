/-
`(*RealFIFO).Pop(process)` (`the_real_fifo.go:403`): wait for a delta, pop it, process it (the lock released meanwhile when `UnlockWhileProcessing`), then one initial item fewer. Lean-first; phase 4 of `notes/k8s-daemonset-plan.md` (the informers' FIFO).
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

/-- **`f.Pop(process)`**, with two linearization points, each the caller's fancy update on the
queue's state (the single consumer's spec; the caller, an invariant, opens them):
* **the pop** (`popAU`): at a state with a delta `d` first, the queue without it, and the
  processing's precondition `Ψ d b` (`b`: not synced yet, `isInInitialList`); or, at an empty and
  closed queue, unchanged, and `Pop` returns `ErrFIFOClosed` (`Φ` of any value and error);
* the processing: `process(Deltas{v}, b)` (`v` the Go delta, `fdAt OK d v`) from `Ψ d b` to
  `Ψ' d err`;
* **the deferred step** (`doneAU`): from `Ψ' d err`, the state `q.popDone`, then `Φ` of the
  returned `Deltas{v}` and `err`. -/
def popAU (γ : FifoNames) (Ψ : FD → Bool → IProp GF) (Φ : val → IProp GF) : IProp GF :=
  iprop(▷ |={⊤, ∅}=> ∃ q : FQ, fifoSt γ q ∗
    ((⌜q.items = [] ∧ q.closed = true⌝ -∗ fifoSt γ q ={∅, ⊤}=∗
        ∀ (x e : GoInterface), Φ (PairV #x #e)) ∧
     (∀ d ds, ⌜q.items = d :: ds⌝ -∗ fifoSt γ { q with items := ds } ={∅, ⊤}=∗ Ψ d (!q.synced))))

def doneAU (γ : FifoNames) (Ψ' : FD → GoInterface → IProp GF) (Φ : val → IProp GF) : IProp GF :=
  iprop(∀ d err, Ψ' d err -∗ ▷ |={⊤, ∅}=> ∃ q : FQ, fifoSt γ q ∗
    (fifoSt γ q.popDone ={∅, ⊤}=∗ ∀ x : GoInterface, Φ (PairV #x #err)))

def processOk (OK : GoInterface → IProp GF) (process : GoFunc) (Ψ : FD → Bool → IProp GF)
    (Ψ' : FD → GoInterface → IProp GF) : IProp GF :=
  iprop(∀ (d : FD) (b : Bool) (v : Delta) (sl : GoSlice), fdAt OK d v -∗ sl ↦* [v] -∗ Ψ d b -∗
    WP (App (App (Val #process) (Val #(interface.mkOk Deltas.ty #sl))) (Val #b)) {{ r, ∃ err : GoInterface,
      ⌜r = #err⌝ ∗ Ψ' d err }})

abbrev RealFIFO.Pop.spec : Prop :=
  ∀ (f : Loc) (γ : FifoNames) (OK : GoInterface → IProp GF)
    (process : GoFunc) (Ψ : FD → Bool → IProp GF) (Ψ' : FD → GoInterface → IProp GF)
    (Ω : val → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ isFIFO f γ OK ∗
      processOk OK process Ψ Ψ' ∗ popAU γ Ψ Ω ∗ doneAU γ Ψ' Ω }}
    (App (Val (f @!! go.GoType.PointerType RealFIFO.ty @!! go!"Pop")) (Val #process))
  {{ (v : val), RET v; Ω v }}

end spec

end cache
end EtcdGrove
end Perennial
