/-
`(*RealFIFO).PopBatch(processBatch, processSingle)` (`the_real_fifo.go:486`): the batch path's pop
(`InOrderInformersBatchProcess`, on by default): wait for a delta, take a batch (`FQ.batch`),
process it (one delta by `processSingle`, more by `processBatch`; the lock released meanwhile when
`UnlockWhileProcessing`), then that many initial items fewer. Lean-first; phase 4 of
`notes/k8s-daemonset-plan.md` (fourth round).

**Names only** (gap D3, `notes/k8s-daemonset-goose.md`: the slow-batch trace's
`min(100*time.Millisecond*time.Duration(len(deltas)), time.Second)` is rejected by the pinned Goose),
so this spec is a **named hypothesis** (`?` in `etc/link-lean-first-k8scache.txt`), stated as what
the code does (read 2026-10-27, client-go `569675c57fa3`), in the shape of `Pop`'s proved spec:

```go
f.lock.Lock(); defer f.lock.Unlock()
for len(f.items) == 0 { if f.closed { return ErrFIFOClosed }; f.cond.Wait() }
isInInitialList := !f.hasSynced_locked()                  // !syncedClosed
deltas := ...
for i := 0; i < f.batchSize && i < len(f.items); i++ {    // batchSize 1000 (newQueueFIFO)
  if f.initialPopulationCount > 0 && i >= f.initialPopulationCount { break }
  if !batchable[f.items[i].Type] { if len(deltas) == 0 { take(i) }; break }
  take(i)
}
f.items = f.items[len(deltas):]
defer func() { if f.initialPopulationCount > 0 {
  f.initialPopulationCount -= len(deltas); f.checkSynced_locked() } }()
if len(f.items) > 10 { trace ...; defer trace.LogIfLong(min(...)) }   // the gap
f.metrics.numberOfQueuedItem.Set(len(f.items))
if len(deltas) == 1 { return f.whileProcessing_locked(func() error {
  return processSingle(Deltas{deltas[0]}, isInInitialList) }) }
return f.whileProcessing_locked(func() error { return processBatch(deltas, isInInitialList) })
```

The two linearization points are `Pop`'s: the batch's removal (`popBatchAU`, at the state the lock
holds; or `ErrFIFOClosed` at an empty closed queue) and, after the processing (the lock possibly
released meanwhile, `whileProcessing_locked`), the deferred step `FQ.popDoneN` (`doneBatchAU`).
`batchable` is `Sync`, `Replaced`, `Added`, `Updated`, `Deleted` (`FD.batchable`; the atomic FIFO
queues `ReplacedAll` and `Bookmark`, which are not). The returned error is the processing's.
-/
module

public import Spec.k8s_io.client_go.tools.cache.RealFIFO__Pop
public import Proof.k8s_io.client_go.tools.cache.BatchDefs

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

/-- **The batch's removal**: at a state with deltas, the queue without its batch (`q.batch`) and the
processing's precondition `Ψ q.batch (!q.synced)`; or, at an empty closed queue, unchanged, and
`PopBatch` returns `ErrFIFOClosed` (`Φ` of any error). -/
def popBatchAU (γ : FifoNames) (Ψ : List FD → Bool → IProp GF) (Φ : val → IProp GF) : IProp GF :=
  iprop(▷ |={⊤, ∅}=> ∃ q : FQ, fifoSt γ q ∗
    ((⌜q.items = [] ∧ q.closed = true⌝ -∗ fifoSt γ q ={∅, ⊤}=∗ ∀ e : GoInterface, Φ #e) ∧
     (⌜q.items ≠ []⌝ -∗ fifoSt γ { q with items := q.items.drop q.batch.length } ={∅, ⊤}=∗
        Ψ q.batch (!q.synced))))

/-- **The deferred step**: from `Ψ' ds err`, the state `q.popDoneN |ds|`, then `Φ` of the
processing's error. The caller shows that a batch of several deltas does not outnumber the initial
items left (`ds.length ≤ q.initCount` unless none is left): Go's `initialPopulationCount -=
len(deltas)` would go negative, which `FQ`'s `Nat` count (and `fifoRes`'s field) cannot hold. It
holds of the informer's queue: a batch of several deltas is popped from a populated queue, after
which only the single consumer's deferred steps change the count, and the batch is at most the
count then (`FQ.batch`); a lone delta never goes below zero. -/
def doneBatchAU (γ : FifoNames) (Ψ' : List FD → GoInterface → IProp GF) (Φ : val → IProp GF) :
    IProp GF :=
  iprop(∀ ds err, Ψ' ds err -∗ ▷ |={⊤, ∅}=> ∃ q : FQ, fifoSt γ q ∗
    ⌜ds.length = 1 ∨ q.initCount = 0 ∨ ds.length ≤ q.initCount⌝ ∗
    (fifoSt γ (q.popDoneN ds.length) ={∅, ⊤}=∗ Φ #err))

/-- **A batch processing function's contract** (`ProcessBatchFunc`): on a batch of at least two
batchable deltas `ds` (the Go deltas `vs` in the slice `sl`), from `Ψ ds b` to `Ψ' ds err`. -/
def processBatchOk (OK : GoInterface → IProp GF) (pbf : GoFunc) (Ψ : List FD → Bool → IProp GF)
    (Ψ' : List FD → GoInterface → IProp GF) : IProp GF :=
  iprop(∀ (ds : List FD) (b : Bool) (vs : List Delta) (sl : GoSlice),
    ⌜2 ≤ ds.length ∧ ∀ d ∈ ds, d.batchable = true⌝ -∗ ([∗list] d;v ∈ ds;vs, fdAt OK d v) -∗
    sl ↦* vs -∗ Ψ ds b -∗
    WP (App (App (Val #pbf) (Val #sl)) (Val #b)) {{ r, ∃ err : GoInterface, ⌜r = #err⌝ ∗ Ψ' ds err }})

/-- **`f.PopBatch(pbf, pf)`**: one batch, as above; a lone delta by `pf` (`processOk` with the
batch's contracts at `[d]`), more by `pbf` (`processBatchOk`). -/
abbrev RealFIFO.PopBatch.spec : Prop :=
  ∀ (f : Loc) (γ : FifoNames) (OK : GoInterface → IProp GF) (pbf pf : GoFunc)
    (Ψ : List FD → Bool → IProp GF) (Ψ' : List FD → GoInterface → IProp GF) (Ω : val → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ isFIFO f γ OK ∗
      processOk OK pf (fun d b => Ψ [d] b) (fun d e => Ψ' [d] e) ∗ processBatchOk OK pbf Ψ Ψ' ∗
      popBatchAU γ Ψ Ω ∗ doneBatchAU γ Ψ' Ω }}
    (App (App (Val (f @!! go.GoType.PointerType RealFIFO.ty @!! go!"PopBatch")) (Val #pbf))
      (Val #pf))
  {{ (v : val), RET v; Ω v }}

end spec

end cache
end EtcdGrove
end Perennial
