/-
`processDeltasInBatch(logger, handler, clientState, deltas, isInInitialList, keyFunc)`
(`controller.go:899`): the batch path's processing (`InOrderInformersBatchProcess`, on by default)
of the batch `RealFIFO.PopBatch` hands its batch function: one store transaction for the whole
batch, then the handler's events in order. Lean-first; phase 4 of `notes/k8s-daemonset-plan.md`
(fourth round).

For the informers' store (a `*cache`, a `TransactionStore`, `batchTyOk`) and object deltas of the
kinds the atomic FIFO queues (`Added`, `Updated`, `Deleted`), keyed without error by both key
functions: for each delta in order, the key's current object (`inBatch`'s, else the store's, read
through the exclusive writer) decides `Update`/`OnUpdate(old, obj)` or `Add`/`OnAdd(obj, b)`, a
deletion `Delete`/`OnDelete(obj)`; then `Transaction` of the writes (`cache.Transaction`, no error:
every key computes), then the callbacks in order; no error (`errors.Join` of no key error).

**The store reflects the whole batch before any handler hears of it** (the single-delta path:
before each delta's events); the events are those of the deltas one by one (`batchEvs`), each
`OnUpdate`'s old object the key's object after the batch's earlier deltas. The store's resource
version is the last object's (one transaction), where the deltas one by one would leave the last
version an object had (the same when every object has one, `rvOf`).
-/
module

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

/-- **`processDeltasInBatch(lg, h, ca, deltas, b, kf')`**, the store `ca` held by its exclusive
writer at `σ`, for a batch `ds` of object deltas (the Go deltas `vs` in `deltas`) of the kinds the
atomic FIFO queues, their objects keyed by the cache's `kf` and by `kf'` alike (`KF`), with
versions `rvOf`: no error; the store's next state and the handler's events are `batchStep`'s. -/
abbrev processDeltasInBatch.spec : Prop :=
  ∀ (lg : github_com.go_logr.logr.Logger) (h : GoInterface) (ca ts : Loc) (γ : TsNames)
    (OK : GoInterface → IProp GF) (Fam : Nat → Fn GF) (kf kf' : GoFunc)
    (KF : GoInterface → GoString) (rvOf : GoInterface → Option GoString) (SW : St → IProp GF) (Rw : St → St → Prop)
    (σ : St) (H : List Ev → IProp GF) (evs : List Ev) (ds : List FD) (vs : List Delta)
    (sl : GoSlice) (b : Bool),
  batchTyOk →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ isCache ca ts γ OK Fam kf ∗
      tsReader ts γ OK Fam ∗ storeWriter γ SW Rw ∗ SW σ ∗
      ⌜Rw σ σ ∧ Rw σ (batchStore KF rvOf σ ds)⌝ ∗ handlerOk OK h H ∗ H evs ∗
      ([∗list] d;v ∈ ds;vs, fdAt OK d v) ∗ sl ↦* vs ∗ ⌜∀ d ∈ ds, d.isObjOk⌝ ∗
      keyOk (fun x => iprop(⌜x ∈ ds.map FD.obj?⌝)) kf KF ∗
      keyOk (fun x => iprop(⌜x ∈ ds.map FD.obj?⌝)) kf' KF ∗
      rvAcc (fun x => iprop(⌜x ∈ ds.map FD.obj?⌝)) rvOf }}
    (App (App (App (App (App (App (Val (@! processDeltasInBatch)) (Val #lg)) (Val #h))
      (Val #(interface.mkOk (go.GoType.PointerType k8s_io.client_go.tools.cache.cache.ty) #ca)))
      (Val #sl)) (Val #b)) (Val #kf'))
  {{ RET #interface.nil; ∃ (σ' : St) (evs' : List Ev), ⌜batchStep KF rvOf b σ ds σ' evs'⌝ ∗
      SW σ' ∗ H (evs ++ evs') ∗ sl ↦* vs ∗ tsReader ts γ OK Fam }}

end spec

end cache
end EtcdGrove
end Perennial
