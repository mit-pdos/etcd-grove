/-
`(*sharedIndexInformer).handleBatchDeltas(logger, deltas, isInInitialList)` (`shared_informer.go:1100`):
the shared informer's batch processing function (the batch path, `InOrderInformersBatchProcess`),
`processDeltasInBatch` under `blockDeltas` with the informer itself as the handler. Lean-first;
phase 4 of `notes/k8s-daemonset-plan.md` (fourth round).
-/
module

public import Spec.k8s_io.client_go.tools.cache.processDeltasInBatch
public import Spec.k8s_io.client_go.tools.cache.sharedIndexInformer__handleDeltas

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

/-- **`s.handleBatchDeltas(lg, deltas, b)`**, as `handleDeltas` for a batch `ds` of object deltas
(`processDeltasInBatch`): no error; under the lock, the store and the events step by `batchStep`,
which the client's view shift `Hstep` turns from `P` into `Q` (its relation `BL` kept). -/
abbrev sharedIndexInformer.handleBatchDeltas.spec : Prop :=
  ∀ (s : Loc) (lg : github_com.go_logr.logr.Logger) (ca ts : Loc) (γ : TsNames)
    (OK : GoInterface → IProp GF) (Fam : Nat → Fn GF) (kf kf' : GoFunc)
    (KF : GoInterface → GoString) (rvOf : GoInterface → Option GoString) (SW : St → IProp GF) (Rw : St → St → Prop)
    (H : List Ev → IProp GF) (BL : St → List Ev → IProp GF) (ds : List FD) (vs : List Delta)
    (sl : GoSlice) (b : Bool) (P Q : IProp GF),
  batchTyOk →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗
      s.[sharedIndexInformer, go!"indexer"] ↦□
        interface.mkOk (go.GoType.PointerType k8s_io.client_go.tools.cache.cache.ty) #ca ∗
      s.[sharedIndexInformer, go!"keyFunc"] ↦□ kf' ∗
      isCache ca ts γ OK Fam kf ∗ tsReader ts γ OK Fam ∗ storeWriter γ SW Rw ∗
      ⌜∀ σ, Rw σ σ ∧ Rw σ (batchStore KF rvOf σ ds)⌝ ∗
      sync.isMutex (s.[sharedIndexInformer, go!"blockDeltas"]) (blockDeltasRes SW H BL) ∗
      handlerOk OK (siiObj s) H ∗
      ([∗list] d;v ∈ ds;vs, fdAt OK d v) ∗ sl ↦* vs ∗ ⌜∀ d ∈ ds, d.isObjOk⌝ ∗
      keyOk (fun x => iprop(⌜x ∈ ds.map FD.obj?⌝)) kf KF ∗
      keyOk (fun x => iprop(⌜x ∈ ds.map FD.obj?⌝)) kf' KF ∗
      rvAcc (fun x => iprop(⌜x ∈ ds.map FD.obj?⌝)) rvOf ∗ P ∗
      (∀ (σ : St) (evs : List Ev) (σ' : St) (evs' : List Ev),
        P -∗ BL σ evs -∗ ⌜batchStep KF rvOf b σ ds σ' evs'⌝ ={⊤}=∗ BL σ' (evs ++ evs') ∗ Q) }}
    (App (App (App (Val (s @!! go.GoType.PointerType sharedIndexInformer.ty @!! go!"handleBatchDeltas"))
      (Val #lg)) (Val #sl)) (Val #b))
  {{ RET #interface.nil; Q ∗ sl ↦* vs ∗ tsReader ts γ OK Fam }}

end spec

end cache
end EtcdGrove
end Perennial
