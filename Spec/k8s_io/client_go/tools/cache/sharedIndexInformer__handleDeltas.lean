/-
`(*sharedIndexInformer).handleDeltas(logger, obj, isInInitialList)` (`shared_informer.go:1090`): the
shared informer's processing function, `processDeltas` under `blockDeltas` with the informer itself
as the handler. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.processDeltas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI k8s_io.client_go.tools.cache

/-- The shared informer `s` as an interface (its handler, `ResourceEventHandler`). -/
def siiObj [FfiSyntax] [GoGlobalContext] (s : Loc) : GoInterface :=
  interface.mkOk (go.GoType.PointerType sharedIndexInformer.ty) #s

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- **The `blockDeltas` lock's resource**: the store's exclusive writer at some state, the
handler's delivered events, and the client's relation `BL` between them. -/
def blockDeltasRes (SW : St → IProp GF) (H : List Ev → IProp GF) (BL : St → List Ev → IProp GF) :
    IProp GF :=
  iprop(∃ (σ : St) (evs : List Ev), SW σ ∗ H evs ∗ BL σ evs)

/-- **`s.handleDeltas(lg, Deltas{v}, b)`** for the shared informer `s` over the cache `ca` (its
indexer, key function `kf'`), its `blockDeltas` lock guarding `blockDeltasRes`, the informer being
a handler for `H` (`handlerOk`, its `OnAdd`/`OnUpdate`/`OnDelete`), one queued delta as for
`processDeltas`: no error; under the lock, the store and the events step by `stepFD`, which the
client's view shift `Hstep` turns from `P` into `Q` (its relation `BL` kept). -/
abbrev sharedIndexInformer.handleDeltas.spec : Prop :=
  ∀ (s : Loc) (lg : github_com.go_logr.logr.Logger) (ca ts : Loc) (γ : TsNames)
    (OK : GoInterface → IProp GF) (Fam : Nat → Fn) (kf kf' : GoFunc)
    (KF : GoInterface → GoString) (rvOf : GoInterface → Option GoString) (SW : St → IProp GF)
    (H : List Ev → IProp GF) (BL : St → List Ev → IProp GF) (d : FD) (v : Delta) (sl : GoSlice)
    (b : Bool) (P Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗
      s.[sharedIndexInformer, go!"indexer"] ↦□
        interface.mkOk (go.GoType.PointerType k8s_io.client_go.tools.cache.cache.ty) #ca ∗
      s.[sharedIndexInformer, go!"keyFunc"] ↦□ kf' ∗
      isCache ca ts γ OK Fam kf ∗ tsReader ts γ OK Fam ∗ storeWriter γ SW ∗
      sync.isMutex (s.[sharedIndexInformer, go!"blockDeltas"]) (blockDeltasRes SW H BL) ∗
      handlerOk OK (siiObj s) H ∗
      fdAt OK d v ∗ sl ↦* [v] ∗ ⌜d.kindOk⌝ ∗
      keyOk (fun x => iprop(⌜x ∈ d.objs⌝)) kf KF ∗ keyOk (fun x => iprop(⌜x ∈ d.objs⌝)) kf' KF ∗
      rvAcc (fun x => iprop(⌜x ∈ d.objs⌝)) rvOf ∗ P ∗
      (∀ (σ : St) (evs : List Ev) (σ' : St) (evs' : List Ev),
        P -∗ BL σ evs -∗ ⌜stepFD KF rvOf b σ d σ' evs'⌝ ={⊤}=∗ BL σ' (evs ++ evs') ∗ Q) }}
    (App (App (App (Val (s @!! go.GoType.PointerType sharedIndexInformer.ty @!! go!"handleDeltas"))
      (Val #lg)) (Val #(interface.mkOk Deltas.ty #sl))) (Val #b))
  {{ RET #interface.nil; Q ∗ sl ↦* [v] ∗ tsReader ts γ OK Fam }}

end spec

end cache
end EtcdGrove
end Perennial
