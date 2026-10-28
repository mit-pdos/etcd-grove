/-
**What the reflector's watch path is stated with** (phase 4 of `notes/k8s-daemonset-plan.md`, fifth
round): the predicates of `handleAnyWatch`'s named hypothesis (gap D4) and of the reflector's
specs that do not need the informer's invariant. Lean-first.

* `resObjTy r`, `resListTy r`: the Go types of resource `r`'s objects (`*v1.Pod`, ...) and lists
  (`*v1.PodList`, ...).
* `fifoAU γ op K`: the FIFO's logically atomic update `op` with continuation `K` (the form of the
  FIFO's specs' atomic updates, `RealFIFO.Add`, ...).
* `watchFdTy typ`: the FIFO delta type a watch event's type gives (`ADDED` an `Add`, `MODIFIED` an
  `Update`, `DELETED` a `Delete`).
* `evAct γ OK typ x rv K`: what `handleAnyWatch` does with an event of type `typ` whose object `x`
  has resource version `rv`, for the FIFO `γ`: `Add`/`Update`/`Delete(x)` (with the FIFO's object
  contract `OK x`) or `Bookmark(rv)` through `fifoAU`, then `K`; no other type (the model's watch
  sends none).
* `typeOfOk et r` (persistent): `reflect.TypeOf` of a `*T` of resource `r` returns `et` (the
  reflector's `expectedType`).
* `errChOk ch`: the reflector's `resyncerrc` (`make(chan error, 1)`), a channel nothing is ever
  sent on and never closed (with resync period `0`, `startResync` never sends; its spec says so).
* `cbOk cb C L` (persistent): the callback `setLastSyncResourceVersion(rv, b)` takes `C i p rv` to
  `L i p`.
-/
module

public import Proof.k8s_io.client_go.tools.cache.FIFODefs
public import Proof.k8s_io.client_go.tools.cache.RefCtx
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI apimodel k8s_io.client_go.tools.cache

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The Go type of resource `r`'s objects (behind the pointer). -/
def resObjTy : Res → go.GoType
  | .pods => k8s_io.api.core.v1.Pod.ty
  | .nodes => k8s_io.api.core.v1.Node.ty
  | .daemonSets => k8s_io.api.apps.v1.DaemonSet.ty
  | .revisions => k8s_io.api.apps.v1.ControllerRevision.ty

/-- The Go type of resource `r`'s lists (behind the pointer). -/
def resListTy : Res → go.GoType
  | .pods => k8s_io.api.core.v1.PodList.ty
  | .nodes => k8s_io.api.core.v1.NodeList.ty
  | .daemonSets => k8s_io.api.apps.v1.DaemonSetList.ty
  | .revisions => k8s_io.api.apps.v1.ControllerRevisionList.ty

/-- **The deep value of a `ListOptions` literal** whose `SendInitialEvents` is `nil`, its timeout
pointer's target `ts`. -/
def loOf (v : k8s_io.apimachinery.pkg.apis.«meta».v1.ListOptions) (ts : Option w64) :
    kd.meta.ListOptions :=
  ⟨⟨v.TypeMeta'.Kind', v.TypeMeta'.APIVersion'⟩, v.LabelSelector', v.FieldSelector', v.Watch',
    v.AllowWatchBookmarks', v.ResourceVersion', v.ResourceVersionMatch', ts, v.Limit', v.Continue',
    none, v.ShardSelector'⟩

open Iris.ProofMode in
theorem lo_own_intro (v : k8s_io.apimachinery.pkg.apis.«meta».v1.ListOptions) (ts : Option w64)
    (dq : DFrac) (hsie : v.SendInitialEvents' = null) :
    ownPtrD (GF := GF) ownBaseD v.TimeoutSeconds' dq ts ⊢ kd.meta.ListOptions.own v dq (loOf v ts) := by
  iintro H
  unfold kd.meta.ListOptions.own kd.meta.TypeMeta.own loOf
  iframe
  simp only [ownPtrD]
  iframe
  ipureintro
  simp [hsie]

/-- **The FIFO's logically atomic update** `op`, then `K`. -/
def fifoAU (γ : FifoNames) (op : FQ → FQ) (K : IProp GF) : IProp GF :=
  iprop(|={⊤ \ ∅, ∅}=> ∃ q, fifoSt γ q ∗ (fifoSt γ (op q) ={∅, ⊤ \ ∅}=∗ K))

/-- The FIFO delta type of a watch event's type. -/
def watchFdTy (typ : GoString) : GoString :=
  if typ = go!"ADDED" then go!"Added"
  else if typ = go!"MODIFIED" then go!"Updated"
  else go!"Deleted"

/-- **What `handleAnyWatch` does with one event** of type `typ`, object `x`, resource version `rv`. -/
def evAct (γ : FifoNames) (OK : GoInterface → IProp GF) (typ : GoString) (x : GoInterface)
    (rv : GoString) (K : IProp GF) : IProp GF :=
  if typ = go!"ADDED" ∨ typ = go!"MODIFIED" ∨ typ = go!"DELETED" then
    iprop(□ OK x ∗ fifoAU γ (FQ.addObj (watchFdTy typ) x) K)
  else if typ = go!"BOOKMARK" then
    fifoAU γ (fun q => { q with items := q.items ++ [.bookmark rv] }) K
  else iprop(False)

/-- **`reflect.TypeOf` of resource `r`'s objects is `et`** (persistent). -/
def typeOfOk (et : reflect.Type') (r : Res) : IProp GF :=
  iprop(□ ∀ (l : Loc) (Φ : val → IProp GF), ▷ Φ #et -∗
    WP (App (Val (@! reflect.TypeOf)) (Val #(interface.mkOk (go.GoType.PointerType (resObjTy r)) #l)))
      {{ Φ }})

instance typeOfOk_persistent (et : reflect.Type') (r : Res) :
    Persistent (typeOfOk (GF := GF) et r) := by
  unfold typeOfOk; infer_instance

/-- **The resync error channel**: nothing is ever sent on it (persistent). -/
def errChOk (ch : GoChan) : IProp GF :=
  iprop(∃ γ : ChanNames, isChan ch γ GoInterface ∗
    inv (nroot.@"resyncerrc") (ownChan γ GoInterface (.Buffered [])))

instance errChOk_persistent (ch : GoChan) : Persistent (errChOk (GF := GF) ch) := by
  unfold errChOk; infer_instance

/-- **The watch's callback** `setLastSyncResourceVersion(rv, b)` takes `C i p rv` to `L i p`
(persistent). -/
def cbOk (cb : GoFunc) (C : Nat → Pos' → GoString → IProp GF) (L : Nat → Pos' → IProp GF) :
    IProp GF :=
  iprop(□ ∀ (i : Nat) (p : Pos') (rv : GoString) (b : Bool) (Φ : val → IProp GF),
    C i p rv -∗ ▷ (L i p -∗ Φ #()) -∗ WP (App (App (Val #cb) (Val #rv)) (Val #b)) {{ Φ }})

instance cbOk_persistent (cb : GoFunc) (C : Nat → Pos' → GoString → IProp GF)
    (L : Nat → Pos' → IProp GF) : Persistent (cbOk cb C L) := by
  unfold cbOk; infer_instance

/-- **Each event's step** (persistent), what the caller of `handleAnyWatch` provides: after `i`
events at the watch's position `p` (`L i p`), the `i`-th event `ev` of the watch `γw` (its contract
`evOk`) gives its next position `p'`, the event's object read-only, of resource `r`, and the
store's step for it (`evAct`), whose continuation is the callback's precondition `C (i + 1) p'`
at the object's resource version. -/
def evStepOk (γa : ApiNames) (γw : WatchNames) (r : Res) (bm : Bool) (inits : List Obj)
    (γ : FifoNames) (OK : GoInterface → IProp GF) (L : Nat → Pos' → IProp GF)
    (C : Nat → Pos' → GoString → IProp GF) : IProp GF :=
  iprop(□ ∀ (i : Nat) (p : Pos') (ev : k8s_io.apimachinery.pkg.watch.Event),
    L i p -∗ monoListIdxOwn γw.cur i p -∗ evOk γa γw r go!"" bm inits (i : Int) ev ={⊤}=∗
    ∃ (o : Obj) (p' : Pos'), monoListIdxOwn γw.cur (i + 1) p' ∗
      □ apimodel.objAt ev.Object' DFrac.discard o ∗ ⌜o.res = r⌝ ∗
      evAct γ OK ev.Type' ev.Object' o.meta.ResourceVersion'
        (C (i + 1) p' o.meta.ResourceVersion'))

/-- **The watch's retry state** (`watch`'s `RetryWithDeadline`): a `*retryWithDeadlineImpl` owned by
the reflector's goroutine, over a real clock, whose `isRetryable` is `apierrors.IsInternalError`. -/
def retryOwn (rt : GoInterface) : IProp GF :=
  iprop(∃ (l : Loc) (v : retryWithDeadlineImpl) (c : k8s_io.utils.clock.RealClock),
    ⌜rt = interface.mkOk (go.GoType.PointerType retryWithDeadlineImpl.ty) #l⌝ ∗ l ↦ v ∗
    ⌜v.clock' = interface.mkOk k8s_io.utils.clock.RealClock.ty #c ∧
      v.isRetryable' = functions k8s_io.apimachinery.pkg.api.errors.IsInternalError []⌝)

instance evStepOk_persistent (γa : ApiNames) (γw : WatchNames) (r : Res) (bm : Bool)
    (inits : List Obj) (γ : FifoNames) (OK : GoInterface → IProp GF) (L : Nat → Pos' → IProp GF)
    (C : Nat → Pos' → GoString → IProp GF) :
    Persistent (evStepOk γa γw r bm inits γ OK L C) := by
  unfold evStepOk; infer_instance

end defs

section tyOk
variable [ext : FfiSyntax] [go_gctx : GoGlobalContext] [GoLocalContext] [GoSemanticsFunctions]

/-- **`*RealFIFO` is not a `ResourceVersionUpdater`** (a method-set fact, a premise as
`batchTyOk`: `methodSet` is uninterpreted in the model): `RealFIFO` has no `UpdateResourceVersion`
method (`the_real_fifo.go`), so the watch's callback's `r.store.(ResourceVersionUpdater)` fails. -/
def rvuTyOk : Prop :=
  go.typeSetContains (go.GoType.PointerType RealFIFO.ty) ResourceVersionUpdater.ty = false

/-- **`*RealFIFO` is a `ReflectorBookmarkStore`** (a method-set fact, a premise as `rvuTyOk`): it has
`Bookmark(string) error` (`the_real_fifo.go`), so `handleAnyWatch`'s `store.(ReflectorBookmarkStore)`
succeeds and a bookmark reaches the FIFO. -/
def bmTyOk : Prop :=
  go.typeSetContains (go.GoType.PointerType RealFIFO.ty) ReflectorBookmarkStore.ty = true

end tyOk

end cache
end EtcdGrove
end Perennial
