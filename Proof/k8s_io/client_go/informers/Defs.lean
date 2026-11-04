/-
**client-go's informer factory, as the DaemonSet driver uses it** (`informers/factory.go`, the
group and version packages `informers/{apps,core}{,/v1}`): the predicates its specs are stated with.
Lean-first; the DaemonSet run's track A (`notes/k8s-daemonset-run/design.md`).

* `facVal f`: the factory `*sharedInformerFactory` as a `SharedInformerFactory`.
* **Scope**: the informers of the run's model API server (`apimodel`: its four resources, its
  history, its clientset); a client of another API server cannot use these predicates.
* `nsIdxFn` (an index relation, `Fn`): `MetaNamespaceIndexFunc`'s, an object's namespace. The
  factory's informers index their store by namespace (`cache.NamespaceIndex`:
  `Fams r go!"namespace" = nsIdxFn`).
* **Index relations by name** (review 1's M1): `Fams r n` is the relation of the index named `n`
  of resource `r`'s store, fixed when the factory is made, whoever registers the index (the
  factory, or a client's `AddIndexers`). A departure (a persistent family fixed at creation, as
  `c3-store-law.md`'s): index names are a global convention in client-go, and Go trusts the name
  (`AddPodControllerIndexer` skips a name already registered).
* `isFactory f γF γa cfg Fams` (persistent): the factory over the model API server's (non-admin)
  clientset (`clientsetAt`), with read access to its state (`apiReader`) and its writers' good keys
  (`keysOk`), the default resync `0`, all namespaces, no tweak, transform, shard selector or name,
  the informers' feature gates (`features.informerGates`, taken at its construction, for the
  informers it makes); its informer of resource `r` (once created) has the relations `Fams r`. Its lock's resource
  (`facLocked`) is internal: the informers made (the ghost map `γF.infs`, `facInf`), each with its
  `isInformer`. (Refined by the proofs of `InformerFor`/`Start`: the maps' contents and the
  `reflect.Type` keys, which need a stronger `reflect.TypeOf` boundary spec, see the run's report.)
* `facInf γF r I` (persistent): the factory's informer of resource `r` has names `I`, for good
  (`facInf_agree`): every `Informer()` and `Lister()` of the resource's typed informer is over the
  same informer; its not-started token is the factory's of `r` (`I.γi.ns = γF.ns r`).
* **The not-started tokens** (decision R6): the factory preallocates one per resource (`γF.ns r`,
  `informer.nsAlloc`), before the informer of `r` exists. `facNotStarted γF r q` is fraction `q` of
  the callers' half, which the factory's constructor hands out (`[∗list] r ∈ resAll,
  facNotStarted γF r 1`); once `Informer()` has given `facInf γF r I`, it is the informer's
  (`facNotStarted_inf`: `infNotStarted I.γi q`), which `AddEventHandlerWithOptions`/`AddIndexers`
  borrow, and `Start`/`StartWithContext` take every resource's whole callers' half back (to run the
  informers it starts, `infRunOk`). The start-lock half waits in the factory's lock until
  `InformerFor` makes the informer, whose constructor takes it (`newInfFnOk`).
* `facRefAt T l f` (persistent): a struct `*T` at `l` holding the factory `f` with namespace `""`
  and no tweak (the groups `apps.group`/`core.group`, the versions `v1.version`, the typed
  informers `daemonSetInformer`, ...; the node informer has no namespace, `facRefAtNoNs`):
  `typedInfAt r l f` for resource `r`'s typed informer.
* `doneChOk ch` (persistent): the stop channel given to `Start` (a context's `Done()` channel: a
  broadcast channel, or the closed `closedchan`).
-/
module

public import Proof.k8s_io.client_go.informers.Base
public import Proof.k8s_io.client_go.tools.cache.InformerApi
public import Proof.k8s_io.client_go.tools.cache.RefCtx
public import Proof.k8s_io.client_go.features.GateDefs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace informers

open Iris Iris.BI apimodel cache informer

/-- The factory's ghost names: its registry of informers (resource to names), and the
not-started token of each resource's informer (preallocated, see the file header). -/
structure FacNames where
  infs : GName
  ns : Res → GName

/-- The resources (the factory's informers' possible kinds). -/
def resAll : List Res := [.pods, .nodes, .daemonSets, .revisions]

theorem mem_resAll (r : Res) : r ∈ resAll := by cases r <;> simp [resAll]

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [cache_sem : k8s_io.client_go.tools.cache.Assumptions]
variable [ctx_sem : _root_.Perennial.context.Assumptions]

/-- The factory as a `SharedInformerFactory`. -/
def facVal (f : Loc) : GoInterface :=
  interface.mkOk (go.GoType.PointerType k8s_io.client_go.informers.sharedInformerFactory.ty) #f

/-- The model's clientset as a `kubernetes.Interface`. -/
def clientVal (c : Loc) : GoInterface :=
  interface.mkOk
    (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Clientset.ty)
    #c

/-- **`MetaNamespaceIndexFunc`'s relation**: an object's namespace. -/
def nsIdxFn : Fn GF :=
  fun x vs => iprop(∃ o : Obj, □ apimodel.objAt x DFrac.discard o ∗ ⌜vs = [o.meta.Namespace']⌝)

/-- **The factory's informer of resource `r` has names `I`** (persistent). -/
def facInf (γF : FacNames) (r : Res) (I : InfH) : IProp GF :=
  iprop(r ↪[γF.infs]□ I ∗ ⌜I.γi.ns = γF.ns r⌝)

instance facInf_persistent (γF : FacNames) (r : Res) (I : InfH) :
    Persistent (facInf (GF := GF) γF r I) := by
  unfold facInf; infer_instance

open Iris.ProofMode in
/-- **One informer per resource.** -/
theorem facInf_agree (γF : FacNames) (r : Res) (I I' : InfH) :
    facInf (GF := GF) γF r I ∗ facInf γF r I' ⊢ ⌜I = I'⌝ := by
  unfold facInf
  iintro ⟨⟨H1, -⟩, ⟨H2, -⟩⟩
  iapply (ghostMapElem_agree r γF.infs DFrac.discard DFrac.discard I I') $$ H1 H2

/-- **Resource `r`'s informer has not started** (fraction `q` of the callers' half of the factory's
token of `r`; see the file header). -/
def facNotStarted (γF : FacNames) (r : Res) (q : Qp) : IProp GF := notStartedAt (γF.ns r) q

instance facNotStarted_fractional (γF : FacNames) (r : Res) :
    Fractional (facNotStarted (GF := GF) γF r) := by
  unfold facNotStarted; exact notStartedAt_fractional _

instance facNotStarted_timeless (γF : FacNames) (r : Res) (q : Qp) :
    Timeless (facNotStarted (GF := GF) γF r q) := by
  unfold facNotStarted; infer_instance

open Iris.ProofMode in
/-- **The factory's token of `r` is its informer's.** -/
theorem facNotStarted_inf (γF : FacNames) (r : Res) (I : InfH) (q : Qp) :
    facInf (GF := GF) γF r I ⊢ (facNotStarted γF r q ∗-∗ infNotStarted I.γi q) := by
  unfold facInf facNotStarted infNotStarted
  iintro ⟨-, %h⟩
  rw [h]
  iapply wandIff_refl

/-- The factory's read-only fields (internal). -/
def facFixed (f c : Loc) : IProp GF :=
  iprop(f.[k8s_io.client_go.informers.sharedInformerFactory, go!"client"] ↦□
      (clientVal c : k8s_io.client_go.kubernetes.Interface) ∗
    f.[k8s_io.client_go.informers.sharedInformerFactory, go!"namespace"] ↦□ (go!"" : GoString) ∗
    f.[k8s_io.client_go.informers.sharedInformerFactory, go!"tweakListOptions"] ↦□
      (func.nil : k8s_io.client_go.informers.internalinterfaces.TweakListOptionsFunc) ∗
    f.[k8s_io.client_go.informers.sharedInformerFactory, go!"defaultResync"] ↦□
      (W64 0 : time.Duration) ∗
    f.[k8s_io.client_go.informers.sharedInformerFactory, go!"transform"] ↦□
      (func.nil : k8s_io.client_go.tools.cache.TransformFunc) ∗
    f.[k8s_io.client_go.informers.sharedInformerFactory, go!"shardSelector"] ↦□
      (interface.nil : k8s_io.apimachinery.pkg.sharding.Selector) ∗
    f.[k8s_io.client_go.informers.sharedInformerFactory, go!"informerName"] ↦□ (null : Loc))

/-- **The factory's lock's resource** (internal, see the file header): the informers made, each an
informer of its resource over the factory's family, over the factory's not-started token of its
resource; for each resource not made, its token's start-lock half. -/
def facLocked (f : Loc) (γF : FacNames) (γa : ApiNames) (Fams : Res → GoString → Fn GF) : IProp GF :=
  iprop(∃ (mi ms : GoMap) (sd : Bool) (G : GMap Res InfH),
    f.[k8s_io.client_go.informers.sharedInformerFactory, go!"informers"] ↦ mi ∗
    f.[k8s_io.client_go.informers.sharedInformerFactory, go!"startedInformers"] ↦ ms ∗
    f.[k8s_io.client_go.informers.sharedInformerFactory, go!"shuttingDown"] ↦ sd ∗
    ghostMapAuth γF.infs 1 G ∗
    ([∗map] r ↦ I ∈ G, ∃ x : GoInterface, ⌜I.γi.ns = γF.ns r⌝ ∗ isInformer x γa r I (Fams r) ∗
      infRunOk x I.γi ∗ infIdx I go!"namespace") ∗
    [∗list] r ∈ resAll, ⌜(G !! r).isSome⌝ ∨ nsLock (γF.ns r) false)

/-- **The factory** (persistent): see the file header. -/
def isFactory (f : Loc) (γF : FacNames) (γa : ApiNames)
    (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config)
    (Fams : Res → GoString → Fn GF) : IProp GF :=
  iprop(∃ c : Loc, facFixed f c ∗ clientsetAt c γa cfg false ∗ apiReader γa ∗ keysOk γa ∗
    features.informerGates ∗ ⌜∀ r, Fams r go!"namespace" = nsIdxFn⌝ ∗
    sync.isMutex (f.[k8s_io.client_go.informers.sharedInformerFactory, go!"lock"])
      (facLocked f γF γa Fams))

instance isFactory_persistent (f : Loc) (γF : FacNames) (γa : ApiNames)
    (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config)
    (Fams : Res → GoString → Fn GF) : Persistent (isFactory f γF γa cfg Fams) := by
  unfold isFactory facFixed clientsetAt; infer_instance

/-- **A struct `*T` at `l` holding the factory `f`** (persistent; the groups, the versions, the
typed informers: their three fields). -/
def facRefAt (T : Type) (l f : Loc) : IProp GF :=
  iprop(structFieldRef T go!"factory" l ↦□
      (facVal f : k8s_io.client_go.informers.internalinterfaces.SharedInformerFactory) ∗
    structFieldRef T go!"namespace" l ↦□ (go!"" : GoString) ∗
    structFieldRef T go!"tweakListOptions" l ↦□
      (func.nil : k8s_io.client_go.informers.internalinterfaces.TweakListOptionsFunc))

instance facRefAt_persistent (T : Type) (l f : Loc) : Persistent (facRefAt (GF := GF) T l f) := by
  unfold facRefAt; infer_instance

/-- The Go struct type of resource `r`'s typed informer. -/
def typedInfStruct : Res → Type
  | .daemonSets => k8s_io.client_go.informers.apps.v1.daemonSetInformer
  | .revisions => k8s_io.client_go.informers.apps.v1.controllerRevisionInformer
  | .pods => k8s_io.client_go.informers.core.v1.podInformer
  | .nodes => k8s_io.client_go.informers.core.v1.nodeInformer

/-- The Go type of resource `r`'s typed informer. -/
def typedInfTy : Res → go.GoType
  | .daemonSets => k8s_io.client_go.informers.apps.v1.daemonSetInformer.ty
  | .revisions => k8s_io.client_go.informers.apps.v1.controllerRevisionInformer.ty
  | .pods => k8s_io.client_go.informers.core.v1.podInformer.ty
  | .nodes => k8s_io.client_go.informers.core.v1.nodeInformer.ty

/-- A struct `*T` at `l` holding the factory `f` and no tweak, without a namespace (the node
informer: nodes are cluster-scoped). -/
def facRefAtNoNs (T : Type) (l f : Loc) : IProp GF :=
  iprop(structFieldRef T go!"factory" l ↦□
      (facVal f : k8s_io.client_go.informers.internalinterfaces.SharedInformerFactory) ∗
    structFieldRef T go!"tweakListOptions" l ↦□
      (func.nil : k8s_io.client_go.informers.internalinterfaces.TweakListOptionsFunc))

instance facRefAtNoNs_persistent (T : Type) (l f : Loc) :
    Persistent (facRefAtNoNs (GF := GF) T l f) := by
  unfold facRefAtNoNs; infer_instance

/-- **Resource `r`'s typed informer at `l`, of the factory `f`** (persistent). -/
def typedInfAt (r : Res) (l f : Loc) : IProp GF :=
  match r with
  | .nodes => facRefAtNoNs (typedInfStruct r) l f
  | _ => facRefAt (typedInfStruct r) l f

instance typedInfAt_persistent (r : Res) (l f : Loc) : Persistent (typedInfAt (GF := GF) r l f) := by
  cases r <;> unfold typedInfAt <;> infer_instance

/-- **What the factory's informer of `r` gives**: its names, for good, the informer as the value
`x`, its store indexed by namespace. -/
def facInfOut (γF : FacNames) (γa : ApiNames) (r : Res) (Fams : Res → GoString → Fn GF)
    (x : GoInterface) : IProp GF :=
  iprop(∃ I : InfH, facInf γF r I ∗ isInformer x γa r I (Fams r) ∗ infIdx I go!"namespace")

instance facInfOut_persistent (γF : FacNames) (γa : ApiNames) (r : Res)
    (Fams : Res → GoString → Fn GF) (x : GoInterface) :
    Persistent (facInfOut γF γa r Fams x) := by
  unfold facInfOut; infer_instance

/-- **A new informer of `r`** (an `InformerFor`'s `newFunc` result, before the factory registers
it): the informer as `x`, its not-started token `γns`, runnable, its store indexed by namespace. -/
def newInfOut (γa : ApiNames) (r : Res) (FamN : GoString → Fn GF) (γns : GName) (x : GoInterface) :
    IProp GF :=
  iprop(∃ I : InfH, ⌜I.γi.ns = γns⌝ ∗ isInformer x γa r I FamN ∗ infRunOk x I.γi ∗
    infIdx I go!"namespace")

instance newInfOut_persistent (γa : ApiNames) (r : Res) (FamN : GoString → Fn GF) (γns : GName)
    (x : GoInterface) : Persistent (newInfOut γa r FamN γns x) := by
  unfold newInfOut; infer_instance

/-- **`InformerFor`'s `newFunc` contract**: called with a clientset of the server and resync `0`,
the start-lock half of a not-started token `γns` and the informers' feature gates, it returns a new
informer of `r` over that token (persistent). -/
def newInfFnOk (nf : GoFunc) (γa : ApiNames)
    (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config) (r : Res)
    (FamN : GoString → Fn GF) : IProp GF :=
  iprop(□ ∀ (c : Loc) (γns : GName) (Φ : val → IProp GF), clientsetAt c γa cfg false -∗
    features.informerGates -∗ nsLock γns false -∗
    ▷ (∀ x : GoInterface, newInfOut γa r FamN γns x -∗ Φ #x) -∗
    WP (App (App (Val #nf) (Val #(clientVal c))) (Val #(W64 0 : time.Duration))) {{ Φ }})

instance newInfFnOk_persistent (nf : GoFunc) (γa : ApiNames)
    (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config) (r : Res)
    (FamN : GoString → Fn GF) : Persistent (newInfFnOk nf γa cfg r FamN) := by
  unfold newInfFnOk; infer_instance

/-- **A stop channel** (persistent): a broadcast channel, or the closed `closedchan`. -/
def doneChOk (ch : GoChan) : IProp GF :=
  iprop(∃ γch : ChanNames, (∃ Q : IProp GF, ownBroadcastChan ch γch Q .Unknown) ∨
    (isChan ch γch Unit ∗ inv context.closedchanN (ownChan γch Unit (.Closed []))))

instance doneChOk_persistent (ch : GoChan) : Persistent (doneChOk (GF := GF) ch) := by
  unfold doneChOk; infer_instance

end defs

end informers
end EtcdGrove
end Perennial
