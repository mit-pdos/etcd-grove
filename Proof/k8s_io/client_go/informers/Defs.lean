/-
**client-go's informer factory, as the DaemonSet driver uses it** (`informers/factory.go`, the
group and version packages `informers/{apps,core}{,/v1}`): the predicates its specs are stated with.
Lean-first; the DaemonSet run's track A (`notes/k8s-daemonset-run/design.md`).

* `facVal f`: the factory `*sharedInformerFactory` as a `SharedInformerFactory`.
* `nsIdxFn` (an index relation, `Fn`): `MetaNamespaceIndexFunc`'s, an object's namespace. The
  factory's informers index their store by namespace (`cache.NamespaceIndex`, id `0` of their
  family: `Fams r 0 = nsIdxFn`).
* `isFactory f γF γa cfg Fams` (persistent): the factory over the model API server's (non-admin)
  clientset (`clientsetAt`), with read access to its state (`apiReader`) and its writers' good keys
  (`keysOk`), the default resync `0`, all namespaces, no tweak, transform, shard selector or name;
  its informer of resource `r` (once created) has the store's family `Fams r`. Its lock's resource
  (`facLocked`) is internal: the informers made (the ghost map `γF.infs`, `facInf`), each with its
  `isInformer`. (Refined by the proofs of `InformerFor`/`Start`: the maps' contents and the
  `reflect.Type` keys, which need a stronger `reflect.TypeOf` boundary spec, see the run's report.)
* `facInf γF r I` (persistent): the factory's informer of resource `r` has names `I`, for good
  (`facInf_agree`): every `Informer()` and `Lister()` of the resource's typed informer is over the
  same informer.
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

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace informers

open Iris Iris.BI apimodel cache informer

/-- The factory's ghost names: its registry of informers (resource to names). -/
structure FacNames where
  infs : GName

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
def facInf (γF : FacNames) (r : Res) (I : InfH) : IProp GF := r ↪[γF.infs]□ I

instance facInf_persistent (γF : FacNames) (r : Res) (I : InfH) :
    Persistent (facInf (GF := GF) γF r I) := by
  unfold facInf; infer_instance

open Iris.ProofMode in
/-- **One informer per resource.** -/
theorem facInf_agree (γF : FacNames) (r : Res) (I I' : InfH) :
    facInf (GF := GF) γF r I ∗ facInf γF r I' ⊢ ⌜I = I'⌝ := by
  unfold facInf
  iintro ⟨H1, H2⟩
  iapply (ghostMapElem_agree r γF.infs DFrac.discard DFrac.discard I I') $$ H1 H2

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
informer of its resource over the factory's family. -/
def facLocked (f : Loc) (γF : FacNames) (γa : ApiNames) (Fams : Res → Nat → Fn GF) : IProp GF :=
  iprop(∃ (mi ms : GoMap) (sd : Bool) (G : GMap Res InfH),
    f.[k8s_io.client_go.informers.sharedInformerFactory, go!"informers"] ↦ mi ∗
    f.[k8s_io.client_go.informers.sharedInformerFactory, go!"startedInformers"] ↦ ms ∗
    f.[k8s_io.client_go.informers.sharedInformerFactory, go!"shuttingDown"] ↦ sd ∗
    ghostMapAuth γF.infs 1 G ∗
    [∗map] r ↦ I ∈ G, ∃ x : GoInterface, isInformer x γa r I (Fams r) ∗ infRunOk x ∗
      infIdx I go!"namespace" 0)

/-- **The factory** (persistent): see the file header. -/
def isFactory (f : Loc) (γF : FacNames) (γa : ApiNames)
    (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config)
    (Fams : Res → Nat → Fn GF) : IProp GF :=
  iprop(∃ c : Loc, facFixed f c ∗ clientsetAt c γa cfg false ∗ apiReader γa ∗ keysOk γa ∗
    ⌜∀ r, Fams r 0 = nsIdxFn⌝ ∗
    sync.isMutex (f.[k8s_io.client_go.informers.sharedInformerFactory, go!"lock"])
      (facLocked f γF γa Fams))

instance isFactory_persistent (f : Loc) (γF : FacNames) (γa : ApiNames)
    (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config)
    (Fams : Res → Nat → Fn GF) : Persistent (isFactory f γF γa cfg Fams) := by
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
def facInfOut (γF : FacNames) (γa : ApiNames) (r : Res) (Fams : Res → Nat → Fn GF)
    (x : GoInterface) : IProp GF :=
  iprop(∃ I : InfH, facInf γF r I ∗ isInformer x γa r I (Fams r) ∗ infIdx I go!"namespace" 0)

instance facInfOut_persistent (γF : FacNames) (γa : ApiNames) (r : Res)
    (Fams : Res → Nat → Fn GF) (x : GoInterface) :
    Persistent (facInfOut γF γa r Fams x) := by
  unfold facInfOut; infer_instance

/-- **A new informer of `r`** (an `InformerFor`'s `newFunc` result, before the factory registers
it): the informer as `x`, runnable, its store indexed by namespace. -/
def newInfOut (γa : ApiNames) (r : Res) (Fam : Nat → Fn GF) (x : GoInterface) : IProp GF :=
  iprop(∃ I : InfH, isInformer x γa r I Fam ∗ infRunOk x ∗ infIdx I go!"namespace" 0)

instance newInfOut_persistent (γa : ApiNames) (r : Res) (Fam : Nat → Fn GF) (x : GoInterface) :
    Persistent (newInfOut γa r Fam x) := by
  unfold newInfOut; infer_instance

/-- **`InformerFor`'s `newFunc` contract**: called with a clientset of the server and resync `0`,
it returns a new informer of `r` (persistent). -/
def newInfFnOk (nf : GoFunc) (γa : ApiNames)
    (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config) (r : Res)
    (Fam : Nat → Fn GF) : IProp GF :=
  iprop(□ ∀ (c : Loc) (Φ : val → IProp GF), clientsetAt c γa cfg false -∗
    ▷ (∀ x : GoInterface, newInfOut γa r Fam x -∗ Φ #x) -∗
    WP (App (App (Val #nf) (Val #(clientVal c))) (Val #(W64 0 : time.Duration))) {{ Φ }})

instance newInfFnOk_persistent (nf : GoFunc) (γa : ApiNames)
    (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config) (r : Res)
    (Fam : Nat → Fn GF) : Persistent (newInfFnOk nf γa cfg r Fam) := by
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
