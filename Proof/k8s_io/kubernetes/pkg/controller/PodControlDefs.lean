/-
**The pod control's predicates** (`pkg/controller/controller_utils.go`'s `RealPodControl`; phase 5 of
`notes/k8s-daemonset-plan.md`). Lean-first.

* `clientIs kc γ cfg`: the controller's clientset, the model API server's non-admin one
  (`apimodel.clientsetAt`).
* `recorderOk r`: an event recorder whose `Eventf` returns and changes nothing the caller owns
  (events do not reach the model: `tools/record`'s broadcaster, names only, its recorder's spec a
  boundary hypothesis).
* `createAU γ cfg ns d Ψ`: the caller's fancy update at a pod create's linearization point (the
  model's `podClient.Create`, `CreateOut`), giving `Ψ oc` of the outcome (as `RealFIFO.Pop`'s
  `popAU`).
* `onWriteOk f Ψ Ψ'`: the pod control's write callback (`OnWrite`; the DaemonSet controller's is
  `podWriteCallback`, a `WroteAt` of the consistency store), called with the created pod after a
  create that returned it, from `Ψ` of the create's outcome to `Ψ'`.
-/
module

public import Proof.k8s_io.kubernetes.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI apimodel

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The controller's clientset** (persistent): the model API server's non-admin clientset. -/
def clientIs (kc : k8s_io.client_go.kubernetes.Interface) (γ : ApiNames)
    (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config) : IProp GF :=
  iprop(∃ c : Loc, ⌜kc = interface.mkOk
      (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Clientset.ty)
      #c⌝ ∗ clientsetAt c γ cfg false ∗
    isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel)

instance clientIs_persistent (kc : k8s_io.client_go.kubernetes.Interface) (γ : ApiNames)
    (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config) :
    Persistent (clientIs (GF := GF) kc γ cfg) := by
  unfold clientIs clientsetAt; infer_instance

/-- **An event recorder** (persistent): `Eventf(object, type, reason, fmt, args...)` returns and
changes nothing the caller owns but the arguments' slice, given back. -/
def recorderOk (r : k8s_io.client_go.tools.record.EventRecorder) : IProp GF :=
  iprop(∃ i : GoInterfaceOk, ⌜r = GoInterface.ok i⌝ ∗
    □ ∀ (o : GoInterface) (ty reason msg : GoString) (args : GoSlice) (dq : DFrac)
      (xs : List GoInterface) (Φ : val → IProp GF),
    args ↦*{dq} xs -∗ ▷ (args ↦*{dq} xs -∗ Φ #()) -∗
    WP (App (App (App (App (App (Val #(methods i.ty go!"Eventf" i.v)) (Val #o)) (Val #ty))
      (Val #reason)) (Val #msg)) (Val #args)) {{ Φ }})

instance recorderOk_persistent (r : k8s_io.client_go.tools.record.EventRecorder) :
    Persistent (recorderOk (GF := GF) r) := by
  unfold recorderOk; infer_instance

/-- **A pod create's linearization point**, the caller's: at the API state `σ`, a state `σ'` the
model's `Create` of the pod `d` in namespace `ns` may move to (`CreateOut`, the controller's
client not an admin's), and `Ψ` of the outcome. -/
def createAU (γ : ApiNames) (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config)
    (ns : GoString) (d : kd.core.Pod) (Ψ : Except ApiErr (Bool × Obj) → IProp GF) : IProp GF :=
  iprop(|={⊤, ∅}=> ∃ σ, apiState γ σ ∗
    ∀ σ' oc, ⌜CreateOut cfg.FailWrites' false .pods ns (.pod d) σ oc σ'⌝ -∗ apiState γ σ'
      ={∅, ⊤}=∗ Ψ oc)

/-- **The write callback** `f` (`RealPodControl.OnWrite`, not `nil`), for one call: with the
created pod (`p`, owned, deep value `dp`, the create's object) and the controller reference given
to the create, from `Ψ (ok (true, .pod dp))` it reaches `Ψ' dp`, the pod given back. (The caller
proves it of the callback's own spec for its `Ψ`: the DaemonSet controller's is a `WroteAt`.) -/
def onWriteOk (f : GoFunc) (cref : Loc) (Ψ : Except ApiErr (Bool × Obj) → IProp GF)
    (Ψ' : kd.core.Pod → IProp GF) : IProp GF :=
  iprop(⌜f ≠ func.nil⌝ ∗ ∀ (p : Loc) (dp : kd.core.Pod) (Φ : val → IProp GF),
    podAt p (DFrac.own 1) dp -∗ Ψ (.ok (true, .pod dp)) -∗
    ▷ (podAt p (DFrac.own 1) dp -∗ Ψ' dp -∗ Φ #()) -∗
    WP (App (App (Val #f) (Val #p)) (Val #cref)) {{ Φ }})

/-- **A pod delete's linearization point**, the caller's (as `createAU`, over the model's
`Delete`, `DeleteOut`, with the controller's default options). -/
def deleteAU (γ : ApiNames) (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config)
    (ns name : GoString) (Ψ : Except ApiErr Bool → IProp GF) : IProp GF :=
  iprop(|={⊤, ∅}=> ∃ σ, apiState γ σ ∗
    ∀ σ' oc, ⌜DeleteOut cfg.FailWrites' false .pods ns name kd.meta.DeleteOptions.zero σ oc σ'⌝ -∗
      apiState γ σ' ={∅, ⊤}=∗ Ψ oc)

/-- A pod template in the heap, owned at `dq`, with deep value `t`. -/
def tmplAt (tp : Loc) (dq : DFrac) (t : kd.core.PodTemplateSpec) : IProp GF :=
  iprop(∃ v : k8s_io.api.core.v1.PodTemplateSpec, tp ↦{dq} v ∗ kd.core.PodTemplateSpec.own v dq t)

/-- **An owner reference, read-only for good** (persistent; `metav1.NewControllerRef`'s result,
which nothing writes: the pod built from it shares its `*bool` fields). -/
def refAt (cref : Loc) (r : kd.meta.OwnerReference) : IProp GF :=
  iprop(∃ v : k8s_io.apimachinery.pkg.apis.«meta».v1.OwnerReference, cref ↦□ v ∗
    □ kd.meta.OwnerReference.own v DFrac.discard r)

instance refAt_persistent (cref : Loc) (r : kd.meta.OwnerReference) :
    Persistent (refAt (GF := GF) cref r) := by
  unfold refAt; infer_instance

/-- **The pod name validator** (`validation.ValidatePodName`, a package variable of a names-only
package, `apimachineryvalidation.NameIsDNSSubdomain`): it holds a function that returns some
slice. (A fact of `pkg/apis/core/validation`'s initialization, whose initializer is not
translated: an assumption of the specs that call `getPodsPrefix` until the closed theorem's
`Init.lean` gives it, from a trust-boundary statement of the initializer, pending approval.) -/
def podNameValidatorOk : IProp GF :=
  iprop(∃ f : GoFunc,
    globalAddr k8s_io.kubernetes.pkg.apis.core.validation.ValidatePodName ↦□ f ∗
    □ ∀ (s : GoString) (b : Bool) (Φ : val → IProp GF), ▷ (∀ sl : GoSlice, Φ #sl) -∗
      WP (App (App (Val #f) (Val #s)) (Val #b)) {{ Φ }})

instance podNameValidatorOk_persistent : Persistent (podNameValidatorOk (GF := GF)) := by
  unfold podNameValidatorOk; infer_instance

end defs

section pure
variable [GooseExts]

/-- **`getPodsPrefix(name)`'s possible results**: `name + "-"`, or `name` when the validator
rejects that. -/
def prefixOk (name pfx : GoString) : Prop := pfx = name ++ go!"-" ∨ pfx = name

/-- **The pod `GetPodFromTemplate(template, owner, ref)` builds**: the template's labels,
annotations (copied into fresh maps, empty for none) and finalizers, the generated name
`pfx`, the owner reference, the template's spec (a deep copy); every other field zero. -/
def podFromTemplate (t : kd.core.PodTemplateSpec) (pfx : GoString)
    (ref : Option kd.meta.OwnerReference) : kd.core.Pod :=
  { kd.core.Pod.zero with
    ObjectMeta' := { kd.meta.ObjectMeta.zero with
      Labels' := some (t.ObjectMeta'.Labels'.getD ∅)
      Annotations' := some (t.ObjectMeta'.Annotations'.getD ∅)
      GenerateName' := pfx
      Finalizers' := t.ObjectMeta'.Finalizers'
      OwnerReferences' := ref.toList }
    Spec' := t.Spec' }

/-- **`validateControllerRef(ref)` accepts `r`**: an API version, a kind, `Controller` and
`BlockOwnerDeletion` set to `true`. -/
def ctlRefValid (r : kd.meta.OwnerReference) : Prop :=
  r.APIVersion' ≠ go!"" ∧ r.Kind' ≠ go!"" ∧ r.Controller' = some true ∧
    r.BlockOwnerDeletion' = some true

end pure

end dsctl
end EtcdGrove
end Perennial
