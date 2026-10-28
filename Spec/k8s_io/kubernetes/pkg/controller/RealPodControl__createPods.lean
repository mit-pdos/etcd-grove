/-
`r.createPods(ctx, namespace, pod, object, controllerRef)` (`controller_utils.go:592`): the pod
control's create. Lean-first; phase 5 of `notes/k8s-daemonset-plan.md`. Its body is gap D2's
(`RealPodControl__createPods_body.lean`, a named hypothesis).

**What the code does** (read 2026-10-28 at the pin): a pod with no labels is refused (an error,
no request); otherwise the clientset's `CoreV1().Pods(namespace).Create(ctx, pod, {})`. On an
error it records a warning event (unless the namespace is terminating) and **returns the error,
before `OnWrite`**: whether the create took effect or not. On success it calls
`OnWrite(newPod, controllerRef)` (when set), logs, records an event, and returns `nil`.

So, over the model API server: the create's linearization point is the caller's (`createAU`, the
outcome `oc` per `CreateOut`), and
* `nil`: the create wrote the pod, the callback ran (`onWriteOk`, to `Ψ'`);
* an error: the outcome's `Ψ oc`, the callback not run, where the outcome is no effect
  (`.error _`) **or a write** (`.ok (true, _)`) **whose call returned the timeout**
  (`AmbiguousWrites`: `writeRet`'s second branch); this is the outcome S1's proof cannot account
  for (`issues/k8s-daemonset-ambiguous-create-duplicate-pod.md`);
* an error before any request (no labels): the linearization point unused (`createAU` back).
-/
module

public import Proof.k8s_io.kubernetes.pkg.controller.PodControlDefs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI apimodel k8s_io.kubernetes.pkg.controller

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.kubernetes.pkg.controller.Assumptions]
variable [api_sem : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Assumptions]

/-- **A create that reported an error**: no effect, or a write whose call returned the timeout
(possible only with `AmbiguousWrites`). -/
def createErrOutcome (amb : Bool) : Except ApiErr (Bool × Obj) → Prop
  | .error _ => True
  | .ok (w, _) => w = true ∧ mayHappen amb false

/-- **`r.createPods(ctx, ns, p, obj, cref)`**: see the file header. The controller object `obj`
is a `*DaemonSet` (`l`, read-only), as the DaemonSet controller passes. -/
abbrev RealPodControl.createPods.spec : Prop :=
  ∀ [ApiDeps] (r : RealPodControl) (γ : ApiNames)
    (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config)
    (ctx : GoInterface) (ns : GoString) (p : Loc) (d : kd.core.Pod) (l : Loc)
    (dd : kd.apps.DaemonSet) (cref : Loc) (Ψ : Except ApiErr (Bool × Obj) → IProp GF)
    (Ψ' : kd.core.Pod → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.controller ∗ ⌜ctx ≠ interface.nil⌝ ∗
      clientIs r.KubeClient' γ cfg ∗ recorderOk r.Recorder' ∗ dsAt l DFrac.discard dd ∗
      podAt p (DFrac.own 1) d ∗ createAU γ cfg ns d Ψ ∗ onWriteOk r.OnWrite' cref Ψ Ψ' }}
    (App (App (App (App (App (Val #(methods RealPodControl.ty go!"createPods" #r)) (Val #ctx))
      (Val #ns)) (Val #p))
      (Val #(interface.mkOk (go.GoType.PointerType k8s_io.api.apps.v1.DaemonSet.ty) #l :
        k8s_io.apimachinery.pkg.runtime.Object))) (Val #cref))
  {{ (err : GoInterface), RET #err; podAt p (DFrac.own 1) d ∗
      ((⌜err = interface.nil⌝ ∗ ∃ dp, Ψ' dp) ∨
       (⌜err ≠ interface.nil⌝ ∗ ∃ oc, Ψ oc ∗ ⌜createErrOutcome cfg.AmbiguousWrites' oc⌝) ∨
       (⌜err ≠ interface.nil ∧ (d.ObjectMeta'.Labels'.getD ∅) = ∅⌝ ∗ createAU γ cfg ns d Ψ)) }}

end spec

end dsctl
end EtcdGrove
end Perennial
