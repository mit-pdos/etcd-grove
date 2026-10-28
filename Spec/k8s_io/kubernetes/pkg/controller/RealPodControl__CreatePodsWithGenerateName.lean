/-
`r.CreatePodsWithGenerateName(ctx, namespace, template, controllerObject, controllerRef,
generateName)` (`controller_utils.go:544`), for an empty `generateName` (as `CreatePods` passes).
Lean-first; phase 5 of `notes/k8s-daemonset-plan.md`.

What the code does: `validateControllerRef` (an error, no request, for a reference without an API
version, a kind, `Controller` or `BlockOwnerDeletion` set); `GetPodFromTemplate`; then
`createPods` of that pod (`RealPodControl__createPods.lean`: the outcomes, the ambiguous one
included).
-/
module

public import Spec.k8s_io.kubernetes.pkg.controller.RealPodControl__createPods

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI apimodel k8s_io.kubernetes.pkg.controller

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.kubernetes.pkg.controller.Assumptions]
variable [api_sem : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Assumptions]

/-- **What a pod-control create returns** for the template `t` (the pod for some generated name
`pfx`): `nil` and `Ψ'` (the callback ran); an error and `Ψ` of a create that reported one (no
effect, or an ambiguous write); or an error before any request, the linearization point unused
(an invalid reference, or no labels). -/
def podCreateRet (amb : Bool) (Ψ : Except ApiErr (Bool × Obj) → IProp GF)
    (Ψ' : kd.core.Pod → IProp GF) (unused : IProp GF) (err : GoInterface) : IProp GF :=
  iprop((⌜err = interface.nil⌝ ∗ ∃ dp, Ψ' dp) ∨
    (⌜err ≠ interface.nil⌝ ∗ ∃ oc, Ψ oc ∗ ⌜createErrOutcome amb oc⌝) ∨
    (⌜err ≠ interface.nil⌝ ∗ unused))

/-- **`r.CreatePodsWithGenerateName(ctx, ns, tp, ds, cref, "")`**: see the file header. The
caller's linearization point is for the pod of any of `getPodsPrefix`'s results. -/
abbrev RealPodControl.CreatePodsWithGenerateName.spec : Prop :=
  ∀ [ApiDeps] (r : RealPodControl) (γ : ApiNames)
    (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config)
    (ctx : GoInterface) (ns : GoString) (tp : Loc) (dq : DFrac) (t : kd.core.PodTemplateSpec)
    (l : Loc) (dd : kd.apps.DaemonSet) (cref : Loc) (ref : kd.meta.OwnerReference)
    (Ψ : Except ApiErr (Bool × Obj) → IProp GF) (Ψ' : kd.core.Pod → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.controller ∗ podNameValidatorOk ∗
      ⌜ctx ≠ interface.nil⌝ ∗ clientIs r.KubeClient' γ cfg ∗ recorderOk r.Recorder' ∗
      tmplAt tp dq t ∗ dsAt l DFrac.discard dd ∗ refAt cref ref ∗
      (∀ pfx, ⌜prefixOk dd.ObjectMeta'.Name' pfx⌝ -∗
        createAU γ cfg ns (podFromTemplate t pfx (some ref)) Ψ) ∗
      onWriteOk r.OnWrite' cref Ψ Ψ' }}
    (App (App (App (App (App (App (Val #(methods RealPodControl.ty go!"CreatePodsWithGenerateName" #r))
      (Val #ctx)) (Val #ns)) (Val #tp))
      (Val #(interface.mkOk (go.GoType.PointerType k8s_io.api.apps.v1.DaemonSet.ty) #l :
        k8s_io.apimachinery.pkg.runtime.Object))) (Val #cref)) (Val #go!""))
  {{ (err : GoInterface), RET #err; tmplAt tp dq t ∗
      podCreateRet cfg.AmbiguousWrites' Ψ Ψ'
        (iprop(∃ pfx, ⌜¬ ctlRefValid ref ∨ (t.ObjectMeta'.Labels'.getD ∅) = ∅⌝ ∗
          createAU γ cfg ns (podFromTemplate t pfx (some ref)) Ψ))
        err }}

end spec

end dsctl
end EtcdGrove
end Perennial
