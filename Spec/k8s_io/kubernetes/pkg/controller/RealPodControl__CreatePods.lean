/-
`r.CreatePods(ctx, namespace, template, controllerObject, controllerRef)`
(`controller_utils.go:540`): `CreatePodsWithGenerateName(..., "")`. Lean-first; phase 5 of
`notes/k8s-daemonset-plan.md`. The spec is `CreatePodsWithGenerateName`'s.
-/
module

public import Spec.k8s_io.kubernetes.pkg.controller.RealPodControl__CreatePodsWithGenerateName

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

/-- **`r.CreatePods(ctx, ns, tp, ds, cref)`**: as `CreatePodsWithGenerateName`'s with `""`. -/
abbrev RealPodControl.CreatePods.spec : Prop :=
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
    (App (App (App (App (App (Val #(methods RealPodControl.ty go!"CreatePods" #r))
      (Val #ctx)) (Val #ns)) (Val #tp))
      (Val #(interface.mkOk (go.GoType.PointerType k8s_io.api.apps.v1.DaemonSet.ty) #l :
        k8s_io.apimachinery.pkg.runtime.Object))) (Val #cref))
  {{ (err : GoInterface), RET #err; tmplAt tp dq t ∗
      podCreateRet cfg.AmbiguousWrites' Ψ Ψ'
        (iprop(∃ pfx, ⌜¬ ctlRefValid ref ∨ (t.ObjectMeta'.Labels'.getD ∅) = ∅⌝ ∗
          createAU γ cfg ns (podFromTemplate t pfx (some ref)) Ψ))
        err }}

end spec

end dsctl
end EtcdGrove
end Perennial
