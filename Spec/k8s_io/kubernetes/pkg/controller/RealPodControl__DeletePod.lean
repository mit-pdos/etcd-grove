/-
`r.DeletePod(ctx, namespace, podID, object)` (`controller_utils.go:619`): the pod control's
delete. Lean-first; phase 5 of `notes/k8s-daemonset-plan.md`. Its body is gap D2's
(`RealPodControl__DeletePod_body.lean`, a named hypothesis).

What the code does: `meta.Accessor(object)` (for the `*DaemonSet` the DaemonSet controller passes:
the object, no error), a log line, then the clientset's `CoreV1().Pods(namespace).Delete(ctx,
podID, {})`; on its error it returns it as is when `apierrors.IsNotFound` says so, otherwise
records a warning event and returns `fmt.Errorf("unable to delete pods: %v", err)`; on success it
records an event and returns `nil`. Over the model API server the delete's linearization point is
the caller's (`deleteAU`, `DeleteOut`); the call returns `nil`, or an error: for any outcome of the
model (`deleteRet`: no effect, or with `AmbiguousWrites` a delete that took effect).
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

/-- **`r.DeletePod(ctx, ns, name, ds)`**: the delete's outcome `oc` per the model, `Ψ oc`, and
`nil` only for an outcome the model returns `nil` for (`deleteRet`: `ok _`). -/
abbrev RealPodControl.DeletePod.spec : Prop :=
  ∀ [ApiDeps] (r : RealPodControl) (γ : ApiNames)
    (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config)
    (ctx : GoInterface) (ns name : GoString) (l : Loc) (dd : kd.apps.DaemonSet)
    (Ψ : Except ApiErr Bool → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.controller ∗ ⌜ctx ≠ interface.nil⌝ ∗
      clientIs r.KubeClient' γ cfg ∗ recorderOk r.Recorder' ∗ dsAt l DFrac.discard dd ∗
      deleteAU γ cfg ns name Ψ }}
    (App (App (App (App (Val #(methods RealPodControl.ty go!"DeletePod" #r)) (Val #ctx))
      (Val #ns)) (Val #name))
      (Val #(interface.mkOk (go.GoType.PointerType k8s_io.api.apps.v1.DaemonSet.ty) #l :
        k8s_io.apimachinery.pkg.runtime.Object)))
  {{ (err : GoInterface), RET #err; dsAt l DFrac.discard dd ∗
      ∃ oc, Ψ oc ∗ ⌜err = interface.nil → ∃ w, oc = .ok w⌝ }}

end spec

end dsctl
end EtcdGrove
end Perennial
