/-
`GetPodFromTemplate(template, parentObject, controllerRef)` (`controller_utils.go:567`): the pod a
controller creates from a template. Lean-first; phase 5 of `notes/k8s-daemonset-plan.md`.

What the code does: copies the template's labels and annotations into fresh maps
(`getPodsLabelSet`, `getPodsAnnotationSet`) and its finalizers into a fresh slice; takes the
parent's name through `meta.Accessor` (an error only for an object without metadata, not the
`*DaemonSet` the DaemonSet controller passes); the generated name `getPodsPrefix(name)`
(`name-`, or `name` if the pod name validator rejects that); the controller reference appended
(a copy of `*controllerRef`, sharing its `*bool` fields); the template's spec deep-copied. The
pod is returned read-only (`DFrac.discard`): it shares the reference's `*bool`s, which are
read-only for good (`refAt`), and nothing writes it afterwards in the DaemonSet controller (its
`CreatePodsWithGenerateName` sets the generated name only for a non-empty argument, never).
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

/-- **`GetPodFromTemplate(tp, ds, cref)`** for a `*DaemonSet` parent: the pod
`podFromTemplate t pfx (some r)` (`pfx` one of `getPodsPrefix`'s results for the parent's name),
read-only, and `nil`; the template and the parent back. -/
abbrev GetPodFromTemplate.spec : Prop :=
  ∀ (tp : Loc) (dq : DFrac) (t : kd.core.PodTemplateSpec) (l : Loc) (dqd : DFrac)
    (dd : kd.apps.DaemonSet) (cref : Loc) (r : kd.meta.OwnerReference),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.controller ∗ podNameValidatorOk ∗
      tmplAt tp dq t ∗ dsAt l dqd dd ∗ refAt cref r }}
    (App (App (App (Val (@! k8s_io.kubernetes.pkg.controller.GetPodFromTemplate)) (Val #tp))
      (Val #(interface.mkOk (go.GoType.PointerType k8s_io.api.apps.v1.DaemonSet.ty) #l :
        k8s_io.apimachinery.pkg.runtime.Object))) (Val #cref))
  {{ (p : Loc) (err : GoInterface), RET (PairV #p #err); ⌜err = interface.nil⌝ ∗
      ∃ pfx, ⌜prefixOk dd.ObjectMeta'.Name' pfx⌝ ∗
        podAt p DFrac.discard (podFromTemplate t pfx (some r)) ∗ tmplAt tp dq t ∗ dsAt l dqd dd }}

end spec

end dsctl
end EtcdGrove
end Perennial
