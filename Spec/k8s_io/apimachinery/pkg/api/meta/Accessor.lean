/-
`meta.Accessor(obj)` (`k8s.io/apimachinery/pkg/api/meta/meta.go:96`, names-only): the object's
metadata accessor. **A named hypothesis, boundary pending approval** (the pod control's create and
`GetPodFromTemplate` call it on the controller object; phase 5 of `notes/k8s-daemonset-plan.md`):
`?` in `etc/link-lean-first-k8sdaemon.txt`.

What the code does, for a pointer to one of the model's API types (`*v1.Pod`, `*v1.Node`,
`*apps.DaemonSet`, `*apps.ControllerRevision`): the type switch's first case (`metav1.Object`,
which the type implements through its embedded `ObjectMeta`) returns the object itself, as a
`metav1.Object`, and `nil`. It reads nothing.
-/
module

public import Proof.k8s_io.apimachinery.pkg.api.meta.Init
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apimeta

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.api.«meta».Assumptions]

/-- The pointer types of the model's API objects. -/
def apiPtrTy [GoGlobalContext] : apimodel.Res → go.GoType
  | .pods => go.GoType.PointerType k8s_io.api.core.v1.Pod.ty
  | .nodes => go.GoType.PointerType k8s_io.api.core.v1.Node.ty
  | .daemonSets => go.GoType.PointerType k8s_io.api.apps.v1.DaemonSet.ty
  | .revisions => go.GoType.PointerType k8s_io.api.apps.v1.ControllerRevision.ty

/-- **`meta.Accessor(x)`** of a pointer `l` to an API object: `x` itself and `nil`. -/
abbrev Accessor.spec : Prop :=
  ∀ (r : apimodel.Res) (l : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.api.«meta» }}
    (App (Val (@! k8s_io.apimachinery.pkg.api.«meta».Accessor))
      (Val #(interface.mkOk (apiPtrTy r) #l : GoInterface)))
  {{ RET (PairV #(interface.mkOk (apiPtrTy r) #l : k8s_io.apimachinery.pkg.apis.«meta».v1.Object)
      #(interface.nil : GoInterface)); True }}

end spec

end apimeta
end EtcdGrove
end Perennial
