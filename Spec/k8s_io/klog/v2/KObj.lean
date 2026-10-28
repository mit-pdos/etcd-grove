/-
`klog.KObj(obj)` (`k8s.io/klog/v2/k8s_references.go:78`, names-only): an `ObjectRef` of the
object's name and namespace (the zero one for a `nil` object). **A named hypothesis, boundary
pending approval** (the DaemonSet controller's log arguments; phase 5 of
`notes/k8s-daemonset-plan.md`): `?` in `etc/link-lean-first-k8sdaemon.txt`. Stated for an object of
the model's API types (`apimodel.objAt`): it reads the object's `GetName()` and `GetNamespace()`
(so the caller must own it, at any fraction, given back), and returns some `ObjectRef`.
-/
module

public import Proof.k8s_io.klog.v2.Init
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.klog.v2.Assumptions]

/-- `klog.KObj(x)` of an API object: some `ObjectRef`, the object back. -/
abbrev klog.KObj.spec : Prop :=
  ∀ (x : GoInterface) (dq : DFrac) (o : apimodel.Obj),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.klog.v2 ∗ apimodel.objAt x dq o }}
    (App (Val (@! k8s_io.klog.v2.KObj)) (Val #x))
  {{ (r : k8s_io.klog.v2.ObjectRef), RET #r; apimodel.objAt x dq o }}

end spec

end EtcdGrove
end Perennial
