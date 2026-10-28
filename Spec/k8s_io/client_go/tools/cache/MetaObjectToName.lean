/-
`MetaObjectToName(obj)` (`store.go:176`): the object's namespace and name, as an `ObjectName`
(the namespace `""` when it is empty: the same value). Stated for a `*DaemonSet` (the DaemonSet
controller's key function's argument), owned at any fraction, given back. Lean-first.
-/
module

public import Proof.k8s_io.client_go.tools.cache.Keys
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI k8s_io.client_go.tools.cache apimodel

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- **`MetaObjectToName(ds)`** of a `*DaemonSet`: `ObjectName{ns, name}` of its metadata. -/
abbrev MetaObjectToName.spec : Prop :=
  ∀ (l : Loc) (dq : DFrac) (dd : kd.apps.DaemonSet),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ dsAt l dq dd }}
    (App (Val (@! k8s_io.client_go.tools.cache.MetaObjectToName))
      (Val #(interface.mkOk (go.GoType.PointerType k8s_io.api.apps.v1.DaemonSet.ty) #l :
        k8s_io.apimachinery.pkg.apis.«meta».v1.Object)))
  {{ RET #(ObjectName.mk dd.ObjectMeta'.Namespace' dd.ObjectMeta'.Name'); dsAt l dq dd }}

end spec

end cache
end EtcdGrove
end Perennial
