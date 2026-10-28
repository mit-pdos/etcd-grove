/-
`isUnsupportedTableListObject(rawObject)` (`reflector.go:1326`): whether the list is an unstructured
`Table` list of a well-known unsupported GVK. Lean-first; phase 4 of `notes/k8s-daemonset-plan.md`,
fifth round. Stated for a typed list of the model (`*v1.PodList`, ...): not an `*UnstructuredList`,
so `false`.
-/
module

public import Proof.k8s_io.client_go.tools.cache.RefWatchDefs

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

/-- **`isUnsupportedTableListObject(list)`** of a typed list: `false`. -/
abbrev isUnsupportedTableListObject.spec : Prop :=
  ∀ (res : Res) (q : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache }}
    (App (Val (@! k8s_io.client_go.tools.cache.isUnsupportedTableListObject))
      (Val #(interface.mkOk (go.GoType.PointerType (resListTy res)) #q)))
  {{ (gvk : k8s_io.apimachinery.pkg.runtime.schema.GroupVersionKind), RET (PairV #false #gvk); True }}

end spec

end cache
end EtcdGrove
end Perennial
