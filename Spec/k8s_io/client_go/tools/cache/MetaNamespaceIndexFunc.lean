/-
`cache.MetaNamespaceIndexFunc(obj)` (`index.go`): `meta.Accessor(obj)`, then
`[]string{meta.GetNamespace()}`: on a model object (owned read-only), its namespace, no error
(the namespace index's relation `informers.nsIdxFn`). Lean-first; the DaemonSet run's track A.
-/
module

public import Proof.k8s_io.client_go.tools.cache.InformerApi

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI apimodel cache informer k8s_io.client_go.tools.cache

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]
variable [ctx_sem : _root_.Perennial.context.Assumptions]

/-- **`MetaNamespaceIndexFunc(x)`**: `[namespace of x]`. -/
abbrev MetaNamespaceIndexFunc.spec : Prop :=
  ∀ (x : GoInterface) (o : Obj),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ □ apimodel.objAt x DFrac.discard o }}
    (App (Val (@! MetaNamespaceIndexFunc)) (Val #x))
  {{ (sl : GoSlice) (err : GoInterface), RET (PairV #sl #err);
      ⌜err = interface.nil⌝ ∗ ∃ dq : DFrac, sl ↦*{dq} [o.meta.Namespace'] }}

end spec

end cache
end EtcdGrove
end Perennial
