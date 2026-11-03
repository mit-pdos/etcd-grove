/-
`(*sharedInformerFactory).InformerFor(obj, newFunc)` (`informers/factory.go`): under the
factory's lock, the informer of `obj`'s type (`reflect.TypeOf`): the existing one, or a new one
from `newFunc(f.client, f.defaultResync)`, registered. For the example object of resource `r`
(a `*DaemonSet`, ...): the factory's informer of `r` (`facInfOut`: its names `facInf γF r I`,
the same for every call). Lean-first; the DaemonSet run's track A.

Its proof needs `reflect.TypeOf` to be deterministic in the dynamic type and injective on the
four resources' pointer types (the factory's map is keyed by it): stronger than the current
boundary spec `Spec/reflect/TypeOf.lean` (a proposed axiom change, the run's report).
-/
module

public import Proof.k8s_io.client_go.informers.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace informers

open Iris Iris.BI apimodel cache informer informers

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.informers.Assumptions]
variable [cache_sem : k8s_io.client_go.tools.cache.Assumptions]
variable [ctx_sem : _root_.Perennial.context.Assumptions]

/-- **`f.InformerFor(obj, newFunc)`**: see the file header. -/
abbrev sharedInformerFactory.InformerFor.spec : Prop :=
  ∀ (f : Loc) (γF : FacNames) (γa : ApiNames) (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config) (Fams : Res → Nat → Fn GF) (r : Res) (p : Loc) (nf : GoFunc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.informers ∗ isFactory f γF γa cfg Fams ∗ newInfFnOk nf γa cfg r (Fams r) }}
    (App (App (Val (f @!! go.GoType.PointerType k8s_io.client_go.informers.sharedInformerFactory.ty @!! go!"InformerFor"))
      (Val #(interface.mkOk (go.GoType.PointerType (resObjTy r)) #p :
        k8s_io.apimachinery.pkg.runtime.Object))) (Val #nf))
  {{ (x : GoInterface), RET #x; facInfOut γF γa r Fams x }}

end spec

end informers
end EtcdGrove
end Perennial
