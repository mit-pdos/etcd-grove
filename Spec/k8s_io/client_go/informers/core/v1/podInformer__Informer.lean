/-
`(*podInformer).Informer()`: `f.TypedInformer()`, the factory's shared informer of `.pods` (made on
the first call, `defaultInformer`) in a typed wrapper: `isInformer` of it, its names the
factory's for good (`facInf`), so the factory's not-started token of the resource (the
callers' halves, `facNotStarted`, from the factory's constructor) is the informer's
(`facNotStarted_inf`), and its store indexed by namespace. Lean-first; the DaemonSet run's
track A.
-/
module

public import Proof.k8s_io.client_go.informers.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace coreinformers

open Iris Iris.BI apimodel cache informer informers

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.informers.core.v1.Assumptions]
variable [cache_sem : k8s_io.client_go.tools.cache.Assumptions]
variable [ctx_sem : _root_.Perennial.context.Assumptions]

/-- **`i.Informer()`**: the factory's informer of `.pods`. -/
abbrev podInformer.Informer.spec : Prop :=
  ∀ (l f : Loc) (γF : FacNames) (γa : ApiNames) (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config) (Fams : Res → GoString → Fn GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.informers.core.v1 ∗ typedInfAt .pods l f ∗ isFactory f γF γa cfg Fams }}
    (App (Val (l @!! go.GoType.PointerType k8s_io.client_go.informers.core.v1.podInformer.ty @!! go!"Informer")) (Val #()))
  {{ (x : GoInterface), RET #x; facInfOut γF γa .pods Fams x }}

end spec

end coreinformers
end EtcdGrove
end Perennial
