/-
`(*nodeInformer).Informer()`: `f.TypedInformer()`, the factory's shared informer of `.nodes` (made on
the first call, `defaultInformer`) in a typed wrapper: `isInformer` of it, its names the
factory's for good (`facInf`), its store indexed by namespace. Lean-first; the DaemonSet run's
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

/-- **`i.Informer()`**: the factory's informer of `.nodes`. -/
abbrev nodeInformer.Informer.spec : Prop :=
  ∀ (l f : Loc) (γF : FacNames) (γa : ApiNames) (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config) (Fams : Res → Nat → Fn GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.informers.core.v1 ∗ typedInfAt .nodes l f ∗ isFactory f γF γa cfg Fams }}
    (App (Val (l @!! go.GoType.PointerType k8s_io.client_go.informers.core.v1.nodeInformer.ty @!! go!"Informer")) (Val #()))
  {{ (x : GoInterface), RET #x; facInfOut γF γa .nodes Fams x }}

end spec

end coreinformers
end EtcdGrove
end Perennial
