/-
`(*sharedInformerFactory).Apps()`: the `apps` group of the factory (`apps.New(f, f.namespace,
f.tweakListOptions)`). Lean-first; the DaemonSet run's track A.
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

/-- **`f.Apps()`**: a `*apps.group` of the factory. -/
abbrev sharedInformerFactory.Apps.spec : Prop :=
  ∀ (f : Loc) (γF : FacNames) (γa : ApiNames) (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config) (Fams : Res → Nat → Fn GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.informers ∗ isFactory f γF γa cfg Fams }}
    (App (Val (f @!! go.GoType.PointerType k8s_io.client_go.informers.sharedInformerFactory.ty @!! go!"Apps")) (Val #()))
  {{ (g : Loc), RET #(interface.mkOk
        (go.GoType.PointerType k8s_io.client_go.informers.apps.group.ty) #g);
      facRefAt k8s_io.client_go.informers.apps.group g f }}

end spec

end informers
end EtcdGrove
end Perennial
