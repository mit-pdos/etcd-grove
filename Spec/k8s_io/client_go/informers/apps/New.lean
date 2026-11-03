/-
`informers/apps.New(f, namespace, tweakListOptions)`: the group `&group{f, namespace,
tweakListOptions}`, for the factory `f`, all namespaces, no tweak. Lean-first; the DaemonSet
run's track A.
-/
module

public import Proof.k8s_io.client_go.informers.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace informersapps

open Iris Iris.BI apimodel cache informer informers

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.informers.apps.Assumptions]
variable [cache_sem : k8s_io.client_go.tools.cache.Assumptions]
variable [ctx_sem : _root_.Perennial.context.Assumptions]

/-- **`apps.New(f, "", nil)`**: a `*group` holding the factory. -/
abbrev New.spec : Prop :=
  ∀ (f : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.informers.apps }}
    (App (App (App (Val (@! k8s_io.client_go.informers.apps.New)) (Val #(facVal f)))
      (Val #(go!"" : GoString)))
      (Val #(func.nil : k8s_io.client_go.informers.internalinterfaces.TweakListOptionsFunc)))
  {{ (g : Loc), RET #(interface.mkOk
        (go.GoType.PointerType k8s_io.client_go.informers.apps.group.ty) #g);
      facRefAt k8s_io.client_go.informers.apps.group g f }}

end spec

end informersapps
end EtcdGrove
end Perennial
