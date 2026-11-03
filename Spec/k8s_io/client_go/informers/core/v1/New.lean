/-
`informers/core/v1.New(f, namespace, tweakListOptions)`: the version `&version{f, namespace,
tweakListOptions}`. Lean-first; the DaemonSet run's track A.
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

/-- **`v1.New(f, "", nil)`**: a `*version` holding the factory. -/
abbrev New.spec : Prop :=
  ∀ (f : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.informers.core.v1 }}
    (App (App (App (Val (@! k8s_io.client_go.informers.core.v1.New)) (Val #(facVal f)))
      (Val #(go!"" : GoString)))
      (Val #(func.nil : k8s_io.client_go.informers.internalinterfaces.TweakListOptionsFunc)))
  {{ (v : Loc), RET #(interface.mkOk
        (go.GoType.PointerType k8s_io.client_go.informers.core.v1.version.ty) #v);
      facRefAt k8s_io.client_go.informers.core.v1.version v f }}

end spec

end coreinformers
end EtcdGrove
end Perennial
