/-
`(*group).V1()` (`informers/core`): `v1.New(g.factory, g.namespace, g.tweakListOptions)`.
Lean-first; the DaemonSet run's track A.
-/
module

public import Proof.k8s_io.client_go.informers.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace informerscore

open Iris Iris.BI apimodel cache informer informers

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.informers.core.Assumptions]
variable [cache_sem : k8s_io.client_go.tools.cache.Assumptions]
variable [ctx_sem : _root_.Perennial.context.Assumptions]

/-- **`g.V1()`**: a `*v1.version` holding the factory. -/
abbrev group.V1.spec : Prop :=
  ∀ (g f : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.informers.core ∗
      facRefAt k8s_io.client_go.informers.core.group g f }}
    (App (Val (g @!! go.GoType.PointerType k8s_io.client_go.informers.core.group.ty @!! go!"V1"))
      (Val #()))
  {{ (v : Loc), RET #(interface.mkOk
        (go.GoType.PointerType k8s_io.client_go.informers.core.v1.version.ty) #v);
      facRefAt k8s_io.client_go.informers.core.v1.version v f }}

end spec

end informerscore
end EtcdGrove
end Perennial
