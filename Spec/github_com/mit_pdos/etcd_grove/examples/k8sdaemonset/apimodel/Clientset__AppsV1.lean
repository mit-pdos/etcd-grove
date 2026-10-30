/-
`c.AppsV1()`.
Lean-first (no Rocq counterpart); phase 3 of `notes/k8s-daemonset-plan.md` (the model API server's
specs, D50's internal layer).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apimodel

open Iris Iris.BI
open github_com.mit_pdos.etcd_grove.examples.k8sdaemonset

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : apimodel.Assumptions]

abbrev Clientset.AppsV1.spec : Prop :=
  ∀ [ApiDeps] (c : Loc) (γ : ApiNames) (cfg : apimodel.Config) (admin : Bool),
  {{ (clientsetAt c γ cfg admin : IProp GF) }}
    (App (Val (c @!! go.GoType.PointerType apimodel.Clientset.ty @!! go!"AppsV1")) (Val #()))
  {{ (x : GoInterface), RET #x; isAppsV1 x γ cfg admin }}

end spec

end apimodel
end EtcdGrove
end Perennial
