/-
`c.DaemonSets(ns)`: the resource's typed client.
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : apimodel.Assumptions]

abbrev appsV1.DaemonSets.spec : Prop :=
  ∀ (l : Loc) (γ : ApiNames) (cfg : apimodel.Config) (admin : Bool) (ns : GoString),
  {{ (appsV1At l γ cfg admin : IProp GF) }}
    (App (Val (l @!! go.GoType.PointerType apimodel.appsV1.ty @!! go!"DaemonSets")) (Val #ns))
  {{ (x : GoInterface), RET #x; isDSClient x γ cfg ns admin }}

end spec

end apimodel
end EtcdGrove
end Perennial
