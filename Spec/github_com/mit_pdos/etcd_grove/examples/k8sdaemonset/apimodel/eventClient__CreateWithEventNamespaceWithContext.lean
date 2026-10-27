/-
`c.CreateWithEventNamespaceWithContext(...)`: the event, dropped.
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

abbrev eventClient.CreateWithEventNamespaceWithContext.spec : Prop :=
  ∀ (c : Loc) (e : Loc) (ctx : GoInterface),
  {{ (True : IProp GF) }}
    (App (App (Val (c @!! go.GoType.PointerType apimodel.eventClient.ty @!! go!"CreateWithEventNamespaceWithContext")) (Val #ctx)) (Val #e))
  {{ RET (PairV #e #interface.nil); True }}

end spec

end apimodel
end EtcdGrove
end Perennial
