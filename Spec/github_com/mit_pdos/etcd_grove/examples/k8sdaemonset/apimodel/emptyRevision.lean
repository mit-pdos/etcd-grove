/-
`emptyRevision()`: a new zero object of the resource.
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

abbrev emptyRevision.spec : Prop :=
  ∀ [ApiDeps],
  {{ (True : IProp GF) }}
    (App (Val (@! apimodel.emptyRevision)) (Val #()))
  {{ (x : GoInterface), RET #x; objAt x (DFrac.own 1) (zeroObj .revisions) }}

end spec

end apimodel
end EtcdGrove
end Perennial
