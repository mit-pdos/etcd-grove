/-
`noGrace(o, opts)`: 0 (the grace period of resources deleted at once).
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

abbrev noGrace.spec : Prop :=
  ∀ [ApiDeps] (o : GoInterface) (opts : k8s_io.apimachinery.pkg.apis.«meta».v1.DeleteOptions),
  {{ (True : IProp GF) }}
    (App (App (Val (@! apimodel.noGrace)) (Val #o)) (Val #opts))
  {{ RET #(W64 0); True }}

end spec

end apimodel
end EtcdGrove
end Perennial
