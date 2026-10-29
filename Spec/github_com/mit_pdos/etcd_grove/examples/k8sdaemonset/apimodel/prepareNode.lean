/-
`prepareNode(o)`: the create strategy of the resource: nothing.
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

abbrev prepareNode.spec : Prop :=
  ∀ [ApiDeps] (x : GoInterface) (o : Obj),
  {{ (objAt x (DFrac.own 1) o : IProp GF) ∗ ⌜o.res = .nodes⌝ }}
    (App (Val (@! apimodel.prepareNode)) (Val #x))
  {{ RET #(); objAt x (DFrac.own 1) (prepareD o) }}

end spec

end apimodel
end EtcdGrove
end Perennial
