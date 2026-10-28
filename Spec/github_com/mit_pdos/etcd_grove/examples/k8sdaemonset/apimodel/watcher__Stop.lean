/-
`w.Stop()`: stops the watch (its goroutine closes the result channel).
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

abbrev watcher.Stop.spec : Prop :=
  ∀ [ApiDeps] (w : Loc) (γ : ApiNames) (γw : WatchNames) (r : Res) (ns : GoString) (bm : Bool) (inits : List Obj),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗
      watchAt (interface.mkOk (go.GoType.PointerType apimodel.watcher.ty) #w) γ γw r ns bm inits }}
    (App (Val (w @!! go.GoType.PointerType apimodel.watcher.ty @!! go!"Stop")) (Val #()))
  {{ RET #(); True }}

end spec

end apimodel
end EtcdGrove
end Perennial
