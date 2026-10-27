/-
`w.run()`: the watch's goroutine. It sends the initial objects, then each change of the table's
log in the namespace (and, if allowed, bookmarks), every event satisfying `evOk` (its cursor's
step, `evStep`), until the watch is stopped, ended or expired, and closes the result channel.
Its precondition is what `watch` hands it (`runPre`).
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

abbrev watcher.run.spec : Prop :=
  ∀ [ApiDeps] (w : Loc) (γ : ApiNames) (γw : WatchNames) (cfg : apimodel.Config) (r : Res)
    (ns : GoString) (admin bm : Bool) (inits : List Obj),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel ∗
      runPre w γ γw cfg r ns admin bm inits }}
    (App (Val (w @!! go.GoType.PointerType apimodel.watcher.ty @!! go!"run")) (Val #()))
  {{ RET #(); True }}

end spec

end apimodel
end EtcdGrove
end Perennial
