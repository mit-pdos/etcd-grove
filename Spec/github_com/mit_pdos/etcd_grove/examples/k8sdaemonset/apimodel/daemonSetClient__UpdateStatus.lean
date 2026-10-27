/-
`c.UpdateStatus(ctx, ds, opts)`, logically atomic: the server's `update` with the status strategy (`dsStatusMut`).
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

abbrev daemonSetClient.UpdateStatus.spec : Prop :=
  ∀ [ApiDeps] (c : Loc) (γ : ApiNames) (cfg : apimodel.Config) (ns : GoString) (admin : Bool) (ctx : GoInterface)
    (p : Loc) (dq : DFrac) (d : kd.apps.DaemonSet)
    (opts : k8s_io.apimachinery.pkg.apis.«meta».v1.UpdateOptions),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel ∗ dsClientAt c γ cfg ns admin ∗ dsAt p dq d }}
  <<{ ∀∀ σ, apiState γ σ }>>
    (App (App (App (Val (c @!! go.GoType.PointerType apimodel.daemonSetClient.ty @!! go!"UpdateStatus")) (Val #ctx)) (Val #p)) (Val #opts)) @@ ∅
  <<{ ∃∃ σ' oc, apiState γ σ' ∗ ⌜UpdateOut cfg.FailWrites' admin .daemonSets ns (.ds d) dsStatusMut σ oc σ'⌝ }>>
  {{ (q : Loc) (err : GoInterface), RET (PairV #q #err); dsAt p dq d ∗
      writeRet cfg.AmbiguousWrites' admin oc q err }}

end spec

end apimodel
end EtcdGrove
end Perennial
