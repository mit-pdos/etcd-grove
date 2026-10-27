/-
`c.List(ctx, opts)`, logically atomic (a read): the typed list of the namespace's objects at the current version.
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

abbrev daemonSetClient.List.spec : Prop :=
  ∀ [ApiDeps] (c : Loc) (γ : ApiNames) (cfg : apimodel.Config) (ns : GoString) (admin : Bool) (ctx : GoInterface)
    (opts : k8s_io.apimachinery.pkg.apis.«meta».v1.ListOptions) (dq : DFrac) (lo : kd.meta.ListOptions),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel ∗ dsClientAt c γ cfg ns admin ∗ kd.meta.ListOptions.own opts dq lo }}
  <<{ ∀∀ σ, apiState γ σ }>>
    (App (App (Val (c @!! go.GoType.PointerType apimodel.daemonSetClient.ty @!! go!"List")) (Val #ctx)) (Val #opts)) @@ ∅
  <<{ apiState γ σ }>>
  {{ (q : Loc) (err : GoInterface), RET (PairV #q #err); kd.meta.ListOptions.own opts dq lo ∗
      typedListRet γ cfg.FailReads' admin .daemonSets ns lo σ q err }}

end spec

end apimodel
end EtcdGrove
end Perennial
