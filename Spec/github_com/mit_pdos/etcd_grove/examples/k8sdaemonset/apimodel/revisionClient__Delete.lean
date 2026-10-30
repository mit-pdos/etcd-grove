/-
`c.Delete(ctx, name, opts)`, logically atomic: the server's `remove` of the resource.
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

abbrev revisionClient.Delete.spec : Prop :=
  ∀ [ApiDeps] (c : Loc) (γ : ApiNames) (cfg : apimodel.Config) (ns : GoString) (admin : Bool) (ctx : GoInterface)
    (name : GoString) (opts : k8s_io.apimachinery.pkg.apis.«meta».v1.DeleteOptions) (dq : DFrac)
    (dop : kd.meta.DeleteOptions),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel ∗ crClientAt c γ cfg ns admin ∗ kd.meta.DeleteOptions.own opts dq dop }}
  <<{ ∀∀ σ, apiState γ σ }>>
    (App (App (App (Val (c @!! go.GoType.PointerType apimodel.revisionClient.ty @!! go!"Delete")) (Val #ctx)) (Val #name)) (Val #opts)) @@ ∅
  <<{ ∃∃ σ' oc, apiState γ σ' ∗ ⌜DeleteOut cfg.FailWrites' admin .revisions ns name dop σ oc σ'⌝ }>>
  {{ (err : GoInterface), RET #err; kd.meta.DeleteOptions.own opts dq dop ∗
      deleteRet cfg.AmbiguousWrites' admin oc err }}

end spec

end apimodel
end EtcdGrove
end Perennial
