/-
`s.remove(t, ns, name, opts, grace, admin)`, logically atomic: `DeleteOut` at its linearization point; it returns `deleteRet`.
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

abbrev Server.remove.spec : Prop :=
  ∀ [ApiDeps] (s : Loc) (γ : ApiNames) (cfg : apimodel.Config) (r : Res) (t : Loc) (ns name : GoString)
    (opts : k8s_io.apimachinery.pkg.apis.«meta».v1.DeleteOptions) (dq : DFrac)
    (dop : kd.meta.DeleteOptions) (grace : GoFunc) (admin : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel ∗ isServer s γ cfg ∗ tableOf s r t ∗ graceOk r grace ∗
      kd.meta.DeleteOptions.own opts dq dop }}
  <<{ ∀∀ σ, apiState γ σ }>>
    (App (App (App (App (App (App (Val (s @!! go.GoType.PointerType apimodel.Server.ty @!! go!"remove")) (Val #t)) (Val #ns)) (Val #name)) (Val #opts)) (Val #grace)) (Val #admin)) @@ ∅
  <<{ ∃∃ σ' oc, apiState γ σ' ∗ ⌜DeleteOut cfg.FailWrites' admin r ns name dop σ oc σ'⌝ }>>
  {{ (err : GoInterface), RET #err; kd.meta.DeleteOptions.own opts dq dop ∗
      deleteRet cfg.AmbiguousWrites' admin oc err }}

end spec

end apimodel
end EtcdGrove
end Perennial
