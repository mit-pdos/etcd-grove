/-
`s.get(t, ns, name, admin)`, logically atomic (a read): the stored object (`getRet`).
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

abbrev Server.get.spec : Prop :=
  ∀ [ApiDeps] (s : Loc) (γ : ApiNames) (cfg : apimodel.Config) (r : Res) (t : Loc) (ns name : GoString)
    (admin : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel ∗ isServer s γ cfg ∗ tableOf s r t }}
  <<{ ∀∀ σ, apiState γ σ }>>
    (App (App (App (App (Val (s @!! go.GoType.PointerType apimodel.Server.ty @!! go!"get")) (Val #t)) (Val #ns)) (Val #name)) (Val #admin)) @@ ∅
  <<{ apiState γ σ }>>
  {{ (x err : GoInterface), RET (PairV #x #err);
      getRet cfg.FailReads' admin (getObj r ns name σ) x err }}

end spec

end apimodel
end EtcdGrove
end Perennial
