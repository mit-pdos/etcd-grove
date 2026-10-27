/-
`s.list(t, ns, opts, admin)`, logically atomic (a read): the namespace's objects at the current version (`listRet`).
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

abbrev Server.list.spec : Prop :=
  ∀ (s : Loc) (γ : ApiNames) (cfg : apimodel.Config) (r : Res) (t : Loc) (ns : GoString)
    (opts : k8s_io.apimachinery.pkg.apis.«meta».v1.ListOptions) (dq : DFrac) (lo : kd.meta.ListOptions)
    (admin : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel ∗ isServer s γ cfg ∗ tableOf s r t ∗ kd.meta.ListOptions.own opts dq lo }}
  <<{ ∀∀ σ, apiState γ σ }>>
    (App (App (App (App (Val (s @!! go.GoType.PointerType apimodel.Server.ty @!! go!"list")) (Val #t)) (Val #ns)) (Val #opts)) (Val #admin)) @@ ∅
  <<{ apiState γ σ }>>
  {{ (sl : GoSlice) (rv : GoString) (err : GoInterface), RET (PairV (PairV #sl #rv) #err);
      kd.meta.ListOptions.own opts dq lo ∗ listRet γ cfg.FailReads' admin r ns lo σ sl rv err }}

end spec

end apimodel
end EtcdGrove
end Perennial
