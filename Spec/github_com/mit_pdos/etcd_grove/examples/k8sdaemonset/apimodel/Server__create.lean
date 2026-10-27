/-
`s.create(t, ns, in, prepare, admin)`, logically atomic: `CreateOut` at its linearization point (a flagged failure or a check's error with no effect, or the write); it returns `writeRetI` (the stored object, or a timeout after the write if ambiguous writes are flagged).
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

abbrev Server.create.spec : Prop :=
  ∀ [ApiDeps] (s : Loc) (γ : ApiNames) (cfg : apimodel.Config) (r : Res) (t : Loc) (ns : GoString)
    (inp : GoInterface) (dq : DFrac) (o : Obj) (prep : GoFunc) (admin : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel ∗ isServer s γ cfg ∗ tableOf s r t ∗ prepareOk r prep ∗
      objAt inp dq o ∗ ⌜o.res = r⌝ }}
  <<{ ∀∀ σ, apiState γ σ }>>
    (App (App (App (App (App (Val (s @!! go.GoType.PointerType apimodel.Server.ty @!! go!"create")) (Val #t)) (Val #ns)) (Val #inp)) (Val #prep)) (Val #admin)) @@ ∅
  <<{ ∃∃ σ' oc, apiState γ σ' ∗ ⌜CreateOut cfg.FailWrites' admin r ns o σ oc σ'⌝ }>>
  {{ (x err : GoInterface), RET (PairV #x #err); objAt inp dq o ∗
      writeRetI cfg.AmbiguousWrites' admin oc x err }}

end spec

end apimodel
end EtcdGrove
end Perennial
