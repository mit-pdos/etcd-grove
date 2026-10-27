/-
`s.update(t, ns, in, mutate, admin)`, logically atomic: `UpdateOut` at its linearization point; it returns `writeRetI`.
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

abbrev Server.update.spec : Prop :=
  ∀ [ApiDeps] (s : Loc) (γ : ApiNames) (cfg : apimodel.Config) (r : Res) (t : Loc) (ns : GoString)
    (inp : GoInterface) (dq : DFrac) (o : Obj) (mutF : GoFunc)
    (mutR : Obj → Obj → Option Obj → Prop) (admin : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel ∗ isServer s γ cfg ∗ tableOf s r t ∗ mutateOk r mutR mutF ∗
      objAt inp dq o ∗ ⌜o.res = r⌝ }}
  <<{ ∀∀ σ, apiState γ σ }>>
    (App (App (App (App (App (Val (s @!! go.GoType.PointerType apimodel.Server.ty @!! go!"update")) (Val #t)) (Val #ns)) (Val #inp)) (Val #mutF)) (Val #admin)) @@ ∅
  <<{ ∃∃ σ' oc, apiState γ σ' ∗ ⌜UpdateOut cfg.FailWrites' admin r ns o mutR σ oc σ'⌝ }>>
  {{ (x err : GoInterface), RET (PairV #x #err); objAt inp dq o ∗
      writeRetI cfg.AmbiguousWrites' admin oc x err }}

end spec

end apimodel
end EtcdGrove
end Perennial
