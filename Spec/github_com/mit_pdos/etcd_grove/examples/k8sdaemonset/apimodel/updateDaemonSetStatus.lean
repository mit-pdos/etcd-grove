/-
`updateDaemonSetStatus(old, req)`: the status strategy (`dsStatusMut`): nil, or the stored DaemonSet with the request's status.
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

abbrev updateDaemonSetStatus.spec : Prop :=
  ∀ (x y : GoInterface) (st req : Obj),
  {{ (objAt x (DFrac.own 1) st : IProp GF) ∗ objAt y (DFrac.own 1) req ∗
      ⌜st.res = .daemonSets ∧ req.res = .daemonSets⌝ }}
    (App (App (Val (@! apimodel.updateDaemonSetStatus)) (Val #x)) (Val #y))
  {{ (z : GoInterface), RET #z; (⌜z = interface.nil ∧ dsStatusMut st req none⌝) ∨
      (∃ o, ⌜dsStatusMut st req (some o) ∧ o.res = .daemonSets⌝ ∗ objAt z (DFrac.own 1) o) }}

end spec

end apimodel
end EtcdGrove
end Perennial
