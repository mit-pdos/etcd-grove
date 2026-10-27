/-
`daemonSetStatusEqual(a, b)`: true only if the statuses agree but for the conditions' transition times, which compare by `time.Time.Equal` (some `bool` in Perennial's spec).
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

abbrev daemonSetStatusEqual.spec : Prop :=
  ∀ (a b : Loc) (va vb : k8s_io.api.apps.v1.DaemonSetStatus) (da db : kd.apps.DaemonSetStatus),
  {{ (a ↦ va : IProp GF) ∗ kd.apps.DaemonSetStatus.own va (DFrac.own 1) da ∗
      b ↦ vb ∗ kd.apps.DaemonSetStatus.own vb (DFrac.own 1) db }}
    (App (App (Val (@! apimodel.daemonSetStatusEqual)) (Val #a)) (Val #b))
  {{ (eq : Bool), RET #eq; a ↦ va ∗ kd.apps.DaemonSetStatus.own va (DFrac.own 1) da ∗
      b ↦ vb ∗ kd.apps.DaemonSetStatus.own vb (DFrac.own 1) db ∗
      ⌜eq = true → dsStatusEqNoTimes da db⌝ }}

end spec

end apimodel
end EtcdGrove
end Perennial
