/-
`storeDaemonSetStatus(ctx, dsClient, ds, desired, current, misscheduled, ready, updated,
available, unavailable, updateObservedGen)` (`daemon_controller.go:1155`): nothing if the cached
status already has the counters (`nil`, `nil`); otherwise `UpdateStatus` of a copy with them, with up
to `StatusUpdateRetries` retries over a fresh `Get`. Lean-first; Stage 3, track B.

Each `UpdateStatus` and `Get` is the model's, linearizing inside `apiInv` and `s1Inv` (a status
write keeps `s1Ok`: `dsStatusMut` changes the status only, and the written status keeps the
collision count, `nil`). On success, the written DaemonSet (its UID the cached one's).
-/
module

public import Proof.k8s_io.kubernetes.pkg.controller.daemon.SyncDefs

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI apimodel consistency k8s_io.kubernetes.pkg.controller.daemon

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.kubernetes.pkg.controller.daemon.Assumptions]

/-- **`storeDaemonSetStatus(...)`**: see the file header. -/
abbrev storeDaemonSetStatus.spec : Prop :=
  ∀ [workqueue.QItem (GF := GF) GoString go.string] (c : DscComp) (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config)
    (γa : ApiNames) (γ : S1Names) (ctx : GoInterface) (dsClient : GoInterface) (ds : Loc) (o : Owner)
    (d : kd.apps.DaemonSet) (n1 n2 n3 n4 n5 n6 n7 : w64) (b : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.controller.daemon ∗ apiInv γa γ ∗ s1Inv γ c ∗
      ⌜ctx ≠ interface.nil⌝ ∗ isDSClient dsClient γa cfg d.ObjectMeta'.Namespace' false ∗ dsArg γa ds o d }}
    (App (App (App (App (App (App (App (App (App (App (App (Val (@! k8s_io.kubernetes.pkg.controller.daemon.storeDaemonSetStatus)) (Val #ctx)) (Val #dsClient)) (Val #ds)) (Val #n1)) (Val #n2)) (Val #n3)) (Val #n4)) (Val #n5)) (Val #n6)) (Val #n7)) (Val #b))
  {{ (r : Loc) (err : GoInterface), RET (PairV #r #err); fmt.argOk err ∗
      (⌜r = null⌝ ∨ ∃ d', ⌜err = interface.nil ∧ d'.ObjectMeta'.UID' = d.ObjectMeta'.UID'⌝ ∗
        dsAt r (DFrac.own 1) d') }}

end spec

end dsctl
end EtcdGrove
end Perennial
