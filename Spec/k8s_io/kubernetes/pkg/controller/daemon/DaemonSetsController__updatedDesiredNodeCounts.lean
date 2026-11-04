/-
`(*DaemonSetsController).updatedDesiredNodeCounts(ctx, ds, nodeList, nodeToDaemonPods)`
(`update.go:590`): the number of nodes that should run the pod, an empty entry in the map for each
of them without one, and the surge and unavailability allowances (`util.SurgeCount`,
`util.UnavailableCount`). Lean-first; Stage 3, track B. The map only gains empty entries; the
counts are any integers.
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

/-- **`dsc.updatedDesiredNodeCounts(ctx, ds, nl, m)`**: see the file header. -/
abbrev DaemonSetsController.updatedDesiredNodeCounts.spec : Prop :=
∀ (dsc : Loc) (c : DscComp)
    (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config)
    (γa : ApiNames) (F : DscFams GF) (γ : S1Names) (ctx : GoInterface) (ds : Loc) (o : Owner)
    (d : kd.apps.DaemonSet) (nl : GoSlice) (ns : List kd.core.Node) (m : GoMap)
    (Mp : GMap GoString (List kd.core.Pod)),
  {{ dscEnv dsc c cfg γa F γ ∗ threadTok ∗ ⌜ctx ≠ interface.nil⌝ ∗ dsArg γa ds o d ∗ nodesAt nl ns ∗ podMapAt m Mp }}
    (App (App (App (App (Val (dsc @!! go.GoType.PointerType DaemonSetsController.ty @!! go!"updatedDesiredNodeCounts")) (Val #ctx)) (Val #ds)) (Val #nl)) (Val #m))
  {{ (s u n : w64) (err : GoInterface), RET (PairV (PairV (PairV #s #u) #n) #err);
      threadTok ∗ fmt.argOk err ∗ ∃ Mp', podMapAt m Mp' ∗
        ⌜∀ x, Mp' !! x = Mp !! x ∨ (Mp !! x = none ∧ Mp' !! x = some [])⌝ }}

end spec

end dsctl
end EtcdGrove
end Perennial
