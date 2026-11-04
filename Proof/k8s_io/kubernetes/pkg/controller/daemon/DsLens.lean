/-
**Lenses into a DaemonSet's deep ownership** for the sync path's glue proofs (fields the
controller reads off the DaemonSet it got from its lister, read-only for good). Lean-first.
-/
module

public import Proof.k8s_io.kubernetes.pkg.controller.daemon.SyncDefs

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI Iris.ProofMode apimodel

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [apps_sem : k8s_io.api.apps.v1.Assumptions]

/-- **The DaemonSet's update strategy type** (`ds.Spec.UpdateStrategy.Type`), read-only. -/
theorem dsAt_updType (ds : Loc) (d : kd.apps.DaemonSet) :
    dsAt (GF := GF) ds DFrac.discard d ⊢
      ds.[k8s_io.api.apps.v1.DaemonSet, go!"Spec"].[k8s_io.api.apps.v1.DaemonSetSpec,
        go!"UpdateStrategy"].[k8s_io.api.apps.v1.DaemonSetUpdateStrategy, go!"Type"] ↦□
        d.Spec'.UpdateStrategy'.Type' := by
  unfold dsAt
  iintro ⟨%v, Hl, Hd⟩
  iStructNamed Hl
  iStructNamedPrefix Spec "S"
  iStructNamedPrefix SUpdateStrategy "U"
  iunfold kd.apps.DaemonSet.own at Hd
  icases Hd with ⟨-, -, DSpec, -⟩
  iunfold kd.apps.DaemonSetSpec.own at DSpec
  icases DSpec with ⟨-, -, DU, -, -⟩
  iunfold kd.apps.DaemonSetUpdateStrategy.own at DU
  icases DU with ⟨%hty, -⟩
  rw [← hty]
  iexact UType'

end lemmas

end dsctl
end EtcdGrove
end Perennial
