/-
The results of etcd's auto-periodic compactor (`server/etcdserver/api/v3compactor`, added by
etcd#22095; branch `pr-verify/etcd-22095`), restated at top level, with the trust base of each
printed in the build log (`#print axioms`).

* `New` builds, for the mode `auto-periodic`, an auto-periodic compactor over a real clock with
  the given retention, quota, revision getter, compactable and size getter (`newResult`).
* `Run` starts the sampling goroutine: every compaction it asks keeps the last `retention`
  revisions of a store at the revision the getter returned, is at a positive revision, above
  the last one that succeeded (or was already compacted); `Defs.lean`'s `apCompactOk`.
* `Pause`, `Resume`, `Stop` return; with `Pause` and `Resume` the compactor meets the server's
  contract on `s.compactor` (`compactorOk`, `InvRun.lean`): `compactorOk_autoPeriodic`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Link
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRun

@[expose] public section

-- `#print axioms` prints the axioms by their full names (shortening them is slow).
set_option pp.fullNames true

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace v3compactor

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api

section results
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Assumptions]

/-- **`New`** (`Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3compactor/New.lean`). -/
theorem compactor_new : v3compactor.New.spec (GF := GF) (hG := hG) := wp_New

/-- **`Run`** (`Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3compactor/AutoPeriodic__Run.lean`),
under the float-to-integer conversion's model assumption. -/
theorem compactor_run [f2i : Float64ToInt64] [f2i_sem : Float64ToInt64Semantics] :
    v3compactor.AutoPeriodic.Run.spec (GF := GF) (hG := hG) := AutoPeriodic.wp_Run

/-- **The auto-periodic compactor meets the server's contract on `s.compactor`**
(`compactorOk`, `InvRun.lean`: its `Pause` and `Resume` return). -/
theorem compactorOk_autoPeriodic (ac : Loc) (P : APParams) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor ∗
      isAutoPeriodic ac P ⊢
    compactorOk (GF := GF) (GoInterface.ok ⟨go.GoType.PointerType
      go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.AutoPeriodic.ty, #ac⟩) := by
  iintro ⟨#Hp, #Ha⟩
  unfold compactorOk
  iright
  iexists _
  isplitr
  · ipureintro; rfl
  isplitr
  · imodintro
    imodintro
    iintro %Φ - HΦ
    iapply (AutoPeriodic.wp_Pause (GF := GF) ac P) $$ [] HΦ
    iframe #
  · imodintro
    imodintro
    iintro %Φ - HΦ
    iapply (AutoPeriodic.wp_Resume (GF := GF) ac P) $$ [] HΦ
    iframe #

end results

#print axioms compactor_new
#print axioms compactor_run
#print axioms compactorOk_autoPeriodic

end v3compactor
end EtcdGrove
end Perennial
