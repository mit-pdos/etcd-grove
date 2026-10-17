/-
The results of etcd's periodic and revision compactors (`server/etcdserver/api/v3compactor`,
with etcd#18472's `interval`; branch `pr-verify/etcd-18472`), restated at top level, with the
trust base of each printed in the build log (`#print axioms`).

* `New` builds, for `periodic`, a periodic compactor with the given period and `interval`, and,
  for `revision`, a revision compactor with the given retention and the wait `rvInterval
  interval` (`interval`, or 5 minutes for `0`), both over a real clock (`newResult`).
* `Revision.Run` starts the compaction goroutine: it waits only `rc.interval` between rounds (its
  clock is taken at `D := (· = interval)`), and every compaction it asks keeps the last
  `retention` revisions of a store at the revision the getter returned, is at a positive revision,
  not the last one that succeeded (`rvCompactOk`).
* `Periodic.Run` starts the sampling goroutine: it waits only `getRetryInterval()` between
  samples, whatever `interval` is, and every compaction is at a revision the getter returned, not
  the last one that succeeded (`pdCompactOk`).
* `getCompactInterval` returns the configured `interval` when it is non-zero, and what it
  returned before etcd#18472 when it is `0` (`getCompactInterval_compat`).
* Both compactors meet the server's contract on `s.compactor` (`compactorOk`, `InvRun.lean`: its
  `Pause` and `Resume` return), and so does whatever `New` returns (`compactorOk_new`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Link
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Periodic__getCompactInterval
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

/-- **The revision compactor's `Run`** (`Spec/.../v3compactor/Revision__Run.lean`). -/
theorem revision_run : v3compactor.Revision.Run.spec (GF := GF) (hG := hG) := Revision.wp_Run

/-- **The periodic compactor's `Run`** (`Spec/.../v3compactor/Periodic__Run.lean`). -/
theorem periodic_run : v3compactor.Periodic.Run.spec (GF := GF) (hG := hG) := Periodic.wp_Run

/-- **`getCompactInterval`** at `interval = 0` returns what it returned before etcd#18472. -/
theorem getCompactInterval_compat :
    ∀ (pc : Loc) (p : w64) (dq dq' : DFrac),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor ∗
        pdPeriodAddr pc ↦{dq} p ∗ pdIntervalAddr pc ↦{dq'} (W64 0) }}
      (App (Val (pc @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Periodic.ty @!! go!"getCompactInterval")) (Val #()))
    {{ RET #(pdCompactIntervalOld p); pdPeriodAddr pc ↦{dq} p ∗ pdIntervalAddr pc ↦{dq'} (W64 0) }} :=
  v3compactor.Periodic.getCompactInterval.spec_implies_old Periodic.wp_getCompactInterval

/-- **The revision compactor meets the server's contract on `s.compactor`**. -/
theorem compactorOk_revision (rc : Loc) (P : RVParams) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor ∗
      isRevision rc P ⊢
    compactorOk (GF := GF) (GoInterface.ok ⟨go.GoType.PointerType
      go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Revision.ty, #rc⟩) := by
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
    iapply (Revision.wp_Pause (GF := GF) rc P) $$ [] HΦ
    iframe #
  · imodintro
    imodintro
    iintro %Φ - HΦ
    iapply (Revision.wp_Resume (GF := GF) rc P) $$ [] HΦ
    iframe #

/-- **The periodic compactor meets the server's contract on `s.compactor`**. -/
theorem compactorOk_periodic (pc : Loc) (P : PDParams) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor ∗
      isPeriodic pc P ⊢
    compactorOk (GF := GF) (GoInterface.ok ⟨go.GoType.PointerType
      go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Periodic.ty, #pc⟩) := by
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
    iapply (Periodic.wp_Pause (GF := GF) pc P) $$ [] HΦ
    iframe #
  · imodintro
    imodintro
    iintro %Φ - HΦ
    iapply (Periodic.wp_Resume (GF := GF) pc P) $$ [] HΦ
    iframe #

/-- **What `New` returns meets the server's contract on `s.compactor`** (in every mode: the
other modes return a nil compactor). -/
theorem compactorOk_new (lg : Loc) (mode : GoString) (retention interval : w64) (rg c : GoInterface)
    (cmp err : GoInterface) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor ∗
      v3compactor.newResult lg mode retention interval rg c cmp err ⊢
    compactorOk (GF := GF) cmp := by
  iintro ⟨#Hp, Hr⟩
  unfold v3compactor.newResult
  split
  · icases Hr with ⟨-, %pc, %lg', %clk, %Heq, #Hpc, -, -, -⟩
    rw [Heq.1]
    iapply compactorOk_periodic pc _
    iframe #
  split
  · icases Hr with ⟨-, %rc, %lg', %clk, %Heq, #Hrc, -⟩
    rw [Heq.1]
    iapply compactorOk_revision rc _
    iframe #
  icases Hr with %Heq
  rw [Heq.1]
  unfold compactorOk
  ileft
  ipureintro; rfl

end results

#print axioms compactor_new
#print axioms revision_run
#print axioms periodic_run
#print axioms getCompactInterval_compat
#print axioms compactorOk_new

end v3compactor
end EtcdGrove
end Perennial
