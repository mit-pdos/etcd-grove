/-
Package initialization of `go_etcd_io.etcd.server.v3.etcdserver.errors`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`errorsInit`, `errors/Base.lean`): `ErrNoSpace` holds a pointer error. Its
initializer runs its variables' initializers, all untranslated `errors.New` calls (`errors.go`),
which the trust-boundary axiom `errorsNewVarsInit` states.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.errors.Base
public import Proof.errors.NewVar

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial

/-- `x ∈ [a, ..., x, ...]`, linear in the list (`simp` overflows on the long ones). -/
local macro "mem_tac" : tactic =>
  `(tactic| repeat (first | exact List.Mem.head _ | apply List.Mem.tail))

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section opaqueInits
namespace go_etcd_io.etcd.server.v3.etcdserver.errors
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `go_etcd_io.etcd.server.v3.etcdserver.errors`'s variables initialized by `errors.New`.** Each
listed `X.init` (untranslated) runs Go's `var X = errors.New(msg)`, as its Go source has
it. -/
axiom errorsNewVarsInit :
    ∀ (init : val) (X msg : GoString), (init, X, msg) ∈ ([(ErrUnknownMethod.init, ErrUnknownMethod, go!"etcdserver: unknown method"),
        (ErrStopped.init, ErrStopped, go!"etcdserver: server stopped"),
        (ErrCanceled.init, ErrCanceled, go!"etcdserver: request cancelled"),
        (ErrTimeout.init, ErrTimeout, go!"etcdserver: request timed out"),
        (ErrTimeoutDueToLeaderFail.init, ErrTimeoutDueToLeaderFail, go!"etcdserver: request timed out, possibly due to previous leader failure"),
        (ErrTimeoutDueToConnectionLost.init, ErrTimeoutDueToConnectionLost, go!"etcdserver: request timed out, possibly due to connection lost"),
        (ErrTimeoutLeaderTransfer.init, ErrTimeoutLeaderTransfer, go!"etcdserver: request timed out, leader transfer took too long"),
        (ErrTimeoutWaitAppliedIndex.init, ErrTimeoutWaitAppliedIndex, go!"etcdserver: request timed out, waiting for the applied index took too long"),
        (ErrLeaderChanged.init, ErrLeaderChanged, go!"etcdserver: leader changed"),
        (ErrNotEnoughStartedMembers.init, ErrNotEnoughStartedMembers, go!"etcdserver: re-configuration failed due to not enough started members"),
        (ErrLearnerNotReady.init, ErrLearnerNotReady, go!"etcdserver: can only promote a learner member which is in sync with leader"),
        (ErrNoLeader.init, ErrNoLeader, go!"etcdserver: no leader"),
        (ErrNotLeader.init, ErrNotLeader, go!"etcdserver: not leader"),
        (ErrRequestTooLarge.init, ErrRequestTooLarge, go!"etcdserver: request is too large"),
        (ErrNoSpace.init, ErrNoSpace, go!"etcdserver: no space"),
        (ErrTooManyRequests.init, ErrTooManyRequests, go!"etcdserver: too many requests"),
        (ErrUnhealthy.init, ErrUnhealthy, go!"etcdserver: unhealthy cluster"),
        (ErrCorrupt.init, ErrCorrupt, go!"etcdserver: corrupt cluster"),
        (ErrBadLeaderTransferee.init, ErrBadLeaderTransferee, go!"etcdserver: bad leader transferee"),
        (ErrClusterVersionUnavailable.init, ErrClusterVersionUnavailable, go!"etcdserver: cluster version not found during downgrade"),
        (ErrWrongDowngradeVersionFormat.init, ErrWrongDowngradeVersionFormat, go!"etcdserver: wrong downgrade target version format"),
        (ErrKeyNotFound.init, ErrKeyNotFound, go!"etcdserver: key not found")] : List (val × GoString × GoString)) →
    EtcdGrove.errorsNewVarInit (GF := GF) init X msg

end go_etcd_io.etcd.server.v3.etcdserver.errors
end opaqueInits

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.errors.Assumptions]

namespace go_etcd_io.etcd.server.v3.etcdserver.errors

theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_etcd_io.etcd.server.v3.etcdserver.errors get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.errors }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  wp_apply (errorsNewVarsInit ErrUnknownMethod.init ErrUnknownMethod go!"etcdserver: unknown method" (by mem_tac))
    as ⟨%xErrUnknownMethod, HErrUnknownMethod, #MErrUnknownMethod⟩
  wp_apply (errorsNewVarsInit ErrStopped.init ErrStopped go!"etcdserver: server stopped" (by mem_tac))
    as ⟨%xErrStopped, HErrStopped, #MErrStopped⟩
  wp_apply (errorsNewVarsInit ErrCanceled.init ErrCanceled go!"etcdserver: request cancelled" (by mem_tac))
    as ⟨%xErrCanceled, HErrCanceled, #MErrCanceled⟩
  wp_apply (errorsNewVarsInit ErrTimeout.init ErrTimeout go!"etcdserver: request timed out" (by mem_tac))
    as ⟨%xErrTimeout, HErrTimeout, #MErrTimeout⟩
  wp_apply (errorsNewVarsInit ErrTimeoutDueToLeaderFail.init ErrTimeoutDueToLeaderFail go!"etcdserver: request timed out, possibly due to previous leader failure" (by mem_tac))
    as ⟨%xErrTimeoutDueToLeaderFail, HErrTimeoutDueToLeaderFail, #MErrTimeoutDueToLeaderFail⟩
  wp_apply (errorsNewVarsInit ErrTimeoutDueToConnectionLost.init ErrTimeoutDueToConnectionLost go!"etcdserver: request timed out, possibly due to connection lost" (by mem_tac))
    as ⟨%xErrTimeoutDueToConnectionLost, HErrTimeoutDueToConnectionLost, #MErrTimeoutDueToConnectionLost⟩
  wp_apply (errorsNewVarsInit ErrTimeoutLeaderTransfer.init ErrTimeoutLeaderTransfer go!"etcdserver: request timed out, leader transfer took too long" (by mem_tac))
    as ⟨%xErrTimeoutLeaderTransfer, HErrTimeoutLeaderTransfer, #MErrTimeoutLeaderTransfer⟩
  wp_apply (errorsNewVarsInit ErrTimeoutWaitAppliedIndex.init ErrTimeoutWaitAppliedIndex go!"etcdserver: request timed out, waiting for the applied index took too long" (by mem_tac))
    as ⟨%xErrTimeoutWaitAppliedIndex, HErrTimeoutWaitAppliedIndex, #MErrTimeoutWaitAppliedIndex⟩
  wp_apply (errorsNewVarsInit ErrLeaderChanged.init ErrLeaderChanged go!"etcdserver: leader changed" (by mem_tac))
    as ⟨%xErrLeaderChanged, HErrLeaderChanged, #MErrLeaderChanged⟩
  wp_apply (errorsNewVarsInit ErrNotEnoughStartedMembers.init ErrNotEnoughStartedMembers go!"etcdserver: re-configuration failed due to not enough started members" (by mem_tac))
    as ⟨%xErrNotEnoughStartedMembers, HErrNotEnoughStartedMembers, #MErrNotEnoughStartedMembers⟩
  wp_apply (errorsNewVarsInit ErrLearnerNotReady.init ErrLearnerNotReady go!"etcdserver: can only promote a learner member which is in sync with leader" (by mem_tac))
    as ⟨%xErrLearnerNotReady, HErrLearnerNotReady, #MErrLearnerNotReady⟩
  wp_apply (errorsNewVarsInit ErrNoLeader.init ErrNoLeader go!"etcdserver: no leader" (by mem_tac))
    as ⟨%xErrNoLeader, HErrNoLeader, #MErrNoLeader⟩
  wp_apply (errorsNewVarsInit ErrNotLeader.init ErrNotLeader go!"etcdserver: not leader" (by mem_tac))
    as ⟨%xErrNotLeader, HErrNotLeader, #MErrNotLeader⟩
  wp_apply (errorsNewVarsInit ErrRequestTooLarge.init ErrRequestTooLarge go!"etcdserver: request is too large" (by mem_tac))
    as ⟨%xErrRequestTooLarge, HErrRequestTooLarge, #MErrRequestTooLarge⟩
  wp_apply (errorsNewVarsInit ErrNoSpace.init ErrNoSpace go!"etcdserver: no space" (by mem_tac))
    as ⟨%xErrNoSpace, HErrNoSpace, #MErrNoSpace⟩
  wp_apply (errorsNewVarsInit ErrTooManyRequests.init ErrTooManyRequests go!"etcdserver: too many requests" (by mem_tac))
    as ⟨%xErrTooManyRequests, HErrTooManyRequests, #MErrTooManyRequests⟩
  wp_apply (errorsNewVarsInit ErrUnhealthy.init ErrUnhealthy go!"etcdserver: unhealthy cluster" (by mem_tac))
    as ⟨%xErrUnhealthy, HErrUnhealthy, #MErrUnhealthy⟩
  wp_apply (errorsNewVarsInit ErrCorrupt.init ErrCorrupt go!"etcdserver: corrupt cluster" (by mem_tac))
    as ⟨%xErrCorrupt, HErrCorrupt, #MErrCorrupt⟩
  wp_apply (errorsNewVarsInit ErrBadLeaderTransferee.init ErrBadLeaderTransferee go!"etcdserver: bad leader transferee" (by mem_tac))
    as ⟨%xErrBadLeaderTransferee, HErrBadLeaderTransferee, #MErrBadLeaderTransferee⟩
  wp_apply (errorsNewVarsInit ErrClusterVersionUnavailable.init ErrClusterVersionUnavailable go!"etcdserver: cluster version not found during downgrade" (by mem_tac))
    as ⟨%xErrClusterVersionUnavailable, HErrClusterVersionUnavailable, #MErrClusterVersionUnavailable⟩
  wp_apply (errorsNewVarsInit ErrWrongDowngradeVersionFormat.init ErrWrongDowngradeVersionFormat go!"etcdserver: wrong downgrade target version format" (by mem_tac))
    as ⟨%xErrWrongDowngradeVersionFormat, HErrWrongDowngradeVersionFormat, #MErrWrongDowngradeVersionFormat⟩
  wp_apply (errorsNewVarsInit ErrKeyNotFound.init ErrKeyNotFound go!"etcdserver: key not found" (by mem_tac))
    as ⟨%xErrKeyNotFound, HErrKeyNotFound, #MErrKeyNotFound⟩
  ipersist HErrNoSpace
  iframe Hown
  imodintro
  isplitr
  · ipureintro
    exact isPanic_intoVal _
  is_pkg_init_finish
  try (isplitl []; · (imodintro; itrivial))
  imodintro
  iexists _
  iframe HErrNoSpace
  ipureintro
  exact ⟨_, _, rfl, rfl⟩


end go_etcd_io.etcd.server.v3.etcdserver.errors

end init

end Perennial
