/-
Package initialization of `go_etcd_io.etcd.server.v3.etcdserver.errors`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`errorsInit`, `errors/Base.lean`): `ErrNoSpace` holds a pointer error, and every
error variable its `errors.New` error (`errorsNewVars errorsMsgs`). Its initializer allocates its
variables and runs their translated initializers, `errors.New` calls (`errors.go`; with their
message cells, `EtcdGrove.wp_New_errorString_cell`; until 2026-11-19 the trust-boundary axiom
`errorsNewVarsInit`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.errors.Base
public import Perennial.Proof.errors.Link
public import Perennial.Proof.errors.NewVar
public import Proof.errors.NewVarCell
public import Proof.runtime.PkgInitExt

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

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.errors.Assumptions]

namespace go_etcd_io.etcd.server.v3.etcdserver.errors

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_etcd_io.etcd.server.v3.etcdserver.errors get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.errors }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrKeyNotFound _ as HErrKeyNotFound
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrWrongDowngradeVersionFormat _ as HErrWrongDowngradeVersionFormat
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrClusterVersionUnavailable _ as HErrClusterVersionUnavailable
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrBadLeaderTransferee _ as HErrBadLeaderTransferee
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrCorrupt _ as HErrCorrupt
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrUnhealthy _ as HErrUnhealthy
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrTooManyRequests _ as HErrTooManyRequests
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrNoSpace _ as HErrNoSpace
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrRequestTooLarge _ as HErrRequestTooLarge
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrNotLeader _ as HErrNotLeader
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrNoLeader _ as HErrNoLeader
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrLearnerNotReady _ as HErrLearnerNotReady
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrNotEnoughStartedMembers _ as HErrNotEnoughStartedMembers
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrLeaderChanged _ as HErrLeaderChanged
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrTimeoutWaitAppliedIndex _ as HErrTimeoutWaitAppliedIndex
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrTimeoutLeaderTransfer _ as HErrTimeoutLeaderTransfer
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrTimeoutDueToConnectionLost _ as HErrTimeoutDueToConnectionLost
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrTimeoutDueToLeaderFail _ as HErrTimeoutDueToLeaderFail
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrTimeout _ as HErrTimeout
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrCanceled _ as HErrCanceled
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrStopped _ as HErrStopped
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrUnknownMethod _ as HErrUnknownMethod
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.errors _root_.Perennial.errors.initialize'
      EtcdGrove.ExternalInit.errors _root_.Perennial.errors.wp_initialize' _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  -- translated initializer of ErrUnknownMethod))
  try wp_auto
  wp_apply EtcdGrove.wp_New_errorString_cell as %xErrUnknownMethod ⟨#MErrUnknownMethod, #CErrUnknownMethod⟩
  -- translated initializer of ErrStopped))
  try wp_auto
  wp_apply EtcdGrove.wp_New_errorString_cell as %xErrStopped ⟨#MErrStopped, #CErrStopped⟩
  -- translated initializer of ErrCanceled))
  try wp_auto
  wp_apply EtcdGrove.wp_New_errorString_cell as %xErrCanceled ⟨#MErrCanceled, #CErrCanceled⟩
  -- translated initializer of ErrTimeout))
  try wp_auto
  wp_apply EtcdGrove.wp_New_errorString_cell as %xErrTimeout ⟨#MErrTimeout, #CErrTimeout⟩
  -- translated initializer of ErrTimeoutDueToLeaderFail))
  try wp_auto
  wp_apply EtcdGrove.wp_New_errorString_cell as %xErrTimeoutDueToLeaderFail ⟨#MErrTimeoutDueToLeaderFail, #CErrTimeoutDueToLeaderFail⟩
  -- translated initializer of ErrTimeoutDueToConnectionLost))
  try wp_auto
  wp_apply EtcdGrove.wp_New_errorString_cell as %xErrTimeoutDueToConnectionLost ⟨#MErrTimeoutDueToConnectionLost, #CErrTimeoutDueToConnectionLost⟩
  -- translated initializer of ErrTimeoutLeaderTransfer))
  try wp_auto
  wp_apply EtcdGrove.wp_New_errorString_cell as %xErrTimeoutLeaderTransfer ⟨#MErrTimeoutLeaderTransfer, #CErrTimeoutLeaderTransfer⟩
  -- translated initializer of ErrTimeoutWaitAppliedIndex))
  try wp_auto
  wp_apply EtcdGrove.wp_New_errorString_cell as %xErrTimeoutWaitAppliedIndex ⟨#MErrTimeoutWaitAppliedIndex, #CErrTimeoutWaitAppliedIndex⟩
  -- translated initializer of ErrLeaderChanged))
  try wp_auto
  wp_apply EtcdGrove.wp_New_errorString_cell as %xErrLeaderChanged ⟨#MErrLeaderChanged, #CErrLeaderChanged⟩
  -- translated initializer of ErrNotEnoughStartedMembers))
  try wp_auto
  wp_apply EtcdGrove.wp_New_errorString_cell as %xErrNotEnoughStartedMembers ⟨#MErrNotEnoughStartedMembers, #CErrNotEnoughStartedMembers⟩
  -- translated initializer of ErrLearnerNotReady))
  try wp_auto
  wp_apply EtcdGrove.wp_New_errorString_cell as %xErrLearnerNotReady ⟨#MErrLearnerNotReady, #CErrLearnerNotReady⟩
  -- translated initializer of ErrNoLeader))
  try wp_auto
  wp_apply EtcdGrove.wp_New_errorString_cell as %xErrNoLeader ⟨#MErrNoLeader, #CErrNoLeader⟩
  -- translated initializer of ErrNotLeader))
  try wp_auto
  wp_apply EtcdGrove.wp_New_errorString_cell as %xErrNotLeader ⟨#MErrNotLeader, #CErrNotLeader⟩
  -- translated initializer of ErrRequestTooLarge))
  try wp_auto
  wp_apply EtcdGrove.wp_New_errorString_cell as %xErrRequestTooLarge ⟨#MErrRequestTooLarge, #CErrRequestTooLarge⟩
  -- translated initializer of ErrNoSpace))
  try wp_auto
  wp_apply EtcdGrove.wp_New_errorString_cell as %xErrNoSpace ⟨#MErrNoSpace, #CErrNoSpace⟩
  -- translated initializer of ErrTooManyRequests))
  try wp_auto
  wp_apply EtcdGrove.wp_New_errorString_cell as %xErrTooManyRequests ⟨#MErrTooManyRequests, #CErrTooManyRequests⟩
  -- translated initializer of ErrUnhealthy))
  try wp_auto
  wp_apply EtcdGrove.wp_New_errorString_cell as %xErrUnhealthy ⟨#MErrUnhealthy, #CErrUnhealthy⟩
  -- translated initializer of ErrCorrupt))
  try wp_auto
  wp_apply EtcdGrove.wp_New_errorString_cell as %xErrCorrupt ⟨#MErrCorrupt, #CErrCorrupt⟩
  -- translated initializer of ErrBadLeaderTransferee))
  try wp_auto
  wp_apply EtcdGrove.wp_New_errorString_cell as %xErrBadLeaderTransferee ⟨#MErrBadLeaderTransferee, #CErrBadLeaderTransferee⟩
  -- translated initializer of ErrClusterVersionUnavailable))
  try wp_auto
  wp_apply EtcdGrove.wp_New_errorString_cell as %xErrClusterVersionUnavailable ⟨#MErrClusterVersionUnavailable, #CErrClusterVersionUnavailable⟩
  -- translated initializer of ErrWrongDowngradeVersionFormat))
  try wp_auto
  wp_apply EtcdGrove.wp_New_errorString_cell as %xErrWrongDowngradeVersionFormat ⟨#MErrWrongDowngradeVersionFormat, #CErrWrongDowngradeVersionFormat⟩
  -- translated initializer of ErrKeyNotFound))
  try wp_auto
  wp_apply EtcdGrove.wp_New_errorString_cell as %xErrKeyNotFound ⟨#MErrKeyNotFound, #CErrKeyNotFound⟩
  ipersist HErrUnknownMethod
  ipersist HErrStopped
  ipersist HErrCanceled
  ipersist HErrTimeout
  ipersist HErrTimeoutDueToLeaderFail
  ipersist HErrTimeoutDueToConnectionLost
  ipersist HErrTimeoutLeaderTransfer
  ipersist HErrTimeoutWaitAppliedIndex
  ipersist HErrLeaderChanged
  ipersist HErrNotEnoughStartedMembers
  ipersist HErrLearnerNotReady
  ipersist HErrNoLeader
  ipersist HErrNotLeader
  ipersist HErrRequestTooLarge
  ipersist HErrNoSpace
  ipersist HErrTooManyRequests
  ipersist HErrUnhealthy
  ipersist HErrCorrupt
  ipersist HErrBadLeaderTransferee
  ipersist HErrClusterVersionUnavailable
  ipersist HErrWrongDowngradeVersionFormat
  ipersist HErrKeyNotFound
  iframe Hown
  imodintro
  isplitr
  · ipureintro
    exact isPanic_intoVal _
  is_pkg_init_finish
  try (isplitl []; · (imodintro; itrivial))
  imodintro
  unfold errorsInit errorsMsgs
  simp only [EtcdGrove.errorsNewVars, EtcdGrove.errorsNewVar, EtcdGrove.errVarCells, EtcdGrove.errVarCell]
  iframe #
  ipureintro
  exact ⟨_, _, rfl, rfl⟩

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_etcd_io.etcd.server.v3.etcdserver.errors get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.errors }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end go_etcd_io.etcd.server.v3.etcdserver.errors

end init

end Perennial
