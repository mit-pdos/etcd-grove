/-
Package initialization for `server/v3/etcdserver/errors` (names-only): `ErrNoSpace` holds a
fixed non-nil error (`errors.New` at init: a pointer error, `errors.IsPointerError`), which the
entry applier compares the applier's error with (`errors.Is`); and (item 8, 2026-10-17) every
error variable holds its `errors.New` error (`errorsNewVars errorsMsgs`), which the server's,
the apply and txn packages' and the read loop's facts take from here. Proved from `initialize'`
(`Init.lean`). Moved unchanged from `etcdserver/BaseApply.lean` (2026-10-11), so that the server's
txn package has it without the apply thread's translation (which reaches raft's).
-/
module

public import Code.go_etcd_io.etcd.server.v3.etcdserver.errors
public import GeneratedProof.go_etcd_io.etcd.server.v3.etcdserver.errors
public import Perennial.Proof.errors
public import Proof.errors.NewVarCell

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

namespace go_etcd_io.etcd.server.v3.etcdserver.errors

/-- The package's error variables and their messages (`errors.go`). -/
def errorsMsgs : List (GoString × GoString) :=
  [(ErrUnknownMethod, go!"etcdserver: unknown method"),
    (ErrStopped, go!"etcdserver: server stopped"),
    (ErrCanceled, go!"etcdserver: request cancelled"),
    (ErrTimeout, go!"etcdserver: request timed out"),
    (ErrTimeoutDueToLeaderFail, go!"etcdserver: request timed out, possibly due to previous leader failure"),
    (ErrTimeoutDueToConnectionLost, go!"etcdserver: request timed out, possibly due to connection lost"),
    (ErrTimeoutLeaderTransfer, go!"etcdserver: request timed out, leader transfer took too long"),
    (ErrTimeoutWaitAppliedIndex, go!"etcdserver: request timed out, waiting for the applied index took too long"),
    (ErrLeaderChanged, go!"etcdserver: leader changed"),
    (ErrNotEnoughStartedMembers, go!"etcdserver: re-configuration failed due to not enough started members"),
    (ErrLearnerNotReady, go!"etcdserver: can only promote a learner member which is in sync with leader"),
    (ErrNoLeader, go!"etcdserver: no leader"),
    (ErrNotLeader, go!"etcdserver: not leader"),
    (ErrRequestTooLarge, go!"etcdserver: request is too large"),
    (ErrNoSpace, go!"etcdserver: no space"),
    (ErrTooManyRequests, go!"etcdserver: too many requests"),
    (ErrUnhealthy, go!"etcdserver: unhealthy cluster"),
    (ErrCorrupt, go!"etcdserver: corrupt cluster"),
    (ErrBadLeaderTransferee, go!"etcdserver: bad leader transferee"),
    (ErrClusterVersionUnavailable, go!"etcdserver: cluster version not found during downgrade"),
    (ErrWrongDowngradeVersionFormat, go!"etcdserver: wrong downgrade target version format"),
    (ErrKeyNotFound, go!"etcdserver: key not found")]

/-- `etcdserver/errors`' package facts: `ErrNoSpace` is a fixed non-nil error, an
`errors.New` error (a pointer error); and (item 8, 2026-10-17) every error variable holds its
`errors.New` error (`errorsNewVars errorsMsgs`), with its message cell (`errVarCells errorsMsgs`,
D19k: what tells `ErrNoSpace` apart from the others). -/
abbrev errorsInit : IProp GF :=
  iprop((∃ e : GoInterfaceOk, globalAddr ErrNoSpace ↦□ GoInterface.ok e ∗
    ⌜_root_.Perennial.errors.IsPointerError e⌝) ∗ EtcdGrove.errorsNewVars errorsMsgs ∗
    EtcdGrove.errVarCells errorsMsgs)

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.errors :=
  define_is_pkg_init errorsInit
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.errors :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.etcdserver.errors

end init

end Perennial
