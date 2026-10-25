/-
`(*EtcdServer).tryAutoPromoteLearners()` (`server.go`, PR `etcd-io/etcd#21744`): iterates over
`s.cluster.Members()`, skips non-learners (`!m.IsLearner`), and calls `s.promoteMember(ctx, m.ID)`
with `ctx := s.authStore.WithRoot(s.ctx)`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplier
public import Spec.github_com.prometheus.client_golang.prometheus.CounterVec__WithLabelValues

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

/-- The 10 target error values checked by the `switch` in `EtcdServer.tryAutoPromoteLearners`:
1. `membership.ErrIDNotFound`
2. `membership.ErrMemberNotLearner`
3. `errors.ErrCanceled`
4. `errors.ErrStopped`
5. `errors.ErrTimeoutWaitAppliedIndex`
6. `errors.ErrTimeout`
7. `errors.ErrLeaderChanged`
8. `errors.ErrNotLeader`
9. `errors.ErrNotEnoughStartedMembers`
10. `errors.ErrLearnerNotReady` -/
structure AutoPromoteTargets [FfiSyntax] where
  idNotFound : GoInterfaceOk
  notLearner : GoInterfaceOk
  canceled : GoInterfaceOk
  stopped : GoInterfaceOk
  timeoutWaitApplied : GoInterfaceOk
  timeout : GoInterfaceOk
  leaderChanged : GoInterfaceOk
  notLeader : GoInterfaceOk
  notEnoughStarted : GoInterfaceOk
  learnerNotReady : GoInterfaceOk

/-- Whether a leaf error `e` matches any of the 10 targets in `tryAutoPromoteLearners`'s `switch`. -/
def AutoPromoteTargets.mem [FfiSyntax] (ts : AutoPromoteTargets) (e : GoInterfaceOk) : Bool :=
  Bool.or (decide (e = ts.idNotFound))
    (Bool.or (decide (e = ts.notLearner))
      (Bool.or (decide (e = ts.canceled))
        (Bool.or (decide (e = ts.stopped))
          (Bool.or (decide (e = ts.timeoutWaitApplied))
            (Bool.or (decide (e = ts.timeout))
              (Bool.or (decide (e = ts.leaderChanged))
                (Bool.or (decide (e = ts.notLeader))
                  (Bool.or (decide (e = ts.notEnoughStarted))
                    (decide (e = ts.learnerNotReady))))))))))

/-- Each of the 10 target errors in `AutoPromoteTargets` is a pointer error (`errors.New`). -/
def AutoPromoteTargets.allPtr [FfiSyntax] [GoGlobalContext] (ts : AutoPromoteTargets) : Prop :=
  _root_.Perennial.errors.IsPointerError ts.idNotFound ∧
  _root_.Perennial.errors.IsPointerError ts.notLearner ∧
  _root_.Perennial.errors.IsPointerError ts.canceled ∧
  _root_.Perennial.errors.IsPointerError ts.stopped ∧
  _root_.Perennial.errors.IsPointerError ts.timeoutWaitApplied ∧
  _root_.Perennial.errors.IsPointerError ts.timeout ∧
  _root_.Perennial.errors.IsPointerError ts.leaderChanged ∧
  _root_.Perennial.errors.IsPointerError ts.notLeader ∧
  _root_.Perennial.errors.IsPointerError ts.notEnoughStarted ∧
  _root_.Perennial.errors.IsPointerError ts.learnerNotReady

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- The 10 global error variables read by the `switch` in `tryAutoPromoteLearners`. -/
def autoPromoteTargetVars (ts : AutoPromoteTargets) : IProp GF :=
  iprop(⌜ts.allPtr⌝ ∗
    globalAddr go_etcd_io.etcd.server.v3.etcdserver.api.membership.ErrIDNotFound ↦□ GoInterface.ok ts.idNotFound ∗
    globalAddr go_etcd_io.etcd.server.v3.etcdserver.api.membership.ErrMemberNotLearner ↦□ GoInterface.ok ts.notLearner ∗
    globalAddr go_etcd_io.etcd.server.v3.etcdserver.errors.ErrCanceled ↦□ GoInterface.ok ts.canceled ∗
    globalAddr go_etcd_io.etcd.server.v3.etcdserver.errors.ErrStopped ↦□ GoInterface.ok ts.stopped ∗
    globalAddr go_etcd_io.etcd.server.v3.etcdserver.errors.ErrTimeoutWaitAppliedIndex ↦□ GoInterface.ok ts.timeoutWaitApplied ∗
    globalAddr go_etcd_io.etcd.server.v3.etcdserver.errors.ErrTimeout ↦□ GoInterface.ok ts.timeout ∗
    globalAddr go_etcd_io.etcd.server.v3.etcdserver.errors.ErrLeaderChanged ↦□ GoInterface.ok ts.leaderChanged ∗
    globalAddr go_etcd_io.etcd.server.v3.etcdserver.errors.ErrNotLeader ↦□ GoInterface.ok ts.notLeader ∗
    globalAddr go_etcd_io.etcd.server.v3.etcdserver.errors.ErrNotEnoughStartedMembers ↦□ GoInterface.ok ts.notEnoughStarted ∗
    globalAddr go_etcd_io.etcd.server.v3.etcdserver.errors.ErrLearnerNotReady ↦□ GoInterface.ok ts.learnerNotReady)

instance autoPromoteTargetVars_persistent (ts : AutoPromoteTargets) :
    Persistent (autoPromoteTargetVars (GF := GF) ts) := by
  unfold autoPromoteTargetVars; infer_instance

/-- **`s.authStore.WithRoot(sctx)`** returns `rctx` (persistent). -/
def authWithRootOk (st sctx rctx : GoInterface) : IProp GF :=
  iprop(∃ ai : GoInterfaceOk, ⌜st = GoInterface.ok ai⌝ ∗
    □ ({{ True }} (App (Val #(methods ai.ty go!"WithRoot" ai.v)) (Val #sctx))
      {{ RET #rctx; True }}))

instance authWithRootOk_persistent (st sctx rctx : GoInterface) :
    Persistent (authWithRootOk (GF := GF) st sctx rctx) := by
  unfold authWithRootOk; infer_instance

/-- An error `err` returned by `s.promoteMember`: either `nil`, or a leaf pointer error whose
`Error()` returns a valid UTF-8 message string (so `learnerPromoteFailed.WithLabelValues` does not
panic). -/
def promoteErrOk (err : GoInterface) : IProp GF :=
  iprop(⌜err = GoInterface.nil⌝ ∨
    ∃ (e : GoInterfaceOk) (msg : GoString),
      ⌜err = GoInterface.ok e ∧ errLeaf e ∧ utf8Valid msg⌝ ∗
      □ ({{ True }} (App (Val #(methods e.ty go!"Error" e.v)) (Val #()))
        {{ RET #msg; True }}))

instance promoteErrOk_persistent (err : GoInterface) :
    Persistent (promoteErrOk (GF := GF) err) := by
  unfold promoteErrOk; infer_instance

/-- **`s.promoteMember(rctx, id)`** (names-only contract): called with the exact context `rctx`
returned by `s.authStore.WithRoot(s.ctx)` (Finding 1: never wrapped in `context.WithTimeout`),
returns some slice and an error satisfying `promoteErrOk`. -/
def promoteMemberOk (s : Loc) (rctx : GoInterface) : IProp GF :=
  iprop(□ ∀ (id : w64),
    {{ True }}
      (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"promoteMember"))
        (Val #rctx)) (Val #id))
    {{ (sl : GoSlice) (err : GoInterface), RET (PairV #sl #err);
        promoteErrOk err }})

instance promoteMemberOk_persistent (s : Loc) (rctx : GoInterface) :
    Persistent (promoteMemberOk (GF := GF) s rctx) := by
  unfold promoteMemberOk; infer_instance

/-- Persistent server and package resources read by `EtcdServer.tryAutoPromoteLearners`. -/
def srvAutoPromotePre (s lg : Loc) : IProp GF :=
  iprop(srvLgAddr s ↦□ lg ∗ ⌜lg ≠ null⌝ ∗
    (∃ lgMu : Loc, srvLgMuAddr s ↦□ lgMu) ∗
    (∃ mid : w64, srvMemberIDAddr s ↦□ mid) ∗
    (∃ cl : Loc, srvClusterAddr s ↦□ cl ∗ membership.isRaftCluster cl) ∗
    (∃ sctx st rctx : GoInterface, structFieldRef EtcdServer go!"ctx" s ↦□ sctx ∗
      srvAuthStoreAddr s ↦□ st ∗ authWithRootOk st sctx rctx ∗ promoteMemberOk s rctx) ∗
    (∃ cSucc : GoInterfaceOk, globalAddr learnerPromoteSucceed ↦□ GoInterface.ok cSucc ∗
      prometheus.counterSpec cSucc) ∗
    (∃ cvFail : Loc, globalAddr learnerPromoteFailed ↦□ cvFail ∗
      ⌜prometheus.vecLabels cvFail [go!"ReasonForFailure"]⌝) ∗
    (∃ ts : AutoPromoteTargets, autoPromoteTargetVars ts))

instance srvAutoPromotePre_persistent (s lg : Loc) :
    Persistent (srvAutoPromotePre (GF := GF) s lg) := by
  unfold srvAutoPromotePre; infer_instance

/-- **`s.tryAutoPromoteLearners()`**: gets the logger and `ctx := s.authStore.WithRoot(s.ctx)`,
iterates over `s.cluster.Members()`, skips non-learners (`!m.IsLearner`), and calls
`s.promoteMember(ctx, m.ID)` with the raw `WithRoot(s.ctx)` context `ctx`. On `nil` it increments
`learnerPromoteSucceed` and logs at `Info`; on a non-`nil` error matching one of the 10
`AutoPromoteTargets` it logs at `Debug`; on any other non-`nil` error it increments
`learnerPromoteFailed` and logs at `Warn`. -/
abbrev EtcdServer.tryAutoPromoteLearners.spec : Prop :=
  ∀ (s lg : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvAutoPromotePre s lg ∗ srvLgReader s }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"tryAutoPromoteLearners")) (Val #()))
  {{ RET #(); srvLgReader s }}

end defs

end EtcdGrove
end Perennial
