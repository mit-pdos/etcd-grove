/-
`apply.uberApplier.Alarm` (uber_applier.go). Lean-first (no Rocq counterpart); the vocabulary is
`Proof/go_etcd_io/etcd/server/v3/etcdserver/apply/InvUber.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.InvUber

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **`a.Alarm(r)`** (called by `dispatch`, inside the chain's `Apply`): the current applier's
`Alarm` (one critical section of the batch lock, or none), then, for an `ACTIVATE` or a
`DEACTIVATE`, `restoreAlarms`: `applyV3` is the chain the alarm store's answers ask for. The
chain's resources `chainRes c a` are those of the applier `Apply` was called on, given back. -/
abbrev apply.uberApplier.Alarm.spec : Prop :=
  ∀ (E : AEnv GF) (p : Loc) (opts : ApplierOptions) (c : apply.Chain) (a : GoInterface) (r : Loc)
    (am : apply.AlarmModel) (log : mvcc.Log) (Pre Q Post : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗ apply.uberIs E p opts ∗
      structFieldRef uberApplier go!"applyV3" p ↦ a ∗ apply.applierSpec E c a ∗
      apply.alarmRequestIs r am ∗ apply.mPre E c a log Pre Q Post }}
    (App (Val (p @!! go.GoType.PointerType uberApplier.ty @!! go!"Alarm")) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      apply.mPost E c a log Pre Post ∗ applyErrIs err ∗ ∃ (a' : GoInterface) (c' : apply.Chain),
        structFieldRef uberApplier go!"applyV3" p ↦ a' ∗ apply.applierSpec E c' a' ∗
        ⌜(c' = c ∧ a' = a) ∨ ∃ ns cr, c' = apply.alarmChain ns cr⌝ }}

end spec

end EtcdGrove
end Perennial
