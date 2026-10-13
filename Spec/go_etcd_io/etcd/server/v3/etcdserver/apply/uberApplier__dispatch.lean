/-
`apply.uberApplier.dispatch` (uber_applier.go). Lean-first (no Rocq counterpart); the vocabulary is
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

/-- **`a.dispatch(r, shouldApplyV3)`**, the `applyFunc` `uberApplier.Apply` hands the chain's
`Apply` (`a.dispatch`, a method value): under the chain's resources `chainRes c a` (`a` the
applier `Apply` was called on, `applyV3`'s value then), the request `rq` dispatched to the
method its first set field names (`dispatchKind`; the premise `dispatchOk`: not a compaction, not
an empty request), with the apply thread's KV at `log` and the critical-section contract with
`v3` (`cPre v3`); the KV and `applyV3` (changed by an alarm request) after it (`dispatchStep`,
`chainAfter`), the result (`dispatchResult`). Its deferred metrics (`ApplySecObserve`, the
warnings) return. A write token of the store (`mvcc.storeWT E.γ`) is handed to the method
that may open a store write transaction (2026-10-13, unit 6). -/
abbrev apply.uberApplier.dispatch.spec : Prop :=
  ∀ (E : AEnv GF) (p : Loc) (opts : ApplierOptions) (c : apply.Chain) (a : GoInterface)
    (r : Loc) (rq : IRRModel) (skip v3 : Bool) (log : mvcc.Log) (Pre Q Post : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗ apply.uberIs E p opts ∗
      apply.irrWrapperIs r rq skip ∗ apply.chainRes c a ∗
      structFieldRef uberApplier go!"applyV3" p ↦ a ∗ apply.applierSpec E c a ∗
      apply.kvOwn E log ∗ mvcc.storeWT E.γ ∗ apply.cPre v3 E.P E.f Pre Q Post ∗
      ⌜apply.rqOk log rq ∧ apply.dispatchOk rq⌝ }}
    (App (App (Val (p @!! go.GoType.PointerType uberApplier.ty @!! go!"dispatch")) (Val #r)) (Val #v3))
  {{ (ar : Loc), RET #ar; apply.chainRes c a ∗
      ∃ (a' : GoInterface) (c' : apply.Chain) (o : apply.Outcome),
        structFieldRef uberApplier go!"applyV3" p ↦ a' ∗ apply.applierSpec E c' a' ∗
        apply.kvOwn E (o.logAfter log) ∗ apply.cPost v3 Pre Post ∗
        ⌜apply.dispatchStep c rq v3 log o ∧ apply.chainAfter rq v3 c c'⌝ ∗
        apply.dispatchResult rq v3 log skip ar o }}

end spec

end EtcdGrove
end Perennial
