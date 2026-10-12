/-
`apply.uberApplier.Apply` (uber_applier.go). Lean-first (no Rocq counterpart); the vocabulary is
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

/-- **`a.Apply(r, shouldApplyV3)`**: the current applier's `Apply` with `dispatch`: the auth
layer's admin rejection (the state as it is), or `dispatch`'s outcome (`applyStep`, from the state
`x`). The wrapper's `SkipRangeExecution` is set only for a transaction (`apply.Apply` sets it so). -/
abbrev apply.uberApplier.Apply.spec : Prop :=
  ∀ (E : AEnv GF) (p : Loc) (opts : ApplierOptions) (x : apply.ApplyKV) (r : Loc)
    (rq : IRRModel) (skip v3 : Bool) (Pre Q Post : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗ apply.uberIs E p opts ∗
      apply.irrWrapperIs r rq skip ∗ apply.uberOwn E p x.chain ∗ apply.kvOwn E x.log ∗
      apply.cPre v3 E.P E.f Pre Q Post ∗ ⌜apply.rqOk x.log rq ∧ apply.dispatchOk rq⌝ ∗
      ⌜skip = true → rq.txn.isSome = true⌝ }}
    (App (App (Val (p @!! go.GoType.PointerType uberApplier.ty @!! go!"Apply")) (Val #r)) (Val #v3))
  {{ (ar : Loc), RET #ar; ∃ (x' : apply.ApplyKV) (out : apply.ApplyOut),
      apply.uberOwn E p x'.chain ∗ apply.kvOwn E x'.log ∗ apply.cPost v3 Pre Post ∗
      ⌜apply.applyStep rq v3 x x' out ∧ (out = .rejected ∨ ∃ o, out = .dispatched o skip)⌝ ∗
      apply.applyResultIs rq v3 x.log ar out }}

end spec

end EtcdGrove
end Perennial
