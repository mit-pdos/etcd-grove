/-
`checkTxnPermission(as, ai, lessor, rt)` (`auth.go:128-138`): the checks of a transaction: its comparisons' reads, then both branches

**Users.** the auth applier (the apply thread: `S` the stores' one state, exact) and `CheckTxnAuth` (the request path: `S` the reached auth states)

**Proof sketch.** 3d's `IsRangePermitted` per comparison; `checkTxnReqsPermission.spec` twice.

**Changes** from `specs-ref`'s file of the same name: one spec for both callers, parametric in the states the reads see (`permReads`); the old two-mode `isAuthStore … on` and `authApplyErrIs` gone

**Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.ApiResult

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Apply

open Iris Iris.BI EtcdModel

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **The checks of a transaction: its comparisons' reads, then both branches** at the reads' states `S`: `checksOut`. -/
def checkTxnPermission.spec : Prop :=
  ∀ (ast le : GoInterface) (ai : Loc) (dq : DFrac) (u : GoString) (rev : w64) (A : IProp GF)
    (S : State → IProp GF) (rt : Loc) (t : TxnReq) (dq' : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗ permReads ast le A S ∗ A ∗ ai.[go_etcd_io.etcd.server.v3.auth.AuthInfo, go!"Username"] ↦{dq} u ∗
      ai.[go_etcd_io.etcd.server.v3.auth.AuthInfo, go!"Revision"] ↦{dq} rev ∗ EtcdWire.txnReqOwn rt dq' t ∗ threadTok }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.apply.checkTxnPermission)) (Val #ast)) (Val #ai)) (Val #le)) (Val #rt))
  {{ (err : GoInterface), RET #err; A ∗ ai.[go_etcd_io.etcd.server.v3.auth.AuthInfo, go!"Username"] ↦{dq} u ∗
      ai.[go_etcd_io.etcd.server.v3.auth.AuthInfo, go!"Revision"] ↦{dq} rev ∗ threadTok ∗ EtcdWire.txnReqOwn rt dq' t ∗
      checksOut S u (uint.nat rev) (RequestOp.checks (RequestOp.txn t.compare t.success t.failure)) err }}

end spec

end Apply
end EtcdGrove
end Perennial
