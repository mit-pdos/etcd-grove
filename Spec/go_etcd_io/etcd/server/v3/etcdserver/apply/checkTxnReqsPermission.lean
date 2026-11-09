/-
`checkTxnReqsPermission(as, ai, lessor, reqs)` (`auth.go:140-189`): the checks of a branch's operations, in order (a nested transaction recursively)

**Users.** the auth applier (the apply thread: `S` the stores' one state, exact) and `CheckTxnAuth` (the request path: `S` the reached auth states)

**Proof sketch.** per operation: 3d's checks, `checkPutAuth.spec`, `checkTxnPermission.spec` (recursion on the nesting).

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

/-- **The checks of a branch's operations, in order (a nested transaction recursively)** at the reads' states `S`: `checksOut`. -/
def checkTxnReqsPermission.spec : Prop :=
  ∀ (ast le : GoInterface) (ai : Loc) (dq : DFrac) (u : GoString) (rev : w64) (A : IProp GF)
    (S : State → IProp GF) (sl : GoSlice) (ops : List RequestOp) (dq' : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗ permReads ast le A S ∗ A ∗ ai.[go_etcd_io.etcd.server.v3.auth.AuthInfo, go!"Username"] ↦{dq} u ∗
      ai.[go_etcd_io.etcd.server.v3.auth.AuthInfo, go!"Revision"] ↦{dq} rev ∗ EtcdWire.msgsOwn EtcdWire.requestOpOwn sl dq' ops ∗ threadTok }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.apply.checkTxnReqsPermission)) (Val #ast)) (Val #ai)) (Val #le)) (Val #sl))
  {{ (err : GoInterface), RET #err; A ∗ ai.[go_etcd_io.etcd.server.v3.auth.AuthInfo, go!"Username"] ↦{dq} u ∗
      ai.[go_etcd_io.etcd.server.v3.auth.AuthInfo, go!"Revision"] ↦{dq} rev ∗ threadTok ∗ EtcdWire.msgsOwn EtcdWire.requestOpOwn sl dq' ops ∗
      checksOut S u (uint.nat rev) (RequestOp.checksL ops) err }}

end spec

end Apply
end EtcdGrove
end Perennial
