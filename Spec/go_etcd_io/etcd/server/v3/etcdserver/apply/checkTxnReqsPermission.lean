/-
`checkTxnReqsPermission(as, ai, lessor, reqs)` (`auth.go:140-189`): the checks of a branch's operations, in order (a nested transaction recursively)

**Users.** the auth applier (the apply thread: `permReads_writer`, `C` exact at the stores' one state) and `CheckTxnAuth` (the request path: `permReads_reader`, `C` 3d's `checkPost` from a lower bound, no lease check)

**Proof sketch.** per operation: 3d's checks, `checkPutAuth.spec`, `checkTxnPermission.spec` (recursion on the nesting).

**Changes** from `specs-ref`'s file of the same name: one spec for both callers, parametric in how each check is reported (`permReads`' `C`); the old two-mode `isAuthStore … on` and `authApplyErrIs` gone

**Margin.** None.

**Integration (I5).** `permReads` takes the auth info and a per-check report `C` in place of a
set of states `S` (3d's reader check names three views, not one state), and `L` (lease checks
allowed: the request path holds no lessor reader token).
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

/-- **The checks of a branch's operations, in order (a nested transaction recursively)** each check reported by `C`: `checksOut`. -/
def checkTxnReqsPermission.spec : Prop :=
  ∀ (ast le : GoInterface) (ai : Loc) (dq : DFrac) (u : GoString) (rev : w64) (A : IProp GF)
    (L : Bool)
    (C : Check → GoInterface → IProp GF) (sl : GoSlice) (ops : List RequestOp) (dq' : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗ permReads ast le u rev A L C ∗ A ∗ ⌜L = false → ∀ c ∈ (RequestOp.checksL ops), c.isLease = false⌝ ∗  ai.[go_etcd_io.etcd.server.v3.auth.AuthInfo, go!"Username"] ↦{dq} u ∗
      ai.[go_etcd_io.etcd.server.v3.auth.AuthInfo, go!"Revision"] ↦{dq} rev ∗ EtcdWire.msgsOwn EtcdWire.requestOpOwn sl dq' ops ∗ threadTok }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.apply.checkTxnReqsPermission)) (Val #ast)) (Val #ai)) (Val #le)) (Val #sl))
  {{ (err : GoInterface), RET #err; A ∗ ai.[go_etcd_io.etcd.server.v3.auth.AuthInfo, go!"Username"] ↦{dq} u ∗
      ai.[go_etcd_io.etcd.server.v3.auth.AuthInfo, go!"Revision"] ↦{dq} rev ∗ threadTok ∗ EtcdWire.msgsOwn EtcdWire.requestOpOwn sl dq' ops ∗
      checksOut C (RequestOp.checksL ops) err }}

end spec

end Apply
end EtcdGrove
end Perennial
