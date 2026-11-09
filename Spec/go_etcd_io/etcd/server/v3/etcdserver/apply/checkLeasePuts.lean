/-
`checkLeasePuts(as, ai, lessor, leaseID)` (`auth.go:198-205`): the check of a lease's keys: none for a lease the lessor does not have

**Users.** the auth applier (the apply thread: `S` the stores' one state, exact) and `CheckTxnAuth` (the request path: `S` the reached auth states)

**Proof sketch.** 3c's `Lookup` (through `permReads`); `checkLeasePutsKeys.spec`.

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

/-- **The check of a lease's keys: none for a lease the lessor does not have** at the reads' states `S`: `checksOut`. -/
def checkLeasePuts.spec : Prop :=
  ∀ (ast le : GoInterface) (ai : Loc) (dq : DFrac) (u : GoString) (rev : w64) (A : IProp GF)
    (S : State → IProp GF) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗ permReads ast le A S ∗ A ∗ ai.[go_etcd_io.etcd.server.v3.auth.AuthInfo, go!"Username"] ↦{dq} u ∗
      ai.[go_etcd_io.etcd.server.v3.auth.AuthInfo, go!"Revision"] ↦{dq} rev ∗ threadTok }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.apply.checkLeasePuts)) (Val #ast)) (Val #ai)) (Val #le)) (Val #id))
  {{ (err : GoInterface), RET #err; A ∗ ai.[go_etcd_io.etcd.server.v3.auth.AuthInfo, go!"Username"] ↦{dq} u ∗
      ai.[go_etcd_io.etcd.server.v3.auth.AuthInfo, go!"Revision"] ↦{dq} rev ∗ threadTok ∗
      checksOut S u (uint.nat rev) [Check.lease (sint.Z id)] err }}

end spec

end Apply
end EtcdGrove
end Perennial
