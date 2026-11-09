/-
`checkLeasePutsKeys(as, ai, l)` (`auth.go:207-220`): the check of a live lease's keys: none for an administrator, else each key's write

**Users.** the auth applier (the apply thread: `S` the stores' one state, exact) and `CheckTxnAuth` (the request path: `S` the reached auth states)

**Proof sketch.** 3d's `IsAdminPermitted`; 3c's `Lease.Keys` (through `permReads`: `l` is the lease `id` the lessor returned); 3d's `IsPutPermitted` per key.

**Changes** from `specs-ref`'s file of the same name: one spec for both callers, parametric in the states the reads see (`permReads`); the old two-mode `isAuthStore … on` and `authApplyErrIs` gone

**Margin.** None. (Round 1: `l` tied to `id` by 3c's `Lease.leaseObj`.)
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.ApiResult
public import Spec.go_etcd_io.etcd.server.v3.lease.Api

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

/-- **The check of a live lease's keys: none for an administrator, else each key's write** at the reads' states `S`: `checksOut`. -/
def checkLeasePutsKeys.spec : Prop :=
  ∀ (ast le : GoInterface) (ai : Loc) (dq : DFrac) (u : GoString) (rev : w64) (A : IProp GF)
    (S : State → IProp GF) (l : Loc) (id : w64) (γl : Lease.Names) (ttl : Int),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗ permReads ast le A S ∗ A ∗ ai.[go_etcd_io.etcd.server.v3.auth.AuthInfo, go!"Username"] ↦{dq} u ∗
      ai.[go_etcd_io.etcd.server.v3.auth.AuthInfo, go!"Revision"] ↦{dq} rev ∗ Lease.leaseObj γl l (sint.Z id) ttl ∗ threadTok }}
    (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.apply.checkLeasePutsKeys)) (Val #ast)) (Val #ai)) (Val #l))
  {{ (err : GoInterface), RET #err; A ∗ ai.[go_etcd_io.etcd.server.v3.auth.AuthInfo, go!"Username"] ↦{dq} u ∗
      ai.[go_etcd_io.etcd.server.v3.auth.AuthInfo, go!"Revision"] ↦{dq} rev ∗ threadTok ∗
      checksOut S u (uint.nat rev) [Check.lease (sint.Z id)] err }}

end spec

end Apply
end EtcdGrove
end Perennial
