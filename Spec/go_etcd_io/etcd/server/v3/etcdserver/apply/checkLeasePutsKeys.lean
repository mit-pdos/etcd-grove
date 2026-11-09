/-
`checkLeasePutsKeys(as, ai, l)` (`auth.go:207-220`): the check of a live lease's keys: none for an administrator, else each key's write

**Users.** the auth applier (the apply thread: `permReads_writer`, `C` exact at the stores' one state) and `CheckTxnAuth` (the request path: `permReads_reader`, `C` 3d's `checkPost` from a lower bound, no lease check)

**Proof sketch.** 3d's `IsAdminPermitted`; 3c's `Lease.Keys` (through `permReads`: `l` is the lease `id` the lessor returned); 3d's `IsPutPermitted` per key.

**Changes** from `specs-ref`'s file of the same name: one spec for both callers, parametric in how each check is reported (`permReads`' `C`); the old two-mode `isAuthStore … on` and `authApplyErrIs` gone

**Margin.** None.

**Integration (I5).** `permReads` takes the auth info and a per-check report `C` in place of a
set of states `S` (3d's reader check names three views, not one state), and `L` (lease checks
allowed: the request path holds no lessor reader token). (Round 1: `l` tied to `id` by 3c's `Lease.leaseObj`.)
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

/-- **The check of a live lease's keys: none for an administrator, else each key's write** each check reported by `C`: `checksOut`. -/
def checkLeasePutsKeys.spec : Prop :=
  ∀ (ast le : GoInterface) (ai : Loc) (dq : DFrac) (u : GoString) (rev : w64) (A : IProp GF)
    (L : Bool)
    (C : Check → GoInterface → IProp GF) (l : Loc) (id : w64) (γl : Lease.Names) (ttl : Int),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗ permReads ast le u rev A L C ∗ A ∗ ⌜L = true⌝ ∗  ai.[go_etcd_io.etcd.server.v3.auth.AuthInfo, go!"Username"] ↦{dq} u ∗
      ai.[go_etcd_io.etcd.server.v3.auth.AuthInfo, go!"Revision"] ↦{dq} rev ∗ Lease.leaseObj γl l (sint.Z id) ttl ∗ threadTok }}
    (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.apply.checkLeasePutsKeys)) (Val #ast)) (Val #ai)) (Val #l))
  {{ (err : GoInterface), RET #err; A ∗ ai.[go_etcd_io.etcd.server.v3.auth.AuthInfo, go!"Username"] ↦{dq} u ∗
      ai.[go_etcd_io.etcd.server.v3.auth.AuthInfo, go!"Revision"] ↦{dq} rev ∗ threadTok ∗
      checksOut C [Check.lease (sint.Z id)] err }}

end spec

end Apply
end EtcdGrove
end Perennial
