/-
`checkLeasePuts(as, ai, lessor, leaseID)` (`auth.go:198-205`): the check of a lease's keys: none for a lease the lessor does not have

**Users.** the auth applier (the apply thread: `permReads_writer`, `C` exact at the stores' one state) and `CheckTxnAuth` (the request path: `permReads_reader`, `C` 3d's `checkPost` from a lower bound, no lease check)

**Proof sketch.** 3c's `Lookup` (through `permReads`); `checkLeasePutsKeys.spec`.

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

/-- **The check of a lease's keys: none for a lease the lessor does not have** each check reported by `C`: `checksOut`. -/
def checkLeasePuts.spec : Prop :=
  ∀ (ast le : GoInterface) (ai : Loc) (dq : DFrac) (u : GoString) (rev : w64) (A : IProp GF)
    (L : Bool)
    (C : Check → GoInterface → IProp GF) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗ permReads ast le u rev A L C ∗ A ∗ ⌜L = true⌝ ∗  ai.[go_etcd_io.etcd.server.v3.auth.AuthInfo, go!"Username"] ↦{dq} u ∗
      ai.[go_etcd_io.etcd.server.v3.auth.AuthInfo, go!"Revision"] ↦{dq} rev ∗ threadTok }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.apply.checkLeasePuts)) (Val #ast)) (Val #ai)) (Val #le)) (Val #id))
  {{ (err : GoInterface), RET #err; A ∗ ai.[go_etcd_io.etcd.server.v3.auth.AuthInfo, go!"Username"] ↦{dq} u ∗
      ai.[go_etcd_io.etcd.server.v3.auth.AuthInfo, go!"Revision"] ↦{dq} rev ∗ threadTok ∗
      checksOut C [Check.lease (sint.Z id)] err }}

end spec

end Apply
end EtcdGrove
end Perennial
