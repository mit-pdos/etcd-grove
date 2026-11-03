/-
`apply.checkPutAuth` (auth.go). Lean-first (no Rocq counterpart); the vocabulary is
`Proof/go_etcd_io/etcd/server/v3/etcdserver/apply/Chain.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Chain
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.AuthClass

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **`checkPutAuth(as, ai, lessor, r)`**: the auth store's `IsPutPermitted` of the key, `checkLeasePuts` of the put's lease and, with `PrevKv`, `IsRangePermitted` of the key: the first error, or `nil`; the `AuthInfo` kept, nothing written. By the lease owner (`lease.lessorUser`, lent and given back): a `nil` answer also gives the class of the put's lease's keys at the owner's item map `I` (its wire `Lease`, whatever `IgnoreLease` says: `leaseKeysClass`). -/
abbrev apply.checkPutAuth.spec : Prop :=
  ∀ (st le : GoInterface) (γ : mvcc.StoreNames) (P : IProp GF) (f : val) (RD : IProp GF) (on : auth.AuthMode) (RW : IProp GF) (ai : Loc)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (dq : DFrac) (r : Loc) (o : OpFull) (L : List w64)
    (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗ apply.isAuthStore st γ P f RD on RW ∗ apply.isApplyLessorAny le γ P f RW ∗ ai ↦{dq} info ∗ RD ∗
      lease.lessorUser γ.leases L I ∗ txn.putRequestIs r o }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.apply.checkPutAuth))
      (Val #st)) (Val #ai)) (Val #le)) (Val #r))
  {{ (err : GoInterface), RET #err; ai ↦{dq} info ∗ RD ∗ lease.lessorUser γ.leases L I ∗
      authApplyErrIs err ∗ ⌜on.isOn = false → err = GoInterface.nil⌝ ∗
      (∀ _ : err = GoInterface.nil, apply.putClass on info o ∗
        apply.leaseKeysClass on info I o.leaseID) }}

end spec

end EtcdGrove
end Perennial
