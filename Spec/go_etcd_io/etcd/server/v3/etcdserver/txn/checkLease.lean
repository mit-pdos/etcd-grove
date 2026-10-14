/-
`txn.checkLease` (put.go). Lean-first (no Rocq counterpart); see `Proof/.../etcdserver/txn/Write.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Write

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

/-- `checkLease(lessor, p)`: no lease, or one the lessor finds (`Lookup` returns a lease, which
the lessor granted: `leaseOk`); else `lease.ErrLeaseNotFound`. -/
abbrev txn.checkLease.spec : Prop :=
  ∀ (le : GoInterface) (γl : GName) (p : Loc) (o : OpFull) (L : List w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ txn.isTxnLessor le γl ∗
      lease.lessorUser γl L ∗ txn.putRequestIs p o }}
    (App (App (Val (@! txn.checkLease)) (Val #le)) (Val #p))
  {{ (err : GoInterface), RET #err; lease.lessorUser γl L ∗
      ((⌜err = GoInterface.nil⌝ ∗ txn.leaseOk L o.leaseID) ∨
      (⌜o.leaseID ≠ W64 0⌝ ∗ txn.errVarIs go_etcd_io.etcd.server.v3.lease.ErrLeaseNotFound err)) }}

end spec

end EtcdGrove
end Perennial
