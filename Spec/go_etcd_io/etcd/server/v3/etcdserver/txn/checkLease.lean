/-
`checkLease(lessor, p)` (`put.go`), internal (`Put`, `checkPut`): `lessor.Lookup(p.Lease)` (3c: `nil`
exactly for a lease not live at the pin). Old spec: over the lessor's owner `L`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Txn

open Iris Iris.BI EtcdModel EtcdWire

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

open Classical in
/-- `checkLease(le, p)`: `ErrLeaseNotFound` for a lease (not `0`) not live at the pin. -/
def checkLease.spec : Prop :=
  ∀ (le : GoInterface) (γ : MvccName) (p : Loc) (dq : DFrac) (pm : PutReq)
    (ls : Int → Option LeaseRec),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ lessorAt le γ ∗ leasesPin γ ls ∗ putReqOwn p dq pm }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.checkLease)) (Val #le)) (Val #p))
  {{ (err : GoInterface), RET #err; leasesPin γ ls ∗ putReqOwn p dq pm ∗
      (if pm.lease ≠ 0 ∧ ls pm.lease = none then errIs err .leaseNotFound
       else iprop(⌜err = GoInterface.nil⌝)) }}

end spec
end Txn
end EtcdGrove
end Perennial
