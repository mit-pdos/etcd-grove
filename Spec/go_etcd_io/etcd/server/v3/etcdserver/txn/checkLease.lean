/-
`checkLease(lessor, p)` (`put.go`), internal (`Put`, `checkPut`): `lessor.Lookup(p.Lease)` (3c's
`lessor.Lookup.spec` at `lessorLb γl n`, from the writer's token: answered at the state `n` itself,
`lessorState_le`, `lessorAt_agree`; `nil` exactly for a lease not live). Old spec: over the lessor's
owner `L`.
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
/-- `checkLease(le, p)`: `ErrLeaseNotFound` for a lease (not `0`) not live in the writer's state. -/
def checkLease.spec : Prop :=
  ∀ (leL : Loc) (γl : Lease.Names) (c : Lease.Cfg) (n : Nat) (ls : Lease.LessorState) (p : Loc)
    (dq : DFrac) (pm : PutReq),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ Lease.isLessor leL γl c ∗ Lease.lessorState γl n ls ∗ putReqOwn p dq pm }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.checkLease)) (Val #(Lease.lessorIface leL))) (Val #p))
  {{ (err : GoInterface), RET #err; Lease.lessorState γl n ls ∗ putReqOwn p dq pm ∗
      (if pm.lease ≠ 0 ∧ ls.leases pm.lease = none then errIs err .leaseNotFound
       else iprop(⌜err = GoInterface.nil⌝)) }}

end spec
end Txn
end EtcdGrove
end Perennial
