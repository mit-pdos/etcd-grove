/-
**The lessor's writes to the rest buckets** (leases T3, L3c, 2026-10-27; `notes/leases-plan.md`):
the `lease` bucket's part of the rest model (`RestModel.lean`). Lean-first (no Rocq counterpart).

A grant puts the lease's record under its key (the id's 8 big-endian bytes, `leaseIDToBytes`):
`lease.leaseEnc` of the id, the TTL the lessor gives it (`lease.grantTTL` of its minimum and the
requested TTL) and a remaining TTL of 0 (`lessor.Grant`'s spec); a revoke deletes it
(`lessor.Revoke`'s). As the tracked buckets, these are `mvcc.rbSet` and `mvcc.rbDel`, the
effects the lessor's specs state (`grant_bk`, `revoke_bk`). The apply thread's model does not use
them yet: no lease request is admitted (`rqOk`) until the apply layer threads the lease table
(L3b, L3c).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.RestModel
public import Proof.go_etcd_io.etcd.server.v3.lease.LeaseRecord
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apply

/-- **A lease's key in the `lease` bucket**: its id as 8 big-endian bytes. -/
def leaseKey (id : w64) : GoString := (u64Le id).reverse

/-- **`Grant(id, ttl)`'s write** by a lessor whose minimum TTL is `mt`: the record put. -/
def restGrant (mt id ttl : w64) (r : RestM) : RestM :=
  r.putIn mvcc.leaseName (leaseKey id) (lease.leaseEnc id (lease.grantTTL mt ttl) (W64 0))

/-- **`Revoke(id)`'s write**: the record deleted. -/
def restRevoke (id : w64) (r : RestM) : RestM :=
  r.delIn mvcc.leaseName (leaseKey id)

/-- A put into the rest model's buckets is the tracked buckets' `rbSet`. -/
theorem bkPut_rbSet (bk : GMap GoString backend.BktData) (n k v : GoString) :
    bkPut bk n k v = mvcc.rbSet bk n k v := rfl

/-- A delete is `rbDel`. -/
theorem bkDel_rbDel (bk : GMap GoString backend.BktData) (n k : GoString) :
    bkDel bk n k = mvcc.rbDel bk n k := rfl

/-- The grant's buckets are those `lessor.Grant` puts its record into. -/
theorem grant_bk (mt id ttl : w64) (r : RestM) :
    (restGrant mt id ttl r).bk =
      mvcc.rbSet r.bk mvcc.leaseName (u64Le id).reverse
        (lease.leaseEnc id (lease.grantTTL mt ttl) (W64 0)) := rfl

/-- The revoke's buckets are those `lessor.Revoke` deletes its record from. -/
theorem revoke_bk (id : w64) (r : RestM) :
    (restRevoke id r).bk = mvcc.rbDel r.bk mvcc.leaseName (u64Le id).reverse := rfl

/-- Neither changes the members. -/
theorem restGrant_mem (mt id ttl : w64) (r : RestM) : (restGrant mt id ttl r).mem = r.mem := rfl

theorem restRevoke_mem (id : w64) (r : RestM) : (restRevoke id r).mem = r.mem := rfl

end apply
end EtcdGrove
end Perennial
