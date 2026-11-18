/-
**A lease's record in the `Lease` bucket, and a put into the tracked buckets** (leases T3, L3c,
2026-10-27; `notes/leases-plan.md`). Lean-first (no Rocq counterpart).

`lease.leaseEnc id ttl rem` is what `schema.MustUnsafePutLease` writes for a lease (opaque:
`proto.Marshal`, which no proof here models), `mvcc.rbSet r n k v` the tracked buckets `r`
(`backend.rbData`) after the put (as `mvcc.rbDel` after a delete). A module of its own, small, so
that the lessor's backend contract (`LessorBackend.lean`), the schema's boundary spec and the
apply package's rest model share them without a change to a widely imported module.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.Base
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBbolt

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

namespace lease

/-- **A lease's record** (opaque): `proto.Marshal` of a `leasepb.Lease` with the id `id`, the TTL
`ttl` and the remaining TTL `rem` and no unknown fields (`schema.MustUnsafePutLease`'s value; the
message's internal state and size cache are caches the encoding does not read). -/
opaque leaseEnc (id ttl rem : w64) : GoString

/-- **The TTL `Grant` gives a lease** asked for `ttl` by a lessor with the minimum `mt`
(`if l.ttl < le.minLeaseTTL { l.ttl = le.minLeaseTTL }`, signed). -/
def grantTTL (mt ttl : w64) : w64 := if sint.Z ttl < sint.Z mt then mt else ttl

end lease

namespace mvcc

/-- The tracked buckets `r` after `n/k := v` (the bucket created if absent, as the backend's
`UnsafePut` leaves it): the lessor's put. -/
def rbSet (r : GMap GoString backend.BktData) (n k v : GoString) : GMap GoString backend.BktData :=
  r.insert n (((r.lookup n).getD ∅).insert k v)

end mvcc

end EtcdGrove
end Perennial
