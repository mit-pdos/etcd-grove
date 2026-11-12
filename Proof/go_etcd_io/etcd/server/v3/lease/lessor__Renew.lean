/-
The trust boundary: `(*lessor).Renew` (names only; the lease-renew plan's C1, 2026-11-01): the
lease's renewal (its expiry, the expiry heap, the checkpointer). It returns a TTL and `nil`, or one
of the lease package's errors.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Renew

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.lease

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

axiom lease.lessor.Renew.wp_proof : lease.lessor.Renew.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
