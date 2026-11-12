/-
The trust boundary: `leasehttp.RenewHTTP` (names only; the lease-renew plan's C5, 2026-11-01): the
renewal forwarded to the leader over HTTP.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.leasehttp.RenewHTTP

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.leasehttp.Assumptions]

axiom leasehttp.RenewHTTP.wp_proof : leasehttp.RenewHTTP.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
