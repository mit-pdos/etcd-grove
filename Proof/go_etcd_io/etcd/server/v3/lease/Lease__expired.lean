/-
The trust boundary: `(*Lease).expired()`'s payload (prove-ps2-newlessor3, 2026-11-21; the user's
choice "(a)"): why the statement is true of the Go code is in its spec's docstring
(`Spec/go_etcd_io/etcd/server/v3/lease/Lease__expired.lean`) and
`notes/axiom-review/lease-expired-payload.md`. It replaced `lease.NewLessor.wp_proof`, whose
`expiredC` payload (`¬ leasesNoExpiry`) it is the only source of.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.Lease__expired

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

axiom lease.Lease.expired.wp_proof : lease.Lease.expired.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
