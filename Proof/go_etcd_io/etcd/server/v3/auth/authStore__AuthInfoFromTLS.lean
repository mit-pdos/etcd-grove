/-
The trust boundary: `(*authStore).AuthInfoFromTLS` (names only: `credentials.TLSInfo` and the
x509 chains are axiomatized types; `peer.FromContext`, `metadata.FromIncomingContext`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__AuthInfoFromTLS

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.auth auth

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

axiom auth.authStore.AuthInfoFromTLS.wp_proof : auth.authStore.AuthInfoFromTLS.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
