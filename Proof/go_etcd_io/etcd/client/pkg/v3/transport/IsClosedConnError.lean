/-
The trust boundary: `transport.IsClosedConnError` (`go.etcd.io/etcd/client/pkg/v3/transport` is
names-only).
-/
module

public import Spec.go_etcd_io.etcd.client.pkg.v3.transport.IsClosedConnError

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.client.pkg.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

axiom transport.IsClosedConnError.wp_proof : transport.IsClosedConnError.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
