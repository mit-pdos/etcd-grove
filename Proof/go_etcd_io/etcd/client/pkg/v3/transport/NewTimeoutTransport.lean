/-
The trust boundary: `transport.NewTimeoutTransport` (`go.etcd.io/etcd/client/pkg/v3/transport` is
names-only; the HTTP boundary's, D39). Why it is true of the Go code: its spec's docstring.
-/
module

public import Spec.go_etcd_io.etcd.client.pkg.v3.transport.NewTimeoutTransport

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.client.pkg.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

axiom transport.NewTimeoutTransport.wp_proof : transport.NewTimeoutTransport.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
