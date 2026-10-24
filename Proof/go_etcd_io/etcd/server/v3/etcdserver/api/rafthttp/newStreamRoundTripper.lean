/-
The trust boundary: `newStreamRoundTripper` (untranslated; the HTTP boundary's, D39).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.newStreamRoundTripper

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **Trust boundary** (rafthttp stage 6c, D39): `newStreamRoundTripper` (`util.go`) is
`transport.NewTimeoutTransport(tlsInfo, dialTimeout, ConnReadTimeout, ConnWriteTimeout)` (`client/pkg/transport`): an
`*http.Transport` dialing with the timeout, with a read and a write timeout (a connection's read or write past it fails), and with `tlsInfo`'s TLS
configuration, or the error of reading its certificates. Go's `http.Transport` is a client of
the HTTP boundary (`http.roundTripperOk`'s docstring: a `RoundTrip` fails or returns the
response the server's handler wrote, which is how `H`'s protocol relates the two). The ghost
network `H` does not enter the Go code, and `roundTripperOk` holds of every `H`: its
`RoundTrip` takes the host's registration (`httpProtoAt`), which ties `H` to the server. -/
axiom rafthttp.newStreamRoundTripper.wp_proof : rafthttp.newStreamRoundTripper.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
