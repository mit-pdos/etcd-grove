/-
The trust boundary: `NewRoundTripper` (untranslated; the HTTP boundary's, D39).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.NewRoundTripper

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **Trust boundary** (rafthttp stage 6c, D39): `NewRoundTripper` (`util.go`) is
`transport.NewTimeoutTransport(tlsInfo, dialTimeout, 0, 0)` (`client/pkg/transport`): an
`*http.Transport` dialing with the timeout, with no read or write timeout, and with `tlsInfo`'s TLS
configuration, or the error of reading its certificates. Go's `http.Transport` is a client of
the HTTP boundary (`http.roundTripperOk`'s docstring: a `RoundTrip` fails or returns the
response a handler run of the request wrote, or one the server made itself, `http.srvStatuses`,
which every registered protocol admits, `http.Proto.srvOk`; this is how `H`'s protocol relates the
two). (http-boundary-fix, 2026-11-14) Its `RoundTrip` replays a request Go deems replayable
(`http.onceOnly` false: a `GET`) on a reused connection whose response read fails, which may run
the request's handler twice: only a handler of a request never replayed receives the request's
ticket (`http.reqTicketOnce`), `examples/premisefix/httpreplay`. The ghost
network `H` does not enter the Go code, and `roundTripperOk` holds of every `H`: its
`RoundTrip` takes the host's registration (`httpProtoAt`), which ties `H` to the server. -/
axiom rafthttp.NewRoundTripper.wp_proof : rafthttp.NewRoundTripper.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
