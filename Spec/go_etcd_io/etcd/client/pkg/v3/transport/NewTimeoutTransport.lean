/-
`transport.NewTimeoutTransport(info, dialtimeoutd, rdtimeoutd, wtimeoutd)` (`timeout_transport.go`):
the trust boundary (`go.etcd.io/etcd/client/pkg/v3/transport` is names-only; the HTTP boundary's,
D39). rafthttp's round trippers (`NewRoundTripper`, `newStreamRoundTripper`, `util.go`) are this
call (rafthttpfix, 2026-11-20: until then each was an axiom of its own). Lean-first.
-/
module

public import Proof.net.http.Boundary
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Base
public import GeneratedProof.go_etcd_io.etcd.client.pkg.v3.transport
public import Proof.go_etcd_io.etcd.client.pkg.v3.transport.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.client.pkg.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`NewTimeoutTransport(info, dt, rd, wr)`**: an error, or an `*http.Transport` that is a round
tripper of any network `H` (`http.roundTripperOk`).

Against etcd's `client/pkg/transport/timeout_transport.go` (the fork's pin): `NewTransport(info, dt)`
(an `*http.Transport` with `info`'s TLS configuration, `info.ClientConfig()`, or the error of reading
its certificates),
`MaxIdleConnsPerHost` set, and its `Dial` a `rwTimeoutDialer` (a `net.Dialer` with the dial timeout,
whose connections set read and write deadlines `rd`, `wr` before each read and write when non-zero).
Go's `http.Transport` is a client of the HTTP boundary (`http.roundTripperOk`'s docstring: a
`RoundTrip` fails, with a `net/http` error, or returns the response a handler run of the request
wrote, or one the server made itself; a deadline only makes more `RoundTrip`s and reads fail, which
the predicate allows). (http-boundary-fix, 2026-11-14) Its `RoundTrip` replays a request Go deems
replayable (`http.onceOnly` false: a `GET`) on a reused connection whose response read fails, which
may run the request's handler twice: only a handler of a request never replayed receives the
request's ticket (`http.reqTicketOnce`), `examples/premisefix/httpreplay`. The ghost network `H`
does not enter the Go code, and `roundTripperOk` holds of every `H`: its `RoundTrip` takes the host's
registration (`httpProtoAt`), which ties `H` to the server.

(2026-11-25, `notes/axiom-review/transport-emptycn.md`) For a `TLSInfo` with no certificate and no
key file (`transport.tlsEmpty`, Go's `info.Empty()`), the only kind etcd's examples configure: its
`ClientConfig` loads no certificate (`transport.tlsEmpty`'s docstring). Until then the spec covered
every `TLSInfo`, false of Go in two ways: with `EmptyCN` set, `ClientConfig` reads the certificate file
a second time and dereferences `pem.Decode`'s block unchecked, so a file rewritten between the two reads
panics (`issues/etcd-transport-emptycn-cert-reread-panic.md`); and with a certificate and `AllowedCN`,
`baseConfig` logs a warning through `info.Logger`, which panics on a zero `&zap.Logger{}`. -/
abbrev transport.NewTimeoutTransport.spec : Prop :=
  ∀ (H : http.HttpNet GF) (info : go_etcd_io.etcd.client.pkg.v3.transport.TLSInfo) (dt rd wr : w64),
  transport.tlsEmpty info →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.transport }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.client.pkg.v3.transport.NewTimeoutTransport))
      (Val #info)) (Val #dt)) (Val #rd)) (Val #wr))
  {{ (tr : Loc) (err : GoInterface), RET (PairV #tr #err);
      ⌜err ≠ GoInterface.nil⌝ ∨ ⌜err = GoInterface.nil⌝ ∗
        http.roundTripperOk H (interface.mkOk (go.GoType.PointerType _root_.Perennial.net.http.Transport.ty) #tr) }}

end spec

end EtcdGrove
end Perennial
