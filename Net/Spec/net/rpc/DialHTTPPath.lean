/-
`DialHTTPPath(nw, a, path)` (`nw` `"tcp"` or `"tcp4"`) to an address `a` of world `W` serving net/rpc
over HTTP at `path` (`rpcAddrP W a (connectReq path) connectAns`: the dialer's handshake is the
`CONNECT` request, the acceptor's its `200` answer): `net.Dial` (the library's `dial_rdl_au`), the
connection registered in `W`, the `CONNECT` request written (its error ignored, as Go does), the
answer read with `http.ReadResponse` over a `bufio.Reader` of the connection (no byte after a read
error: the net extension's D1 v3.5, the dialer setting no read deadline), and on the status `"200 Connected to Go RPC"`
`NewClient`: a client of `a`, its reader just after the answer (the acceptor writes nothing more
before a request, and nothing before the whole request is written: `respProto`); or an error (the
dial's, or the `*OpError` `"dial-http"` wrapping the answer's, with its `Error()`, `errAny`).
`httpEnv` is what the answer's read needs of the package's state (`http.ReadResponse.spec`);
`isPkgInit net` (net's initialization: net/rpc has no initialization proof) gives `internal/poll`'s,
which `Conn.Read` takes (since the Go-model overlays S6: Go's `conn.Read` compares with `io.EOF`).
Proved in `Net/Proof/net/rpc/DialHTTPPath.lean`, over `http.ReadResponse.spec`.
-/
module

public import Net.Proof.net.rpc.ClientDefs
public import Net.Spec.net.http.ReadResponse

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace net.rpc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions]
variable [π : NetProtoGS]

/-- See the file header. -/
abbrev DialHTTPPath.spec : Prop :=
  ∀ (nw : GoString), net.tcpNet nw → ∀ (W : RpcWorld GF) (a path : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net ∗ ⌜receiptBound GF ≤ 2 ^ 64⌝ ∗ cliEnv ∗ net.http.httpEnv ∗
      globalAddr net.rpc.connected ↦□ connectedStatus ∗
      rpcAddrP (Gg := hG.goose_globalGS) W a (connectReq path) connectAns }}
    (App (App (App (Val (@! net.rpc.DialHTTPPath)) (Val #nw)) (Val #a)) (Val #path))
  {{ (c : Loc) (err : GoInterface), RET (PairV #c #err);
      (⌜err = interface.nil⌝ ∗ isClient c W a) ∨
      (⌜err ≠ interface.nil⌝ ∗ models_lab.errAny err) }}

end spec

end net.rpc
end Perennial
