/-
`server.ServeHTTP(w, req)` (`server.go`), net/rpc's handler, as net/http's server calls it on a
`CONNECT` request (`reqHead`) whose head, the dialer's handshake `W.hs a`, it has read on the
acceptor's end of a connection `cn` dialed to `a`, with the right to hijack it through the response
`rp` (`hijackOk`, over `a`'s rpc protocols): it hijacks the connection, writes the handshake's
answer `W.hsAns a` (`connectAns`; the write's error is not looked at, as in Go: a cut answer leaves
the dialer without one, and the server reads no request, `rpcAccepted`), and serves it
(`ServeConn`), on a server whose registrations serve `a` (`srvServes`); and gives back what the
hijack gave for the server (`D`). A request of another method
is answered 405 in Go; net/http's server gives this handler only `CONNECT` requests of rpc dialers
(`reqProto`: their head is `connectReq path`). Proved in `Net/Proof/net/rpc/Server__ServeHTTP.lean`.
-/
module

public import Net.Proof.net.rpc.ServerDefs
public import Net.Proof.net.http.ServerDefs

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
abbrev Server.ServeHTTP.spec : Prop :=
  ∀ (s : Loc) (γs : GName) (C : CodecSpec GF) (W : RpcWorld GF) (a : GoString) (cn : Nat)
    (rp req : Loc) (D : IProp GF),
  {{ ⌜threadBound GF ≤ 2 ^ 31⌝ ∗ isServerAny s γs ∗ srvServes γs C W a ∗ srvEnv ∗ codecSet C ∗
      globalAddr net.rpc.connected ↦□ connectedStatus ∗ ⌜W.hs a ≠ [] ∧ W.hsAns a = connectAns⌝ ∗
      net.http.reqHead req go!"CONNECT" ∗
      net.http.hijackOk rp cn a (reqProto (Gg := hG.goose_globalGS) W a)
        (respProto (Gg := hG.goose_globalGS) W a) (W.hs a) D ∗ threadTok }}
    (App (App (Val (s @!! go.GoType.PointerType net.rpc.Server.ty @!! go!"ServeHTTP"))
      (Val #(interface.mkOk (go.GoType.PointerType net.http.response.ty) #rp))) (Val #req))
  {{ RET #(); threadTok ∗ D }}

end spec
end net.rpc
end Perennial
