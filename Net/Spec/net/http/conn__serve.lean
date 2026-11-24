/-
`c.serve(ctx)` (the model's `server.go`), the goroutine `Server.Serve` starts for a connection it
accepted (`connNew c s t`: `newConn`, `setState(StateNew)`), served by `http.Serve`'s server `s`
(`srvDflt`, `srvServe`), with `ctx` `Background()` or `*valueCtx`s over it (`context.ctxBg`), on the acceptor's
end of the connection `cn` dialed to `a`, nothing read or written yet, whose dialer writes net/rpc's
`CONNECT path` request (`headLaw P (connectReq path) Z`, `path` a `reqPath` of at most `2^20` bytes)
and nothing past it before the answer (`zLaw Z Q`). It reads the request (`conn.readRequest`):
* on an error it answers Go's `400` (`Q` must allow `badReqAns`: net/rpc's `respProto`'s `hsErr`), or
  nothing (the stream's `io.EOF` or a read `*OpError`: `isCommonNetReadError`), and closes the
  connection: never `431` (`errTooLarge`), `501` or a `statusError`'s answer, which `readRequest`
  never returns on such a stream;
* on the request it runs the server's handler (`srvHandler`: for `http.Serve(l, nil)` the mux's net/rpc
  handler), giving it the right to hijack the connection (`hijackOk`, from `response.Hijack.spec`),
  which it uses; then it returns, the connection the handler's.
Either way it returns the thread token the handler needs (`go c.serve(ctx)`'s).
Proved in `Net/Proof/net/http/conn__serve.lean`.
-/
module

public import Net.Proof.net.http.ServeDefs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace net.http

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem' : net.http.Assumptions]
variable [π : NetProtoGS]

/-- See the file header. -/
abbrev conn.serve.spec : Prop :=
  ∀ (c s t : Loc) (cn : Nat) (a : GoString) (la ra : GoInterface) (P Q : Proto GF)
    (Z : Nat → IProp GF) (path : List w8) (ctx : GoInterfaceOk),
  c ≠ null → reqPath path → path.length ≤ 2 ^ 20 → ProtoPrefixClosed Q →
  {{ httpEnv ∗ readEnv ∗ isPkgInit (PROP := IProp GF) pkg_id.context ∗ srvConst s ∗ srvDflt s ∗
      srvServe s ∗ ctxKeys ∗ wPools ∗ rPool ∗ (∃ tm : time.Time, globalAddr net.http.aLongTimeAgo ↦□ tm) ∗
      context.ctxBg ctx ∗ connNew c s t ∗
      connAt t cn true a la ra ∗ sendTok (Gg := hG.goose_globalGS) cn true Q [] ∗
      recvTok (Gg := hG.goose_globalGS) cn true P [] ∗ connFresh (Gg := hG.goose_globalGS) cn true ∗
      rdlTok (Gg := hG.goose_globalGS) cn true false ∗
      headLaw P (net.rpc.connectReq path) Z ∗ zLaw Z Q ∗ (□ Q cn net.rpc.badReqAns) ∗
      srvHandler s cn a P Q path ∗ threadTok }}
    (App (Val (c @!! go.GoType.PointerType net.http.conn.ty @!! go!"serve"))
      (Val #(interface.ok ctx)))
  {{ RET #(); threadTok }}

end spec

end net.http
end Perennial
