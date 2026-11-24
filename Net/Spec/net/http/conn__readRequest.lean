/-
`c.readRequest(ctx)` (the model's `server.go`) on the first request of a connection `c` (served by
the default `Server` `s`, `srvDflt`; its last method not `POST`), whose dialer writes net/rpc's
`CONNECT` request (`headLaw P (connectReq path) Z`, `path` a `reqPath` of at most `2^20` bytes, so the
request is shorter than the head's read limit `srvL`): the connection not hijacked (`connMuInv`'s
ghost half at `false`), its reader `cr` in the main phase (`crMain` at no byte read) and its
buffered reader `br` fresh over it (`bufio.freshReader`). It sets the read limit, reads the head
through `br` (`readRequestLimit`, the reader in the head phase `crHead` at a fresh once-cell `γe`),
taking the response's buffered writer from net/http's writer pools (`wPools`), and returns:

* an error (`reqErr (crHeadErr γe) err`: the stream's, `io.EOF`'s `*errorString` or a read's
  `*OpError`, a `textproto.ProtocolError`, `io.ErrUnexpectedEOF`, or a `badStringError`; never
  `ErrHijacked`, `errTooLarge`, a `statusError` or a `badRequestError`), the reader still in the head
  phase at what it read; or
* the response `w` (`respNew w c req`) of the request `req` (`rrReqVal`: `CONNECT path HTTP/1.0`,
  its URL `u` of path `path`, an empty header `m`, no body, its context set, `RemoteAddr` the
  connection's `remoteAddr`) and `nil`, the reader back in the main phase past exactly the request,
  its read limit lifted (`maxInt64`), the end's read deadline cleared (or the end closed and its
  reading dead), and `c.lastMethod` `CONNECT`.

Either way the buffered reader is raw again (`conn.serve` puts it back in its pool), and `c`'s other
fields are as they were (`c.bufr` taken at any fraction and given back: `conn.serve` clears it after an
error). Proved in `Net/Proof/net/http/conn__readRequest.lean`.
-/
module

public import Net.Proof.net.http.ReadRequestDefs
public import Net.Proof.net.http.ConnReaderHead

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
abbrev conn.readRequest.spec : Prop :=
  ∀ (c s cr br : Loc) (γ : CrNames) (γh : GName) (t : Loc) (cn : Nat) (a : GoString)
    (la ra : GoInterface) (P Q : Proto GF) (Z : Nat → IProp GF) (path : List w8) (rmt lm : GoString)
    (v : w64) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (dq : DFrac),
  c ≠ null → reqPath path → path.length ≤ 2 ^ 20 → lm ≠ go!"POST" →
  {{ httpEnv ∗ readEnv ∗ isPkgInit (PROP := IProp GF) pkg_id.context ∗ srvConst s ∗ srvDflt s ∗ wPools ∗
      context.isContext ctx cd ∗ context.isCancelCtxCtx ctx cd ∗
      structFieldRef net.http.conn go!"server" c ↦□ s ∗
      structFieldRef net.http.conn go!"r" c ↦□ cr ∗
      structFieldRef net.http.conn go!"bufr" c ↦{dq} br ∗
      structFieldRef net.http.conn go!"rwc" c ↦□
        interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t ∗
      structFieldRef net.http.conn go!"remoteAddr" c ↦□ rmt ∗
      structFieldRef net.http.conn go!"tlsState" c ↦□ (null : Loc) ∗
      sync.isMutex (structFieldRef net.http.conn go!"mu" c) (connMuInv c γh) ∗
      ghostVar γh (1 : Qp).half false ∗
      structFieldRef net.http.conn go!"lastMethod" c ↦ lm ∗
      crIs cr γ cn P (net.rpc.connectReq path) Z ∗ headLaw P (net.rpc.connectReq path) Z ∗
      zLaw Z Q ∗ crConnOk c ∗
      structFieldRef net.http.connReader go!"rwc" cr ↦□
        interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t ∗
      connAt t cn true a la ra ∗ crMain cr γ cn P Q c [] v ∗
      EtcdGrove.bufio.freshReader br
        (interface.mkOk (go.GoType.PointerType net.http.connReader.ty) #cr) }}
    (App (Val (c @!! go.GoType.PointerType net.http.conn.ty @!! go!"readRequest"))
      (Val #(interface.ok ctx)))
  {{ (w : Loc) (err : GoInterface), RET (PairV #w #err);
      ghostVar γh (1 : Qp).half false ∗ EtcdGrove.bufio.rawReader br ∗
      structFieldRef net.http.conn go!"bufr" c ↦{dq} br ∗
      ((⌜err ≠ interface.nil⌝ ∗ structFieldRef net.http.conn go!"lastMethod" c ↦ lm ∗
          ∃ (γe : GName) (r : List w8), crHead cr γ γe cn P Q srvL c r ∗
            reqErr (crHeadErr γe) err) ∨
        (⌜err = interface.nil⌝ ∗ structFieldRef net.http.conn go!"lastMethod" c ↦ go!"CONNECT" ∗
          ∃ (req u m : Loc) (cl : Bool) (nb : net.http.noBody) (ctx' : GoInterface),
          req ↦ rrReqVal path u m cl nb ctx' rmt ∗
          u ↦ { (_root_.Perennial.zero_val net.url.URL) with Path' := path } ∗
          m ↦$ (∅ : GMap GoString GoSlice) ∗ respNew w c req ∗
          ghostVar γ.ph (1 : Qp).half false ∗
          (∃ ab : Bool,
            structFieldRef net.http.connReader go!"conn" cr ↦ c ∗
            structFieldRef net.http.connReader go!"hasByte" cr ↦ false ∗
            structFieldRef net.http.connReader go!"inRead" cr ↦ false ∗
            structFieldRef net.http.connReader go!"aborted" cr ↦ ab) ∗
          structFieldRef net.http.connReader go!"remain" cr ↦ W64 (2 ^ 63 - 1) ∗
          (∃ arr : GoArray w8 1, structFieldRef net.http.connReader go!"byteBuf" cr ↦ arr) ∗
          sendTok (Gg := hG.goose_globalGS) cn true Q [] ∗
          recvTok (Gg := hG.goose_globalGS) cn true P (net.rpc.connectReq path) ∗
          ∃ b : Bool, rdlTok (Gg := hG.goose_globalGS) cn true b ∗
            (⌜b = false⌝ ∨ readDead (Gg := hG.goose_globalGS) cn true))) }}

end spec

end net.http
end Perennial
