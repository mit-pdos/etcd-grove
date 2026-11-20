/-
The protocol vocabulary of the lab's model of `net/http` (`harness/rpcmodel/src/net/http`,
`notes/craq-net.md`, "rpc specs"): what a client of an address served by `ListenAndServe` writes
first, and what a handler registered for a path must do with a connection.

* `connectHead p`: the request head a client of path `p` writes, `"CONNECT " ++ p ++ "
  HTTP/1.0\n\n"` (net/rpc's `DialHTTPPath`). The model's `readHead` reads it up to its blank
  line and `parseRequestLine` gives the method `"CONNECT"` and the URI `p`.
* `httpReqP p Pb`: the protocol of the bytes a dialer of an address writes, when the address
  serves `p`: a prefix of `connectHead p`, or `connectHead p` followed by bytes `rest` with
  `Pb cid rest` (the protocol of what follows the head, for the handler). An address's
  protocols are fixed once, for every party (`addrProto`, set from the start resources), so a
  client and the server of an address cannot use different protocols.
* `respWriter w c`: the `ResponseWriter` the model's `serveConn` hands a handler (`*response`
  over the connection `c`, nothing written, not hijacked), owned by the handler during the call
  and handed back (`respWriterBack`), since `serveConn` reads `hijacked` after the handler
  returns.
* `handlerOk h p Pb Q` (persistent): the handler `h` (a non-nil `Handler`) serves any
  connection end accepted on an address with protocols `httpReqP p Pb` / `Q` whose head
  `connectHead p` has been read, nothing written, given the request `{CONNECT, p}`.
-/
module

public import Harness.Proof.net.http.Base

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std NetConn


namespace net.http

/-- The request head a client of path `p` writes (net/rpc's `DialHTTPPath`). -/
def connectHead (p : GoString) : GoString := go!"CONNECT " ++ p ++ go!" HTTP/1.0\n\n"

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netConnExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF]

/-- The protocol of what a dialer of an address serving path `p` writes: a prefix of
`connectHead p`, or `connectHead p` and then bytes meeting `Pb`. -/
def httpReqP (p : GoString) (Pb : Proto GF) : Proto GF := fun cid bs =>
  iprop(⌜bs <+: connectHead p⌝ ∨ ∃ rest, ⌜bs = connectHead p ++ rest⌝ ∗ Pb cid rest)

end defs

section handler
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netConnExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [net.Assumptions] [net.model.Assumptions] [net.http.Assumptions]

/-- The `ResponseWriter` `w` that `serveConn` passes a handler: a `*response` over the
connection `c` (a `*TCPConn` as a `net.Conn`), nothing written, not hijacked. -/
def respWriter (w : GoInterface) (c : Loc) : IProp GF :=
  iprop(∃ l : Loc, ⌜w = interface.mkOk (go.GoType.PointerType net.http.response.ty) #l⌝ ∗
    l ↦ (net.http.response.mk (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #c)
      false false))

/-- The `*response` behind `w`, in whatever state the handler left it. -/
def respWriterBack (w : GoInterface) : IProp GF :=
  iprop(∃ (l : Loc) (v : net.http.response),
    ⌜w = interface.mkOk (go.GoType.PointerType net.http.response.ty) #l⌝ ∗ l ↦ v)

/-- The handler `h` serves path `p` of an address whose dialers write `httpReqP p Pb` and whose
acceptors write `Q` (persistent): called by `serveConn` with the acceptor's end `c` of `cid`,
the head read (`recvTok … (connectHead p)`), nothing written, the end's fresh token, and the
request `{CONNECT, p}`. -/
def handlerOk (h : GoInterfaceOk) (p : GoString) (Pb Q : Proto GF) : IProp GF :=
  iprop(□ ∀ (w : GoInterface) (req c : Loc) (cid : w64) (Φ : val → IProp GF),
    isPkgInit (PROP := IProp GF) pkg_id.net.http -∗
    respWriter w c -∗ req ↦ (net.http.Request.mk go!"CONNECT" p) -∗
    net.ownTCPConn c cid true -∗
    recvTok cid true (httpReqP p Pb) (connectHead p) -∗ sendTok cid true Q [] -∗
    connFresh cid true -∗
    ▷ (respWriterBack w -∗ Φ #()) -∗
    WP (App (App (Val #(methods h.ty go!"ServeHTTP" h.v)) (Val #w)) (Val #req)) {{ Φ }})

/-- `(*response).Hijack()` on a response not hijacked: its connection and no error; the response
is hijacked (what a handler that takes over the connection calls; proved in `Handler.lean`). -/
abbrev response.Hijack.spec : Prop :=
  ∀ (l : Loc) (cv : GoInterface) (wh : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.http ∗ l ↦ net.http.response.mk cv wh false }}
    (App (Val #(methods (go.GoType.PointerType net.http.response.ty) go!"Hijack" #l)) (Val #()))
  {{ RET (PairV #cv #interface.nil); l ↦ net.http.response.mk cv wh true }}

instance handlerOk_persistent (h : GoInterfaceOk) (p : GoString) (Pb Q : Proto GF) :
    Persistent (handlerOk (GF := GF) h p Pb Q) := by
  unfold handlerOk; infer_instance

end handler

end net.http

end Perennial
