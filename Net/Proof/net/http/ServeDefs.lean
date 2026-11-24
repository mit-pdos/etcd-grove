/-
The vocabulary of `conn.serve`'s spec (`Net/Spec/net/http/conn__serve.lean`): net/http's server
serving one connection whose dialer speaks net/rpc's `CONNECT` handshake, up to the handler's
hijack, beside `ReadRequestDefs.lean`'s.

* `connNew c s t`: the connection `c` as `Server.Serve` leaves it (`newConn(rw)`, then
  `setState(StateNew)`): its server `s` and its `*TCPConn` `t` (read-only from then on), the other
  fields zero, its state word owned.
* `srvServe s` (persistent): the fields of the `Server` `s` that `conn.serve` reads besides
  `srvDflt`'s, as `http.Serve`'s `&Server{Handler: handler}` leaves them: no `ReadHeaderTimeout`, no
  `Protocols`, no `TLSNextProto`, and never shut down (`inShutdown` false, nobody calls `Shutdown`).
* `reqRest req rv`: the fields of the request `req` other than `Method` and `RemoteAddr` (which
  `reqHead` gives, persistent), at `rv`'s values.
* `ctxKeys` (persistent): `ServerContextKey` and `LocalAddrContextKey` hold pointers (Go's
  `&contextKey{"http-server"}`, `&contextKey{"local-addr"}`; their initializers are not translated, so
  this is a premise, as `httpEnv`, discharged where the package initializer is).
* `SprintfOut_noVerb`: a format without `%`, and no arguments, prints as itself (`conn.serve`'s
  `fmt.Fprintf(c.rwc, "HTTP/1.1 400 Bad Request…")`).
* `srvHandler s cn a P Q path` (persistent): `serverHandler{s}.ServeHTTP(w, req)` on net/rpc's
  `CONNECT path` request (`rrReqVal`, its URL and empty header) read on the acceptor's end of `cn`
  (dialed to `a`), given the right to hijack (`hijackOk`, with evidence `D`) and the thread token,
  returns both. For `http.Serve(l, nil)` it is `DefaultServeMux`'s dispatch to net/rpc's handler
  (`rpcHjHandler`), proved over the mux.
-/
module

public import Net.Proof.net.http.ReadRequestDefs
public import Net.Proof.context.CtxBg
public import Perennial.Proof.fmt.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace net.http

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem' : net.http.Assumptions]
variable [π : NetProtoGS]

/-- See the file header. -/
def connNew (c s t : Loc) : IProp GF :=
  iprop(structFieldRef net.http.conn go!"server" c ↦□ s ∗
    structFieldRef net.http.conn go!"rwc" c ↦□
      interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t ∗
    structFieldRef net.http.conn go!"cancelCtx" c ↦ (func.nil : GoFunc) ∗
    structFieldRef net.http.conn go!"remoteAddr" c ↦ ([] : GoString) ∗
    structFieldRef net.http.conn go!"tlsState" c ↦ (null : Loc) ∗
    structFieldRef net.http.conn go!"werr" c ↦ (interface.nil : GoInterface) ∗
    structFieldRef net.http.conn go!"r" c ↦ (null : Loc) ∗
    structFieldRef net.http.conn go!"bufr" c ↦ (null : Loc) ∗
    structFieldRef net.http.conn go!"bufw" c ↦ (null : Loc) ∗
    structFieldRef net.http.conn go!"lastMethod" c ↦ ([] : GoString) ∗
    sync.atomic.ownPointer (T' := net.http.response)
      (structFieldRef net.http.conn go!"curReq" c) (DFrac.own 1) null ∗
    (∃ v : w64, sync.atomic.ownUint64 (structFieldRef net.http.conn go!"curState" c)
      (DFrac.own 1) v) ∗
    structFieldRef net.http.conn go!"mu" c ↦ (_root_.Perennial.zero_val sync.Mutex) ∗
    structFieldRef net.http.conn go!"hijackedv" c ↦ false)

/-- See the file header. -/
def srvServe (s : Loc) : IProp GF :=
  iprop(structFieldRef net.http.Server go!"ReadHeaderTimeout" s ↦□ (W64 0) ∗
    structFieldRef net.http.Server go!"Protocols" s ↦□ (null : Loc) ∗
    structFieldRef net.http.Server go!"TLSNextProto" s ↦□ (map.nil : GoMap) ∗
    sync.atomic.ownBool (structFieldRef net.http.Server go!"inShutdown" s) DFrac.discard false)

instance srvServe_persistent (s : Loc) : Persistent (srvServe (GF := GF) s) := by
  unfold srvServe
  rw [sync.atomic.ownBool_unseal]; unfold sync.atomic.ownBoolDef
  infer_instance

/-- See the file header. -/
def reqRest (req : Loc) (rv : net.http.Request) : IProp GF :=
  iprop(structFieldRef net.http.Request go!"URL" req ↦ rv.URL' ∗
    structFieldRef net.http.Request go!"Proto" req ↦ rv.Proto' ∗
    structFieldRef net.http.Request go!"ProtoMajor" req ↦ rv.ProtoMajor' ∗
    structFieldRef net.http.Request go!"ProtoMinor" req ↦ rv.ProtoMinor' ∗
    structFieldRef net.http.Request go!"Header" req ↦ rv.Header' ∗
    structFieldRef net.http.Request go!"Body" req ↦ rv.Body' ∗
    structFieldRef net.http.Request go!"GetBody" req ↦ rv.GetBody' ∗
    structFieldRef net.http.Request go!"ContentLength" req ↦ rv.ContentLength' ∗
    structFieldRef net.http.Request go!"TransferEncoding" req ↦ rv.TransferEncoding' ∗
    structFieldRef net.http.Request go!"Close" req ↦ rv.Close' ∗
    structFieldRef net.http.Request go!"Host" req ↦ rv.Host' ∗
    structFieldRef net.http.Request go!"Form" req ↦ rv.Form' ∗
    structFieldRef net.http.Request go!"PostForm" req ↦ rv.PostForm' ∗
    structFieldRef net.http.Request go!"MultipartForm" req ↦ rv.MultipartForm' ∗
    structFieldRef net.http.Request go!"Trailer" req ↦ rv.Trailer' ∗
    structFieldRef net.http.Request go!"RequestURI" req ↦ rv.RequestURI' ∗
    structFieldRef net.http.Request go!"TLS" req ↦ rv.TLS' ∗
    structFieldRef net.http.Request go!"Cancel" req ↦ rv.Cancel' ∗
    structFieldRef net.http.Request go!"Response" req ↦ rv.Response' ∗
    structFieldRef net.http.Request go!"Pattern" req ↦ rv.Pattern' ∗
    structFieldRef net.http.Request go!"ctx" req ↦ rv.ctx' ∗
    structFieldRef net.http.Request go!"pat" req ↦ rv.pat' ∗
    structFieldRef net.http.Request go!"matches" req ↦ rv.matches' ∗
    structFieldRef net.http.Request go!"otherValues" req ↦ rv.otherValues')

/-- See the file header. -/
def ctxKeys : IProp GF :=
  iprop(∃ sk lk : Loc, globalAddr net.http.ServerContextKey ↦□ sk ∗
    globalAddr net.http.LocalAddrContextKey ↦□ lk)

instance ctxKeys_persistent : Persistent (ctxKeys (GF := GF)) := by
  unfold ctxKeys; infer_instance

/-- See the file header. -/
def srvHandler (s : Loc) (cn : Nat) (a : GoString) (P Q : Proto GF) (path : List w8) : IProp GF :=
  iprop(□ ∀ (rp req : Loc) (rv : net.http.Request) (u m : Loc) (cl : Bool) (nb : net.http.noBody)
      (ctx : GoInterface) (ra : GoString) (D : IProp GF) (Φ : val → IProp GF),
    (⌜rv = rrReqVal path u m cl nb ctx ra⌝ ∗ reqHead req go!"CONNECT" ∗ reqRest req rv ∗
      u ↦ { (_root_.Perennial.zero_val net.url.URL) with Path' := path } ∗
      m ↦$ (∅ : GMap GoString GoSlice) ∗
      hijackOk rp cn a P Q (net.rpc.connectReq path) D ∗ threadTok) -∗
    ▷ (threadTok ∗ D -∗ Φ #()) -∗
    WP (App (App (Val #(methods net.http.serverHandler.ty go!"ServeHTTP"
        #(net.http.serverHandler.mk s)))
      (Val #(interface.mkOk (go.GoType.PointerType net.http.response.ty) #rp))) (Val #req))
      {{ Φ }})

instance srvHandler_persistent (s : Loc) (cn : Nat) (a : GoString) (P Q : Proto GF)
    (path : List w8) : Persistent (srvHandler (GF := GF) s cn a P Q path) := by
  unfold srvHandler; infer_instance

end defs

/-- See the file header. -/
theorem SprintfOut_noVerb [GooseExts] [GoGlobalContext] [GoSemanticsFunctions] :
    ∀ {f out : GoString}, (∀ c ∈ f, c ≠ W8 37) → fmt.SprintfOut f [] out → out = f
  | [], _, _, h => fmt.SprintfOut.done_inv h
  | c :: f, out, hf, h => by
    obtain ⟨out', rfl, h'⟩ := fmt.SprintfOut.byte_inv (hf c (List.mem_cons_self ..)) h
    rw [SprintfOut_noVerb (fun c' hc' => hf c' (List.mem_cons_of_mem _ hc')) h']

end net.http
end Perennial
