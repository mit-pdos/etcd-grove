/-
The vocabulary of `Server.Serve`'s spec (`Net/Spec/net/http/Server__Serve.lean`): net/http's accept
loop on a listener whose every address speaks net/rpc's `CONNECT` handshake, beside `ServeDefs.lean`'s
(`conn.serve`'s).

* `srvServeRest s`: the fields of the `Server` `s` that `Server.Serve` reads or writes besides
  `srvConst`'s, `srvDflt`'s and `srvServe`'s, as `http.Serve`'s `&Server{Handler: handler}` leaves
  them: no `TLSConfig`, `BaseContext`, `ConnContext` or `ErrorLog` (read-only), and, owned, the
  zero `nextProtoOnce` (`setupHTTP2_Serve`'s), `nextProtoErr` and `listenerGroup`
  (`trackListener`'s).
* `serveEnv` (persistent): net/http's `testHookServerServe` is `nil` (Go's zero value: only
  net/http's tests set it), and `DefaultServeMux` is `&defaultServeMux`.
* `srvAddr s a P Q path` (persistent): what `conn.serve` needs of an address `a` the listener takes,
  for a connection to it: the address's protocols `P` (the dialer's) and `Q` (the acceptor's,
  closed under prefixes), the dialer's head `CONNECT path` (`headLaw`, `zLaw`), Go's `400` allowed
  (`Q cn badReqAns`), and the server's handler on its request (`srvHandler`).
* `connHandler h cn a P Q path` (persistent): the handler `h`'s `ServeHTTP` on net/rpc's `CONNECT path`
  request read on the acceptor's end of `cn`, given the right to hijack (`hijackOk`) and the thread
  token, returns both: what `srvHandler` asks of the handler `serverHandler` calls (`h`, or
  `DefaultServeMux` for a `nil` `h`: `effHandler`).
* `srvAddrH h a P Q path`: `srvAddr` with the handler `h`'s contract in place of the server's
  (`http.Serve(l, h)`'s premise).
-/
module

public import Net.Proof.net.http.ServeDefs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace net.http

/-- The handler `serverHandler` calls for the server's `Handler` `h` (see the file header). -/
def effHandler [GooseExts] [GoGlobalContext] [GoSemanticsFunctions] (h : GoInterface) : GoInterface :=
  match h with
  | .nil => interface.mkOk (go.GoType.PointerType net.http.ServeMux.ty)
      #(globalAddr net.http.defaultServeMux)
  | .ok _ => h

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem' : net.http.Assumptions]
variable [π : NetProtoGS]

/-- See the file header. -/
def srvServeRest (s : Loc) : IProp GF :=
  iprop(structFieldRef net.http.Server go!"TLSConfig" s ↦□ (null : Loc) ∗
    structFieldRef net.http.Server go!"BaseContext" s ↦□ (func.nil : GoFunc) ∗
    structFieldRef net.http.Server go!"ConnContext" s ↦□ (func.nil : GoFunc) ∗
    structFieldRef net.http.Server go!"ErrorLog" s ↦□ (null : Loc) ∗
    structFieldRef net.http.Server go!"nextProtoOnce" s ↦
      (_root_.Perennial.zero_val sync.Once) ∗
    structFieldRef net.http.Server go!"nextProtoErr" s ↦ (interface.nil : GoInterface) ∗
    structFieldRef net.http.Server go!"listenerGroup" s ↦
      (_root_.Perennial.zero_val sync.WaitGroup))

/-- See the file header. -/
def serveEnv : IProp GF :=
  iprop(globalAddr net.http.testHookServerServe ↦□ (func.nil : GoFunc) ∗
    globalAddr net.http.DefaultServeMux ↦□ globalAddr net.http.defaultServeMux)

instance serveEnv_persistent : Persistent (serveEnv (GF := GF)) := by
  unfold serveEnv; infer_instance

/-- See the file header. -/
def srvAddr (s : Loc) (a : GoString) (P Q : Proto GF) (path : List w8) : IProp GF :=
  iprop(⌜ProtoPrefixClosed Q⌝ ∗ addrProto (Gg := hG.goose_globalGS) a P Q ∗
    (∃ Z : Nat → IProp GF, headLaw P (net.rpc.connectReq path) Z ∗ zLaw Z Q) ∗
    (□ ∀ cn : Nat, Q cn net.rpc.badReqAns) ∗ (□ ∀ cn : Nat, srvHandler s cn a P Q path))

instance srvAddr_persistent (s : Loc) (a : GoString) (P Q : Proto GF) (path : List w8) :
    Persistent (srvAddr (GF := GF) s a P Q path) := by
  unfold srvAddr; infer_instance

/-- See the file header. -/
def connHandler (h : GoInterface) (cn : Nat) (a : GoString) (P Q : Proto GF) (path : List w8) :
    IProp GF :=
  iprop(∃ ii : GoInterfaceOk, ⌜h = interface.ok ii⌝ ∗
    □ ∀ (rp req : Loc) (rv : net.http.Request) (u m : Loc) (cl : Bool) (nb : net.http.noBody)
      (ctx : GoInterface) (ra : GoString) (D : IProp GF) (Φ : val → IProp GF),
    (⌜rv = rrReqVal path u m cl nb ctx ra⌝ ∗ reqHead req go!"CONNECT" ∗ reqRest req rv ∗
      u ↦ { (_root_.Perennial.zero_val net.url.URL) with Path' := path } ∗
      m ↦$ (∅ : GMap GoString GoSlice) ∗
      hijackOk rp cn a P Q (net.rpc.connectReq path) D ∗ threadTok) -∗
    ▷ (threadTok ∗ D -∗ Φ #()) -∗
    WP (App (App (Val #(methods ii.ty go!"ServeHTTP" ii.v))
      (Val #(interface.mkOk (go.GoType.PointerType net.http.response.ty) #rp))) (Val #req))
      {{ Φ }})

instance connHandler_persistent (h : GoInterface) (cn : Nat) (a : GoString) (P Q : Proto GF)
    (path : List w8) : Persistent (connHandler (GF := GF) h cn a P Q path) := by
  unfold connHandler; infer_instance

/-- See the file header. -/
def srvAddrH (h : GoInterface) (a : GoString) (P Q : Proto GF) (path : List w8) : IProp GF :=
  iprop(⌜ProtoPrefixClosed Q⌝ ∗ addrProto (Gg := hG.goose_globalGS) a P Q ∗
    (∃ Z : Nat → IProp GF, headLaw P (net.rpc.connectReq path) Z ∗ zLaw Z Q) ∗
    (□ ∀ cn : Nat, Q cn net.rpc.badReqAns) ∗ (□ ∀ cn : Nat, connHandler (effHandler h) cn a P Q path))

instance srvAddrH_persistent (h : GoInterface) (a : GoString) (P Q : Proto GF) (path : List w8) :
    Persistent (srvAddrH (GF := GF) h a P Q path) := by
  unfold srvAddrH; infer_instance

end defs

end net.http
end Perennial
