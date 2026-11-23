/-
The vocabulary of a net/http handler's specs (the model's server, `models/net/http/server.go`), for
net/rpc's `Server.ServeHTTP` (2026-11-23): what the server gives a handler of a request whose head
it has read, on the acceptor's end of a connection `cn` dialed to `a` (its protocols `P`, what the
dialer writes, and `Q`, what the acceptor writes).
* `reqHead req m` (persistent): the request `req`'s `Method` is `m`, and its `RemoteAddr` is set.
* `hijackOk rp cn a P Q hs D`: the right to hijack the connection through the response `rp` (a
  `*response`): `rp.Hijack()` returns the connection (`*TCPConn`, the acceptor's end of `cn`) with
  nothing written and exactly the head `hs` read (the server's buffered reader holds nothing more:
  no dialer byte past its head before an answer, the protocol's fact), its fresh token, and `D`,
  what the server gets back from the handler (2026-11-23: the evidence that the connection was
  hijacked, which `conn.serve` needs after the handler returns; a handler's spec returns it).
  Stated as the weakest precondition of the call, which net/http's `conn.serve` gives the handler
  (`response.Hijack.spec`).
-/
module

public import Net.Proof.net.http.Defs
public import Net.Proof.net.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace net.http

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [π : NetProtoGS]

/-- See the file header. -/
def reqHead (req : Loc) (m : GoString) : IProp GF :=
  iprop(structFieldRef net.http.Request go!"Method" req ↦□ m ∗
    ∃ ra : GoString, structFieldRef net.http.Request go!"RemoteAddr" req ↦□ ra)

instance reqHead_persistent (req : Loc) (m : GoString) : Persistent (reqHead (GF := GF) req m) := by
  unfold reqHead; infer_instance

/-- See the file header. -/
def hijackOk (rp : Loc) (cn : Nat) (a : GoString) (P Q : Proto GF) (hs : List w8) (D : IProp GF) :
    IProp GF :=
  iprop(∀ Φ : val → IProp GF,
    (∀ (t : Loc) (la ra : GoInterface) (bw : Loc),
      net.connAt (GF := GF) t cn true a la ra -∗
      sendTok (Gg := hG.goose_globalGS) cn true Q [] -∗
      recvTok (Gg := hG.goose_globalGS) cn true P hs -∗
      connFresh (Gg := hG.goose_globalGS) cn true -∗ D -∗
      Φ (PairV (PairV #(interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t) #bw)
        #(interface.nil : GoInterface))) -∗
    WP (App (Val #(methods (go.GoType.PointerType net.http.response.ty) go!"Hijack" #rp)) (Val #()))
      {{ Φ }})

end defs

end net.http
end Perennial
