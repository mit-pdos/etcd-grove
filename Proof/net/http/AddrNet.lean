/-
**An address reserved for HTTP, on the net extension** (2026-11-24, `notes/decisions.md`, "`http.reserve` fixes the
address's net protocols"; `notes/axiom-review/http-reserve-addrproto.md`). Lean-first.

`http.reserve` (`Proof/net/http/Axioms.lean`) promises every client of an address `a` (`httpProtoAt a P`, which
`RoundTrip` needs) answers of `a`'s HTTP protocol `P`, from before `a`'s listener exists. That holds only if nothing
but Go's net/http ever answers at `a`: a program that reserved `a` must not be able to serve `a` with raw net code.
Here the address's net protocols (the net extension's `addrProto`, `GooseLang/Ext/Net/Proto.lean`) are set, once, to
the opaque `httpNetCliP`/`httpNetSrvP` (trusted text with no law, as grpc's `grpcCliPI`/`grpcSrvPI`): no program but
net/http's own client and server (the HTTP boundary's axioms) writes or learns anything on a connection to `a`.

* `httpAddrNet a` (persistent): `a`'s net protocols are net/http's. What `reserve` needs.
* `httpAddrFree a` := `addrClaim a ∗ httpAddrNet a`: the right to listen at `a`, reserved for HTTP: what a member's
  `net.Listen` of its peer address takes (`net.Listen.specHttp`, `Spec/net/ListenHttp.lean`), in place of
  `netAddrFree a`, which setting the protocols consumed (`httpAddrFree_set`). Nothing gives `netAddrLeft a` for such an
  address, so no program sets `a`'s protocols to its own.
-/
module

public import Proof.net.InvNet

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace http

open Iris Iris.BI Net

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors}

/-- **What net/http's client writes on a connection to an address reserved for HTTP** (opaque, the net protocol of
the dialers of such an address). Opaque so that no program but net/http's client (`RoundTrip`, an axiom of the HTTP
boundary) writes on such a connection anything but nothing: a raw dialer cannot send a request to an HTTP address.
Trusted text, with no law (as `grpcCliPI`). -/
opaque httpNetCliP : Net.Proto GF := fun _ _ => iprop(True)

/-- **What net/http's server writes on a connection to an address reserved for HTTP** (opaque, as `httpNetCliP`: the
net protocol of the acceptors). A raw acceptor at such an address cannot answer a client, so the answers a client of
the address reads are its HTTP server's (`register`, `Serve_ok`). Trusted text, with no law. -/
opaque httpNetSrvP : Net.Proto GF := fun _ _ => iprop(True)

variable {hlc : HasLC} [hG : HeapGS hlc GF]

/-- **`a`'s net protocols are net/http's** (persistent; see the file header): the net extension's protocols of `a`, at
some registry of the net library, `httpNetCliP` for its dialers and `httpNetSrvP` for its acceptors. Set once per
address (`addr_set_proto` consumes `a`'s pending set), so no other protocols are ever `a`'s. -/
def httpAddrNet (a : GoString) : IProp GF :=
  iprop(∃ (_ : HasExt netExt) (π : NetProtoGS),
    addrProto (Gg := hG.goose_globalGS) (π := π) a httpNetCliP httpNetSrvP)

instance httpAddrNet_persistent (a : GoString) : Persistent (httpAddrNet (GF := GF) (hG := hG) a) := by
  unfold httpAddrNet; infer_instance

/-- **The right to listen at `a`, reserved for HTTP** (see the file header): the claim on `a`'s requests and `a`'s net
protocols net/http's. -/
def httpAddrFree (a : GoString) : IProp GF :=
  iprop(addrClaim a ∗ httpAddrNet (hG := hG) a)

/-- **Setting an address's net protocols to net/http's** (proved over the net extension: a fresh registry,
`netProto_alloc`, and `addr_set_proto`): the right to listen at `a` becomes the right to listen at it reserved for
HTTP. -/
theorem httpAddrFree_set (E : CoPset) (a : GoString) :
    ⊢ netAddrFree (hG := hG) a ={E}=∗ httpAddrFree (hG := hG) a := by
  iintro Hf
  unfold netAddrFree
  icases Hf with ⟨Hc, %hX, Hu⟩
  haveI : HasExt netExt := hX
  imod netProto_alloc (Gg := hG.goose_globalGS) E with ⟨%π, #Hreg⟩
  imod addr_set_proto (Gg := hG.goose_globalGS) E a httpNetCliP httpNetSrvP $$ Hreg Hu with #Hp
  imodintro
  unfold httpAddrFree httpAddrNet
  iframe Hc
  iexists hX, π
  iexact Hp

/-- `httpAddrFree a`'s net fact. -/
theorem httpAddrFree_net (a : GoString) :
    httpAddrFree (hG := hG) a ⊢ httpAddrFree (hG := hG) a ∗ httpAddrNet (hG := hG) a := by
  unfold httpAddrFree
  iintro ⟨Hc, #Hn⟩
  iframe Hc Hn

end defs

end http
end EtcdGrove
end Perennial
