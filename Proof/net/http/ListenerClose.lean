/-
**Closing a served listener, to listen on its address again** (the restart plan's R2a, 2026-11-02,
`notes/restart-plan.md`: a restarted member listens again on its peer address). Lean-first (no
Rocq counterpart).

DRAFT trust-boundary statements, not yet axioms: the proofs that need them take them as hypotheses
until the axiom review (the `axiom` skill) has checked them, with the old `http.Serve`'s handlers
still running after the close.

Until now an address is listened on once in a run: `net.Listen` consumes the right to listen at it for good
(for an address reserved for HTTP, `httpAddrFree a`, `net.Listen.specHttp`), and `register` turns the listener into
`httpListenerAt`, which `Serve` takes whole. Here:

* `registerClosable_spec`: the registration keeps a closing half, `httpListenerCloser l a P`, for
  the thread that will close the listener (the Go program keeps the listener; `http.Serve` runs on
  its own goroutine), and says the listener is an interface value with a dynamic type (`net.Listen`
  returns one with a `nil` error), whose `Close` method the program calls. As `register` (2026-11-24) it takes
  no `netAddrLeft a`: `httpProtoOwn a P` comes from `reserve`, which fixed `a`'s net protocols as net/http's, so no
  program holds anything that sets them (`notes/axiom-review/http-reserve-addrproto.md`).
* `ListenerClose_spec`: `l.Close()` with the closing half gives back the right to listen at the address
  reserved for HTTP (`httpAddrFree a`: the claim, and `a`'s net protocols still net/http's; never a fresh
  `netAddrFree a`, whose unset protocols a program could set to its own and then answer `a`'s clients with raw
  bytes, the hole of `notes/axiom-review/http-reserve-addrproto.md`) and the right to serve it with its
  protocol (`httpProtoOwn a P`). The protocol
  stays the address's (`httpProtoAt a P` is persistent): a later listener at `a` serves the same
  protocol. `Serve` then returns (its accept fails); the handlers it started keep running and keep
  what they borrowed, and (http-boundary-fix, second review, 2026-11-14) so do its connections: a
  client's keep-alive connection to the old `Serve` keeps starting new runs of the OLD handler
  after the close, also once a new listener at the same address serves another handler
  (`examples/premisefix/httpkeepalive`). A restart's review must account for those runs (the
  restart-boundary note of `notes/axiom-review/http-boundary-fix.md`).
-/
module

public import Proof.net.http.Boundary
public import Proof.net.InvNet
public import Proof.net.http.AddrNet

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace http

open Iris Iris.BI

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The right to close the served listener `l` at `a`, of protocol `P`** (exclusive, opaque;
DRAFT, see the file header). -/
opaque httpListenerCloser (l : GoInterface) (a : GoString) (P : Proto GF) : IProp GF

/-- **Registration with a closing half** (DRAFT; `register`'s, see the file header). -/
def registerClosable_spec : Prop :=
  ∀ (l : GoInterface) (a : GoString) (P : Proto GF),
    ⊢ netListenerAt (GF := GF) l a -∗ httpProtoOwn a P ==∗
      ⌜∃ li : GoInterfaceOk, l = GoInterface.ok li⌝ ∗ httpListenerAt l a P ∗
        httpListenerCloser l a P

/-- **`l.Close()` of a served listener** (DRAFT, see the file header): the right to listen at the
address, reserved for HTTP, and the right to serve it with its protocol back, whatever the error. -/
def ListenerClose_spec : Prop :=
  ∀ (l : GoInterface) (li : GoInterfaceOk) (a : GoString) (P : Proto GF),
    l = GoInterface.ok li →
    ⊢ {{ httpListenerCloser (GF := GF) l a P }}
        (App (Val #(methods li.ty go!"Close" li.v)) (Val #()))
      {{ (err : GoInterface), RET #err; httpAddrFree (hG := hG) a ∗ httpProtoOwn a P }}

end defs

end http
end EtcdGrove
end Perennial
