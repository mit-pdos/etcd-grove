/-
**Closing a served listener, to listen on its address again** (the restart plan's R2a, 2026-11-02,
`notes/restart-plan.md`: a restarted member listens again on its peer address). Lean-first (no
Rocq counterpart).

DRAFT trust-boundary statements, not yet axioms: the proofs that need them take them as hypotheses
until the axiom review (the `axiom` skill) has checked them, with the old `http.Serve`'s handlers
still running after the close.

Until now an address is listened on once in a run: `net.Listen` consumes `netAddrFree a` for good
(`Proof/net/InvNet.lean`), and `register` turns the listener into `httpListenerAt`, which `Serve`
takes whole. Here:

* `registerClosable_spec`: the registration keeps a closing half, `httpListenerCloser l a P`, for
  the thread that will close the listener (the Go program keeps the listener; `http.Serve` runs on
  its own goroutine).
* `ListenerClose_spec`: `l.Close()` with the closing half gives back the address
  (`netAddrFree a`) and the right to serve it with its protocol (`httpProtoOwn a P`). The protocol
  stays the address's (`httpProtoAt a P` is persistent): a later listener at `a` serves the same
  protocol. `Serve` then returns (its accept fails); the handlers it started keep running and keep
  what they borrowed.
-/
module

public import Proof.net.http.Boundary
public import Proof.net.InvNet

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
      httpListenerAt l a P ∗ httpListenerCloser l a P

/-- **`l.Close()` of a served listener** (DRAFT, see the file header): the address and the right
to serve it with its protocol back, whatever the error. -/
def ListenerClose_spec : Prop :=
  ∀ (l : GoInterface) (li : GoInterfaceOk) (a : GoString) (P : Proto GF),
    l = GoInterface.ok li →
    ⊢ {{ httpListenerCloser (GF := GF) l a P }}
        (App (Val #(methods li.ty go!"Close" li.v)) (Val #()))
      {{ (err : GoInterface), RET #err; netAddrFree a ∗ httpProtoOwn a P }}

end defs

end http
end EtcdGrove
end Perennial
