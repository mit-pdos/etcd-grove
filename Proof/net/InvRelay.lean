/-
**A relay: a listener whose connections only carry another address's bytes** (2026-10-21,
`notes/decisions.md` D26, proposed; `notes/client-cut-plan.md` K1; Lean-first, no Rocq
counterpart). The trust boundary of etcd's test bridge (`third_party/bridge`), which linkv3p puts
between each client and its member: it accepts at a bridge address `a`, dials the member's
address `b` once per accepted connection, and copies bytes between the two, both ways, or drops
them. Perennial has no network model and gRPC's wire protocol is not modeled, so what a client at
`a` reaches is a trust-boundary fact, **`grpc.relay`**: once a listener at `a` is given up to a
relay to `b`, `a` serves, method by method, what `b` serves (`grpcServes`, `InvGrpc.lean`).

The fact holds only of a program that relays, so the specs of the calls on a relay's connections
enforce relaying: each connection accepted on the listener (`relayFresh`) is paired with one
connection dialed to `b` (`netDialed`, `relayPair`), giving the two directions of the bridged
connection, `relayDir l s t rd wr` (exclusive: the bytes `rd` read from `s`, the bytes `wr`
written to `t`), and a `Write` to `t` must keep `wr` a prefix of `rd`. Nothing else reads or
writes a relay's connections. A prefix of the peer's bytes is what a slow or cut connection
delivers anyway; why that is all `grpc.relay` needs of gRPC (complete, length-prefixed frames;
a unary call succeeds only on a complete response and its trailers; a request is handled only
complete, and at most once: D21j) is D26's.

* `netConnOk c` (persistent): `c` is a connection `net`'s `Accept` or `Dial` returned; its
  `Close` returns, from any thread, any number of times (as Go's `net.Conn` allows).
* `relayListener l b` (persistent): `l` is a relay's listener, to `b`; its `Accept` and `Close`
  return, from any thread.
* `relayFresh l c` (exclusive): `c` was accepted on `l` and is not yet paired.
* `netDialed d b` (exclusive): `d` was dialed to `b` and is not yet paired.
* `relayDir l s t rd wr` (exclusive): the direction `s` to `t` of a connection bridged by `l`'s
  relay, with the bytes read from `s` and written to `t` so far.
-/
module

public import Proof.net.InvNet
public import Proof.google_golang_org.grpc.InvGrpc

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

/-- **`c` is a connection `net` returned** (persistent; see the file header). -/
axiom netConnOk {GF : BundledGFunctors} [FfiSyntax] (c : GoInterfaceOk) : IProp GF

axiom netConnOk_persistent {GF : BundledGFunctors} [FfiSyntax] (c : GoInterfaceOk) :
  Persistent (netConnOk (GF := GF) c)

attribute [instance] netConnOk_persistent

/-- **`l` is a relay's listener, to `b`** (persistent; see the file header). -/
axiom relayListener {GF : BundledGFunctors} [FfiSyntax] (l : GoInterfaceOk) (b : GoString) :
  IProp GF

axiom relayListener_persistent {GF : BundledGFunctors} [FfiSyntax] (l : GoInterfaceOk)
    (b : GoString) : Persistent (relayListener (GF := GF) l b)

attribute [instance] relayListener_persistent

/-- **`c` was accepted on the relay's listener `l`, not yet paired** (exclusive). -/
axiom relayFresh {GF : BundledGFunctors} [FfiSyntax] (l c : GoInterfaceOk) : IProp GF

/-- **`d` was dialed to `b`, not yet paired** (exclusive). -/
axiom netDialed {GF : BundledGFunctors} [FfiSyntax] (d : GoInterfaceOk) (b : GoString) : IProp GF

/-- **The direction `s` to `t` of a connection bridged by `l`'s relay, the bytes `rd` read from
`s` and `wr` written to `t`** (exclusive; see the file header). -/
axiom relayDir {GF : BundledGFunctors} [FfiSyntax] (l s t : GoInterfaceOk) (rd wr : List w8) :
  IProp GF

section specs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **Trust boundary: the forwarding fact** (D26, proposed). A listener bound at `a`, given up
to a relay to `b`, makes `a` serve what `b` serves, method by method: a client's connection to
`a` reaches `b`'s server through a relay that only passes on a prefix of each side's bytes,
which gRPC sees as the same server, or as a cut connection (an attempt's error). -/
axiom grpc.relay (l : GoInterface) (a b : GoString) :
  netListenerAt (GF := GF) l a ⊢ |==> ∃ lo : GoInterfaceOk, ⌜l = interface.ok lo⌝ ∗
    relayListener lo b ∗
    □ (∀ (name : GoString) (mh : val) (srv : GoInterface) (ics : List GoFunc) (S : IProp GF),
        grpcServes b name mh srv ics S -∗ grpcServes a name mh srv ics S)

/-- **Trust boundary: `l.Accept()` on a relay's listener** returns a connection, fresh, or an
error (the listener closed). -/
axiom relay.Accept (l : GoInterfaceOk) (b : GoString) :
  {{ relayListener (GF := GF) l b }}
    (App (Val #(methods l.ty go!"Accept" l.v)) (Val #()))
  {{ (c err : GoInterface), RET (PairV #c #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ co : GoInterfaceOk, ⌜c = interface.ok co⌝ ∗ netConnOk co ∗
        relayFresh l co) ∨ ⌜err ≠ GoInterface.nil⌝ }}

/-- **Trust boundary: `l.Close()` on a relay's listener** returns (a blocked `Accept` then
returns an error). -/
axiom relay.ListenerClose (l : GoInterfaceOk) (b : GoString) :
  {{ relayListener (GF := GF) l b }}
    (App (Val #(methods l.ty go!"Close" l.v)) (Val #()))
  {{ (err : GoInterface), RET #err; True }}

/-- **Trust boundary: `c.Close()` on a connection `net` returned** returns, from any thread, any
number of times (a blocked `Read` or `Write` then returns an error). -/
axiom net.ConnClose (c : GoInterfaceOk) :
  {{ netConnOk (GF := GF) c }}
    (App (Val #(methods c.ty go!"Close" c.v)) (Val #()))
  {{ (err : GoInterface), RET #err; True }}

/-- **Trust boundary: pairing** an accepted connection with one dialed to the relay's address
gives the two directions of the bridged connection, nothing read or written yet. -/
axiom relay.pair (l c d : GoInterfaceOk) (b : GoString) :
  relayListener (GF := GF) l b ∗ relayFresh l c ∗ netDialed d b ⊢ |==>
    relayDir l c d [] [] ∗ relayDir l d c [] []

/-- **Trust boundary: `s.Read(buf)`** on the source of a relay's direction (Go's `io.Reader`
contract): it returns `n` and an error, `n` at most the buffer's length, the buffer's first `n`
bytes the ones read, which extend `rd`. -/
axiom relay.Read (l s t : GoInterfaceOk) (rd wr : List w8) (buf : GoSlice) (bs : List w8) :
  {{ relayDir (GF := GF) l s t rd wr ∗ buf ↦* bs }}
    (App (Val #(methods s.ty go!"Read" s.v)) (Val #buf))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
      ∃ bs' : List w8, buf ↦* bs' ∗ ⌜bs'.length = bs.length ∧ 0 ≤ sint.Z n ∧ sint.nat n ≤ bs.length⌝ ∗
        relayDir l s t (rd ++ bs'.take (sint.nat n)) wr }}

/-- **Trust boundary: `t.Write(buf)`** on the destination of a relay's direction (Go's
`io.Writer` contract), of bytes that keep what was written a prefix of what was read: it returns
`nw` and an error, `nw` at most the buffer's length, the first `nw` bytes written. -/
axiom relay.Write (l s t : GoInterfaceOk) (rd wr : List w8) (buf : GoSlice) (dq : DFrac)
    (bs : List w8) :
  {{ relayDir (GF := GF) l s t rd wr ∗ buf ↦*{dq} bs ∗ ⌜wr ++ bs <+: rd⌝ }}
    (App (Val #(methods t.ty go!"Write" t.v)) (Val #buf))
  {{ (nw : w64) (err : GoInterface), RET (PairV #nw #err);
      buf ↦*{dq} bs ∗ ⌜0 ≤ sint.Z nw ∧ sint.nat nw ≤ bs.length⌝ ∗
        relayDir l s t rd (wr ++ bs.take (sint.nat nw)) }}

end specs

end EtcdGrove
end Perennial
