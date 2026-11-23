/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Proto/Wire.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Gryff's wire protocol on a replica's port (`gryffP`, `gryffQ`: what the port's dialers and its
acceptor write), as a grammar over per-message predicates on bytes owned by the protocol
subsystem (sealed here): the stream's structure is the hub's, what each message means is the
protocol's.

A dialer's stream (`dialStream`) starts with a 4-byte little-endian handshake `hs`:
* a peer's (`hs` has the high bit, P1): `hs = id ||| 2^31` where the dialer is replica `id` of
  the deployment (`peerRole`: the registry's, a greater id than the acceptor's); then (stage 2)
  a prefix of the encodings of the dialer's stream of model messages to the acceptor `dst`, with
  the dialer's prediction (`peerStreamOk`, `Proto2/Wire.lean`);
* a client's (`hs < 2^31`): Gryff client `hs`, bound to this connection (`clientConnAt γ hs cid`:
  an id the client node used for this connection only); then whole requests
  (`clientReqsOk γ hs last body`: each registered, `opReg`, with request ids strictly increasing, so
  no request appears twice).
The acceptor's stream (`acceptStream`): with the dialer's handshake `hs` (`sentLbG`, a lower
bound of the dialer's stream), its own stream to a peer (`peerStreamOk γ dst id`), or replies
to a client (`clientReplyOk γ hs m`: a reply with `OK = 1` to request `req` carries `opDone` of
`(hs, req)` with its output).
What a peer message means is the protocol unit's (`peerStreamOk`): a ValTag that names a stored value
carries `tagValIs`; a reply's tag is a lower bound of its sender's store (`storeLb`; a
`Write1Reply` carries `V = -1` and only the bound); a Commit's attributes are `instIs`; an
`Executed` follows its sender's application of the RMW's result.
Both protocols are prefix-closed: a stream is a prefix of a whole one (`□` of it).
-/
module

public import Dsverify.Proof.gryff.Names
public import Dsverify.Proof.gryff.Proto.WireDefs
public import Dsverify.Proof.gryff.Proto2.Wire
public import GooseLang.Ext.Net.Proto
public import Perennial.Std.Word.LittleEndian

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial.gryff

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

attribute [local instance] GooseGlobalGS.gooseInvGS

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF] [π : NetProtoGS]

/-- Replica node `k`'s peer-and-client port (`Shares.replicaAddrs`' `k`-th, `Rpc.Defs.addrOf`;
spelled here, as both are above this module). -/
def portAddr (k : Nat) : GoString :=
  [go!"127.0.0.1:7502", go!"127.0.0.1:7503", go!"127.0.0.1:7504"].getD k go!""

theorem portAddr_inj {k1 k2 : Nat} (h1 : k1 < 3) (h2 : k2 < 3) (h : portAddr k1 = portAddr k2) :
    k1 = k2 := by
  rcases k1 with _|_|_|k1 <;> rcases k2 with _|_|_|k2 <;>
    first | rfl | omega | (exfalso; revert h; decide)

/-- The replicas' peer-and-client ports (the lab's `Shares.replicaAddrs`, the kit's addresses). -/
def replicaAddrs : List GoString := [portAddr 0, portAddr 1, portAddr 2]

/-- The address `waitForPeerConnections` listens at for its node's address `a`:
`a[strings.Index(a, ":"):]`, the wildcard of `a`'s port (`":7502"` for `portAddr 0`). -/
def lisAddrOf (a : GoString) : GoString := a.drop (a.idxOf (W8 58))

instance nodeIdIs_persistent' (γp : ProtoNames) (k : Nat) (id : w64) :
    Persistent (nodeIdIs (GF := GF) γp k id) := by
  unfold nodeIdIs; infer_instance

/-- The replica id of the replica at port address `a` is `id` (persistent; the registry's). -/
@[irreducible] def portId (γ : GryffNames GF) (a : GoString) (id : w32) :
    IProp GF :=
  iprop(∃ k : Nat, ⌜k < 3 ∧ a = portAddr k⌝ ∗ nodeIdIs γ.proto k (W64 (uint.Z id)))
/-- Replica `id` of the deployment dials the replica at port address `a` (persistent; the
registry's: `id` is greater than `a`'s replica's id). -/
@[irreducible] def peerRole (γ : GryffNames GF) (a : GoString) (id : w32) :
    IProp GF :=
  iprop(∃ dst : w32, portId γ a dst ∗ ⌜uint.Z dst < uint.Z id ∧ uint.Z id < 3⌝)
/-- Gryff client id `hs` is used for connection `cid` only (persistent): the client-id map's
element, bound for good (H-U4-8). -/
@[irreducible] def clientConnAt (γ : GryffNames GF) (hs : w32) (cid : Nat) :
    IProp GF := ghostMapElem γ.proto.conns hs DFrac.discard (some cid)
/-- `body` is whole requests of client `hs`: each registered, request ids increasing
(persistent). -/
@[irreducible] def clientReqsOk (γ : GryffNames GF) (hs : w32) (last : Int)
    (body : List w8) : IProp GF := clientReqsBody γ hs last body
/-- Reply `m` (its code and payload) to client `cid` (persistent). -/
@[irreducible] def clientReplyOk (γ : GryffNames GF) (cid : w32) (m : List w8) :
    IProp GF := clientReplyBody γ cid m

/-- Gryff client id `hs` has never been used (exclusive; the client node's): the client-id map's
element, unbound (H-U4-8; declared here for the start's body, H-U3-2). -/
@[irreducible] def idTok (γ : GryffNames GF) (hs : w32) : IProp GF :=
  ghostMapElem γ.proto.conns hs (DFrac.own 1) (none : Option Nat)

/-- The namespace of the placers' invariant (H-U4-12). -/
def placersN : Namespace := ndot nroot "gryff_placers"

/-- Connection `cid`'s acceptor end has been placed (persistent): the placed map's element. The
placers' invariant keeps `cid`'s fresh acceptor token (`connFresh cid true`) from then on, so no
other fresh token of that end can exist (`placedConn_fresh`). Port: the lab made the fresh token
itself read-only (its harness's fresh tokens were ghost-map elements); `Net/`'s `connFresh` is an
exclusive token with no persistent form, so the invariant holds it and this element names it. -/
def connPlaced (γ : GryffNames GF) (cid : Nat) : IProp GF :=
  ghostMapElem γ.proto.placed cid DFrac.discard ()

instance connPlaced_persistent (γ : GryffNames GF) (cid : Nat) :
    Persistent (connPlaced γ cid) := by
  unfold connPlaced; infer_instance

/-- The placers' invariant (H-U4-12): the other half of the placers map's authority (`gryffInv`'s
body holds one), the placed map's authority (the placers map's domain), and the acceptor's
fresh-end token of every connection in it (so a connection gets its placing right once:
`placeRight_intro`, and a placed connection is never accepted again: `placedConn_fresh`). -/
def placersInv (γ : GryffNames GF) : IProp GF :=
  iprop(∃ (P : GMap Nat Int) (D : GMap Nat Unit), ghostMapAuth γ.proto.placers (1 : Qp).half P ∗
    ghostMapAuth γ.proto.placed 1 D ∗ ⌜∀ c, (D.lookup c).isSome = (P.lookup c).isSome⌝ ∗
    [∗map] cid ↦ _n ∈ P, connFresh cid true)

/-- The protocol's invariants (persistent): Gryff's (stage 2's) and the placers'. Port: the lab's
laws here took the hub's `sharedInvs` (`Shares.lean`, which also holds the rpc world's registry
and imports the deployment); these are the two of them the laws open. -/
def protoInvs (γ : GryffNames GF) : IProp GF :=
  iprop(gryffInv2 γ.proto ∗ inv placersN (placersInv γ))

instance protoInvs_persistent (γ : GryffNames GF) : Persistent (protoInvs γ) := by
  unfold protoInvs; infer_instance

/-- The high bit of a peer's handshake (P1, `genericsmr.PeerHandshake`). -/
def peerMark : w32 := W32 (2 ^ 31)

/-- A whole stream of messages, each meeting `ok`. -/
def msgsOk (ok : List w8 → IProp GF) (body : List w8) : IProp GF :=
  iprop(∃ ms : List (List w8), ⌜body = ms.flatten ∧ ∀ m ∈ ms, m ≠ []⌝ ∗ [∗list] m ∈ ms, ok m)

/-- A whole stream a dialer of `a` writes. -/
def dialStream (γ : GryffNames GF) (a : GoString) (cid : Nat) (full : List w8) :
    IProp GF :=
  iprop(∃ (hs : w32) (body : List w8), ⌜full = u32Le hs ++ body⌝ ∗
    ((∃ (id dst : w32), ⌜hs = id ||| peerMark ∧ id < peerMark⌝ ∗ peerRole γ a id ∗
        portId γ a dst ∗ peerStreamOk γ.proto (rid3 id) (rid3 dst) body) ∨
     (⌜hs < peerMark⌝ ∗ clientConnAt γ hs cid ∗ ∃ last, clientReqsOk γ hs last body)))

/-- A whole stream the acceptor of `a` writes on connection `cid`. -/
def acceptStream (γ : GryffNames GF) (a : GoString) (cid : Nat) (full : List w8) :
    IProp GF :=
  iprop(∃ hs : w32, sentLb cid false (u32Le hs) ∗
    ((∃ (id dst : w32), ⌜hs = id ||| peerMark ∧ id < peerMark⌝ ∗ portId γ a dst ∗
        peerStreamOk γ.proto (rid3 dst) (rid3 id) full) ∨
     (⌜hs < peerMark⌝ ∗ msgsOk (clientReplyOk γ hs) full)))

/-- Gryff's protocol for what dialers of a replica's port `a` write. -/
def gryffWireP (γ : GryffNames GF) (a : GoString) : Proto GF :=
  fun cid W => iprop(∃ full, ⌜W <+: full⌝ ∗ □ dialStream γ a cid full)

/-- Gryff's protocol for what the acceptor of a replica's port `a` writes. -/
def gryffWireQ (γ : GryffNames GF) (a : GoString) : Proto GF :=
  fun cid W => iprop(∃ full, ⌜W <+: full⌝ ∗ □ acceptStream γ a cid full)

end

end Perennial.gryff
