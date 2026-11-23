/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/replica/ConnSpecs.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The replica's connection setup (`replica/replica.go`: `waitForPeerConnections`,
`ConnectToPeers`) and the closest-peers computation (`ComputeClosestPeers`,
`UpdatePreferredPeerOrder`): internal specs.

* `replica.elem s i v`: element `i` of slice `s` (the setup's goroutines write disjoint
  indices of `Peers`, `PeerReaders`, `PeerWriters`, `Alive`).
* `replica.peerSlot`: peer `i`'s slot after the handshake: nothing, or a connection registered
  as a peer's with its reader (the dialed one: nothing read; the accepted one: the peer's hello
  read) and its writer (`sp.wrSt` of `sp.peerWrKind me i`), `Alive[i]` then true.
* `replica.pendingOk`: a client's connection accepted while waiting for the peers (P1): its
  reader, which has read the first byte `first` (not the hello's: P1's classification reads it
  with `ReadByte`, the R2 workaround), and its end's writer token (for `clientListener`).
* `replica.acceptSt`: what `waitForPeerConnections` sends on `done`: the slots of the peers
  above this replica, the listener, the pending clients.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.ConnLemmas
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.Specs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]

/-- Element `i` of the slice `s`. -/
abbrev replica.elem {V : Type} [ZeroVal V] [TypedPointsto (GF := netDistGF) V] (s : GoSlice)
    (i : Nat) (v : V) : IProp netDistGF :=
  typedPointsto (sliceIndexRef V (i : Int) s) v (DFrac.own 1)

/-- The reader kind of peer `i`'s connection at replica `me`. -/
def sp.peerRdKind (me : w32) (i : Nat) : sp.RdKind :=
  if (i : Int) < me.toInt then .peerOut else .peerIn (W32 (i : Int))

/-- Peer `i`'s slot (see the file header). -/
def replica.peerSlot (γ : sp.Names) (γc γm : GName) (me : w32) (pssl prsl pwsl alsl : GoSlice)
    (i : Nat) : IProp netDistGF :=
  iprop(∃ (cv : GoInterface) (rd w : Loc) (al : Bool),
    replica.elem pssl i cv ∗ replica.elem prsl i rd ∗ replica.elem pwsl i w ∗
    replica.elem alsl i al ∗
    (⌜rd = null ∧ w = null⌝ ∨
      ∃ (cid : w64) (R : List w8),
        net.rpc.connIface cv cid (sp.peerRdKind me i).side ∗ sp.connKind γ cid .peer ∗
        bufio.ownReader rd cv
          (recvTok cid (sp.peerRdKind me i).side ((sp.peerRdKind me i).proto γ γc γm)) R ∗
        ⌜sp.rdAt (sp.peerRdKind me i) [] R⌝ ∗ sp.wrSt γ γc γm w (sp.peerWrKind me i)))

/-- A client's connection accepted while waiting for the peers (see the file header). -/
def replica.pendingOk (γ : sp.Names) (γc γm : GName) (p : replica.pendingClient) :
    IProp netDistGF :=
  iprop(∃ cid : w64, net.rpc.connIface p.conn' cid true ∗
    bufio.ownReader p.reader' p.conn' (recvTok cid true (sp.inP γ γc γm)) [p.first'] ∗
    ⌜p.first' ≠ W8 0xFF⌝ ∗ sendTok cid true (sp.outQ γ γc γm) [])

/-- The replica's listener `lv`: a TCP listener bound to `a` (persistent). -/
def replica.listenerOk (lv : GoInterface) (a : GoString) : IProp netDistGF :=
  iprop(∃ (ll : Loc) (lid : w64),
    ⌜lv = interface.mkOk (go.GoType.PointerType net.TCPListener.ty) #ll⌝ ∗
    net.ownListener ll lid a)

instance replica.listenerOk_persistent (lv : GoInterface) (a : GoString) :
    Persistent (replica.listenerOk lv a) := by
  unfold replica.listenerOk; infer_instance

/-- What `waitForPeerConnections` hands back on `done` (see the file header). -/
def replica.acceptSt (r : Loc) (γ : sp.Names) (γc γm : GName) (N : Nat) (me : w32) (a : GoString)
    (pssl prsl pwsl alsl : GoSlice) : IProp netDistGF :=
  iprop(∃ (lv : GoInterface) (pcsl : GoSlice) (pcs : List replica.pendingClient),
    replica.fld r go!"Listener" ↦ lv ∗ replica.listenerOk lv a ∗
    replica.fld r go!"pendingClients" ↦ pcsl ∗
    pcsl ↦* pcs ∗ ([∗list] p ∈ pcs, replica.pendingOk γ γc γm p) ∗
    [∗list] i ∈ List.range' (me.toInt.toNat + 1) (N - (me.toInt.toNat + 1)),
      replica.peerSlot γ γc γm me pssl prsl pwsl alsl i)

/-- `r.waitForPeerConnections(done)`: listens on this replica's port (`a`, at the node's IP
`ip`) and accepts a connection per peer above `me` (P1: a client's is kept aside), then sends
the slots on `done`. -/
abbrev replica.Replica.waitForPeerConnections.spec : Prop :=
  ∀ (r : Loc) (γ : sp.Names) (γc γm : GName) (N : Nat) (me : w32) (asl : GoSlice)
    (l : List GoString) (a ip : GoString) (lg : Loc) (pssl prsl pwsl alsl : GoSlice)
    (lv0 : GoInterface) (pcsl0 : GoSlice) (done : Loc) (γd : ChanNames),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.replica ∗
      isPkgInit (PROP := IProp netDistGF) pkg_id.bufio ∗
      isPkgInit (PROP := IProp netDistGF) pkg_id.net ∗
      isPkgInit (PROP := IProp netDistGF) pkg_id.io ∗
      isPkgInit (PROP := IProp netDistGF) pkg_id.encoding.binary ∗
      replica.fld r go!"Logger" ↦□ lg ∗ dlog.quiet lg ∗
      replica.fld r go!"N" ↦□ (W64 N) ∗ replica.fld r go!"Id" ↦□ me ∗
      replica.fld r go!"PeerAddrList" ↦□ asl ∗ asl ↦*□ l ∗
      replica.fld r go!"Peers" ↦□ pssl ∗ replica.fld r go!"PeerReaders" ↦□ prsl ∗
      replica.fld r go!"PeerWriters" ↦□ pwsl ∗ replica.fld r go!"Alive" ↦□ alsl ∗
      replica.fld r go!"Listener" ↦ lv0 ∗ replica.fld r go!"pendingClients" ↦ pcsl0 ∗
      ⌜pcsl0 = slice.nil ∧ l[me.toInt.toNat]? = some a ∧ replicaAddrs.contains a ∧
        ip ++ [W8 58] <+: a ∧ 0 ≤ me.toInt ∧ me.toInt < N ∧ N ≤ 7 ∧ l.length = N ∧
        sint.Z pssl.len = N ∧ sint.Z prsl.len = N ∧ sint.Z pwsl.len = N ∧ sint.Z alsl.len = N⌝ ∗
      addrTok a ∗ nodeIp ip ∗ addrProto a (sp.inP γ γc γm) (sp.outQ γ γc γm) ∗
      ([∗list] i ∈ List.range' (me.toInt.toNat + 1) (N - (me.toInt.toNat + 1)),
        ∃ (cv : GoInterface) (rd w : Loc) (al : Bool), replica.elem pssl i cv ∗
          replica.elem prsl i rd ∗ replica.elem pwsl i w ∗ replica.elem alsl i al ∗
          ⌜rd = null ∧ w = null⌝) ∗
      isChanBag γd done (fun _ : Bool =>
        replica.acceptSt r γ γc γm N me a pssl prsl pwsl alsl) }}
    (App (Val (r @!! go.GoType.PointerType replica.Replica.ty @!! go!"waitForPeerConnections"))
      (Val #done))
  {{ RET #(); True }}

/-- What `ConnectToPeers` starts from (the state `replica.New` and swift's `New` leave, and
`swift.New`'s frozen precondition): the replica's persistent slots but the mutex and the
peers' writers (`isReplica` less `pws` and `r.M`), the connection slices owned, `Latencies` and
`Ewma` owned, `r.M` a zero mutex, the clients' writers map empty, the port's token and the
replicas' ports' protocols. -/
def replica.connPre (r : Loc) (γ : sp.Names) (γc γm γl : GName) (N : Nat) (me : w32)
    (a ip : GoString) : IProp netDistGF :=
  iprop(∃ (lg cfgp tbl pc : Loc) (fr : Bool) (nid : w8) (ents : GMap w8 rpc.Pair')
      (γpc : ChanNames) (asl pssl prsl pwsl alsl latsl ewsl : GoSlice) (l : List GoString)
      (cwm : GoMap) (lats ews : List w64) (al : GoString),
    sp.inv γ γc γm γl ∗
    replica.fld r go!"Logger" ↦□ lg ∗ dlog.quiet lg ∗
    replica.fld r go!"N" ↦□ (W64 N) ∗ replica.fld r go!"Id" ↦□ me ∗
    replica.fld r go!"Config" ↦□ cfgp ∗ config.plain cfgp fr ∗
    replica.fld r go!"RPC" ↦□ tbl ∗ rpc.isTable tbl DFrac.discard nid ents ∗
    sp.tableOk γ γc γm ents ∗
    replica.fld r go!"ProposeChan" ↦□ pc ∗ isChanBag γpc pc (sp.proposeP γ) ∗
    replica.fld r go!"Shutdown" ↦□ false ∗ replica.fld r go!"LRead" ↦□ false ∗
    replica.fld r go!"Dt" ↦□ null ∗ replica.fld r go!"Alias" ↦□ al ∗
    replica.fld r go!"PeerAddrList" ↦□ asl ∗ asl ↦*□ l ∗
    replica.fld r go!"Peers" ↦□ pssl ∗ pssl ↦* List.replicate N interface.nil ∗
    replica.fld r go!"PeerReaders" ↦□ prsl ∗ prsl ↦* List.replicate N null ∗
    replica.fld r go!"PeerWriters" ↦□ pwsl ∗ pwsl ↦* List.replicate N null ∗
    replica.fld r go!"Alive" ↦□ alsl ∗ alsl ↦* List.replicate N false ∗
    replica.fld r go!"Latencies" ↦□ latsl ∗ latsl ↦* lats ∗
    replica.fld r go!"Ewma" ↦□ ewsl ∗ ewsl ↦* ews ∗
    replica.fld r go!"ClientWriters" ↦□ cwm ∗ cwm ↦$ (∅ : GMap w32 Loc) ∗
    replica.fld r go!"M" ↦ Perennial.zero_val sync.Mutex ∗
    replica.fld r go!"Listener" ↦ interface.nil ∗ replica.fld r go!"pendingClients" ↦ slice.nil ∗
    ⌜l[me.toInt.toNat]? = some a ∧ replicaAddrs.contains a ∧ ip ++ [W8 58] <+: a ∧
      0 ≤ me.toInt ∧ me.toInt < N ∧ N ≤ 7 ∧ l.length = N ∧ (∀ a' ∈ l, a' ∈ replicaAddrs) ∧
      lats.length = N ∧ ews.length = N⌝ ∗
    addrTok a ∗ nodeIp ip ∗
    [∗list] a' ∈ replicaAddrs, addrProto a' (sp.inP γ γc γm) (sp.outQ γ γc γm))

/-- What serving the clients needs (`ConnectToPeers`' post besides `isReplica`; the pre of
`WaitForClientConnections`): the listener bound to `a`, with its protocols, the clients accepted
while waiting for the peers, the alias. -/
def replica.serveSt (r : Loc) (γ : sp.Names) (γc γm : GName) (a : GoString) : IProp netDistGF :=
  iprop(∃ (lv : GoInterface) (pcsl : GoSlice) (pcs : List replica.pendingClient) (al : GoString),
    replica.fld r go!"Listener" ↦ lv ∗ replica.listenerOk lv a ∗
    addrProto a (sp.inP γ γc γm) (sp.outQ γ γc γm) ∗
    replica.fld r go!"pendingClients" ↦ pcsl ∗ pcsl ↦* pcs ∗
    ([∗list] p ∈ pcs, replica.pendingOk γ γc γm p) ∗
    replica.fld r go!"Alias" ↦□ al)

/-- `r.ConnectToPeers()`: dials the peers below `me` (each connection registered as a peer's,
the hello written), accepts the others (`waitForPeerConnections`), starts a `replicaListener`
per connected peer: then the replica (`isReplica`, with a fresh name `γw` for the clients'
writers) and the clients accepted meanwhile. -/
abbrev replica.Replica.ConnectToPeers.spec : Prop :=
  ∀ (r : Loc) (γ : sp.Names) (γc γm γl : GName) (N : Nat) (me : w32) (a ip : GoString),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.replica ∗
      isPkgInit (PROP := IProp netDistGF) pkg_id.bufio ∗
      isPkgInit (PROP := IProp netDistGF) pkg_id.net ∗
      isPkgInit (PROP := IProp netDistGF) pkg_id.io ∗
      isPkgInit (PROP := IProp netDistGF) pkg_id.encoding.binary ∗
      replica.connPre r γ γc γm γl N me a ip }}
    (App (Val (r @!! go.GoType.PointerType replica.Replica.ty @!! go!"ConnectToPeers")) (Val #()))
  {{ RET #(); ∃ γw : GName, replica.isReplica r γ γc γm γw N me ∗ replica.serveSt r γ γc γm a }}

/-- `r.ComputeClosestPeers()`: 20 rounds of beacons to the alive peers, then this replica's
peers ordered by measured latency (`PreferredPeerOrder`: `N` peer ids) and their mean
latencies (`N - 1` of them). The old order's entries must be peer ids (`UpdatePreferredPeerOrder`
looks each up in the ranking; an entry that is not one would overflow its buffer). -/
abbrev replica.Replica.ComputeClosestPeers.spec : Prop :=
  ∀ (r : Loc) (γ : sp.Names) (γc γm γw : GName) (N : Nat) (me : w32) (ppsl : GoSlice)
    (pp : List w32),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.replica ∗
      replica.isReplica r γ γc γm γw N me ∗
      replica.fld r go!"PreferredPeerOrder" ↦ ppsl ∗ ppsl ↦* pp ∗
      ⌜∀ p ∈ pp, 0 ≤ p.toInt ∧ p.toInt < N⌝ }}
    (App (Val (r @!! go.GoType.PointerType replica.Replica.ty @!! go!"ComputeClosestPeers"))
      (Val #()))
  {{ (sl : GoSlice), RET #sl; ∃ (ls : List w64) (ppsl' : GoSlice) (pp' : List w32),
      sl ↦* ls ∗ ⌜ls.length = N - 1⌝ ∗
      replica.fld r go!"PreferredPeerOrder" ↦ ppsl' ∗ ppsl' ↦* pp' ∗
      ⌜pp'.length = N ∧ ∀ p ∈ pp', 0 ≤ p.toInt ∧ p.toInt < N⌝ }}

/-- `r.UpdatePreferredPeerOrder(quorum)`: the order becomes `quorum`'s entries but `me`, then
those of the old order not among them (here: `me`); `N` entries, each `quorum`'s or `0`. -/
abbrev replica.Replica.UpdatePreferredPeerOrder.spec : Prop :=
  ∀ (r : Loc) (γ : sp.Names) (γc γm γw : GName) (N : Nat) (me : w32) (qsl : GoSlice)
    (Q : List w32) (ppsl : GoSlice) (pp : List w32),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.replica ∗
      replica.isReplica r γ γc γm γw N me ∗ qsl ↦* Q ∗
      replica.fld r go!"PreferredPeerOrder" ↦ ppsl ∗ ppsl ↦* pp ∗
      ⌜Q.length = N ∧ me ∈ Q ∧ ∀ p ∈ pp, p ∈ Q⌝ }}
    (App (Val (r @!! go.GoType.PointerType replica.Replica.ty @!! go!"UpdatePreferredPeerOrder"))
      (Val #qsl))
  {{ RET #(); ∃ (ppsl' : GoSlice) (pp' : List w32), qsl ↦* Q ∗ ppsl ↦* pp ∗
      replica.fld r go!"PreferredPeerOrder" ↦ ppsl' ∗ ppsl' ↦* pp' ∗
      ⌜pp'.length = N ∧ ∀ x ∈ pp', x ∈ Q ∨ x = W32 0⌝ }}

end specs

end Perennial.github_com.imdea_software.swiftpaxos
