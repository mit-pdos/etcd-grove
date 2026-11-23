/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/N/SpecsDefs.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit N: bodies of its sealed slots in `Replica2/Specs.lean` (so that its proofs, which
`Specs.lean` can import, do not depend on `Specs.lean`)
-/
module

public import Dsverify.Proof.gryff.Replica2.State

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.netN

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto
open Perennial.gryff.model (Msg)

attribute [local instance] GooseGlobalGS.gooseInvGS

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]


/-- `peerReaderAt`'s body: the reader `rd` (over `rdi`, `I`) has returned `hdr` and the encodings
`V` of `ms`; what the underlying stream delivers after `hdr` is a prefix of `q`'s stream to `k`
(once it delivered a byte: the dialer's reader learns `q`'s prediction from `q`'s bytes). Port:
the lab stated the last fact of the reader's state `I` and peeked through the reader; dsv-bufio's
reader is not unfolded, so it is stated of the reader resource (`wire.readNext`'s shape, from
`net.connReader_proto` where the reader is made). -/
def peerReaderB (γ : GryffNames GF) (q k : Fin 3) (rd : Loc) (ms : List Msg) : IProp GF :=
  iprop(∃ (rdi : wire.RSt GF) (I : List w8 → IProp GF) (hdr V : List w8),
    wire.readerOk rdi I ∗ wire.ownReader rd rdi I (hdr ++ V) ∗ ⌜msgsWire ms V⌝ ∗
    □ (∀ Y, ⌜Y ≠ []⌝ -∗ wire.ownReader rd rdi I (hdr ++ Y) ={⊤}=∗ wire.ownReader rd rdi I (hdr ++ Y) ∗
      ∃ W, peerStreamOk γ.proto q k W ∗ ⌜Y <+: W⌝))

/-- `PreferredPeerOrder[m]` as `NewReplicaDurable` sets it: `int32((int(r.Id) + 1 + m) % r.N)`
(B3). -/
def ppoVal (id len : w64) (m : Nat) : w32 :=
  W32 (sint.Z (BitVec.srem (W64 (sint.Z (W32 (sint.Z id))) + W64 1 + W64 (m : Int)) len))

/-- The rest of a generic replica as `NewReplicaDurable` builds it (`id`, addresses `nodes`): every
field but the rpc tables, with what `genericOk`, `connectRes`, `replicaChans`, `proposeOwn`,
`valOwn` and `isReplica` are made of (framed by `RegisterRPC` / `RegisterClientRPC`). Fixed fields
are persistent points-tos; the channels are made but not yet given their bag predicates (their
ghost names `γ…` are the ones `Repl2Names` will carry), but `pingChan`, already a bag of `False`
(`monitorPings` runs on it); the client-map mutex is not yet initialized (its invariant is over
`Repl2Names`); `PreferredPeerOrder`'s entries are `ppoVal`'s (N-9; B3: recorded for
`genericFixed`). -/
def builtRest (gR : Loc) (id : w64) (nodes : List GoString) : IProp GF :=
  iprop(∃ (sl pS rS wS aS ppoS ewS dS dlS : GoSlice)
      (stl smR propC beaC occ pc crm cwm mu st dac : Loc)
      (γprop γbea γocc γp γda : ChanNames) (ps : List w32) (ms mls : List Loc),
    ⌜nodes.length = sint.nat sl.len ∧ 0 ≤ sint.Z sl.len ∧ ps.length = nodes.length ∧
      ms.length = nodes.length ∧ mls.length = nodes.length ∧
      ∀ m : Nat, m < nodes.length → ps[m]? = some (ppoVal id sl.len m)⌝ ∗
    gR.[src.genericsmr.Replica, go!"N"] ↦□ sl.len ∗
    gR.[src.genericsmr.Replica, go!"Id"] ↦□ W32 (sint.Z id) ∗
    gR.[src.genericsmr.Replica, go!"PeerAddrList"] ↦□ sl ∗ sl ↦* nodes ∗
    gR.[src.genericsmr.Replica, go!"Peers"] ↦□ pS ∗
      pS ↦* List.replicate nodes.length (zero_val GoInterface) ∗
    gR.[src.genericsmr.Replica, go!"PeerReaders"] ↦□ rS ∗
      rS ↦* List.replicate nodes.length (zero_val Loc) ∗
    gR.[src.genericsmr.Replica, go!"PeerWriters"] ↦□ wS ∗
      wS ↦* List.replicate nodes.length (zero_val Loc) ∗
    gR.[src.genericsmr.Replica, go!"Alive"] ↦□ aS ∗
      aS ↦* List.replicate nodes.length (zero_val Bool) ∗
    gR.[src.genericsmr.Replica, go!"Listener"] ↦ interface.nil ∗
    gR.[src.genericsmr.Replica, go!"State"] ↦□ stl ∗
      stl.[src.state.State, go!"Store"] ↦ smR ∗ smR ↦$ (∅ : GMap w64 w64) ∗
    gR.[src.genericsmr.Replica, go!"ProposeChan"] ↦□ propC ∗ isChan propC γprop Loc ∗
      ownChan γprop Loc (.Buffered []) ∗
    gR.[src.genericsmr.Replica, go!"BeaconChan"] ↦□ beaC ∗ isChan beaC γbea Loc ∗
      ownChan γbea Loc (.Buffered []) ∗
    gR.[src.genericsmr.Replica, go!"Shutdown"] ↦□ false ∗
    gR.[src.genericsmr.Replica, go!"Thrifty"] ↦□ false ∗
    gR.[src.genericsmr.Replica, go!"Exec"] ↦□ true ∗
    gR.[src.genericsmr.Replica, go!"Dreply"] ↦□ true ∗
    gR.[src.genericsmr.Replica, go!"Beacon"] ↦ false ∗ -- B2: owned (`NewReplica` stores it)
    gR.[src.genericsmr.Replica, go!"Durable"] ↦ false ∗
    gR.[src.genericsmr.Replica, go!"PreferredPeerOrder"] ↦□ ppoS ∗ ppoS ↦* ps ∗
    gR.[src.genericsmr.Replica, go!"Ewma"] ↦□ ewS ∗
      ewS ↦* List.replicate nodes.length (zero_val w64) ∗
    gR.[src.genericsmr.Replica, go!"OnClientConnect"] ↦□ occ ∗ isChan occ γocc Bool ∗
      ownChan γocc Bool (.Buffered []) ∗
    gR.[src.genericsmr.Replica, go!"clientConnect"] ↦□ false ∗
    gR.[src.genericsmr.Replica, go!"pingChan"] ↦□ pc ∗
      isChanBag γp pc (fun _ : Loc => iprop(False)) ∗
    gR.[src.genericsmr.Replica, go!"clientReaders"] ↦□ crm ∗ crm ↦$ (∅ : GMap w32 Loc) ∗
    gR.[src.genericsmr.Replica, go!"clientWriters"] ↦□ cwm ∗ cwm ↦$ (∅ : GMap w32 Loc) ∗
    gR.[src.genericsmr.Replica, go!"clientIdMapsLock"] ↦□ mu ∗
      typedPointsto mu (zero_val sync.Mutex) (DFrac.own 1) ∗
    gR.[src.genericsmr.Replica, go!"Stats"] ↦□ st ∗ statsOkB st ∗
    gR.[src.genericsmr.Replica, go!"DoneAdaptingChan"] ↦□ dac ∗ isChan dac γda Bool ∗
      ownChan γda Bool (.Buffered []) ∗
    gR.[src.genericsmr.Replica, go!"delayRPC"] ↦□ dS ∗ dS ↦* ms ∗
      ([∗list] mp ∈ ms, mp ↦$ (∅ : GMap w8 Bool)) ∗
    gR.[src.genericsmr.Replica, go!"delayedRPC"] ↦□ dlS ∗ dlS ↦* mls ∗
      ([∗list] mp ∈ mls, mp ↦$ (∅ : GMap w8 Loc)))

/-- The channel of `op`'s last registration in `cregs`. -/
def lastReg (cregs : List (w8 × Loc)) (op : w8) : Option Loc :=
  (cregs.reverse.find? (fun e => e.1 == op)).map Prod.snd

/-- `genericBuilt`'s body: the rpc table maps each registered code (`8 + i` for the `i`-th, at
most 248 of them) to its pair, the client table each registered op code to a pair with its
channel (its last registration's). -/
def genericBuiltB (gR : Loc) (_id : w64) (_nodes : List GoString)
    (regs : List (w8 × GoInterface × Loc)) (cregs : List (w8 × Loc)) : IProp GF :=
  iprop(∃ (rt ct : Loc) (M CM : GMap w8 Loc),
    gR.[src.genericsmr.Replica, go!"rpcTable"] ↦□ rt ∗ rt ↦$ M ∗
    gR.[src.genericsmr.Replica, go!"rpcCode"] ↦ W8 (8 + regs.length) ∗
    ⌜regs.map Prod.fst = (List.range regs.length).map (fun i : Nat => W8 ((8 + i : Nat) : Int)) ∧
      regs.length ≤ 248⌝ ∗
    ([∗list] e ∈ regs, ∃ (pp : Loc), ⌜M !! e.1 = some pp⌝ ∗
      pp ↦□ src.genericsmr.RPCPair.mk e.2.1 e.2.2) ∗
    gR.[src.genericsmr.Replica, go!"clientRpcTable"] ↦□ ct ∗ ct ↦$ CM ∗
    □ (∀ (op : w8) (ch : Loc), ⌜lastReg cregs op = some ch⌝ -∗
      ∃ (pp : Loc) (obj : GoInterface), ⌜CM !! op = some pp⌝ ∗
        pp ↦□ src.genericsmr.ClientRPCPair.mk obj ch) ∗
    builtRest gR _id _nodes)

end

end Perennial.gryff.netN
