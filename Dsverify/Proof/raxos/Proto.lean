/-
The network protocols of the deployment (interface of stage 3, `notes/stage3-plan.md`): what may
be written on each configured address's connections, and the gRPC method specs of the
recorders. Node 0 is the orchestrator, node `1 + c` client `c`'s (c < 6), node `6 + k` server node
`k` (k = 1..5); a configuration runs replicas `1..c.n`. The client machines' request addresses
(`ClientAddrs`) are remote's.

* **A configuration port** (`cconfAddr c` of client node `c`, `confAddr k` of server node `k`,
  `CfgAddrs`): its dialers (the orchestrator's `sendConf`) write the configuration's five bytes
  (`encConf c`, the configuration chosen: `confIs γ c`); the node (`awaitConf`) answers one
  acknowledgment byte (`0x6b`).
* **A proxy's port** (`proxyAddr k`, `Addrs()[6+k]`): its dialers (the client nodes'
  `kit.go`) write a client's handshake (`hs (21 + c)`), then `ClientBatch` frames (`frame b`: code
  1, the encoding's 8-byte length, the encoding), each of a registered batch (`batchReg`), frame
  `n` of connection `cid` carrying a ticket of replica `k` (`tixAt`: the slots' bound); the proxy
  writes nothing on these connections.
* **A client's port** (`clientAddr c`, `Addrs()[1+c]`): its dialers (the proxies'
  connections back, `connectToClient`, `internalSendMessage`) write their handshake (`hs k`),
  then answer frames, each a fit `ClientBatch` with one result `r` that is the answer of its
  request (`opAns γ x r`). `internalSendMessage` encodes an answer before it writes its code byte
  (P4), so nothing of an answer that cannot be encoded is written. The client writes nothing on
  them.
* **Node 0's port** (`orchAddr`): nobody listens or dials (silent both ways).
* **A recorder's port** (`recAddr r`, `RecAddrs()[6+r]`): gRPC's protocols (the hypotheses')
  (`grpcAddr`), with the method specs `consensusMS γ r`:
  * `/Consensus/ESP`: the request encodes a well-formed `ProposerMessage` whose proposal was sent
    at its step (`evIn γ (.send i me s v)`), whose client batches are registered and whose decided
    slots are decided; the reply encodes the recorder's state after its `record` event for it, or
    the not-found reply (server mode 1's; step 0);
  * `/Consensus/FetchBatches`: any well-formed request; the reply's batches are registered;
  * `/Consensus/InformDecision`: every slot of the request is decided; the reply is `Empty`.

Changed against the lab (notes/dsv-quepaxa.md): the addresses are distinct ports of `127.0.0.1`
(`portAddr`); the protocols are `Net/`'s (`GooseLang/Ext/Net/Proto.lean`, connections numbered
by the extension); gRPC's vocabulary is the hypotheses' (`Hyp.lean`'s `QpVocab` instance); the
unused ports of the address lists are silent.
-/
module

public import Dsverify.Proof.raxos.Ghost
public import Dsverify.Proof.raxos.Msg
public import Dsverify.Proof.raxos.Hyp

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.raxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.raxos.pure Perennial.raxos.msg
open hyp.grpc (GrpcWorld UnarySpec GrpcVocab grpcAddr)

/-! ## Addresses -/

/-- The address `127.0.0.1:p` (`kit.go`'s address lists: every machine's ports are distinct ports
of `127.0.0.1`, in place of the lab's hosts `10.77.0.(10+n)` with the same ports on each). -/
def portAddr (p : Nat) : GoString := go!"127.0.0.1:" ++ decStr p

/-- Node 0's port (`Addrs()[0]`, 7600): the orchestrator holds no QuePaxa client; nobody listens
or dials there. -/
def orchAddr : GoString := portAddr 7600

/-- Client `c`'s address (node `1 + c`, `Addrs()[1+c]`): its listener for the replicas'
connections back. -/
def clientAddr (c : Nat) : GoString := portAddr (7601 + c)

/-- Client node `c`'s configuration address (`CfgAddrs()[1+c]`). -/
def cconfAddr (c : Nat) : GoString := portAddr (7641 + c)

/-- Replica `k`'s proxy address (server node `k`, node `6 + k`; `Addrs()[6+k]`). -/
def proxyAddr (k : Nat) : GoString := portAddr (7606 + k)

/-- Replica `r`'s recorder address (`RecAddrs()[6+r]`). -/
def recAddr (r : Nat) : GoString := portAddr (7626 + r)

/-- Server node `k`'s configuration address (`CfgAddrs()[6+k]`). -/
def confAddr (k : Nat) : GoString := portAddr (7646 + k)

/-- The addresses of the lists nobody uses (the orchestrator's and the client nodes' recorder
ports, the orchestrator's configuration port): silent. -/
def unusedAddrs : List GoString :=
  portAddr 7640 :: (List.range 7).map (fun n => portAddr (7620 + n))

/-- A server node's acknowledgment of a configuration (`confAck`). -/
def confAck : w8 := W8 0x6b

/-! ## Framing -/

/-- A node's handshake: its name in the first two bytes, little-endian, of four
(`binary.LittleEndian.PutUint16` on a `[4]byte`). -/
def hs (k : Nat) : List w8 := [W8 (k % 256), W8 (k / 256 % 256), W8 0, W8 0]

/-- The 8 bytes, little-endian, of `n` (`binary.LittleEndian.PutUint64`). -/
def le8 (n : Nat) : List w8 := (List.range 8).map (fun i => W8 (n / 2 ^ (8 * i) % 256))

/-- A `ClientBatch` message on a proxy connection (`clientBatchRpc`, then `ClientBatch.Marshal`:
the length, then the encoding). -/
def frame (b : Batch) : List w8 := [W8 1] ++ le8 (encBatch b).length ++ encBatch b

section protos
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable {GF : BundledGFunctors} [G : GooseGlobalGS HasLC.hasLC GF]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- What replica `k`'s proxy's dialers (the client nodes) write on connection `cid`: a client's
handshake (`hs (21 + c)`, `c < 6`), then frames of registered batches, frame `n` carrying a ticket
of replica `k` (`tixAt`). -/
def proxyInProto (γ : QNames) (k : Nat) : Proto GF := fun cid bs =>
  iprop(∃ (c : Nat) (L : List Batch), ⌜c < 6 ∧ bs <+: hs (21 + c) ++ (L.map frame).flatten ∧
      ∀ b ∈ L, batchOk b ∧ (encBatch b).length < 2 ^ 63⌝ ∗
    [∗list] n ↦ b ∈ L, batchReg γ b.id b ∗ ∃ c j, tixAt γ ((k : Int), c, j) cid n)

/-- What client `c`'s dialers (the proxies' connections back) write: a handshake, then answer
frames, each a fit batch with one result `r`, the answer of its request (`opAns`). Nothing of an
answer that cannot be encoded is written (P4). The client `c` is not mentioned on purpose: the
client matches answers to its own requests by id through the registry (`opPending`/`opAns`), so
the protocol need not say whose requests the answers are (the review's S3). -/
def clientInProto (γ : QNames) (_c : Nat) : Proto GF := fun _ bs =>
  iprop(∃ (k : Nat) (L : List Batch),
    ⌜k < 2 ^ 16 ∧ bs <+: hs k ++ (L.map frame).flatten ∧ ∀ b ∈ L, batchFit b⌝ ∗
    [∗list] b ∈ L, ∃ r, ⌜b.cmds = [r]⌝ ∗ opAns γ b.id r)

/-- What a configuration port's dialers (the client node) write: the chosen configuration. -/
def confInProto (γ : QNames) : Proto GF := fun _ bs =>
  iprop(∃ c : QConf, ⌜c.ok ∧ bs <+: encConf c⌝ ∗ confIs γ c)

/-- What a server node writes on its configuration port's connections: an acknowledgment. -/
def ackProto : Proto GF := fun _ bs => iprop(⌜bs <+: [confAck]⌝)

/-- Nothing is written (the acceptor's end of a proxy's and of the client's connections). -/
def silentProto : Proto GF := fun _ bs => iprop(⌜bs = []⌝)

/-! ## The recorders' gRPC methods -/

/-- A proposal's value in the consensus model. -/
def _root_.Perennial.raxos.msg.Prop'.val (p : Prop') : pure.Val := ⟨p.prio, p.pid, p.tid, p.ids⟩

/-- A model value as a reply's proposal. -/
def rrPropOf (v : pure.Val) : RRProp := ⟨v.prio, v.pid, v.tid, v.ids⟩

/-- The reply of a recorder whose slot state after the call is `st` (`HandleESP`). -/
def rrOf (st : RecSt) : RR := ⟨st.S, some (rrPropOf st.F), some (rrPropOf st.M), false⟩

/-- The not-found reply (`HandleESP` in server mode 1: step 0, nothing else). -/
def rrNotFound : RR := ⟨0, none, none, true⟩

/-- The facts of an ESP request: its proposal was sent at its step, its client batches are
registered, its decided slots are decided. -/
def pmFacts (γ : QNames) (m : PM) : IProp GF :=
  iprop(∃ (p : Prop') (me : Int), ⌜m.p = some p⌝ ∗ evIn γ (.send m.index me m.s p.val) ∗
    ([∗list] b ∈ p.batches, batchReg γ b.id b ∗ ⌜batchFit b⌝) ∗
    ([∗list] d ∈ m.slots, decided γ d.index d.ids))

/-- `/Consensus/ESP` at recorder `r`. -/
def espSpec (γ : QNames) (r : Int) : UnarySpec GF := fun req Φ =>
  iprop(∃ m : PM, ⌜req = encPM m ∧ pmOk m⌝ ∗ pmFacts γ m ∗
    ∀ rr : RR, ⌜rrOk rr⌝ ∗
      (⌜rr = rrNotFound⌝ ∨
        ∃ p st, ⌜m.p = some p ∧ rr = rrOf st⌝ ∗ evIn γ (.record r m.index m.s p.val st)) -∗
      Φ (encRR rr))

/-- `/Consensus/FetchBatches`. -/
def fetchSpec (γ : QNames) : UnarySpec GF := fun req Φ =>
  iprop(∃ ids : List GoString, ⌜req = encDReq ids ∧ ∀ s ∈ ids, strOk s⌝ ∗
    ∀ bs : List Batch, ⌜∀ b ∈ bs, batchFit b⌝ ∗ ([∗list] b ∈ bs, batchReg γ b.id b) -∗
      Φ (encDResp bs))

/-- `/Consensus/InformDecision`. -/
def informSpec (γ : QNames) : UnarySpec GF := fun req Φ =>
  iprop(∃ ds : List DSlot, ⌜req = encDecs ds ∧ ∀ d ∈ ds, dslotOk d⌝ ∗
    ([∗list] d ∈ ds, decided γ d.index d.ids) ∗ Φ encEmpty)

/-- The recorder named `r` at address `a`, if `a` is one of server nodes `1..5`'s recorder
addresses. -/
def recOfAddr (a : GoString) : Option Nat :=
  ([1, 2, 3, 4, 5] : List Nat).find? (fun r => decide (a = recAddr r))

/-- The method specs: each recorder address offers the three methods of `Consensus`. -/
def consensusMS (γ : QNames) (a fm : GoString) : Option (UnarySpec GF) :=
  match recOfAddr a with
  | none => none
  | some r =>
    if fm = go!"/Consensus/ESP" then some (espSpec γ r)
    else if fm = go!"/Consensus/FetchBatches" then some (fetchSpec γ)
    else if fm = go!"/Consensus/InformDecision" then some (informSpec γ)
    else none

/-- The gRPC world of the deployment. -/
def world (γ : QNames) : GrpcWorld GF := ⟨consensusMS γ, γ.grpc⟩

variable [go_gctx : GoGlobalContext] [π : NetProtoGS] [qv : hyp.QpVocab GF]

/-! ## Every address's protocols -/

/-- The protocols of every configured address but the request addresses (persistent): node 0's
port (silent), the clients', the proxies' and the configuration ports' as above, the recorders'
gRPC's (`grpcAddr` of the deployment's vocabulary `QpVocab`), the unused ones silent. -/
def netProtos (γ : QNames) : IProp GF :=
  iprop(addrProto orchAddr silentProto silentProto ∗
    ([∗list] a ∈ unusedAddrs, addrProto a silentProto silentProto) ∗
    ([∗list] c ∈ List.range 6, addrProto (clientAddr c) (clientInProto γ c) silentProto) ∗
    ([∗list] c ∈ List.range 6, addrProto (cconfAddr c) (confInProto γ) ackProto) ∗
    ([∗list] k ∈ [1, 2, 3, 4, 5], addrProto (proxyAddr k) (proxyInProto γ k) silentProto) ∗
    ([∗list] k ∈ [1, 2, 3, 4, 5], addrProto (confAddr k) (confInProto γ) ackProto) ∗
    ([∗list] r ∈ [1, 2, 3, 4, 5], grpcAddr qv.grpc (world γ) (recAddr r)))

omit go_gctx in
instance netProtos_persistent (γ : QNames) :
    Persistent (netProtos (GF := GF) γ) := by
  unfold netProtos grpcAddr; infer_instance

end protos

end Perennial.raxos
