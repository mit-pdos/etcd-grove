/-
Ported from dsverify-lab examples/swiftpaxos/proof/Spec/client/Defs.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The SwiftPaxos client's states as the adapter (`examples/swiftnet`) sees them, through
`client.NewClientLog`, `NewBufferClient`, `Connect`, `swift.NewClient` and `Write` / `Read`
(the client group: packages `client` and `swift`'s `client.go`). Sealed in spirit: the adapter
uses them only through the specs (`Spec/client/*`, `Spec/swift/NewClient.lean`); the client
group owns the bodies below `ready`'s ghost part.

* `client.fresh cl cid maddr mport`: a client made by `NewClientLog` for the master at
  `maddr:mport`, fast, not leaderless, not connected; its struct owned (the adapter sets its
  `ClientId`);
* `client.bufFresh b cid maddr mport`: `NewBufferClient(cl, ...)` of such a client with id
  `cid`;
* `client.connected b γ γc γm cid N`: `Connect` succeeded: the membership `l` of `N` replicas,
  and for each replica the master listed as alive a connection of kind `client cid`
  (`sp.connKind`), its reader and its writer at the streams' start;
* `client.failed b`: `Connect` failed (only `Disconnect` follows);
* `client.ready b γ γc γm γl cid s`: after `swift.NewClient(b, N)`: the handler and the readers
  run; the client's next sequence number is `s` (`sp.clientSeq`), and the replies the handler
  registers on `Reply` are decided results (`sp.doneRes`) of the client's commands, each with
  its delivery token (so the reply `Write`/`Read` receives is its own command's).

Change log C4: the predicates are sealed (`@[no_expose]`) and owned by the client group; each has
an unfolding law (`_unfold`) for the client group's proofs. The adapter only passes them along.
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Inv
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.dlog.Defs
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.examples.swiftnet.Codec
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.client.Ghost

-- PORT: lab imports dropped: Harness.Proof.bufio.Net, Harness.Proof.net.rpc.ClientDefs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace client

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [π : NetProtoGS]

/-! ## The client's writers and fields (change log C4) -/

/-- What the client has written on a writer with no error: whole frames of its registered
proposals (each with its witness), nothing buffered. -/
def wrAligned (γ : sp.Names) (γc γm : GName) (cid : w32) (sent : List w8) : IProp netDistGF :=
  -- change log C9: the frames are well formed (`sp.framesProto` requires `Msg.wf`)
  iprop(∃ ms : List sp.Msg, ⌜sent = sp.framesOf ms ∧
      ∀ m ∈ ms, sp.Msg.isProposeOf cid m ∧ sp.Msg.wf m⌝ ∗
    [∗list] m ∈ ms, sp.msgOk γ γc γm m)

/-- One of the client's writers: none, or over a connection of kind `client cid`, with a sticky
error, or (no error) everything written whole frames of the client's proposals. -/
def wrOk (γ : sp.Names) (γc γm : GName) (cid : w32) (w : Loc) : IProp netDistGF :=
  iprop(⌜w = null⌝ ∨ ∃ (srv : GoInterface) (c : Nat) (sent pend : List w8) (err : GoInterface),
    net.rpc.connIface srv c false ∗ sp.connKind γ c (.client cid) ∗
    bufio.ownWriter w srv (sendTok c false (sp.inP γ γc γm)) (sp.inP γ γc γm c) sent pend err ∗
    (⌜err ≠ interface.nil⌝ ∨ ⌜pend = []⌝ ∗ wrAligned γ γc γm cid sent))

/-- The fields `SendProposal` reads and the client's `N` writers. -/
def sendSt (γ : sp.Names) (γc γm : GName) (cl : Loc) (cid : w32) (N : Nat) :
    IProp netDistGF :=
  iprop(∃ (lg : Loc) (ld : w64) (ssl wsl : GoSlice) (wrs : List Loc),
    structFieldRef client.Client go!"ClientId" cl ↦□ cid ∗
    structFieldRef client.Client go!"Fast" cl ↦□ true ∗
    structFieldRef client.Client go!"Leaderless" cl ↦□ false ∗
    structFieldRef client.Client go!"Logger" cl ↦□ lg ∗ dlog.quiet lg ∗
    structFieldRef client.Client go!"LeaderId" cl ↦□ ld ∗
    structFieldRef client.Client go!"servers" cl ↦□ ssl ∗
    structFieldRef client.Client go!"writers" cl ↦□ wsl ∗ wsl ↦*□ wrs ∗
    ⌜sint.nat ssl.len = N ∧ 0 ≤ sint.Z ssl.len ∧ wrs.length = N⌝ ∗
    [∗list] w ∈ wrs, wrOk γ γc γm cid w)

/-- The delivery tokens of the replies received (`0 .. s - 1`). -/
def toks (γd : GName) (s : Nat) : IProp netDistGF :=
  iprop([∗list] n ∈ List.range s, ghostMapElem (K := Nat) (V := Unit) γd n (DFrac.own 1) ())

/-! ## The predicates the adapter passes along (sealed) -/

/-- A client from `NewClientLog(server, maddr, mport, true, false, verbose, lg)` with id `cid`:
its struct (the adapter writes `ClientId`: `fresh_setId`), a quiet logger, the master's address, no
master connection, sequence number -1, no pings and no connections yet (nil slices: what
`Connect`'s `findClosest` appends to and what a failed `Connect` leaves; client group, C4). -/
@[no_expose] def fresh (cl : Loc) (cid : w32) (maddr : GoString) (mport : w64) : IProp netDistGF :=
  iprop(∃ v : client.Client, cl ↦ v ∗ dlog.quiet v.Logger' ∗
    ⌜v.ClientId' = cid ∧ v.masterAddr' = maddr ∧ v.masterPort' = mport ∧ v.seqnum' = W32 (-1) ∧
      v.Fast' = true ∧ v.Leaderless' = false ∧ v.master' = null ∧ v.dt' = null ∧
      v.Ping' = slice.nil ∧ v.servers' = slice.nil⌝)

theorem fresh_unfold (cl : Loc) (cid : w32) (maddr : GoString) (mport : w64) :
    fresh cl cid maddr mport ⊣⊢ iprop(∃ v : client.Client, cl ↦ v ∗ dlog.quiet v.Logger' ∗
    ⌜v.ClientId' = cid ∧ v.masterAddr' = maddr ∧ v.masterPort' = mport ∧ v.seqnum' = W32 (-1) ∧
      v.Fast' = true ∧ v.Leaderless' = false ∧ v.master' = null ∧ v.dt' = null ∧
      v.Ping' = slice.nil ∧ v.servers' = slice.nil⌝) := by
  unfold fresh; exact .rfl

/-- `NewBufferClient(cl, reqNum, 0, 0, 0, 0)` of a fresh client with id `cid`: the buffer
client's struct (for good: no field changes after), the client's struct, an empty reply
channel (buffered: `reqNum + 1`). -/
@[no_expose] def bufFresh (b : Loc) (cid : w32) (maddr : GoString) (mport : w64) : IProp netDistGF :=
  iprop(∃ (bv : client.BufferClient) (v : client.Client), b ↦□ bv ∗ bv.Client' ↦ v ∗
    dlog.quiet v.Logger' ∗ ⌜bv.Client' ≠ null ∧ bv.seq' = true ∧ v.ClientId' = cid ∧
      v.masterAddr' = maddr ∧ v.masterPort' = mport ∧ v.seqnum' = W32 (-1) ∧ v.Fast' = true ∧
      v.Leaderless' = false ∧ v.master' = null ∧ v.dt' = null ∧
      v.Ping' = slice.nil ∧ v.servers' = slice.nil⌝ ∗
    ∃ γch : ChanNames, isChan bv.Reply' γch Loc ∗ ownChan γch Loc (ChanState.Buffered []))

theorem bufFresh_unfold (b : Loc) (cid : w32) (maddr : GoString) (mport : w64) :
    bufFresh b cid maddr mport ⊣⊢ iprop(∃ (bv : client.BufferClient) (v : client.Client), b ↦□ bv ∗ bv.Client' ↦ v ∗
    dlog.quiet v.Logger' ∗ ⌜bv.Client' ≠ null ∧ bv.seq' = true ∧ v.ClientId' = cid ∧
      v.masterAddr' = maddr ∧ v.masterPort' = mport ∧ v.seqnum' = W32 (-1) ∧ v.Fast' = true ∧
      v.Leaderless' = false ∧ v.master' = null ∧ v.dt' = null ∧
      v.Ping' = slice.nil ∧ v.servers' = slice.nil⌝ ∗
    ∃ γch : ChanNames, isChan bv.Reply' γch Loc ∗ ownChan γch Loc (ChanState.Buffered [])) := by
  unfold bufFresh; exact .rfl

/-- One replica's end of a connected client: none (the master listed it as not alive), or a
connection of kind `client cid` to a replica's port with its reader (`bufio`, at the stream's
start, protocol `sp.outQ`) and writer (protocol `sp.inP`, nothing written). -/
@[no_expose] def replicaEnd (γ : sp.Names) (γc γm : GName) (cid : w32) (srv : GoInterface) (rd wr : Loc) : IProp netDistGF :=
  iprop(⌜rd = null ∧ wr = null⌝ ∨
    ∃ c : Nat, net.rpc.connIface srv c false ∗ sp.connKind γ c (.client cid) ∗
      bufio.ownReader rd srv (recvTok c false (sp.outQ γ γc γm)) [] ∗
      bufio.ownWriter wr srv (sendTok c false (sp.inP γ γc γm)) (sp.inP γ γc γm c) [] []
        interface.nil)

theorem replicaEnd_unfold (γ : sp.Names) (γc γm : GName) (cid : w32) (srv : GoInterface) (rd wr : Loc) :
    replicaEnd γ γc γm cid srv rd wr ⊣⊢ iprop(⌜rd = null ∧ wr = null⌝ ∨
    ∃ c : Nat, net.rpc.connIface srv c false ∗ sp.connKind γ c (.client cid) ∗
      bufio.ownReader rd srv (recvTok c false (sp.outQ γ γc γm)) [] ∗
      bufio.ownWriter wr srv (sendTok c false (sp.inP γ γc γm)) (sp.inP γ γc γm c) [] []
        interface.nil) := by
  unfold replicaEnd; exact .rfl

/-- `Connect` succeeded: the membership `l` of `N` replicas (`replicas`), a master rpc client,
and a reader and a writer per replica (those not alive: none). -/
@[no_expose] def connected (b : Loc) (γ : sp.Names) (γc γm : GName) (cid : w32) (N : Nat) : IProp netDistGF :=
  iprop(∃ (bv : client.BufferClient) (v : client.Client) (l : List GoString) (fr : Bool)
      (srvs : List GoInterface) (rds wrs : List Loc),
    b ↦□ bv ∗ bv.Client' ↦ v ∗ dlog.quiet v.Logger' ∗ sp.cfg γc γm N fr l ∗
    v.replicas' ↦* l ∗ v.servers' ↦* srvs ∗ v.readers' ↦* rds ∗ v.writers' ↦* wrs ∗
    ⌜bv.Client' ≠ null ∧ bv.seq' = true ∧ v.ClientId' = cid ∧ v.seqnum' = W32 (-1) ∧
      v.Fast' = true ∧ v.Leaderless' = false ∧ v.dt' = null ∧
      srvs.length = N ∧ rds.length = N ∧ wrs.length = N⌝ ∗
    ([∗list] i ↦ s ∈ srvs, replicaEnd γ γc γm cid s (rds.getD i null) (wrs.getD i null)) ∗
    ∃ γch : ChanNames, isChan bv.Reply' γch Loc ∗ ownChan γch Loc (ChanState.Buffered []))

theorem connected_unfold (b : Loc) (γ : sp.Names) (γc γm : GName) (cid : w32) (N : Nat) :
    connected b γ γc γm cid N ⊣⊢ iprop(∃ (bv : client.BufferClient) (v : client.Client) (l : List GoString) (fr : Bool)
      (srvs : List GoInterface) (rds wrs : List Loc),
    b ↦□ bv ∗ bv.Client' ↦ v ∗ dlog.quiet v.Logger' ∗ sp.cfg γc γm N fr l ∗
    v.replicas' ↦* l ∗ v.servers' ↦* srvs ∗ v.readers' ↦* rds ∗ v.writers' ↦* wrs ∗
    ⌜bv.Client' ≠ null ∧ bv.seq' = true ∧ v.ClientId' = cid ∧ v.seqnum' = W32 (-1) ∧
      v.Fast' = true ∧ v.Leaderless' = false ∧ v.dt' = null ∧
      srvs.length = N ∧ rds.length = N ∧ wrs.length = N⌝ ∗
    ([∗list] i ↦ s ∈ srvs, replicaEnd γ γc γm cid s (rds.getD i null) (wrs.getD i null)) ∗
    ∃ γch : ChanNames, isChan bv.Reply' γch Loc ∗ ownChan γch Loc (ChanState.Buffered [])) := by
  unfold connected; exact .rfl

/-- A reply the handler registers for client `cid` (`RegisterReply`'s `*ReqReply`): its value
`bs` is the decided result of the client's command of sequence number `n` (below `2 ^ 31`: change
log C4), with the delivery token of `n` (the handler mints one per command it delivers: its
`delivered` map's ghost authority, `γd`, is the handler's). -/
@[no_expose] def replyP (γ : sp.Names) (cid : w32) (γd : GName) (p : Loc) : IProp netDistGF :=
  iprop(∃ (rr : client.ReqReply) (bs : List w8) (n : Nat), p ↦□ rr ∗ rr.Val' ↦*□ bs ∗
    ⌜rr.Seqnum' = W64 n ∧ n < 2 ^ 31⌝ ∗ sp.doneRes γ ⟨cid, W32 n⟩ bs ∗
    ghostMapElem (K := Nat) γd n (DFrac.own 1) ())

theorem replyP_unfold (γ : sp.Names) (cid : w32) (γd : GName) (p : Loc) :
    replyP γ cid γd p ⊣⊢ iprop(∃ (rr : client.ReqReply) (bs : List w8) (n : Nat), p ↦□ rr ∗ rr.Val' ↦*□ bs ∗
    ⌜rr.Seqnum' = W64 n ∧ n < 2 ^ 31⌝ ∗ sp.doneRes γ ⟨cid, W32 n⟩ bs ∗
    ghostMapElem (K := Nat) γd n (DFrac.own 1) ()) := by
  unfold replyP; exact .rfl

/-- After `swift.NewClient(b, N)` (change log C4: the fields `SendProposal` reads, writers that
may carry a sticky error, `cid ≥ 1`): the client's own part (its sequence-number field, its
writers, the protocol's next sequence number `s`, the delivery tokens of its `s` received
replies) and the reply channel's protocol; the handler's and the readers' parts are theirs. A
reply on the channel is then its command's: its token is not one of those held, and its command
is registered (`sp.doneRes_seq`), so its sequence number is `s`. L2 (stage 2): the node's ghost is
claimed for the client (`client.nodeGhostB`, the body of `client.nodeGhostOk`; client `cid` is
predicted node `cl (cid - 1)`) and every prediction is registered (`sp.allPredsReg`). -/
@[no_expose] def ready (b : Loc) (γ : sp.Names) (γc γm γl : GName) (cid : w32) (s : Nat) : IProp netDistGF :=
  iprop(∃ (bv : client.BufferClient) (cl : Loc) (N : Nat) (γch : ChanNames) (γd : GName),
    b ↦□ bv ∗ ⌜bv.Client' = cl ∧ cl ≠ null ∧ 1 ≤ cid.toInt⌝ ∗
    structFieldRef client.Client go!"seqnum" cl ↦ W32 ((s : Int) - 1) ∗
    sendSt γ γc γm cl cid N ∗ sp.inv γ γc γm γl ∗ sp.clientSeq γ cid s ∗ toks γd s ∗
    isChanBag γch bv.Reply' (replyP γ cid γd) ∗
    client.nodeGhostB γ (sp.PNode.cl (cid.toNat - 1)) ∗ sp.allPredsReg γ γc)

theorem ready_unfold (b : Loc) (γ : sp.Names) (γc γm γl : GName) (cid : w32) (s : Nat) :
    ready b γ γc γm γl cid s ⊣⊢ iprop(∃ (bv : client.BufferClient) (cl : Loc) (N : Nat) (γch : ChanNames) (γd : GName),
    b ↦□ bv ∗ ⌜bv.Client' = cl ∧ cl ≠ null ∧ 1 ≤ cid.toInt⌝ ∗
    structFieldRef client.Client go!"seqnum" cl ↦ W32 ((s : Int) - 1) ∗
    sendSt γ γc γm cl cid N ∗ sp.inv γ γc γm γl ∗ sp.clientSeq γ cid s ∗ toks γd s ∗
    isChanBag γch bv.Reply' (replyP γ cid γd) ∗
    client.nodeGhostB γ (sp.PNode.cl (cid.toNat - 1)) ∗ sp.allPredsReg γ γc) := by
  unfold ready; exact .rfl

/-- Setting a fresh client's id (the adapter's `cli.ClientId = int32(c) + 1`): the struct, and
the fresh client back with the new id once stored. -/
theorem fresh_setId (cl : Loc) (cid cid' : w32) (maddr : GoString) (mport : w64) :
    fresh cl cid maddr mport ⊢ ∃ v : client.Client, cl ↦ v ∗
      (cl ↦ { v with ClientId' := cid' } -∗ fresh cl cid' maddr mport) := by
  unfold fresh
  iintro ⟨%v, Hcl, #Hq, %Hv⟩
  iexists v
  iframe Hcl
  iintro Hcl
  iexists { v with ClientId' := cid' }
  iframe Hcl Hq
  ipureintro
  simp only
  exact ⟨trivial, Hv.2⟩

end defs

section failed
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [π : NetProtoGS]
variable [net.Assumptions] [net.FieldAssumptions] [net.rpc.Assumptions]

/-- `Connect` failed: the client's struct, whatever it holds, with its master rpc client if any
(change log C4) (only `Disconnect` follows). -/
@[no_expose] def failed (b : Loc) : IProp netDistGF :=
  iprop(∃ (bv : client.BufferClient) (v : client.Client), b ↦□ bv ∗ bv.Client' ↦ v ∗
    dlog.quiet v.Logger' ∗ ⌜bv.Client' ≠ null⌝ ∗
    (⌜v.master' = null⌝ ∨ ∃ (W : net.rpc.RpcWorld netDistGF) (a : GoString),
      net.rpc.isClient v.master' W a) ∗
    ∃ srvs : List GoInterface, v.servers' ↦* srvs ∗
      [∗list] s ∈ srvs, ⌜s = interface.nil⌝ ∨ ∃ c side, net.rpc.connIface s c side)

theorem failed_unfold (b : Loc) :
    failed b ⊣⊢ iprop(∃ (bv : client.BufferClient) (v : client.Client), b ↦□ bv ∗ bv.Client' ↦ v ∗
    dlog.quiet v.Logger' ∗ ⌜bv.Client' ≠ null⌝ ∗
    (⌜v.master' = null⌝ ∨ ∃ (W : net.rpc.RpcWorld netDistGF) (a : GoString),
      net.rpc.isClient v.master' W a) ∗
    ∃ srvs : List GoInterface, v.servers' ↦* srvs ∗
      [∗list] s ∈ srvs, ⌜s = interface.nil⌝ ∨ ∃ c side, net.rpc.connIface s c side) := by
  unfold failed; exact .rfl

end failed

end client

end Perennial.github_com.imdea_software.swiftpaxos
