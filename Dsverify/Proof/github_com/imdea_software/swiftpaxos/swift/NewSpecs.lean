/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/NewSpecs.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`swift.New`'s callees (internal specs of the swift group, not frozen) and what `New` hands to
the run loop (notes/prove-swift.md §1, §4, §6-7, §10).

* `swift.SrvPkgFacts`: the package states' facts `New` uses (from `pkgStates`, at the link).
* `swift.initCs.specR`: `initCs` on the replica's table (all fourteen channels and entries).
* `swift.NewBatcher.specI`, `swift.NewReplyChan.specI`: the batcher's and the reply channel's
  goroutines, with their handles `swift.batcherH`, `swift.replyChanH`.
* `swift.Replica.run.specI`: the run loop, from `swift.runPre` (what `New` leaves).
* `hook.HookUser1.specI`.

**The reply goroutine's reading right** (`swift.replyRes`: a quarter of `ballot`) is the
goroutine's for its whole life (it reads `ballot` at each reply; notes §1.1). `New` spawns it
(`NewReplyChan`) before it writes `ballot` (`r.ballot = r.qs.BallotAt(0)`, then `0`), so the
goroutine gets a one-shot cell (Proof/swift/Cell.lean) that `New` fills once `ballot` is final;
the goroutine claims it at its first message, which carries `cellFilled` (each `replyArgP`).
At `stop()` the goroutine hands back on `ok` its reading right (or the claim token, if it never
claimed) and `historySize`.

The messages' predicates `swift.batchOpP`, `swift.replyArgP` say what a sender (a descriptor's
goroutine) must provide: the replica's sending context (`swift.sendCtx`: its embedded replica's
`isReplica`, its sender, the `cs` codes, all persistent once the run loop started) and the
message's resources with its protocol witness. Their exact contents are fixed by the batcher's
and the reply goroutine's proofs (notes §10).
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.client.NodeGhost
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RunSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.ShInv
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.Cell
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.AqQuorum
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.client.InitCsDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.NewSpec
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.WriterSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.ConnSpecs
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.New
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.MsgSetQ

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

/-- The reply cell's namespace. -/
def swift.replyCellN : Namespace := ndot nroot "swiftpaxos.replyCell"

instance swift.BatcherOp_countableC [GooseExts] : Pos.Countable swift.BatcherOp :=
  countableOfLeftInverse (fun o : swift.BatcherOp => (o.cid', o.msg', o.sendToClient'))
    (fun p => ⟨p.1, p.2.1, p.2.2⟩) (fun _ => rfl)

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions]

/-- The `cs` codes `initCs` registers (table ids from 9, in registration order: the model's
`Msg.code` for the swift messages). -/
def swift.csCodes (v : swift.CommunicationSupply) : Prop :=
  v.fastAckRPC' = W8 9 ∧ v.fastAckClientRPC' = W8 10 ∧ v.slowAckRPC' = W8 11 ∧
  v.lightSlowAckRPC' = W8 12 ∧ v.acksRPC' = W8 13 ∧ v.optAcksRPC' = W8 14 ∧
  v.replyRPC' = W8 15 ∧ v.newLeaderRPC' = W8 16 ∧ v.newLeaderAckNRPC' = W8 17 ∧
  v.syncRPC' = W8 18 ∧ v.pingRPC' = W8 19 ∧ v.pingRepRPC' = W8 20 ∧ v.collectRPC' = W8 21 ∧
  v.acceptRPC' = W8 22

/-- The table's entry of code `c`: a fresh object of the registered type and its channel. -/
def swift.entryIs (M : GMap w8 rpc.Pair') (c : w8) (ty : go.GoType) (ch : GoChan) : Prop :=
  ∃ o : Loc, M !! c = some ⟨interface.mkOk (go.GoType.PointerType ty) #o, ch⟩

/-- What `initCs` leaves in the table: the fourteen entries, nothing else. -/
def swift.tableIs (v : swift.CommunicationSupply) (M : GMap w8 rpc.Pair') : Prop :=
  swift.entryIs M (W8 9) swift.MFastAck.ty v.fastAckChan' ∧
  swift.entryIs M (W8 10) swift.MFastAckClient.ty v.fastAckClientChan' ∧
  swift.entryIs M (W8 11) swift.MSlowAck.ty v.slowAckChan' ∧
  swift.entryIs M (W8 12) swift.MLightSlowAck.ty v.lightSlowAckChan' ∧
  swift.entryIs M (W8 13) swift.MAcks.ty v.acksChan' ∧
  swift.entryIs M (W8 14) swift.MOptAcks.ty v.optAcksChan' ∧
  swift.entryIs M (W8 15) swift.MReply.ty v.replyChan' ∧
  swift.entryIs M (W8 16) swift.MNewLeader.ty v.newLeaderChan' ∧
  swift.entryIs M (W8 17) swift.MNewLeaderAckN.ty v.newLeaderAckNChan' ∧
  swift.entryIs M (W8 18) swift.MSync.ty v.syncChan' ∧
  swift.entryIs M (W8 19) swift.MPing.ty v.pingChan' ∧
  swift.entryIs M (W8 20) swift.MPingRep.ty v.pingRepChan' ∧
  swift.entryIs M (W8 21) swift.MCollect.ty v.collectChan' ∧
  swift.entryIs M (W8 22) swift.MAccept.ty v.acceptChan' ∧
  (∀ c, (M !! c).isSome → 9 ≤ c.toNat ∧ c.toNat ≤ 22)

/-- The fourteen fresh channels `initCs` made. -/
def swift.csChans (v : swift.CommunicationSupply) : IProp netDistGF :=
  iprop(swift.rd.freshChan v.fastAckChan' ∗ swift.rd.freshChan v.fastAckClientChan' ∗
    swift.rd.freshChan v.slowAckChan' ∗ swift.rd.freshChan v.lightSlowAckChan' ∗
    swift.rd.freshChan v.acksChan' ∗ swift.rd.freshChan v.optAcksChan' ∗
    swift.rd.freshChan v.replyChan' ∗ swift.rd.freshChan v.newLeaderChan' ∗
    swift.rd.freshChan v.newLeaderAckNChan' ∗ swift.rd.freshChan v.syncChan' ∗
    swift.rd.freshChan v.pingChan' ∗ swift.rd.freshChan v.pingRepChan' ∗
    swift.rd.freshChan v.collectChan' ∗ swift.rd.freshChan v.acceptChan')

/-- The replica's sending context (persistent, once the run loop started): the embedded
replica's `isReplica`, the sender, the `cs` codes. -/
def swift.sendCtx (γ : sp.Names) (γc γm : GName) (rp : Loc) : IProp netDistGF :=
  iprop(∃ (rr s : Loc) (N : Nat) (me : w32) (γw : GName) (γs : ChanNames)
      (csv : swift.CommunicationSupply),
    swift.fld rp go!"Replica" ↦□ rr ∗ replica.isReplica rr γ γc γm γw N me ∗
    swift.fld rp go!"sender" ↦□ s ∗ isChanBag γs s (replica.sendArgP rr γ γc γm N) ∗
    swift.fld rp go!"cs" ↦□ csv ∗ ⌜swift.csCodes csv⌝)

instance swift.sendCtx_persistent (γ : sp.Names) (γc γm : GName) (rp : Loc) :
    Persistent (swift.sendCtx γ γc γm rp) := by
  unfold swift.sendCtx; infer_instance

/-- The replica's sending context with its size `N` and id `me` (persistent). -/
def swift.sendCtxN (γ : sp.Names) (γc γm : GName) (rp : Loc) (N : Nat) (me : w32) :
    IProp netDistGF :=
  iprop(∃ (rr s : Loc) (γw : GName) (γs : ChanNames) (csv : swift.CommunicationSupply),
    swift.fld rp go!"Replica" ↦□ rr ∗ replica.isReplica rr γ γc γm γw N me ∗
    swift.fld rp go!"sender" ↦□ s ∗ isChanBag γs s (replica.sendArgP rr γ γc γm N) ∗
    swift.fld rp go!"cs" ↦□ csv ∗ ⌜swift.csCodes csv⌝)

instance swift.sendCtxN_persistent (γ : sp.Names) (γc γm : GName) (rp : Loc) (N : Nat)
    (me : w32) : Persistent (swift.sendCtxN γ γc γm rp N me) := by
  unfold swift.sendCtxN; infer_instance

/-- An `MFastAck`'s Go value as the model's (its slices read-only). -/
def swift.fastAckRepr (fa : swift.MFastAck) (f : sp.FastAck) : IProp netDistGF :=
  iprop(⌜fa.Replica' = f.rep ∧ fa.Ballot' = f.bal ∧ swift.toCmdId fa.CmdId' = f.id ∧
      fa.Seqnum' = f.seqnum⌝ ∗
    fa.Dep' ↦*□ f.dep.map swift.ofCmdId ∗ fa.Checksum' ↦*□ f.cs.map swift.handler.shashOf)

instance swift.fastAckRepr_persistent (fa : swift.MFastAck) (f : sp.FastAck) :
    Persistent (swift.fastAckRepr fa f) := by
  unfold swift.fastAckRepr; infer_instance

/-- An `MLightSlowAck`'s Go value as the model's. -/
def swift.slowAckRepr (sa : swift.MLightSlowAck) (s : sp.SlowAck) : Prop :=
  sa.Replica' = s.rep ∧ sa.Ballot' = s.bal ∧ swift.toCmdId sa.CmdId' = s.id

/-- An `Ack` (an `MOptAcks` entry) as the model's (its slices read-only). -/
def swift.ackRepr (a : swift.Ack) (A : sp.Ack) : IProp netDistGF :=
  iprop(⌜swift.toCmdId a.CmdId' = A.id ∧ a.Seqnum' = A.seqnum⌝ ∗
    a.Dep' ↦*□ A.dep.map swift.ofCmdId ∗ a.Checksum' ↦*□ A.cs.map swift.handler.shashOf)

instance swift.ackRepr_persistent (a : swift.Ack) (A : sp.Ack) :
    Persistent (swift.ackRepr a A) := by
  unfold swift.ackRepr; infer_instance

/-- What the client's copy of a fast ack (`MFastAckClient`) needs besides the ack's own
witness: the command, the configuration, the fast-read condition at the leader. -/
def swift.facClientOk (γ : sp.Names) (γc γm : GName) (f : sp.FastAck) : IProp netDistGF :=
  iprop(∃ (c : sp.Cmd) (N : Nat) (fr : Bool) (l : List GoString),
    sp.cmdIs γ f.id c ∗ sp.cfg γc γm N fr l ∗
    ⌜sp.rid f.rep = sp.leaderOf N (sp.bal f.bal) → fr = true ∧ c.isGet⌝)

instance swift.facClientOk_persistent (γ : sp.Names) (γc γm : GName) (f : sp.FastAck) :
    Persistent (swift.facClientOk γ γc γm f) := by
  unfold swift.facClientOk; infer_instance

/-- What a fast-ack operation of the batcher carries: the sending context, the owned
`*MFastAck` (freed after), its model ack sent by this replica with its witness, well formed
and not shaped as a slow ack (`Dep ≠ [id]`), and for a client copy its extra witness. -/
def swift.batchFastP (γ : sp.Names) (γc γm : GName) (rp : Loc) (op : swift.BatcherOp) :
    IProp netDistGF :=
  iprop(∃ (N : Nat) (me : w32) (l : Loc) (fa : swift.MFastAck) (f : sp.FastAck),
    swift.sendCtxN γ γc γm rp N me ∗
    ⌜op.msg' = interface.mkOk (go.GoType.PointerType swift.MFastAck.ty) #l⌝ ∗ l ↦ fa ∗
    swift.fastAckRepr fa f ∗ sp.fastAckOk γ f ∗
    ⌜f.rep = me ∧ f.wf ∧ f.dep ≠ [f.id] ∧ f.cs.length + 1 < 2 ^ 62⌝ ∗
    (if op.sendToClient' then swift.facClientOk γ γc γm f else True))

/-- What a slow-ack operation carries: the sending context, the `*MLightSlowAck` (read-only:
the batcher only reads it, `freeSlowAck` is a no-op; the sender, `fastAckFromLeader`, reads it
after sending; round 11), its model ack sent by this replica with its witness. -/
def swift.batchSlowP (γ : sp.Names) (γc γm : GName) (rp : Loc) (op : swift.BatcherOp) :
    IProp netDistGF :=
  iprop(∃ (N : Nat) (me : w32) (l : Loc) (sa : swift.MLightSlowAck) (s : sp.SlowAck),
    swift.sendCtxN γ γc γm rp N me ∗
    ⌜op.msg' = interface.mkOk (go.GoType.PointerType swift.MLightSlowAck.ty) #l⌝ ∗ l ↦□ sa ∗
    ⌜swift.slowAckRepr sa s ∧ s.rep = me⌝ ∗ sp.msgOk γ γc γm (.lightSlowAck s))

/-- The batcher `b` (persistent): its two channels of operations. -/
def swift.batcherH (γ : sp.Names) (γc γm : GName) (rp b : Loc) : IProp netDistGF :=
  iprop(∃ (fa ls : GoChan) (γ1 γ2 : ChanNames), b ↦□ swift.Batcher.mk fa ls ∗
    isChanBag γ1 fa (swift.batchFastP γ γc γm rp) ∗ isChanBag γ2 ls (swift.batchSlowP γ γc γm rp))

instance swift.batcherH_persistent (γ : sp.Names) (γc γm : GName) (rp b : Loc) :
    Persistent (swift.batcherH γ γc γm rp b) := by
  unfold swift.batcherH; infer_instance

/-- The reply goroutine's reading right: a quarter of `ballot`, of value `b0` (its epoch's). -/
def swift.replyRes (rp : Loc) (b0 : w32) : IProp netDistGF :=
  typedPointsto (swift.fld rp go!"ballot") b0 (DFrac.own (1 : Qp).half.half)

/-- What the leader's reply for `x` needs (persistent; the descriptor that executed `x` gives
it, from its execution record and its sequence: notes/prove-swift.md §12): for the replica `me`
of `N`, if `me` leads `b0` (the goroutine's test `r.Id == r.leader()`), the `MReply` with the
checksum `Hs ++ [d]` (`d` the dependencies' hash `clientChecksum` computes) and the value `vals`
carries its witness. -/
def swift.replyOk (γ : sp.Names) (γc γm : GName) (N : Nat) (me b0 : w32) (x : swift.CommandId)
    (D : List swift.CommandId) (Hs : List sp.Hash) (vals : List w8) : IProp netDistGF :=
  iprop(□ ∀ d : sp.Hash, ⌜me = BitVec.srem b0 (W32 (sint.Z (W64 (N : Int))))⌝ -∗
    sp.depHash (D.map toCmdId) d -∗
    sp.msgOk γ γc γm (.reply me b0 (toCmdId x) (Hs ++ [d]) vals))

instance swift.replyOk_persistent (γ : sp.Names) (γc γm : GName) (N : Nat) (me b0 : w32)
    (x : swift.CommandId) (D : List swift.CommandId) (Hs : List sp.Hash) (vals : List w8) :
    Persistent (swift.replyOk γ γc γm N me b0 x D Hs vals) := by
  unfold swift.replyOk; infer_instance

/-- A history slot (what the reply goroutine sends on a descriptor's channel): an index of
`history` (10010001 slots, `HISTORY_SIZE`), written under `historyL`. -/
def swift.slotIn (n : w64) : Prop := 0 ≤ sint.Z n ∧ sint.Z n < 10010001

/-- What a `*replyArgs` of the epoch of ballot `b0` carries: the arguments (the copies of the
dependencies and hashes owned, the value read-only), the cell's witness, the replica's sending
context (its `isReplica`, the sender, the `cs` codes, `optExec`), the proposal (read-only: the
`GPropose` and its `ClientId`; request SWC-1: `proposeP`'s `ClientId` persistent), the finish
channel taking history slots, and the leader's reply witness (`replyOk`). -/
def swift.replyArgP (γ : sp.Names) (γc γm : GName) (rp : Loc) (γl : swift.CellNames)
    (b0 : w32) (a : Loc) : IProp netDistGF :=
  iprop(∃ (ra : swift.replyArgs) (D : List swift.CommandId) (Hs : List sp.Hash) (vals : List w8)
      (γf : ChanNames) (F : GoInterface → IProp netDistGF)
      (rr s p w mu : Loc) (addr : GoString) (N : Nat) (me : w32) (γw : GName) (γs : ChanNames)
      (csv : swift.CommunicationSupply) (oe : Bool),
    a ↦ ra ∗ swift.cellFilled γl ∗
    ra.dep' ↦* D ∗ ra.hs' ↦* Hs.map swift.handler.shashOf ∗ ra.val' ↦*□ vals ∗
    ⌜sp.hashesWf Hs ∧ Hs.length + 1 < 2 ^ 62 ∧ D.length < 2 ^ 62 ∧ vals.length < 2 ^ 62⌝ ∗
    swift.fld rp go!"Replica" ↦□ rr ∗ replica.isReplica rr γ γc γm γw N me ∗
    swift.fld rp go!"sender" ↦□ s ∗ isChanBag γs s (replica.sendArgP rr γ γc γm N) ∗
    swift.fld rp go!"cs" ↦□ csv ∗ ⌜swift.csCodes csv⌝ ∗ swift.fld rp go!"optExec" ↦□ oe ∗
    ra.propose' ↦□ replica.defs.GPropose.mk p w mu false addr ∗
    typedPointsto (p.[replica.defs.Propose, go!"ClientId"]) ra.cmdId'.ClientId' DFrac.discard ∗
    isChanBag γf ra.finish' F ∗
    □ (∀ n : w64, ⌜swift.slotIn n⌝ -∗ F (interface.mkOk go.int #n)) ∗
    swift.replyOk γ γc γm N me b0 ra.cmdId' D Hs vals)

/-- The reply cell's content (round 13, GAP H-size): the reading right and `historySize`
(whose writer, `handleSync`'s `r.historySize = 0`, runs after `NewReplyChan` and before the
goroutine's first message: the goroutine claims both with that message). -/
def swift.replyCellRes (rp : Loc) (b0 : w32) : IProp netDistGF :=
  iprop(swift.replyRes rp b0 ∗ ∃ n : w64, swift.fld rp go!"historySize" ↦ n ∗
    ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ 10010001⌝)

/-- What `stop()` gets back on `ok`: the cell's content (the reading right and `historySize`),
or the claim token if the goroutine never claimed it (then the cell holds them). -/
def swift.replyBack (rp : Loc) (γl : swift.CellNames) (b0 : w32) : IProp netDistGF :=
  iprop(swift.replyCellRes rp b0 ∨ swift.cellClaimTok γl)

/-- The reply channel `rc` of epoch ballot `b0` (its goroutine running), and the right to stop
it once. -/
def swift.replyChanH (γ : sp.Names) (γc γm : GName) (rp : Loc) (γl : swift.CellNames)
    (b0 : w32) (rc : Loc) : IProp netDistGF :=
  iprop(∃ (rep : Loc) (ok ex args : GoChan) (γok γex γa : ChanNames),
    rc ↦□ swift.replyChan.mk rep ok ex args ∗
    isChanBag γa args (fun a : Loc => swift.replyArgP γ γc γm rp γl b0 a) ∗
    isChanBag γex ex (fun _ : Unit => iprop(True)) ∗
    isChanBag γok ok (fun _ : Unit => swift.replyBack rp γl b0) ∗
    swift.isCell swift.replyCellN γl (swift.replyCellRes rp b0))

/-- What the descriptors' pool holds: owned `*commandDesc`s. -/
def swift.descP (x : GoInterface) : IProp netDistGF :=
  iprop(∃ (dl : Loc) (cd : swift.commandDesc),
    ⌜x = interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #dl⌝ ∗ dl ↦ cd)

/-- The package states' facts `New` uses. -/
structure swift.SrvPkgFacts : Prop where
  rep : isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.replica ⊢
    errors.newVar replica.NO_QUORUM_FILE go!"Quorum file is not provided" ∗
    errors.newVar replica.THREE_QUARTERS go!"ThreeQuarters"
  dfs : isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.replica.defs ⊢
    typedPointsto (globalAddr replica.defs.LatencyConf) (go!"" : GoString) DFrac.discard

/-- **What `New` hands to the run loop** of replica `rid` (node `k`, address `a`): the
persistent context (the receiver's resources, the protocol, the read-only fields and globals,
the sender, the batcher, the reply channel's cell filled), the run loop's fields at their
initial values, `New`'s fresh objects, and the embedded replica's `connPre` once its table is
shown to be `tableOk` (the wand: the table's entries need the messages' `Unmarshal` specs). -/
def swift.runPre (rp : Loc) (γ : sp.Names) (γc γm γl : GName) (N k : Nat) (me : w32)
    (fr : Bool) (l : List GoString) (a ip : GoString) (pl : w64) : IProp netDistGF :=
  iprop(∃ (rr tbl s b rc qs : Loc) (γs : ChanNames) (γrl : swift.CellNames) (γd γdc1 γdl : GName)
      (dm1 : GoSlice) (dch rch : GoChan) (γdc γrc : ChanNames) (hsl : GoSlice)
      (km hm pm propm accm waitm sam : GoMap) (sq fq : replica.QuorumI)
      (csv : swift.CommunicationSupply) (ents : GMap w8 rpc.Pair') (nid : w8) (d : w64),
    -- persistent context
    swift.rcvrRes rp γc γm ∗ sp.inv γ γc γm γl ∗ sp.cfg γc γm N fr l ∗
    ⌜sp.rid me < N ∧ nodeOf l (sp.rid me) = some k ∧ 0 ≤ sint.Z me ∧ 1 ≤ N ∧ N ≤ 7⌝ ∗
    swift.fld rp go!"Replica" ↦□ rr ∗ replica.fld rr go!"Shutdown" ↦□ false ∗
    replica.fld rr go!"N" ↦□ (W64 N) ∗ replica.fld rr go!"Id" ↦□ me ∗
    swift.fld rp go!"sender" ↦□ s ∗ isChanBag γs s (replica.sendArgP rr γ γc γm N) ∗
    swift.fld rp go!"batcher" ↦□ b ∗ swift.batcherH γ γc γm rp b ∗
    swift.fld rp go!"SQ" ↦□ sq ∗ replica.mset.quorumIs sq (N / 2 + 1) (fun _ => True) ∗
    swift.fld rp go!"history" ↦□ hsl ∗
    swift.fld rp go!"historyStart" ↦□ (W64 0) ∗ swift.fld rp go!"optExec" ↦□ true ∗
    swift.fld rp go!"fastRead" ↦□ fr ∗ swift.fld rp go!"fixedMajority" ↦□ true ∗
    swift.fld rp go!"poolLevel" ↦□ pl ∗ swift.fld rp go!"slowAddrs" ↦□ sam ∗
    sam ↦$□ (∅ : GMap GoString Unit) ∗
    swift.fld rp go!"deliverChan" ↦□ dch ∗ swift.fld rp go!"recheckChan" ↦□ rch ∗
    globalAddr swift.MaxDescRoutines ↦□ d ∗ ⌜0 ≤ sint.Z d ∧ sint.Z d ≤ 100⌝ ∗
    globalAddr swift.useFastAckPool ↦□ (decide (1 < sint.Z pl)) ∗
    typedPointsto (globalAddr _root_.Perennial.github_com.orcaman.concurrent_map.SHARD_COUNT)
      (W64 32768) DFrac.discard ∗
    swift.cellFilled γrl ∗
    -- change log C17: gob's codec (the message table's `MSync` decoder)
    encoding.gob.codecSet (GF := netDistGF) ∗
    -- the run loop's fields (classes L and E) at their initial values
    sp.replicaStart γ k ∗
    typedPointsto (swift.fld rp go!"ballot") (W32 0) (DFrac.own (1 : Qp).half) ∗
    swift.fld rp go!"cballot" ↦ (W32 0) ∗ swift.fld rp go!"status" ↦ swift.stNORMAL ∗
    swift.fld rp go!"FQ" ↦ fq ∗ swift.fqOk fq N 0 ∗
    swift.fld rp go!"cmdDescs" ↦ dm1 ∗
    github_com.orcaman.concurrent_map.isCMapV dm1 γdc1 (swift.descR γd) ∗
    github_com.orcaman.concurrent_map.cmapView γdc1 ∅ ∗
    ([∗list] _x ∈ List.replicate github_com.orcaman.concurrent_map.cmapReaders (),
      github_com.orcaman.concurrent_map.readerV dm1 γdc1 (swift.descR γd)) ∗
    ghostMapAuth γd 1 (∅ : GMap Loc sp.CmdId) ∗
    -- `delivered` (its map is in `rcvrRes`): the view and the reader bundles (P2-B: `cntL` hands them out)
    (∃ dm2 : GoSlice, swift.fld rp go!"delivered" ↦□ dm2 ∗
      github_com.orcaman.concurrent_map.isCMapV dm2 γdl swift.deliveredR ∗
      github_com.orcaman.concurrent_map.cmapView γdl ∅ ∗
      ([∗list] _x ∈ List.replicate github_com.orcaman.concurrent_map.cmapReaders (),
        github_com.orcaman.concurrent_map.readerV dm2 γdl swift.deliveredR)) ∗
    swift.fld rp go!"repchan" ↦ rc ∗ swift.replyChanH γ γc γm rp γrl (W32 0) rc ∗
    swift.fld rp go!"keys" ↦ km ∗ km ↦$ (∅ : GMap w64 GoInterface) ∗
    swift.fld rp go!"hlog" ↦ hm ∗ hm ↦$ (∅ : GMap w64 Loc) ∗
    swift.fld rp go!"cntL" ↦ Perennial.zero_val sync.Mutex ∗ swift.fld rp go!"seqnum" ↦ (W64 0) ∗
    swift.fld rp go!"pendingHashUpds" ↦ pm ∗ pm ↦$ (∅ : GMap swift.CommandId Loc) ∗
    swift.fld rp go!"historyL" ↦ Perennial.zero_val sync.Mutex ∗
    hsl ↦* List.replicate 10010001 (Perennial.zero_val swift.commandStaticDesc) ∗
    swift.fld rp go!"qs" ↦□ qs ∗
    swift.fld rp go!"cs" ↦ csv ∗ ⌜swift.csCodes csv ∧ swift.tableIs csv ents⌝ ∗ swift.csChans csv ∗
    swift.fld rp go!"execL" ↦ Perennial.zero_val sync.Mutex ∗
    swift.fld rp go!"execLog" ↦ (slice.nil : GoSlice) ∗
    swift.descPoolOk rp ∗
    swift.fld rp go!"routineCount" ↦ (W64 0) ∗
    swift.fld rp go!"recStart" ↦ (Perennial.zero_val time.Time) ∗
    swift.fld rp go!"newLeaderAckNs" ↦ (null : Loc) ∗
    swift.fld rp go!"newLeaderAckNsBallot" ↦ (W32 0) ∗
    swift.fld rp go!"proposes" ↦ propm ∗ propm ↦$ (∅ : GMap swift.CommandId Loc) ∗
    swift.fld rp go!"handled" ↦ (slice.nil : GoSlice) ∗
    swift.fld rp go!"lastSync" ↦ (null : Loc) ∗
    swift.fld rp go!"acceptL" ↦ Perennial.zero_val sync.Mutex ∗
    swift.fld rp go!"accepted" ↦ accm ∗ accm ↦$ (∅ : GMap swift.CommandId Unit) ∗
    swift.fld rp go!"waiting" ↦ waitm ∗ waitm ↦$ (∅ : GMap swift.CommandId GoSlice) ∗
    swift.fld rp go!"rechecks" ↦ (slice.nil : GoSlice) ∗
    isChan dch γdc swift.CommandId ∗ ownChan γdc swift.CommandId (ChanState.Buffered []) ∗
    isChan rch γrc swift.CommandId ∗ ownChan γrc swift.CommandId (ChanState.Buffered []) ∗
    -- the embedded replica: the fields the run loop and the descriptors use besides `connPre`'s
    (∃ (ppsl : GoSlice) (pp : List w32), replica.fld rr go!"PreferredPeerOrder" ↦ ppsl ∗
      ppsl ↦* pp ∗ ⌜pp.length = N ∧ ∀ p ∈ pp, 0 ≤ p.toInt ∧ p.toInt < N⌝) ∗
    (∃ stp : Loc, replica.fld rr go!"State" ↦ stp ∗ state.ownState stp (fun _ => none)) ∗
    replica.fld rr go!"Exec" ↦□ true ∗ (∃ dr : Bool, replica.fld rr go!"Dreply" ↦□ dr) ∗
    -- the embedded replica, once its table is `tableOk`
    replica.fld rr go!"RPC" ↦□ tbl ∗ rpc.isTable tbl (DFrac.own 1) nid ents ∗
    (sp.tableOk γ γc γm ents -∗ rpc.isTable tbl DFrac.discard nid ents -∗
      replica.connPre rr γ γc γm γl N me a ip) ∗
    -- SWB-11 (fork e411c02): the run loop's own map of the proposals' dependencies
    (∃ pdm : GoMap, swift.fld rp go!"proposeDeps" ↦ pdm ∗ pdm ↦$ (∅ : GMap swift.CommandId swift.Dep)) ∗
    -- L2 (notes/prove-s2-e.md): the node's claimed ghost
    client.nodeGhostOk γ (sp.PNode.rep k))

end defs

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions]

/-- `initCs(&r.cs, r.RPC)` on the replica's empty table: the fourteen fresh channels, their
codes, and the table's entries (`tableIs`). -/
abbrev swift.initCs.specR : Prop :=
  ∀ (cs t : Loc) (v : swift.CommunicationSupply),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      cs ↦ v ∗ rpc.tblOwn t (W8 9) ∅ }}
    (App (App (Val (@! swift.initCs)) (Val #cs)) (Val #t))
  {{ RET #(); ∃ (v' : swift.CommunicationSupply) (M : GMap w8 rpc.Pair'),
      cs ↦ v' ∗ rpc.tblOwn t (W8 23) M ∗ swift.csChans v' ∗
      ⌜swift.csCodes v' ∧ swift.tableIs v' M ∧ v'.maxLatency' = W64 0⌝ }}

/-- `NewBatcher(r, 16, releaseFastAck, func(*MLightSlowAck) {})`: the batcher, its goroutine
running (it reads `r.Shutdown`, then each operation's context). -/
abbrev swift.NewBatcher.specI : Prop :=
  ∀ (rp rr : Loc) (γ : sp.Names) (γc γm : GName) (fs : GoFunc) (upv : Bool),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      swift.fld rp go!"Replica" ↦□ rr ∗ replica.fld rr go!"Shutdown" ↦□ false ∗
      (□ ∀ (x : Loc) (Φ : val → IProp netDistGF), ▷ Φ #() -∗ WP (App (Val #fs) (Val #x)) {{ Φ }}) ∗
      globalAddr swift.useFastAckPool ↦□ upv }}
    (App (App (App (App (Val (@! swift.NewBatcher)) (Val #rp)) (Val #(W64 16)))
      (Val (@! swift.releaseFastAck))) (Val #fs))
  {{ (b : Loc), RET #b; swift.batcherH γ γc γm rp b }}

/-- `NewReplyChan(r)`, before the goroutine's reading right `replyRes rp b0` exists: the cell
`γl` (empty, its claim token to the goroutine) holds it once filled, with `historySize`
(round 13, GAP H-size: the caller keeps `historySize` until it fills the cell). -/
abbrev swift.NewReplyChan.specI : Prop :=
  ∀ (rp rr : Loc) (hsl : GoSlice) (γ : sp.Names) (γc γm : GName)
    (γl : swift.CellNames) (b0 : w32),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      swift.fld rp go!"Replica" ↦□ rr ∗ replica.fld rr go!"Shutdown" ↦□ false ∗
      swift.fld rp go!"history" ↦□ hsl ∗
      swift.isCell swift.replyCellN γl (swift.replyCellRes rp b0) ∗ swift.cellClaimTok γl ∗
      ⌜sint.Z hsl.len = 10010001⌝ }}
    (App (Val (@! swift.NewReplyChan)) (Val #rp))
  {{ (rc : Loc), RET #rc; swift.replyChanH γ γc γm rp γl b0 rc }}

/-- `r.run()` (the run loop: connections, the clients' acceptor, then the `select` loop; it
never returns, `Shutdown` being `false`), from what `New` leaves. Its proof is the run loop's
(notes §10); here a hypothesis of `New`'s proof. -/
abbrev swift.Replica.run.specI : Prop :=
  ∀ (rp : Loc) (γ : sp.Names) (γc γm γl : GName) (N k : Nat) (me : w32) (fr : Bool)
    (l : List GoString) (a ip : GoString) (pl : w64),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      swift.runPre rp γ γc γm γl N k me fr l a ip pl }}
    (App (Val (rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"run")) (Val #()))
  {{ RET #(); True }}

/-- `hook.HookUser1(f)`: registers `f` for `SIGUSR1`, which the net model never delivers
(`f` never runs). -/
abbrev hook.HookUser1.specI : Prop :=
  ∀ (f : GoFunc),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.hook }}
    (App (Val (@! hook.HookUser1)) (Val #f))
  {{ RET #(); True }}

end specs

end Perennial.github_com.imdea_software.swiftpaxos
