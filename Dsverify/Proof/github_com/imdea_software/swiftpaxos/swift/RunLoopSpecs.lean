/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/RunLoopSpecs.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The run loop's internal statements (swift.go `run`; notes/prove-swift.md §11, §13).

* `swift.tableAllocH`: the table's entries are `tableOk` once the fourteen channels are bags
  (the message types' `New`/`Unmarshal` specs; Proof/swift/MsgRep.lean's `msgRep`, `csBags`).
* `swift.runLoopPre`: what the `select` loop starts from: `New`'s `runPre` less what the
  connection phase used (the table's wand, `cs` owned), plus what it produced: the embedded
  replica's `isReplica` (fresh `γw`), the channels' bags, `cs` read-only (its `maxLatency`
  written).
* `swift.runAckW`: the witness of a fast ack the run loop hands to the descriptors: an
  `MFastAck`'s own (`fastAckOk`), or an `MOptAcks` entry's (`ackOk` of the sender's ballot and C16's
  disjunct) for the `MFastAck` the loop builds from it (a slow entry `Dep = [id]` becomes
  `Dep = nil`).
* `swift.RunArms rp γ γc γm I`: the specs, over the loop invariant `I`, of the callees of the
  `select`'s ten arms (`recoveryBallot`, `reinitNewLeaderAckNs`, `handleNewLeader`, `getCmdDesc`
  with "deliver"/"recheck" or a slow ack, `handleProposal`, `leader`, `leaderAckHash`,
  `getCmdDescSeq` with a fast ack, `handleSync`) and of `drainRechecks`, which ends each step
  (N2-loop). Each keeps `I`.
* `swift.RunLoopH X I`: the loop's invariant `I rp γ γc γm x` (`x : X` its ghost names and
  values) is established from `runLoopPre` (the allocations: `nodeInvD`, the lock invariants,
  the epoch pool, the descriptor channels' bags) and the arms' specs hold of it. The run loop's
  proof (RunLoop.lean) is over this hypothesis; its proof is the handlers' (sv-swa, sv-swb) and
  the allocation (§13).
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.client.NodeGhost
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.MsgRep
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.AqQuorum
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.PoolFns
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.MarshalSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.ConnSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.ServeSpecs
public import Dsverify.Spec.encoding.gob.Defs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.MsgSetQ

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions] [swift.Assumptions]

/-- The table's entries, once the channels are bags (the swift messages' `New`/`Unmarshal`),
under the package's facts: `swift`'s package (its `errVarintOverflow`, the readers' packages),
the fast-ack pool's switch `useFastAckPool ↦□ u`, and gob's codec (change log C17: `New` takes
`codecSet`; proved by `swift.tableAllocH_proof`, Proof/swift/TableAllocH.lean). -/
def swift.tableAllocH : Prop :=
  ∀ (γ : sp.Names) (γc γm : GName) (v : swift.CommunicationSupply) (M : GMap w8 rpc.Pair')
    (u : Bool),
    isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      encoding.gob.codecSet (GF := netDistGF) ∗
      typedPointsto (globalAddr swift.useFastAckPool) u DFrac.discard ∗
      swift.csChans v ∗ ⌜swift.tableIs v M⌝ ⊢
      |={⊤}=> ∃ n : swift.CsNames, sp.tableOk γ γc γm M ∗ swift.csBags γ γc γm v n

/-- The `MFastAck` built from an `MOptAcks` entry `a` of `r`'s `MOptAcks` of ballot `b`. -/
def swift.fastOfAck (r b : w32) (a : sp.Ack) : sp.FastAck :=
  ⟨r, b, a.id, if a.dep = [a.id] then [] else a.dep, a.cs, a.seqnum⟩

/-- The witness of a fast ack the run loop hands on (see the file header). -/
def swift.runAckW (γ : sp.Names) (γc γm : GName) (f : sp.FastAck) : IProp netDistGF :=
  iprop(sp.fastAckOk γ f ∨
    ∃ a : sp.Ack, ⌜f = swift.fastOfAck f.rep f.bal a ∧ sp.wireOk f.rep f.bal⌝ ∗
      sp.ackOk γ (sp.rid f.rep) (sp.bal f.bal) a ∗
      (⌜a.dep ≠ [a.id]⌝ ∨ ∃ N fr l, sp.cfg γc γm N fr l ∗ ⌜sp.rid f.rep ≠ sp.leaderOf N (sp.bal f.bal)⌝))

instance swift.runAckW_persistent (γ : sp.Names) (γc γm : GName) (f : sp.FastAck) :
    Persistent (swift.runAckW γ γc γm f) := by
  unfold swift.runAckW; infer_instance

end defs

section defs2
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]

/-- What the `select` loop starts from (see the file header): `runPre` with the connection
phase done. -/
def swift.runLoopPre (rp : Loc) (γ : sp.Names) (γc γm γl : GName) (N k : Nat) (me : w32)
    (fr : Bool) (l : List GoString) (pl : w64) (γw : GName) (csv : swift.CommunicationSupply)
    (n : swift.CsNames) : IProp netDistGF :=
  iprop(∃ (rr s b rc qs : Loc) (γs : ChanNames) (γrl : swift.CellNames) (γd γdc1 γdl : GName)
      (dm1 : GoSlice) (dch rch : GoChan) (γdc γrc : ChanNames) (hsl : GoSlice)
      (km hm pm propm accm waitm sam : GoMap) (sq fq : replica.QuorumI) (d : w64),
    -- persistent context
    swift.rcvrRes rp γc γm ∗ sp.inv γ γc γm γl ∗ sp.cfg γc γm N fr l ∗
    ⌜sp.rid me < N ∧ nodeOf l (sp.rid me) = some k ∧ 0 ≤ sint.Z me ∧ 1 ≤ N ∧ N ≤ 7⌝ ∗
    swift.fld rp go!"Replica" ↦□ rr ∗ replica.isReplica rr γ γc γm γw N me ∗
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
    swift.fld rp go!"cs" ↦□ csv ∗ ⌜swift.csCodes csv⌝ ∗ swift.csBags γ γc γm csv n ∗
    -- (round 18) gob's codec, for `MSync.Marshal` (`handleNewLeaderAckNs`)
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
    isChanBag γdc dch (fun _ : swift.CommandId => iprop(True)) ∗
    isChanBag γrc rch (fun _ : swift.CommandId => iprop(True)) ∗
    (∃ (ppsl : GoSlice) (pp : List w32), replica.fld rr go!"PreferredPeerOrder" ↦ ppsl ∗
      ppsl ↦* pp ∗ ⌜pp.length = N ∧ ∀ p ∈ pp, 0 ≤ p.toInt ∧ p.toInt < N⌝) ∗
    (∃ stp : Loc, replica.fld rr go!"State" ↦ stp ∗ state.ownState stp (fun _ => none)) ∗
    replica.fld rr go!"Exec" ↦□ true ∗ replica.fld rr go!"Shutdown" ↦□ false ∗
    (∃ dr : Bool, replica.fld rr go!"Dreply" ↦□ dr) ∗
    -- SWB-11: the run loop's own map of the proposals' dependencies
    (∃ pdm : GoMap, swift.fld rp go!"proposeDeps" ↦ pdm ∗ pdm ↦$ (∅ : GMap swift.CommandId swift.Dep)) ∗
    -- L2 (notes/prove-s2-e.md): the node's claimed ghost, for its protocol steps' resolutions
    client.nodeGhostOk γ (sp.PNode.rep k))

/-- The specs of the `select` arms' callees over the loop invariant `I` (see the file header). -/
structure swift.RunArms (rp : Loc) (γ : sp.Names) (γc γm : GName) (I : IProp netDistGF) : Prop where
  -- D56 N1-c: the `recover` channel's value is `-1` or an own ballot; `ok` gives an own ballot
  recBal : ∀ nb : w32,
    {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗ I ∗
        swift.recoverOk rp nb }}
      (App (Val (rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"recoveryBallot")) (Val #nb))
    {{ (b : w32) (ok : Bool), RET (PairV #b #ok); I ∗ (⌜ok = true⌝ -∗ swift.ownBallot rp b) }}
  reinit : ∀ b : w32,
    {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗ I ∗
        swift.ownBallot rp b }}
      (App (Val (rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"reinitNewLeaderAckNs")) (Val #b))
    {{ RET #(); I }}
  -- D56 N1-b: the message's sender is a replica (`msgOk`)
  newLeader : ∀ (l : Loc) (r b : w32),
    {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗ I ∗
        typedPointsto l (swift.MNewLeader.mk r b) DFrac.discard ∗
        sp.msgOk γ γc γm (.newLeader r b) }}
      (App (Val (rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"handleNewLeader")) (Val #l))
    {{ RET #(); I }}
  getDesc : ∀ (x : swift.CommandId) (s : GoString),
    {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗ I }}
      (App (App (App (Val (rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"getCmdDesc"))
        (Val #x)) (Val #(interface.mkOk go.string #s))) (Val #slice.nil))
    {{ (d : Loc), RET #d; I }}
  propose : ∀ gp : Loc,
    {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗ I ∗
        sp.proposeP γ gp }}
      (App (Val (rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"handleProposal")) (Val #gp))
    {{ RET #(); I }}
  leader :
    {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗ I }}
      (App (Val (rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"leader")) (Val #()))
    {{ (ld : w32), RET #ld; I }}
  ackHash : ∀ (l : Loc) (fa : swift.MFastAck) (f : sp.FastAck),
    {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗ I ∗
        l ↦□ fa ∗ swift.fastAckRepr fa f ∗ swift.runAckW γ γc γm f }}
      (App (Val (rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"leaderAckHash")) (Val #l))
    {{ RET #(); I }}
  fastDesc : ∀ (l : Loc) (fa : swift.MFastAck) (f : sp.FastAck) (sq : Bool),
    {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗ I ∗
        l ↦□ fa ∗ swift.fastAckRepr fa f ∗ swift.runAckW γ γc γm f }}
      (App (App (App (App (App (Val (rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"getCmdDescSeq"))
        (Val #fa.CmdId')) (Val #(interface.mkOk (go.GoType.PointerType swift.MFastAck.ty) #l)))
        (Val #slice.nil)) (Val #slice.nil)) (Val #sq))
    {{ (d : Loc), RET #d; I }}
  slowDesc : ∀ (l : Loc) (sa : swift.MLightSlowAck) (s : sp.SlowAck),
    {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗ I ∗
        l ↦□ sa ∗ ⌜swift.slowAckRepr sa s⌝ ∗ sp.msgOk γ γc γm (.lightSlowAck s) }}
      (App (App (App (Val (rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"getCmdDesc"))
        (Val #sa.CmdId')) (Val #(interface.mkOk (go.GoType.PointerType swift.MLightSlowAck.ty) #l)))
        (Val #slice.nil))
    {{ (d : Loc), RET #d; I }}
  sync : ∀ (l : Loc) (m : sp.SyncWire),
    {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗ I ∗
        swift.msgRepM (interface.mkOk (go.GoType.PointerType swift.MSync.ty) #l) (.sync m) ∗
        sp.msgOk γ γc γm (.sync m) }}
      (App (Val (rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"handleSync")) (Val #l))
    {{ RET #(); I }}
  -- N2-loop: the end of each step, the rechecks its acceptances freed (DrainRechecks.lean)
  drain :
    {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗ I }}
      (App (Val (rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"drainRechecks")) (Val #()))
    {{ RET #(); I }}

/-- The loop's invariant and its arms (see the file header). -/
structure swift.RunLoopH (X : Type) (I : Loc → sp.Names → GName → GName → X → IProp netDistGF) :
    Prop where
  init : ∀ (rp : Loc) (γ : sp.Names) (γc γm γl : GName) (N k : Nat) (me : w32) (fr : Bool)
      (l : List GoString) (pl : w64) (γw : GName) (csv : swift.CommunicationSupply)
      (n : swift.CsNames),
    isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      swift.runLoopPre rp γ γc γm γl N k me fr l pl γw csv n ⊢ |={⊤}=> ∃ x : X, I rp γ γc γm x
  arms : ∀ (rp : Loc) (γ : sp.Names) (γc γm : GName) (x : X), swift.RunArms rp γ γc γm (I rp γ γc γm x)

/-- The loop's invariant exists with its arms (the allocation and the handlers' specs). -/
def swift.RunLoopOk : Prop :=
  ∃ (X : Type) (I : Loc → sp.Names → GName → GName → X → IProp netDistGF), swift.RunLoopH X I

end defs2

end Perennial.github_com.imdea_software.swiftpaxos

