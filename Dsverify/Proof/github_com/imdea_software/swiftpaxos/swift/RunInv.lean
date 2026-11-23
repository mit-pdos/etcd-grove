/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/RunInv.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
**The run loop's invariant** `swift.runInv` (the `I` of `swift.RunLoopH`/`swift.RunArms`,
Proof/swift/RunLoopSpecs.lean): what holds between two `select` arms of `r.run()`. Internal (the
swift group's); PROVISIONAL in its descriptor part (`swift.descState`, to be refined by the
descriptor side as the handlers' proofs need). Allocated by `swift.runInv_alloc`
(Proof/swift/RunAlloc.lean).

`x : swift.RunX` carries what is fixed for the replica's life: the ghost names (round 13: with
`γa`, `γrm`, the accepted map's epoch and `delivInv`'s removal-mode mirror, so that the run
loop's `rmTok x.γrm` and `syncCtx`'s `delivInv` agree), `N r k`, the embedded replica,
`delivered` (`dm`), `MaxDescRoutines` (`d`) and `CommandId.String`'s function `str`. What changes
from arm to arm (the run loop's fields, the descriptors' map, which `handleSync` replaces, the
epoch with its pool's name `γp`) is existential inside.

* `swift.descCtxE …` (DeliverE.lean; round 46: was `descCtx`): the persistent context the descriptor goroutines share;
* `swift.syncCtx γ N r x.syncN rp` (SyncSpecs.lean): `handleSync`'s context, at `x`'s names
  (the same invariants as descCtx's: both are allocated once, by `runInv_alloc`);
* `swift.runLoopCtx`: the rest of the run loop's persistent context (`rcvrRes`, the sender, the
  batcher, the read-only fields and globals, the table's bags, `cntL`'s mutex over
  `swift.cntLInvR` (P2-B), `historyL`'s over `swift.historyLInv`, the descriptors' pool,
  `SHARD_COUNT`; round 18: gob's `codecSet`, which `handleNewLeaderAckNs` needs);
* the run loop's state `swift.runSt` (Local.lean) for some `ld v M bs hd w`, in normal
  operation (`w.2.2.1`: between two arms the replica is normal, `handleNewLeader` loops while
  `status == RECOVERING`), and **the running epoch** `swift.epRun`;
* its own reader bundle of `delivered` (for itself and the sequential descriptors it runs;
  round 18: `swift.runReader rp x.γdl`, with the field's points-to, as `handleProposal` takes it);
* `swift.runFields` (`recStart`, `FQ`, `repchan`'s half, `newLeaderAckNs` with its ballot
  `newLeaderAckNsBallot` (F2', D30), the embedded
  replica's `PreferredPeerOrder`) and `proposeDeps` (`swift.propDepsOwn`, RunSpecs.lean);
* the descriptors' part `swift.descState` (PROVISIONAL): `cmdDescs` (some map `dm1` with its
  view `γdc1` and the run loop's reader bundle) and the descriptor records' authority `γd`.

**The running epoch** `swift.epRun` (fractions; each field's total is 1):
`ballot`: `runSt` ¼, `ballotL` ¼, the reply goroutine's cell ¼ (`replyRes`), the pool ¼;
`status`: `runSt` ½, the pool ¼, `epochRest` ¼; `State`: the pool ¼, `epochRest` ½ + ¼;
`repchan`: `runFields` ½, the pool ¼, `epochRest` ¼; `γe` (epoch token): `nodeInvD` ½, the pool
¼, `epochRest` ¼; `γxe`: `execLInv` ½, the pool ¼, `epochRest` ¼; `γxp`: `delivInv` ½, the pool
¼, `epochRest` ¼. The pool (`swift.epochRun`, EpochPool.lean) lends shares of its ¼ to the
descriptor goroutines.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RunLoopSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.EpochPool
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.CntL
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RunSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.SyncSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RunCtx
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.CmdStr
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RecSync

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

/-- What is fixed for the replica's life (see the file header). -/
structure swift.RunX where
  γl : GName
  γw : GName
  γv : GName
  γe : GName
  γo : GName
  γx : GName
  γxe : GName
  γxm : GName
  γxp : GName
  γa : GName
  γrm : GName
  γd : GName
  γdl : GName
  γn : GName
  γdc : ChanNames
  str : swift.CommandId → GoString
  rr : Loc
  N : Nat
  r : Nat
  k : Nat
  dm : GoSlice
  d : w64
  /-- round 21 (sv-swb): the descriptors' share map (ShInv.lean; `swift.DC.γsh`) -/
  γsh : GName
  /-- round 32 (sv-swb, framing): the store's ledger and claims (`swift.StN`, DescNode.lean) -/
  γout : GName
  γcl : GName
  /-- round 46 (D-SWC2-5, D57): the execution tickets' map (`swift.xTixK`) -/
  γxu : GName
  /-- round N5 (D72 (1)): the report tokens' map (`swift.repTok`, DescNode.lean) -/
  γrp : GName
  /-- round 56 (D79 (1), 52-3): the epochs' map ballot ↦ that epoch's commit-witness map `γk`
  (`swift.nodeX`, DescNode.lean; read by `retWhy (.rest d γi)`) -/
  γcg : GName

/-- `handleSync`'s names (SyncSpecs.lean) of `x`. -/
def swift.RunX.syncN (x : swift.RunX) : swift.SyncN :=
  ⟨x.γdl, x.γx, x.γxe, x.γxp, x.γxm, x.γa, x.γrm, x.str, x.γn, x.N, x.dm, x.d, x.γsh, x.γout, x.γcl,
    x.γxu, x.γrp, x.γcg⟩

/-- The store's parameters (`swift.StN`, DescNode.lean) of `x` (round 32, sv-swb, framing). -/
abbrev swift.RunX.sn (x : swift.RunX) : swift.StN := ⟨x.γxm, x.γout, x.γcl, x.str, x.N, x.r, x.γxu, x.γrp, x.γcg⟩

/-- The epoch's names (EpochPool.lean) of `x` at the replica `rp`. -/
def swift.RunX.epN (x : swift.RunX) (rp : Loc) : swift.EpN :=
  ⟨x.γe, x.γxe, x.γxp, rp, x.rr, x.N⟩

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]

/-- `historyL`'s lock invariant (round 13): the history's slots (`r.history[i]`, written by a
sequential descriptor's history step, read by the reply goroutine's `getHistory`-like readers
under the lock). PROVISIONAL: the descriptor side's `handleMsg.slotSpecI` may refine it. -/
def swift.historyLInv (hsl : GoSlice) : IProp netDistGF :=
  iprop(∃ cs : List swift.commandStaticDesc, hsl ↦* cs ∗ ⌜cs.length = 10010001⌝)

/-- The run loop's persistent context besides `descCtx` (see the file header). -/
def swift.runLoopCtx (rp : Loc) (γ : sp.Names) (γc γm : GName) (x : swift.RunX) :
    IProp netDistGF :=
  iprop(∃ (s b : Loc) (γs : ChanNames) (sq : replica.QuorumI) (hsl : GoSlice) (fr : Bool)
      (pl : w64) (sam : GoMap) (csv : swift.CommunicationSupply) (n : swift.CsNames),
    swift.rcvrRes rp γc γm ∗
    swift.fld rp go!"sender" ↦□ s ∗ isChanBag γs s (replica.sendArgP x.rr γ γc γm x.N) ∗
    swift.fld rp go!"batcher" ↦□ b ∗ swift.batcherH γ γc γm rp b ∗
    swift.fld rp go!"SQ" ↦□ sq ∗ swift.fld rp go!"history" ↦□ hsl ∗
    swift.fld rp go!"historyStart" ↦□ (W64 0) ∗ swift.fld rp go!"optExec" ↦□ true ∗
    swift.fld rp go!"fastRead" ↦□ fr ∗ swift.fld rp go!"fixedMajority" ↦□ true ∗
    swift.fld rp go!"poolLevel" ↦□ pl ∗ swift.fld rp go!"slowAddrs" ↦□ sam ∗
    sam ↦$□ (∅ : GMap GoString Unit) ∗
    globalAddr swift.MaxDescRoutines ↦□ x.d ∗ ⌜0 ≤ sint.Z x.d ∧ sint.Z x.d ≤ 100⌝ ∗
    globalAddr swift.useFastAckPool ↦□ (decide (1 < sint.Z pl)) ∗
    typedPointsto (globalAddr _root_.Perennial.github_com.orcaman.concurrent_map.SHARD_COUNT)
      (W64 32768) DFrac.discard ∗
    swift.fld rp go!"cs" ↦□ csv ∗ ⌜swift.csCodes csv⌝ ∗ swift.csBags γ γc γm csv n ∗
    sync.isMutex (swift.fld rp go!"cntL") (swift.cntLInvR rp x.dm x.γdl x.γn x.d) ∗
    sync.isMutex (swift.fld rp go!"historyL") (swift.historyLInv hsl) ∗
    inv swift.shN (swift.shInv x.γsh) ∗
    (∃ pf : GoFunc, ⌜pf ≠ func.nil⌝ ∗
      sync.isPool (swift.fld rp go!"descPool") pf iprop(True) (swift.descPoolP (swift.descDFA x.γsh))) ∗
    -- (round 18) gob's codec, for `MSync.Marshal` (`handleNewLeaderAckNs`)
    encoding.gob.codecSet (GF := netDistGF) ∗
    -- (round 25, D22 (1)) the descriptors' string function is `CommandId.String`'s
    ⌜x.str = swift.cmdStr⌝ ∗
    -- (round 37b, sv-swb; table rev 8c §3.17 GAP-37d) the configuration at `fastRead`'s value
    -- (`proposeCtxB` needs both at one `fr`; `descCtx`'s `cfg` is at its own `fr`)
    (∃ lg : List GoString, sp.cfg γc γm x.N fr lg))

/-- The epoch's fractions the run loop keeps besides its pool's (see the file header; round 23:
`FQ`'s half; the pool has a quarter, `runFields` the last one). -/
def swift.epochRest (n : swift.EpN) (v : swift.EpV) : IProp netDistGF :=
  iprop(typedPointsto (swift.fld n.rp go!"status") v.st (DFrac.own (1 : Qp).half.half) ∗
    typedPointsto (replica.fld n.rr go!"State") v.stp (DFrac.own (1 : Qp).half) ∗
    typedPointsto (replica.fld n.rr go!"State") v.stp (DFrac.own (1 : Qp).half.half) ∗
    typedPointsto (swift.fld n.rp go!"repchan") v.rcp (DFrac.own (1 : Qp).half.half) ∗
    swift.epochTok n.γe (1 : Qp).half.half (v.b, v.b) ∗
    ghostVar n.γxe (1 : Qp).half.half (v.b, v.stp) ∗ ghostVar n.γxp (1 : Qp).half.half v.b ∗
    typedPointsto (swift.fld n.rp go!"FQ") v.fq (DFrac.own (1 : Qp).half))

/-- **The running epoch** (see the file header): the pool of a quarter of the epoch, the rest,
the reply goroutine's channel (its cell filled: the goroutine's reading right `replyRes` at the
epoch's ballot), the run loop's half of `delivInv`'s mirror (not in removal mode). -/
def swift.epRun (γ : sp.Names) (γc γm : GName) (rp : Loc) (x : swift.RunX) : IProp netDistGF :=
  iprop(∃ (ev : swift.EpV) (γp : GName) (γl : swift.CellNames),
    swift.epochRun (x.epN rp) ev (1 : Qp).half.half γp ∗ swift.epochRest (x.epN rp) ev ∗
    swift.replyChanH γ γc γm rp γl ev.bw ev.rcp ∗ swift.cellFilled γl ∗
    swift.rmTok x.γrm none ∗ ⌜ev.st = swift.stNORMAL⌝)

/-- An `MNewLeaderAckN`'s ballot (its object is persistent: `swift.ackObj`). -/
def swift.ackBal (p : Loc) (bl : w32) : IProp netDistGF :=
  iprop(∃ (rep cb : w32) (ids ph cm dp : GoSlice),
    p ↦□ swift.MNewLeaderAckN.mk rep bl cb ids ph cm dp)

/-- **The facts of `newLeaderAckNs`'s messages** (the `P` of the set; round 31, sv-swc,
prove-swift.md §36; round 33, F2' (D30): **at the set's ballot `bs`**): the message at key `k` is
an `*MNewLeaderAckN` `p` from replica `k < N`, its report `a.2` (`ackObj`) and its ballot `bs`
(`ackBal`) with `sp.reported` at `bs`. `bs` is `r.newLeaderAckNsBallot` (`swift.runFields`):
`handleNewLeaderAckN` adds only acks with `msg.Ballot = newLeaderAckNsBallot` (fork 65496aa), so
every message of the set is at the ballot it was reinitialised for. -/
def swift.nlP (γ : sp.Names) (N : Nat) (bs : w32) (k : w32) (m : GoInterface) : IProp netDistGF :=
  iprop(∃ (p : Loc) (a : Nat × sp.Report),
    ⌜m = interface.mkOk (go.GoType.PointerType swift.MNewLeaderAckN.ty) #p ∧ sint.Z k = a.1 ∧
      a.1 < N ∧ 0 ≤ sint.Z bs⌝ ∗
    swift.ackObj p a ∗ swift.ackBal p bs ∗ sp.reported γ a.1 (sint.Z bs).toNat a.2)

/-- The quorum of `newLeaderAckNs` (`NewMajorityOf(N)`). -/
def swift.nlQ (N : Nat) : GoInterface :=
  interface.mkOk replica.Majority.ty #(W64 ((N / 2 + 1 : Nat) : Int))

/-- `r.handleNewLeaderAckNs` as a method value: the set's handler. -/
def swift.nlHd (rp : Loc) : GoFunc :=
  methods (go.GoType.PointerType swift.Replica.ty) go!"handleNewLeaderAckNs" #rp

/-- **`r.newLeaderAckNs`** (round 31): nil (before the first recovery) or a set over
`NewMajorityOf(N)` (any key a member), its messages with `swift.nlP`, no leader message
(`PL := False`), accepting all (`A := True`), closures reading nothing (`RA := True`), its
handler `r.handleNewLeaderAckNs`. The handler's spec (`handlerOkQ`) is not here: the caller of
`Add` (`handleNewLeaderAckN`, the descriptor side) states it. -/
def swift.nlSet (γ : sp.Names) (rp : Loc) (N : Nat) (bs : w32) (nl : Loc) : IProp netDistGF :=
  iprop(⌜nl = null⌝ ∨
    replica.mset.ownD nl (swift.nlQ N) (N / 2 + 1) (fun _ => True) (swift.nlP γ N bs)
      (fun _ _ => iprop(True)) (fun _ => iprop(False)) iprop(True) (swift.nlHd rp))

instance swift.ackBal_persistent (p : Loc) (bl : w32) : Persistent (swift.ackBal p bl) := by
  unfold swift.ackBal; infer_instance

instance swift.nlP_persistent (γ : sp.Names) (N : Nat) (bs k : w32) (m : GoInterface) :
    Persistent (swift.nlP γ N bs k m) := by
  unfold swift.nlP sp.reported; infer_instance

/-- The run loop's own fields besides `runSt`'s (see the file header; round 23, D18 G2: `FQ` is
the epoch's, `epochShare`/`epochRest`, but for a quarter kept here: `handleSync` logs it after
handing the new epoch's share over). D56 N1-c: the set's ballot `bs` is led by `r` once the set
is allocated. -/
def swift.runFields (γ : sp.Names) (rp rr : Loc) (N r : Nat) : IProp netDistGF :=
  iprop(∃ (t : time.Time) (fq : replica.QuorumI) (rc nl : Loc) (bs : w32) (ppsl : GoSlice)
      (pp : List w32),
    swift.fld rp go!"recStart" ↦ t ∗
    typedPointsto (swift.fld rp go!"FQ") fq (DFrac.own (1 : Qp).half.half) ∗
    typedPointsto (swift.fld rp go!"repchan") rc (DFrac.own (1 : Qp).half) ∗
    swift.fld rp go!"newLeaderAckNs" ↦ nl ∗ swift.fld rp go!"newLeaderAckNsBallot" ↦ bs ∗
    swift.nlSet γ rp N bs nl ∗
    replica.fld rr go!"PreferredPeerOrder" ↦ ppsl ∗ ppsl ↦* pp ∗
    ⌜pp.length = N ∧ ∀ p ∈ pp, 0 ≤ p.toInt ∧ p.toInt < N⌝ ∗
    -- D56 N1-c: a set is reinitialised only for an own ballot (`RunArms.recBal`'s post)
    ⌜nl ≠ null → sp.leaderOf N (sp.bal bs) = r⌝)

/-- The descriptors' part of the run loop's invariant (PROVISIONAL, see the file header). -/
def swift.descState (rp : Loc) (x : swift.RunX) : IProp netDistGF :=
  iprop(∃ (dm1 : GoSlice) (γdc1 : GName) (D : GMap Loc sp.CmdId),
    swift.fld rp go!"cmdDescs" ↦ dm1 ∗
    github_com.orcaman.concurrent_map.isCMapV dm1 γdc1 (swift.descR x.γd) ∗
    github_com.orcaman.concurrent_map.readerV dm1 γdc1 (swift.descR x.γd) ∗
    ghostMapAuth x.γd 1 D ∗ swift.cntFrozen x.γn false)

end defs

end Perennial.github_com.imdea_software.swiftpaxos
