/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/SyncSpecs.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`handleSync`'s spec and its callees' specs (internal, the swift group's; not frozen). The epoch's
resources (the descriptors' and the reply goroutine's reader tokens, the class-E fields' other
halves, `State`, `delivered`'s contents, `execL`'s and `acceptL`'s lock invariants: notes/
prove-swift.md §1.1, §1.3, to be defined with the descriptor machinery) are a parameter
`Ep : Bool → IProp` (`Ep true`: in normal operation, its goroutines running; `Ep false`: all
stopped, the run loop holds them) and `EpNew γ b' M` (after taking ballot `b'`'s `MSync` `M`,
its committed descriptors created). The callees that touch them are hypotheses over `Ep`.

Callee specs stated here (hypotheses of `handleSync`'s proof): `sortedProposes`,
`replyChan.stop` and `stopDescs` (as one stop of the epoch, `Ep true` to `Ep false`),
`getCmdDesc` with a `*syncEntry` (a committed command of the `MSync`: its `accepted`/`locAt`
facts go to the descriptor). The others it needs are already stated elsewhere:
`swift.syncOrder.specI` (RecDefs.lean), `newLightKeyInfo.spec`/`lightKeyInfo.add.spec`
(KeySpecs.lean), `swift.keysOf.specI` (RecSync.lean, the recovery's), `replica.Leader`
(the replica group's), the cmap `IterCb`/`Remove`/`New` (the cmap group's: requests below).

Requests to the cmap group (sv-swc): `IterCb` visiting every entry when no other writer runs
(`delivered` must be emptied: its `executed` facts are per epoch); `cmap.New`'s result with an
empty ghost view.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.HandleSync
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RunSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.SyncStepD
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.SyncRemove
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.NewSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RunCtx

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [π : NetProtoGS]

/-- The run loop's own class-L/E fields `handleSync` writes besides `runSt`'s (round 11:
`repchan` at half, the other half the epoch's; SWB-11: `proposeDeps`, reset to an empty map).
Round 14 (GAP H-size): `historySize` is no longer here: it is the epoch's (the reply goroutine's
cell content while running; `epStopped`'s when stopped; `epFresh`'s at `0` for the new one).
Round 23 (D18 G2): only a quarter of `FQ` (the rest is the epoch's, `epStopped`/`epFresh`). -/
def swift.syncFieldsOwn (rp : Loc) : IProp netDistGF :=
  iprop(∃ (t : time.Time) (rc : Loc) (fq : replica.QuorumI) (pd : Loc)
      (pdM : GMap swift.CommandId GoSlice),
    swift.fld rp go!"recStart" ↦ t ∗
    swift.fld rp go!"proposeDeps" ↦ pd ∗ pd ↦$ pdM ∗
    typedPointsto (swift.fld rp go!"repchan") rc (DFrac.own (1 : Qp).half) ∗
    typedPointsto (swift.fld rp go!"FQ") fq (DFrac.own (1 : Qp).half.half))

/-- **`syncFieldsOwn` after `handleSync`'s epoch swap** (round 38, table rev 9 T29, Round 33
request 1, plan R9.1 (8)): `r.proposeDeps = make(…)` (recovery.go:604), so the map is fresh and
empty. -/
def swift.syncFieldsOwnE (rp : Loc) : IProp netDistGF :=
  iprop(∃ (t : time.Time) (rc : Loc) (fq : replica.QuorumI) (pd : Loc),
    swift.fld rp go!"recStart" ↦ t ∗
    swift.fld rp go!"proposeDeps" ↦ pd ∗ pd ↦$ (∅ : GMap swift.CommandId GoSlice) ∗
    typedPointsto (swift.fld rp go!"repchan") rc (DFrac.own (1 : Qp).half) ∗
    typedPointsto (swift.fld rp go!"FQ") fq (DFrac.own (1 : Qp).half.half))

/-- The ghost names of the execution record and `delivered` (round 11, sv-swa): `delivInv`'s
and the locks' (Deliver.lean), with `CommandId.String`'s function `str`. -/
structure swift.SyncN where
  γdl : GName
  γx : GName
  γxe : GName
  γxp : GName
  γxm : GName
  γa : GName
  γrm : GName
  str : swift.CommandId → GoString
  /-- round 17: `cntL`'s registry (its freeze flag, `swift.cntFrozen`) -/
  γn : GName
  /-- round 23 (D18 G2): the replica count (`epFresh`'s fast quorum is in `AQ N b'`) -/
  N : Nat
  /-- round 23: `cntL`'s `delivered` slice and `MaxDescRoutines` (`swift.RunX.dm`, `.d`) and the
  descriptors' share map (`.γsh`): the new epoch's descriptors' context (`syncCtx`) -/
  dm : GoSlice
  d : w64
  γsh : GName
  /-- round 32 (sv-swb): the store's ledger and claims (`swift.StN`, DescNode.lean) -/
  γout : GName
  γcl : GName
  /-- round 46 (D-SWC2-5, D57): the execution tickets' map -/
  γxu : GName
  /-- round N5 (D72 (1)): the report tokens' map (`swift.repTok`, DescNode.lean) -/
  γrp : GName
  /-- round 56 (D79 (1), 52-3): the epochs' map ballot ↦ that epoch's commit-witness map `γk`
  (`swift.nodeX`, DescNode.lean; read by `retWhy (.rest d γi)`) -/
  γcg : GName

/-- The store's parameters (`swift.StN`) of `n` at the replica `r` of `N` (round 32). -/
abbrev swift.SyncN.sn (n : swift.SyncN) (N r : Nat) : swift.StN := ⟨n.γxm, n.γout, n.γcl, n.str, N, r, n.γxu, n.γrp, n.γcg⟩

/-- **What `freeDesc`/`allocDesc` read of the replica** (round 16, sv-swb; persistent; main
session's approval (b)): `poolLevel` (read-only) and, when the pool is used (`poolLevel > 0`),
`descPool` with predicate `descPoolP DF` (New allocates it; `runLoopPre`'s pool has `descP`,
which is `descPoolP DF` for `DF d` := the remaining fields of `d`). -/
def swift.descPoolCtx (DF : Loc → IProp netDistGF) (rp : Loc) : IProp netDistGF :=
  iprop(∃ pl : w64, swift.fld rp go!"poolLevel" ↦□ pl ∗
    (⌜sint.Z pl ≤ 0⌝ ∨ ∃ pf : GoFunc, ⌜pf ≠ func.nil⌝ ∗
      sync.isPool (swift.fld rp go!"descPool") pf iprop(True) (swift.descPoolP DF)))

instance swift.descPoolCtx_persistent (DF : Loc → IProp netDistGF) (rp : Loc) :
    Persistent (swift.descPoolCtx DF rp) := by
  unfold swift.descPoolCtx; infer_instance

/-- **The pool's context for a stopped descriptor's rest `DF`** (round 35; table rev 5 C5, T23):
the pool of some `DFp` and a law turning `DF d` into `DFp d` (a stopped goroutine's home whose
token is stored: `handleSync`'s free takes the record's halves back, `swift.descRestS_forget`). -/
def swift.descPoolCtxF (DF : Loc → IProp netDistGF) (rp : Loc) : IProp netDistGF :=
  iprop(∃ DFp : Loc → IProp netDistGF, swift.descPoolCtx DFp rp ∗ □ ∀ d : Loc, DF d ={⊤}=∗ DFp d)

instance swift.descPoolCtxF_persistent (DF : Loc → IProp netDistGF) (rp : Loc) :
    Persistent (swift.descPoolCtxF DF rp) := by
  unfold swift.descPoolCtxF; infer_instance

/-- **The pool's context for the stopped descriptors, with the free permit** (round B1, D82 (4)):
as `descPoolCtxF`, but the law needs a persistent `Pp`, which the stopped view's facts `PS Mc`
give once, by a ghost update (the descriptor side: the stopped epoch's free permit, spent,
`swift.freeSp`). `handleSync` spends `PS Mc` (it dropped them before) for `descPoolCtxF`
before its free (`swift.descPoolCtxS_F`); the report keeps `PS Mc` unspent. -/
def swift.descPoolCtxS (DF : Loc → IProp netDistGF) (PS : GMap GoString GoInterface → IProp netDistGF)
    (rp : Loc) : IProp netDistGF :=
  iprop(∃ (DFp : Loc → IProp netDistGF) (Pp : IProp netDistGF), swift.descPoolCtx DFp rp ∗
    □ (∀ Mc, PS Mc ={⊤}=∗ □ Pp) ∗ □ ∀ d : Loc, Pp -∗ DF d ={⊤}=∗ DFp d)

instance swift.descPoolCtxS_persistent (DF : Loc → IProp netDistGF)
    (PS : GMap GoString GoInterface → IProp netDistGF) (rp : Loc) :
    Persistent (swift.descPoolCtxS DF PS rp) := by
  unfold swift.descPoolCtxS; infer_instance

/-- `handleSync`'s free (round B1): the stopped view's facts spent, `descPoolCtxF`. -/
theorem swift.descPoolCtxS_F (DF : Loc → IProp netDistGF)
    (PS : GMap GoString GoInterface → IProp netDistGF) (rp : Loc) (Mc : GMap GoString GoInterface) :
    swift.descPoolCtxS DF PS rp ∗ PS Mc ⊢ |={⊤}=> swift.descPoolCtxF DF rp := by
  iintro ⟨#H, HPS⟩
  iunfold swift.descPoolCtxS at H
  icases H with ⟨%DFp, %Pp, #Hctx, #Hsp, #Hlaw⟩
  ihave Hsp' := Hsp $$ %Mc HPS
  imod Hsp' with #HPp
  imodintro
  iunfold swift.descPoolCtxF
  iexists DFp
  iframe Hctx
  imodintro
  iintro %d HD
  iapply Hlaw $$ %d HPp HD

/-- What `handleSync` shares with the descriptors (persistent; round 11): `delivered` with its
invariant, the `execL`, `acceptL`, `ballotL` mutexes, `deliveredAny`'s invariant, `SyncHook`
nil; round 13: `fixedMajority` (true), the quorum system `qs`, the history slice and `Shutdown`
(for `qs.AQ`, `NewReplyChan`); round 17: `cntL`'s mutex at the registry `n.γn` (the
`routineCount = 0` step, `swift.cntLGhost_unfreeze`). -/
def swift.syncCtx (γ : sp.Names) (N r : Nat) (n : swift.SyncN) (rp : Loc) : IProp netDistGF :=
  iprop(∃ dm : GoSlice, swift.fld rp go!"delivered" ↦□ dm ∗
    github_com.orcaman.concurrent_map.isCMapV dm n.γdl swift.deliveredR ∗
    inv swift.delivN (swift.delivInv γ N r n.γdl n.γx n.γxp n.γxm n.γa n.γxe n.γrm n.str) ∗
    sync.isMutex (swift.fld rp go!"execL") (swift.execLInvE γ n.γx n.γxe n.γxm n.γxu N r rp) ∗
    sync.isMutex (swift.fld rp go!"acceptL") (swift.acceptInv γ r rp n.γa) ∗
    sync.isMutex (swift.fld rp go!"ballotL") (swift.ballotLInv rp) ∗
    swift.anyInv rp ∗ globalAddr swift.SyncHook ↦□ func.nil ∗
    swift.fld rp go!"fixedMajority" ↦□ true ∗
    (∃ qs : Loc, swift.fld rp go!"qs" ↦□ qs ∗ replica.quorum.isQS qs N) ∗
    (∃ (hsl : GoSlice) (rr : Loc), swift.fld rp go!"history" ↦□ hsl ∗
      ⌜sint.Z hsl.len = 10010001⌝ ∗ swift.fld rp go!"Replica" ↦□ rr ∗
      replica.fld rr go!"Shutdown" ↦□ false) ∗
    (∃ (dmc : GoSlice) (d : w64),
      sync.isMutex (swift.fld rp go!"cntL") (swift.cntLInvR rp dmc n.γdl n.γn d)) ∗
    ⌜n.N = N⌝ ∗
    sync.isMutex (swift.fld rp go!"cntL") (swift.cntLInvR rp n.dm n.γdl n.γn n.d) ∗
    swift.descPoolCtx (swift.descDFA n.γsh) rp ∗
    -- round 27 (D24): the descriptors' spawn context (`descDSCtx`'s)
    inv swift.shN (swift.shInv n.γsh) ∗ globalAddr swift.MaxDescRoutines ↦□ n.d ∗
    (∃ (sq : GoInterface) (szS : Nat) (memS : w32 → Prop),
      swift.fld rp go!"SQ" ↦□ sq ∗ replica.mset.quorumIs sq szS memS) ∗
    -- round 42 (table §3R11 gap 11-2, request R11-Q1): `delivered`'s value is the registry's
    -- `n.dm` (PF29: the field is stored once, in `New`)
    swift.fld rp go!"delivered" ↦□ n.dm ∗
    -- round 54 (D74 (3), 53-1): `SQ` is a quorum with every replica (`NewMajorityOf`, New's
    -- `fun _ => True`), for `descDSCtx`/`ackCtx` (a follower's `sendSlowAck` holds)
    (∃ (sq : GoInterface) (szS : Nat),
      swift.fld rp go!"SQ" ↦□ sq ∗ replica.mset.quorumIs sq szS (fun _ => True)))

-- (`swift.syncMaps_persistent`: moved to Local.lean, round N5)

set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
instance swift.syncCtx_persistent (γ : sp.Names) (N r : Nat) (n : swift.SyncN) (rp : Loc) :
    Persistent (swift.syncCtx γ N r n rp) := by
  unfold swift.syncCtx; infer_instance

/-- A `*MsgSet` field's value as `Free` wants it (round 13, GAP S-free): nil, or a set's
ownership (`replica.mset.ownD`, `MsgSet.Free.specQ`'s, at any parameters) with its handler's
resource `R`. -/
def swift.msgSetFree (ms : Loc) : IProp netDistGF :=
  iprop(∃ (q : GoInterface) (sz : Nat) (mem : w32 → Prop) (P : w32 → GoInterface → IProp netDistGF)
      (A : GoInterface → GoInterface → IProp netDistGF) (PL : GoInterface → IProp netDistGF)
      (R : IProp netDistGF) (hd : GoFunc),
    (⌜ms = null⌝ ∨ replica.mset.ownD ms q sz mem P A PL R hd) ∗ R)

/-- **A stopped descriptor, to be freed** (round 13, GAP S-free): what `handleSync`'s
`cmdDescs.IterCb` closure needs of descriptor `d`: the fields it clears (`msgs`, `stopChan`),
its two message sets for `Free`, and `DF d` for `freeDesc` (the rest of the descriptor, the
descriptor side's: `freeDesc.specI DF`). -/
def swift.descFree (DF : Loc → IProp netDistGF) (d : Loc) : IProp netDistGF :=
  iprop(∃ (m s sl fa : Loc), swift.dfld d go!"msgs" ↦ m ∗ swift.dfld d go!"stopChan" ↦ s ∗
    swift.dfld d go!"slowPathH" ↦ sl ∗ swift.dfld d go!"fastPathH" ↦ fa ∗
    swift.msgSetFree sl ∗ swift.msgSetFree fa ∗ DF d)

-- `swift.descPooled`, `swift.descPoolP`: moved to ShInv.lean (round 21).


/-- **`cmdDescs` with its stopped descriptors** (round 13, GAP S-free; the run loop's once no
descriptor goroutine runs): the field (whole), the map over `descR γd` (persistent part and a
reader bundle), its whole view `Mc` (no other writer), and each entry's descriptor ready to be
freed, once per entry. With `IterCbVN` (Proof/cmap/IterCbN.lean: `fn` learns its key is fresh)
the closure takes each entry's `descFree` exactly once. Round 16: with `descPoolCtx DF rp` (for
`freeDesc`). Round 53 (D70 (3)(a), D73 (4); 51-2 (a)): with the view's facts `PS Mc` (a
parameter: `handleSync` drops them; the run loop keeps the descriptors' commit record `incInv`
and the keys' commands, `swift.stopPS`, NewLeaderSpecs.lean). -/
def swift.descsStopped (γd : GName) (DF : Loc → IProp netDistGF)
    (PS : GMap GoString GoInterface → IProp netDistGF) (rp : Loc) : IProp netDistGF :=
  iprop(∃ (dm : GoSlice) (γdc : GName) (Mc : GMap GoString GoInterface),
    swift.fld rp go!"cmdDescs" ↦ dm ∗
    github_com.orcaman.concurrent_map.isCMapV dm γdc (swift.descR γd) ∗
    github_com.orcaman.concurrent_map.readerV dm γdc (swift.descR γd) ∗
    github_com.orcaman.concurrent_map.cmapView γdc Mc ∗ swift.descPoolCtxS DF PS rp ∗ PS Mc ∗
    [∗map] _k ↦ v ∈ Mc, ∃ d : Loc,
      ⌜v = interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #d⌝ ∗ swift.descFree DF d)

/-- **The new `cmdDescs`** (round 13; `cmap.New()`'s, handed to the new epoch with
`epFresh`): empty view, the reader bundles. -/
def swift.descsFresh (γd : GName) (rp : Loc) : IProp netDistGF :=
  iprop(∃ (dm : GoSlice) (γdc : GName), swift.fld rp go!"cmdDescs" ↦ dm ∗
    github_com.orcaman.concurrent_map.isCMapV dm γdc (swift.descR γd) ∗
    github_com.orcaman.concurrent_map.cmapView γdc ∅ ∗
    ([∗list] _x ∈ List.replicate github_com.orcaman.concurrent_map.cmapReaders (),
      github_com.orcaman.concurrent_map.readerV dm γdc (swift.descR γd)))

/-- **The stopped epoch** (round 11; what the run loop holds once no descriptor goroutine nor the
reply goroutine runs, after `stopDescs`, or in recovery): its half of `ballot` and `status`
(`runStS` holds a quarter / the other half, `ballotL` a quarter), `State`, the node
invariant's epoch token's half at `bc = (ballot, cballot)`, the pins' half and `γxe`'s half at
the record's epoch `bc.2` (the last `cballot`), and its half of `delivInv`'s mirror (`none`).
Round 13: with `cmdDescs` and its stopped descriptors (`swift.descsStopped γd DF rp`).
Round 17 (SWB-14's fix): `cntL`'s freeze flag at `true` (`swift.cntFrozen`: no descriptor
goroutine registered; `stopDescs` set it when it read `routineCount <= 0`). Round 23 (D18 G2):
`FQ`'s three quarters (an epoch field; `handleSync` writes it with `syncFieldsOwn`'s quarter). -/
def swift.epStopped (n : swift.SyncN) (γe γd : GName) (DF : Nat → Loc → IProp netDistGF)
    (PS : Nat → GMap GoString GoInterface → IProp netDistGF) (rp rr : Loc) :
    IProp netDistGF :=
  iprop(∃ (bw : w32) (st : w64) (stp stpX : Loc) (bc : Nat × Nat),
    typedPointsto (swift.fld rp go!"ballot") bw (DFrac.own (1 : Qp).half) ∗
    typedPointsto (swift.fld rp go!"status") st (DFrac.own (1 : Qp).half) ∗
    replica.fld rr go!"State" ↦ stp ∗
    (∃ rc : Loc, typedPointsto (swift.fld rp go!"repchan") rc (DFrac.own (1 : Qp).half)) ∗
    swift.epochTok γe (1 : Qp).half bc ∗
    ghostVar n.γxp (1 : Qp).half bc.2 ∗ ghostVar n.γxe (1 : Qp).half (bc.2, stpX) ∗
    swift.rmTok n.γrm none ∗ swift.descsStopped γd (DF bc.2) (PS bc.2) rp ∗ ghostMapAuth n.γout (1 : Qp).half (∅ : GMap (Nat × sp.CmdId) (Nat × Qp)) ∗
    (∃ hs : w64, swift.fld rp go!"historySize" ↦ hs) ∗ swift.cntFrozen n.γn true ∗
    (∃ fq : replica.QuorumI, typedPointsto (swift.fld rp go!"FQ") fq (DFrac.own (1 : Qp).half) ∗
      typedPointsto (swift.fld rp go!"FQ") fq (DFrac.own (1 : Qp).half.half)))

/-- **The new epoch's resources** (round 11; what `handleSync` hands to the new epoch, before
its descriptors): as `epStopped` at `b'` (`ballot`, `cballot` `b'`, normal), the new `State`
`stp'` (its contents executed by the descriptors) and the new reply channel `rc` (with the
cell `γl` whose reading right is `replyRes rp bw`). `EpS M []` is built from it (hypothesis
`EpS_start` of the proof: the epoch pool's allocation, sv-swc's). Round 17: `cntL`'s freeze
flag cleared (`swift.cntFrozen n.γn false`, the run loop's half for its spawns). Round 23 (D18
G2): `FQ`'s three quarters (`epStopped`'s) at `qs.AQ(b')` with its quorum, members in `AQ N b'`. -/
def swift.epFresh (γ : sp.Names) (γc γm : GName) (n : swift.SyncN) (γe γd : GName) (rp rr : Loc)
    (b' : Nat) : IProp netDistGF :=
  iprop(∃ (bw : w32) (stp' rc : Loc) (γl : swift.CellNames),
    typedPointsto (swift.fld rp go!"ballot") bw (DFrac.own (1 : Qp).half) ∗
    typedPointsto (swift.fld rp go!"status") swift.stNORMAL (DFrac.own (1 : Qp).half) ∗
    replica.fld rr go!"State" ↦ stp' ∗
    typedPointsto (swift.fld rp go!"repchan") rc (DFrac.own (1 : Qp).half) ∗
    swift.replyChanH γ γc γm rp γl bw rc ∗ swift.cellFillTok γl ∗
    swift.epochTok γe (1 : Qp).half (b', b') ∗
    ghostVar n.γxp (1 : Qp).half b' ∗ ghostVar n.γxe (1 : Qp).half (b', stp') ∗
    swift.rmTok n.γrm none ∗ swift.descsFresh γd rp ∗ ghostMapAuth n.γout (1 : Qp).half (∅ : GMap (Nat × sp.CmdId) (Nat × Qp)) ∗
    swift.fld rp go!"historySize" ↦ (W64 0) ∗ ⌜sp.bal bw = b'⌝ ∗ swift.cntFrozen n.γn false ∗
    -- round 56 (D79 (1), 52-3): ballot `b'`'s reserved key in the epochs' map (`takeSync_stepD`)
    ghostMapElem n.γcg (b', false) (DFrac.own 1) (none : Option GName) ∗
    (∃ (fq : GoInterface) (szF : Nat) (memF : w32 → Prop),
      typedPointsto (swift.fld rp go!"FQ") fq (DFrac.own (1 : Qp).half) ∗
      typedPointsto (swift.fld rp go!"FQ") fq (DFrac.own (1 : Qp).half.half) ∗
      replica.mset.quorumIs fq szF memF ∗ ⌜(∀ i : w32, memF i → sp.rid i ∈ sp.AQ n.N b') ∧
        (∀ i : w32, 0 ≤ sint.Z i → sp.rid i = sp.leaderOf n.N b' → memF i)⌝))

/-- What `handleSync`'s tail reads besides `syncCtx` (round 14; persistent): the sender context
(`sendCtxN`: `Replica`, `sender` with its bag, `cs` with the RPC codes) for the followers'
`MLightSlowAck`s, and `SQ` (a quorum value) for the last `log.Println`s. -/
def swift.syncSendCtx (γ : sp.Names) (γc γm : GName) (rp : Loc) (N : Nat) : IProp netDistGF :=
  iprop(∃ me : w32, swift.sendCtxN γ γc γm rp N me ∗
    ∃ (sq : GoInterface) (szS : Nat) (memS : w32 → Prop),
      swift.fld rp go!"SQ" ↦□ sq ∗ replica.mset.quorumIs sq szS memS)

instance swift.syncSendCtx_persistent (γ : sp.Names) (γc γm : GName) (rp : Loc) (N : Nat) :
    Persistent (swift.syncSendCtx γ γc γm rp N) := by
  unfold swift.syncSendCtx; infer_instance

end defs

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions]

/-- `sortedProposes(m)`: `proposes`' keys, sorted (as `sortedIds`; at most `2^62` entries). -/
abbrev swift.sortedProposes.specI : Prop :=
  ∀ (m : Loc) (mk : GMap swift.CommandId Loc) (dq : DFrac),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      m ↦${dq} mk ∗ ⌜GMap.size mk ≤ 2 ^ 62⌝ }}
    (App (Val (@! swift.sortedProposes)) (Val #m))
  {{ (sl : GoSlice) (ids : List swift.CommandId), RET #sl; m ↦${dq} mk ∗ sl ↦* ids ∗
      ⌜ids.Nodup ∧ ∀ k, k ∈ ids ↔ (mk !! k).isSome⌝ }}

/-- `r.repchan.stop()` in normal operation (round 11): the running epoch `EpR` (abstract: the
epoch pool's, sv-swc's) gives the reply goroutine's share back (`EpH`). Round 16 (sv-swb,
GAP S-prop, main session's approval (a)): both are indexed by the run loop's `proposes` map `pM`
(then for the proposal halves; D16 made proposals read-only, the index is unused). Round 16 (main session's request, §20 of
sv-swc): the receiver `rc` is tied to the run loop's `repchan` half (handleSync's `syncFieldsOwn`
holds it), so that the run loop's instance `swift.epRun_stop` (RunAlloc.lean) proves it. -/
abbrev swift.replyChan.stop.specI (EpR EpH : GMap swift.CommandId Loc → IProp netDistGF) (rp : Loc) :
    Prop :=
  ∀ (rc : Loc) (pM : GMap swift.CommandId Loc),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      EpR pM ∗ typedPointsto (swift.fld rp go!"repchan") rc (DFrac.own (1 : Qp).half) }}
    (App (Val (rc @!! go.GoType.PointerType swift.replyChan.ty @!! go!"stop")) (Val #()))
  {{ RET #(); EpH pM ∗ typedPointsto (swift.fld rp go!"repchan") rc (DFrac.own (1 : Qp).half) }}

/-- `r.stopDescs()` after the reply goroutine stopped: every descriptor goroutine stopped, their
shares back: the stopped epoch (SW-F1 fixed in the fork: the passes repeat until none is
active). Round 16 (sv-swb): `EpH pM` is indexed by the run loop's `proposes` map (for the
proposal halves, gone with D16: proposals are read-only; the index is kept, unused). Proved over the concrete epoch: `swift.Replica.stopDescs.specD`
(StopDescs.lean). Round 22 (sv-swb): the receiver `rp` is a parameter (was quantified inside:
unprovable for an `EpH` about a given replica). -/
abbrev swift.Replica.stopDescs.specI (EpH : GMap swift.CommandId Loc → IProp netDistGF) (γ : sp.Names) (n : swift.SyncN)
    (γe γd : GName) (DF : Nat → Loc → IProp netDistGF) (PS : Nat → GMap GoString GoInterface → IProp netDistGF)
    (rr rp : Loc) : Prop :=
  ∀ (pM : GMap swift.CommandId Loc),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      EpH pM }}
    (App (Val (rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"stopDescs")) (Val #()))
  {{ RET #(); swift.epStopped n γe γd DF PS rp rr }}

/-- **`NewReplyChan(r)` without `historySize`** (round 14, GAP H-size; the shape sv-swc's
restated `NewReplyChan.specI` takes: `historySize` is left to the reply goroutine's cell,
claimed with its first message, so the caller keeps it until the epoch fills the cell; Go writes
`r.historySize = 0` after `NewReplyChan(r)`, recovery.go:608). `handleSync`'s proof uses it as a
hypothesis; round 14 (sv-swc): the restated `NewReplyChan.specI` itself (NewSpecs.lean: the cell
holds `replyCellRes`, the ballot quarter and `historySize`), proved: `swift.wp_NewReplyChan`. -/
abbrev swift.NewReplyChan.specIH : Prop := swift.NewReplyChan.specI (hG := hG)

/-- `r.freeDesc(d)` (round 11; round 16: with the pool's context `descPoolCtx DF rp`, and the
four fields `descFree` lists back with `DF d`: `descPooled`): the descriptor goes to the pool
(or is dropped). -/
abbrev swift.Replica.freeDesc.specI (DF : Loc → IProp netDistGF) : Prop :=
  ∀ (rp d : Loc),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      swift.descPoolCtxF DF rp ∗ swift.descPooled DF d }}
    (App (Val (rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"freeDesc")) (Val #d))
  {{ RET #(); True }}

/-- **The replica's id is `r`** (round 47, task 3): its `Replica` field's `Id` is `r`'s
(`runCtxD`'s). `getCmdDesc.syncSpecI`'s instance reads `r = x.r` from it against the record's
context. -/
def swift.ridIs (rp : Loc) (r : Nat) : IProp netDistGF :=
  iprop(∃ (rr : Loc) (me : w32), swift.fld rp go!"Replica" ↦□ rr ∗ replica.fld rr go!"Id" ↦□ me ∗
    ⌜sp.rid me = r⌝)

instance swift.ridIs_persistent (rp : Loc) (r : Nat) : Persistent (swift.ridIs rp r) := by
  unfold swift.ridIs; infer_instance

/-- `r.getCmdDesc(x, &syncEntry{gp, cmd, dep}, nil)` for a command of ballot `b'`'s `MSync`
`M` (`x` at index `i` of its order, accepted by `r` in `b'`): the entry's proposal (read-only,
D16) and facts go to `x`'s new descriptor, which commits and delivers it. Round 32 (T28): with
the entry's `sync` claim (its token is in the store), not the token. Round 45 (plan R8.2 (9),
D55 (2)): with the run loop's reader bundle `runReader rp γdl` and its share of `ballot` at `bw`
(`sp.bal bw = b'`), in and out, as `getCmdDescWith.coreSpecD` takes them. Round 47 (task 3, gap
45-b's names): the names `γ γcl γdl` and the receiver `rp` are the spec's parameters (the
instance's, `swift.Replica.getCmdDesc.syncSpecD`), the replica's id `r` is pinned by `ridIs`;
and (46-2, the sync entry's `repPre`/`pdOk`) `0 < b'` and a non-nil `dep` (`Dep{}` if nil,
recovery.go:664). Round 48 (47-a, D64): the replica's `locLb` of the `MSync`'s sequence (`syncMP`'s;
HandleSyncProof makes it from `takeSync_stepD`'s `locAt`s, `sp.locLb_syncSeq`). Round 54 (D74 (2),
53-4): and the ballot's leader's (`N` the replica count; `msgOk (.sync)`'s, through `handleSync`'s
pre), for a follower's sync entry (`depWhy`'s leader-prefix disjunct). -/
abbrev swift.Replica.getCmdDesc.syncSpecI (EpS : sp.SyncMsg → List sp.CmdId → IProp netDistGF)
    (γ : sp.Names) (γcl γdl : GName) (rp : Loc) (N : Nat) : Prop :=
  ∀ (gp se : Loc) (r b' i : Nat) (M : sp.SyncMsg)
    (done : List sp.CmdId) (x : swift.CommandId) (c : sp.Cmd) (vs dsl : GoSlice) (D : List sp.CmdId)
    (bw : w32) (qb : Qp),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      EpS M done ∗ swift.runReader rp γdl ∗ swift.ridIs rp r ∗
      typedPointsto (swift.fld rp go!"ballot") bw (DFrac.own qb) ∗ ⌜sp.bal bw = b'⌝ ∗ se ↦ swift.syncEntry.mk gp (state.Command.mk c.op c.key vs) dsl ∗
      vs ↦*□ c.val ∗ dsl ↦*□ (D.map ofCmdId) ∗
      swift.propIs γ gp (toCmdId x) c ∗ sp.syncIs γ b' M ∗
      sp.locAt γ r b' i (toCmdId x) ∗ sp.accepted γ r b' (toCmdId x) ∗
      swift.claimTok γcl (b', toCmdId x) .sync ∗ sp.locLb γ r b' (sp.syncSeq M) ∗
      sp.locLb γ (sp.leaderOf N b') b' (sp.syncSeq M) ∗
      ⌜(toCmdId x, c, D) ∈ M ∧ (sp.syncOrder M)[i]? = some (toCmdId x) ∧ 0 < b' ∧
        dsl ≠ slice.nil⌝ }}
    (App (App (App (Val (rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"getCmdDesc"))
      (Val #x)) (Val #(interface.mkOk (go.GoType.PointerType swift.syncEntry.ty) #se)))
      (Val #(slice.nil : GoSlice)))
  {{ (d : Loc), RET #d; EpS M (done ++ [toCmdId x]) ∗ swift.runReader rp γdl ∗
      typedPointsto (swift.fld rp go!"ballot") bw (DFrac.own qb) }}

/-- **`handleSync.specI` with the run loop's own reader bundle** (round 25, SW4 / D21): the
proof (HandleSyncProof's `wp_proofR`) reads `delivered` with it, not with `syncCtx`'s
`readerBorrowV`. Round 30 (SW4 step 2): `readerBorrowV` is gone; `specI` is this. Round 47 (45-b,
D61 (1) option (b)): a persistent `PC` in the pre (the caller's), which the proof passes to
`EpS_start` (the descriptor instance: the descriptors' contexts at the run loop's names,
`swift.descPC`; `syncCtx` is unchanged). -/
abbrev swift.Replica.handleSync.specIR (EpR : GMap swift.CommandId Loc → IProp netDistGF)
    (EpS : sp.SyncMsg → List sp.CmdId → IProp netDistGF) (DF : Nat → Loc → IProp netDistGF)
    (PS : Nat → GMap GoString GoInterface → IProp netDistGF) (γ : sp.Names) (γc γm γl γw γv γd γe γo : GName) (n : swift.SyncN) (rp rr : Loc)
    (PC : IProp netDistGF) : Prop :=
  ∀ (ls : Loc) (N r k : Nat) (ld : Bool)
    (v : swift.RunV) (M0 : Option sp.SyncMsg) (bs hd : sp.Seq) (w : swift.LView) (b' : Nat)
    (M : sp.SyncMsg),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      swift.runCtxD γ γc γm γl γw γv γe γo (n.sn N r) n.γdl rp N r k ∗
      inv swift.nodeN (swift.nodeInvD γ γv γe γo (n.sn N r) k) ∗
      swift.fld rp go!"Replica" ↦□ rr ∗ swift.syncCtx γ N r n rp ∗ □ PC ∗ swift.runReader rp n.γdl ∗
      swift.runStS γ γv rp N r ld v M0 bs hd w b' ∗
      (if w.2.2.1 then EpR v.propsM else swift.epStopped n γe γd DF PS rp rr) ∗
      swift.syncFieldsOwn rp ∗ swift.syncSendCtx γ γc γm rp N ∗
      swift.syncMaps ls b' M ∗ sp.syncIs γ b' M ∗
      -- round 54 (D74 (2), 53-4): the ballot's leader's `locLb` of the `MSync`'s sequence
      -- (`msgOk (.sync)`'s; the leader's own from `computeSync_stepD`)
      sp.locLb γ (sp.leaderOf N b') b' (sp.syncSeq M) ∗
      (⌜w.locAt b' = []⌝ ∨
        (⌜w.locAt b' = sp.syncOrder M⌝ ∗ ([∗list] i ↦ x ∈ sp.syncOrder M, sp.locAt γ r b' i x) ∗
          ([∗list] y ∈ sp.syncOrder M, swift.rowTok γo b' y swift.rowEmpty) ∗
          -- round 46 (D-SWC2-5): the pre-sync tokens' tickets (`computeSync_stepD`)
          [∗list] y ∈ sp.syncOrder M, swift.xTixK (n.sn N r).γxu (b', y))) ∗
      ⌜w.2.1 ≤ w.1 ∧ M.length ≤ 2 ^ 62 ∧ 0 < b' ∧ (w.2.2.1 = false → w.2.1 < w.1)⌝ }}
    (App (Val (rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"handleSync")) (Val #ls))
  {{ RET #(); swift.runReader rp n.γdl ∗
      ((⌜b' < w.1 ∨ (b' = w.1 ∧ w.2.2.1 = true)⌝ ∗ swift.runStS γ γv rp N r ld v M0 bs hd w b' ∗
        (if w.2.2.1 then EpR v.propsM else swift.epStopped n γe γd DF PS rp rr) ∗
        swift.syncFieldsOwn rp) ∨
      (∃ (v' : swift.RunV) (w' : swift.LView),
        swift.runSt γ γv rp N r (decide (sp.leaderOf N b' = r)) v' (some M) (sp.syncSeq M) [] w' ∗
        EpS M (sp.syncOrder M) ∗ swift.syncFieldsOwnE rp ∗
        ⌜w'.1 = b' ∧ w'.2.1 = b' ∧ w'.2.2.1 = true⌝)) }}

/-- **`r.handleSync(msg)`** (see HandleSync.lean's header): the run loop takes ballot `b'`'s
`MSync` `M` (from a peer: `w.locAt b' = []`; or its own as the new leader, with its computed row)
unless its ballot is past it (or equal, in normal operation): then nothing changes. After it,
the run loop is in normal operation at `b'`, its base `syncSeq M`, nothing handled, and the new
epoch is `EpS M (syncOrder M)` (its descriptors created). Round 11 (sv-swa): the epoch's
resources are concrete: the persistent `syncCtx` (names `n`), and the running epoch `EpR`
(abstract, the pool's; `replyChan.stop`/`stopDescs` turn it into the stopped one) or the stopped
one `epStopped n γe γd DF rp rr` (in recovery). `EpS` is `getCmdDesc.syncSpecI`'s. Round 13
(GAP S-free): `cmdDescs` is the epoch's (in `EpR`, or `epStopped`'s `descsStopped`; the new
one in `epFresh`'s `descsFresh`), no more `descRun`; `DF` is `freeDesc.specI`'s. New premise (round 13): in
recovery the ballot is past `cballot` (`w.2.2.1 = false → w.2.1 < w.1`; the record's epoch
`cballot` must be below `b'`: `deliv_rm_exec`, `takeSync_stepD`). Round 14: in recovery the
stopped epoch (round 14's `propsBack`, the other halves of `proposes`' proposals, is gone with
D16), and `syncSendCtx` (the followers' `MLightSlowAck`s, `SQ` for the log).
Round 16 (main session's request, sv-swc's §20): the ghost names and `rp`, `rr` are the spec's
parameters (so `EpR`/`EpS` may be the run loop's epoch at its names, `swift.epRun … x`), and the
context is `swift.runCtxD` (the run loop's, built from `runInv` by `runInv_ctx`).
Round 30 (SW4 step 2, D28): `syncCtx` no longer has `readerBorrowV`; `specI` is `specIR` (the
run loop's `runReader` in and out). -/
abbrev swift.Replica.handleSync.specI (EpR : GMap swift.CommandId Loc → IProp netDistGF)
    (EpS : sp.SyncMsg → List sp.CmdId → IProp netDistGF) (DF : Nat → Loc → IProp netDistGF)
    (PS : Nat → GMap GoString GoInterface → IProp netDistGF) (γ : sp.Names) (γc γm γl γw γv γd γe γo : GName) (n : swift.SyncN) (rp rr : Loc)
    (PC : IProp netDistGF) : Prop :=
  swift.Replica.handleSync.specIR EpR EpS DF PS γ γc γm γl γw γv γd γe γo n rp rr PC

end specs


end Perennial.github_com.imdea_software.swiftpaxos
