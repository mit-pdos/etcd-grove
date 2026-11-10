/-
**The server's construction: the shared interface** (the server-construction unit's stage N0,
2026-10-16; D13 and its addendum D13a-d, `notes/decisions.md`, "The server's construction:
`NewServer` over `bootstrap`'s result"). Lean-first (no Rocq counterpart).

`NewServer.spec` (`Spec/go_etcd_io/etcd/server/v3/etcdserver/NewServer.lean`) gives, on success,
`srvBuilt`: the construction premise `isServerBuilt` (`InvStart.lean`) but the rows no
`NewServer` proof gives, which are factored into one named residual, `srvBuildGap`;
`isServerBuilt_of_gap` (`BuildGap.lean`) puts the two back together. This file holds what both
halves of the unit share, frozen once placed:

* **The names chosen before the call** (D13a, route B): the raft wrapper's environment is fixed
  when `newRaftNode` allocates its channels (`server.go:324`, in the `EtcdServer` literal), before
  the id generator (line 331) and the store (line 370) exist. So the caller chooses the request
  path's names `ρ` (the generator's `ρ.ids`, the read names `ρ.rd`), the store's index names and
  certificate map, and the revisions' map before the call, and passes them in fresh
  (`idutil.idNamesFresh`, `mvcc.idxFresh`, the maps' empty authorities, `srvReadNamesFresh`). The
  apply environment `E` the construction ends with (its store's location, the batch lock's
  invariant, the hook, the auth store's reader resource) is known only afterwards: a premise is
  stated at a stand-in `E₀` that agrees with it on the names (`envAgree`), and `srvC_agree` moves
  the raft contract's `E.C` between the two.
* **The server's raft environment** `srvEr` (`E.C = srvC …`, messages unconstrained, the tick
  credit, the read names, raft's read registrations).
* **The workload clause** `clusterWorkloadOk` (D13c: a premise of `NewServer.spec` until D19c,
  now proved): every committed log's entries have good shapes (`logShape`; until D19c's move the
  apply premises themselves, `entriesOk`) and its ids are claimed under this server's generator
  (`batchWaitOk`). For several members both are facts about the other members' requests
  (`nonissues/etcd-request-id-member-prefix.md`).
* **The built part** `srvBuilt` and **the residual** `srvBuildGap`. Since D17 (2026-10-17) the
  residual has one row, the raft storage's snapshot contract `rnSnapOnce`; the others (the KV
  rows, the write budget, the uber-applier's, `storeSmall`, the id budget, `ClusterVersion()`'s
  contract, the thread bound) are `srvBuilt`'s.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvStart
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvNodeStart
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Net
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvImage

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-! ## The names chosen before the call (D13a) -/

/-- **Two apply environments agree on the names** the raft contract's `E.C` reads (`srvC`: the
results' floors `kvLogLb E.γs` and the store's witness `E.Nx`; the revisions' tokens, `revMinted`),
and on the compaction mode. (Strict M1, 2026-11-06: until then the store's index names and
certificate map, `idxCert`/`certOk`, and the store's logical mode `E.γ.cm`, gone with mvcc's
internals: the API's store has no mode, so `envAgree_mode`, `envAgree_off`, `envAgree_on` are
deleted; their users read the server's mode `E.cmp` off `envAgree`'s last conjunct.) -/
def envAgree (E E' : apply.AEnv GF) : Prop :=
  E.γs = E'.γs ∧ E.Nx = E'.Nx ∧ E.γrev = E'.γrev ∧ E.cmp = E'.cmp

/-- **The start of a new cluster's apply thread** (`x₀`): `NewStore`'s two empty revisions, the
base chain with auth disabled and no alarm, no compaction yet (`-1`). -/
def bootKV : apply.ApplyKV := ⟨[[], []], apply.alarmChain false false false, -1⟩

/-- **The start with auth on or off** (the auth plan's E2i, 2026-10-26): the base chain's auth
layer enabled when `on` (`NewServer.specM`); `bootKV` is its mode off (`bootKVOf_false`). -/
def bootKVOf (on : Bool) : apply.ApplyKV := ⟨[[], []], apply.alarmChain on false false, -1⟩

theorem bootKVOf_false : bootKVOf false = bootKV := rfl

/-- The bootstrap log as the server's entries. -/
def bootEntries (bootLog : List EntryM) : List EntryModel := bootLog.map EntryModel.ofM

/-- A bootstrap log's entries change no lease table (unit T3, L3a). -/
theorem kvTableOf_boot (c₀ : w64) (ch : apply.Chain) (lt : LeaseTable)
    (ccOk : w32 → List w8 → Prop) (ps : List w64) (bootLog : List EntryM)
    (hb : srvBootLogOk ps bootLog) : kvTableOf c₀ ch lt (bootEntries bootLog) = lt := by
  obtain ⟨-, -, he⟩ := hb
  unfold kvTableOf bootEntries
  rw [List.foldl_map]
  suffices h : ∀ (l : List EntryM), (∀ e ∈ l, e.Type' = W32 1) →
      l.foldl (fun lt e => kvTable c₀ ch lt (EntryModel.ofM e)) lt = lt by
    apply h
    intro e hm
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hm
    exact (he k _ (List.getElem?_eq_getElem hk)).2.2.1
  intro l
  induction l with
  | nil => intro _; rfl
  | cons e l ih =>
    intro hl
    rw [List.foldl_cons]
    have ht : e.Type' = W32 1 := hl e (List.mem_cons_self ..)
    have : kvTable c₀ ch lt (EntryModel.ofM e) = lt := by
      unfold kvTable
      simp only [EntryModel.ofM, ht]
      rfl
    rw [this]
    exact ih (fun e' h' => hl e' (List.mem_cons_of_mem _ h'))

/-- **The start state of a bootstrap log has no lease** (unit T3, L3a). -/
theorem kvModelSt_boot (γk : KVNames) (ccOk : w32 → List w8 → Prop) (ps : List w64)
    (bootLog : List EntryM) (hb : srvBootLogOk ps bootLog) :
    kvModelSt γk (bootEntries bootLog) = kvStateOf (kvModel γk (bootEntries bootLog)) := by
  unfold kvModelSt kvLeases
  rw [kvTableOf_boot _ _ _ ccOk ps bootLog hb]

/-- **A message raft hands the server is no `MsgSnap`** (D19p, 2026-10-18; since D21 M3,
2026-10-19, of any cluster in the no-snapshot mode, `RaftNames.reNoSnap`, which `isRaftMsg` says;
until then of a one-member cluster, raft's tracked bound its one node). -/
def srvMsgNoSnap (m : Loc) : IProp GF :=
  iprop(∃ st : MsgSt, msgOwn m DFrac.discard st ∗ ⌜st.msg.Type' ≠ MsgSnap⌝)

/-- **A message raft hands the server, with what its receiver needs** (2026-10-19, D21 stage
M1; 2026-10-27: the node API's): read-only, a message the node `id` of the server's cluster sent
(`sentMsg`: raft's protocol facts and its term bound, and its sender, what the transport's msgappv2
stream needs), with its credits (`msgCredits`: a `MsgReadIndex`'s read credit, a forwarded
proposal's tickets): what a peer's `node.Step` takes of a network message (`stepIn_intro`) but the
receiver's own facts; (raft-entsize §4, 2026-11-10) frozen at the content raft handed it out with
(`msgOut`), of bounded size (`msgOut_netContent`, the server's cluster bounding proposed data). -/
def srvMsgNet (γ : SrvRaft) (id : w64) (m : Loc) : IProp GF :=
  letI := srvStor (GF := GF) γ
  iprop(∃ st : MsgSt, msgOwn m DFrac.discard st ∗ sentMsg γ.cl srvClusterN id st ∗
    msgCredits γ.cl srvClusterN st ∗
    ∃ c : MsgC, msgRoC m c ∗ ⌜c.model = st ∧ c.csUfNil ∧ msgSizeOk c⌝)

/-- **A handed-out message's content for the network** (raft-entsize §4, 2026-11-10): frozen at
the content raft handed it out with (`msgOut`), of bounded size in a cluster with a bound on
proposed data (`Cluster.outObj_size`), unless a `MsgSnap`. -/
theorem msgOut_netContent [StorageModel GF] (γc : Cluster) (m : Loc) (st : MsgSt) (b : Nat)
    (hmd : γc.maxData = some b) (hns : st.msg.Type' ≠ MsgSnap) (hr : st.resps = []) :
    msgOut (GF := GF) γc m DFrac.discard st ⊢
      ∃ c : MsgC, msgRoC m c ∗ ⌜c.model = st ∧ c.csUfNil ∧ msgSizeOk c⌝ := by
  iintro Hmo
  iunfold msgOut at Hmo
  icases Hmo with ⟨%c, #Hc, %Hm, #Ho⟩
  have hcr : c.resps = [] := by
    have h := congrArg MsgSt.resps Hm.1
    simp only [MsgC.model, hr, List.map_eq_nil_iff] at h
    exact h
  ihave #Hro := msgPtsCC_msgRoC m c hcr $$ Hc
  ihave %Hsz := Cluster.outObj_size γc m c b $$ Ho
  iexists c
  iframe Hro
  ipureintro
  exact ⟨Hm.1, Hm.2.1, Hsz hmd (by rw [Hm.1]; exact hns)⟩

/-- Two read-only views of a message agree on its type. -/
theorem msgOwn_type_agree (m : Loc) (st1 st2 : MsgSt) :
    msgOwn (GF := GF) m DFrac.discard st1 ∗ msgOwn m DFrac.discard st2 ⊢
      ⌜st1.msg.Type' = st2.msg.Type'⌝ := by
  simp only [msgOwn, msgPts, msgPtsC]
  iintro ⟨⟨%pty1, %pto1, %pfr1, %pte1, %plt1, %pix1, %pco1, %pvo1, %prj1, %prh1, %es1, %els1,
      %ps1, %cs1, %rs1, %uf1, -, #HTy1, #cTy1, -⟩,
    ⟨%pty2, %pto2, %pfr2, %pte2, %plt2, %pix2, %pco2, %pvo2, %prj2, %prh2, %es2, %els2,
      %ps2, %cs2, %rs2, %uf2, -, #HTy2, #cTy2, -⟩⟩
  icombine HTy1 HTy2 gives %Heq
  subst Heq
  iunfold named at cTy1 cTy2
  iapply (cellRO_agree pty1 st1.msg.Type' st2.msg.Type') $$ [$cTy1 $cTy2]

/-- A message raft hands the server, with its bundle, not a snapshot (D22 S-i: `Send` takes
none), is one the network takes from its sender (`netBundle`; 2026-10-24, rafthttp stage 6d: with
leader transfer off, a `MsgApp` of raft's shape, `SentMsgOk`, from its sender, `AppFrom`;
2026-10-27: the node API's `sentMsg_transferOff`, `sentMsg_appFrom`; 2026-10-30, the repair:
`sentMsg_shape`, no leader-transfer premise). -/
theorem srvMsgNet_bundle (γ : SrvRaft) (id : w64) (m : Loc) :
    srvMsgNet (GF := GF) γ id m ∗ srvMsgNoSnap m ⊢
      netBundle (srvNet γ) id m := by
  letI := srvAnyStor (GF := GF)
  iintro ⟨H, Hns⟩
  iunfold srvMsgNet at H
  icases H with ⟨%st, #Hm, #Hr, Hc, %c, #Hcc, %Hcc⟩
  ihave %Hsh := sentMsg_shape γ.cl srvClusterN id st $$ Hr
  ihave %Hfrom := sentMsg_appFrom γ.cl srvClusterN id st $$ Hr
  iunfold srvMsgNoSnap at Hns
  icases Hns with ⟨%st', #Hm', %Hns⟩
  ihave %Hty := msgOwn_type_agree m st st' $$ [Hm Hm']
  · iframe Hm Hm'
  iunfold netBundle
  iexists st
  simp only [srvNet]
  iframe Hm Hc
  isplitr
  · imodintro
    iexists id; iexact Hr
  isplitr
  · ipureintro
    rw [Hty]
    exact ⟨Hns, Hsh.1.2.2.2.2.2.2.2, fun ha => ⟨Hsh.1.2.2.2.2.2.1 (Hty ▸ ha), Hfrom (Hty ▸ ha)⟩⟩
  iexists c
  iframe Hcc
  ipureintro; exact Hcc

/-- **The server's raft environment** (`RNEnv`): `E.C` the server's (`srvC`), every message raft
hands out but a snapshot (`srvMsgNoSnap`, D19p) with its bundle (`srvMsgNet`, D21 stage M1), a
tick's resource `True`, the read names `ρ.rd`, the server's read registrations (`srvRQ`).
(2026-10-24, rafthttp stage 6d) Of the member `id` (its messages' sender), the transport's `Send`
borrowing `S` (the server's: the raft loop's key, `srvTrKey`); (D43 M5c) its `Stop` (D43 M5e,
2026-10-26) asked of no one (`ST := False`: the static server's transport is frozen, its stop token
the apply thread's, `srvApRes`, which M6's stopping server hands over). (2026-10-27: no budget
names, the node API's term budget is the cluster's.) (2026-11-05, R2b-3d stage 5c) The stop right
`ST` a parameter (the server's: `srvTrStop s`, the live transport the apply thread hands over at the
shutdown), until then `False`. -/
def srvEr (ρ : ReqNames) (E : apply.AEnv GF) (ai₀ c₀ : w64) (x₀ : apply.ApplyKV)
    (id : w64) (S ST : IProp GF) : RNEnv GF :=
  ⟨srvC ρ E ai₀ c₀ x₀, fun m => iprop(srvMsgNet ρ.raft.raft id m ∗ srvMsgNoSnap m),
    iprop(True), ρ.rd, srvRQ ρ.rd.raft, S, ST⟩

/- (2026-10-30, the repair: snapshots allowed) `rnSnapMsg_false` is gone: `msgSnapC` delivers raft's
`MsgSnap`s (`rnSnapMsg`). -/

/-- **The read names' fresh rows but the KV state's variable** (D19g (a), 2026-10-18): what
`NewServer.spec` takes, the KV state's variable having gone into the KV invariant and the
client's `etcdKV` at raft's allocation (`srvRaftBoot_alloc`, `NewServerAlloc.lean`). -/
def srvReadNamesFreshNK (γr : ReadNames) : IProp GF :=
  iprop(monoNatAuthOwn γr.applied 1 0 ∗ monoNatAuthOwn γr.committed 1 0 ∗
    (∃ x : Loc × NeedNames, ghostVar γr.notifier 1 x) ∗
    ghostMapAuth γr.logs 1 (∅ : GMap w64 mvcc.Log) ∗ ghostVar γr.pend 1 false ∗
    ghostVar γr.kv.hi 1 γr.kv.log0.length)

/-! ## The workload clause (D13c; D19c) -/

/-- **The cluster's workload** (persistent): every committed log `L` (after the server's start)
has entries of good shapes (`logShape`: each normal entry's request meets its premise at every
log where the size clauses hold, `rqShape`), and every entry's id is claimed under this server's
generator (`batchWaitOk`): what the raft contract's `E.C` asks beyond the KV invariant
(`rnEnvOk_of_cluster`). A premise of `NewServer.spec` until D19c (2026-10-18, D13c); since then
proved (`clusterWorkloadOk_of`, `BuildGap.lean`) from the KV invariant, which keeps every
committed entry's shape and id claim (`kvWork`), and the reserved id `0` (`idNoZero`); at an
update, as it opens the KV invariant. Until D19c's move (2026-10-18) it asked the apply premises
themselves over every run from `x₀` at the consistent index `c₀` (`entriesOk`), whose size
clauses were the residual premise `clusterLogBound`; the apply thread now checks those at the log
it meets (`entryOk_of_shape`, `srvApplyKV_small`), so `c₀` and `x₀` are unused (kept for the
callers' statements). -/
def clusterWorkloadOk (ρ : ReqNames) (E : apply.AEnv GF) :
    IProp GF :=
  iprop(□ ∀ L : List EntryModel, srvRLogLb ρ.raft L ={⊤}=∗ ⌜logShape ρ.kv.lm L⌝ ∗ batchWaitOk ρ E L)

instance clusterWorkloadOk_persistent (ρ : ReqNames) (E : apply.AEnv GF) :
    Persistent (clusterWorkloadOk (GF := GF) ρ E) := by
  unfold clusterWorkloadOk; infer_instance

/-! ## The built part and the residual -/

/-- `srvFieldsBuilt` (D22 receiver epochs, S7a, 2026-10-23: the same; until then `srvFieldsBuilt`
had the uber-applier, `srvUberApplyAddr`, `applierFor`, a KV row of `srvBuildGap`). -/
def srvFieldsBuiltNA (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (v : SrvFields) : IProp GF :=
  iprop(srvLgAddr s ↦□ v.lg ∗ ⌜v.lg ≠ null⌝ ∗
      ⌜E.Pk = (fun _ => batchLockInv γ TM) ∧ v.hook = #E.f ∧ E.f ≠ func.nil⌝ ∗ ⌜srvEnvOk s γ ci E v.cluster⌝ ∗
      hookSpec γ ci TM v.hook ∗
      srvLessorAddr s ↦□ v.lessor ∗ lessorOk E.lg E.authMode.isOn v.lessor ∗
      srvFirstCommitAddr s ↦□ v.firstCommit ∗ srvAlarmStoreAddr s ↦□ v.alarmStore ∗
      srvClusterAddr s ↦□ v.cluster ∗ membership.isRaftCluster v.cluster ∗
      srvQuotaAddr s ↦□ v.quota ∗
      srvLgMuAddr s ↦□ v.lgMu ∗ srvMemberIDAddr s ↦□ v.memberID ∗ srvLeadInv s ∗
      cfgElectionTicksAddr (srvCfgAddr s) ↦□ v.electionTicks ∗
      cfgTickMsAddr (srvCfgAddr s) ↦□ v.tickMs ∗
      isNotifier v.firstCommit ∗ isAlarmStore v.alarmStore ∗ srvBeHooked s γ ci E)

instance srvFieldsBuiltNA_persistent (s : Loc) (γ : ApplyNames) (ci : Loc)
    (TM : MetaCI → IProp GF) (E : apply.AEnv GF) (v : SrvFields) :
    Persistent (srvFieldsBuiltNA s γ ci TM E v) := by
  unfold srvFieldsBuiltNA; infer_instance

/-- `srvReadBuilt` without the KV rows (`srvKVAddr` and the store's handle: `srvBuildGap`). -/
def srvReadBuiltNK (s : Loc) (E : apply.AEnv GF) (v : ReadFields) : IProp GF :=
  iprop(srvLessorAddr s ↦□ v.lessor ∗ apply.isApplyLessor v.lessor E.γ E.Pk E.f E.BkTie E.RO E.RW ∗
    srvAuthStoreAddr s ↦□ v.auth ∗ apply.isAuthStore v.auth E.Pk E.f E.BkTie E.RD E.authMode E.RW ∗
    srvLgAddr s ↦□ v.lg ∗ ⌜v.lg ≠ null⌝ ∗
    srvCfgFieldAddr s go!"WarningApplyDuration" ↦□ v.wad ∗
    inv srvN (∃ t : w64, sync.atomic.ownUint64 (srvTermAddr s) (DFrac.own 1) t) ∗
    (∃ log₀ : mvcc.Log, srvApi.kvLogLb E.γs log₀ ∗
      ⌜2 ≤ log₀.length ∧ mvcc.LogPutsLe etcdKeyMax log₀⌝) ∗
    srvFirstCommitAddr s ↦□ v.fc)

instance srvReadBuiltNK_persistent (s : Loc) (E : apply.AEnv GF) (v : ReadFields) :
    Persistent (srvReadBuiltNK s E v) := by
  unfold srvReadBuiltNK; infer_instance

/-- `applyBuilt` without the applier's KV state (`applyKV`: `srvBuildGap`). -/
def applyBuiltNA (s : Loc) (γ : ApplyNames) (ci : Loc) (b : GoInterface) (E : apply.AEnv GF)
    (γr : ReadNames) (ai₀ c₀ : w64) (x₀ : apply.ApplyKV) : IProp GF :=
  iprop(∃ (st₀ : ApplyState) (a t : w64) (f : Bool),
    applyThread γ st₀ ∗ ⌜loopOk γ st₀ ai₀ ∧ c₀ = ciEff γ st₀.k⌝ ∗ applyBackend γ ci b ∗
    ciApplying ci a t ∗ srvLgReader s ∗ srvBemuReaderAt s E.γbe ∗ mvcc.api.mvccReaders E.γ 1 ∗
    srvBeOwn s E ∗ revAuth E x₀.log ∗ srvAuthApplyRes s E ∗
    -- (2026-11-04, the lease-expiry plan's step 2) the lessor's range deleter (`mvcc.New`'s)
    (∃ rd : GoFunc, lease.rdOwn (mvcc.api.mvccLeases E.γ) rd ∗ mvcc.api.mvccDeleter rd E.γ) ∗
    srvAppliedOwn γr ai₀ ∗ appliedLogAt γr ai₀ x₀.log ∗ kvRun γr ai₀ c₀ [] x₀ ∗ srvRest E γr [] ∗
    srvApRes s γr [] ∗ srvForceSnapAddr s ↦ f)

/-- **The built part** (`NewServer.spec`'s postcondition, on success): `isServerBuilt` but the
rows of `srvBuildGap` (named as `isServerBuilt`'s; `#Hfb`, `#Hrdb`, `Happ` without their KV
parts, which `#Hkv` and `HWB` give in part: `srv.kv` with its read view and the write budget,
moved from the residual by unit N4's `NewServer` proof, 2026-10-17; `#Hsmall`, `#HNR`, `#Hcv`,
`%Hbound` since D17, from `NewServer.spec`'s lifetime premises and the cluster's contract). -/
def srvBuilt (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (Er : RNEnv GF) (γn : RNNames)
    (b : GoInterface) (ai₀ c₀ : w64) (x₀ : apply.ApplyKV) (N : Nat) : IProp GF :=
  iprop("#Hci" ∷ isServerCI s γ ci ∗
    "#Hfb" ∷ (∃ v : SrvFields, srvFieldsBuiltNA s γ ci TM E v) ∗
    "#Hreqb" ∷ (∃ v : ReqFields, srvReqBuilt s E ρ v) ∗
    "#Hrdb" ∷ (∃ v : ReadFields, srvReadBuiltNK s E v) ∗
    "#Hrunb" ∷ (∃ v : RunFields, srvRunBuilt s v) ∗
    -- (M2, S4) the compactor's run, once (`start` spends it)
    "Hcrun" ∷ (∃ c : GoInterface, srvCompactorAddr s ↦□ c ∗ compactorRun s E c) ∗
    "#Hsab" ∷ srvApplyAllBuilt s γr ∗
    "#Hai" ∷ srvAppliedInv s E γr ∗
    "#Hkvi" ∷ srvKVInvs E γr ∗
    "#Hti" ∷ inv srvN (∃ t : w64, sync.atomic.ownUint64 (srvTermAddr s) (DFrac.own 1) t) ∗
    "#Hci'" ∷ srvCommittedInv s γr ∗
    "#Hrn" ∷ isRaftNode Er γn (srvRAddr s) ∗
    -- (D43 M3, 2026-10-25) a fresh start: no entry replayed (2026-10-30, the repair: in every
    -- cluster, raft's one mode; until then in its dynamic mode)
    "%HEr" ∷ ⌜Er.C = srvC ρ E ai₀ c₀ x₀ ∧ Er.γr = γr ∧
      (uint.Z c₀ ≤ uint.Z ai₀ ∧ γn.pre = [] ∧ ai₀ = W64 0) ∧
      -- (R2d'a A6, DRAFT) a first start: the restart point's backend log `γn.a0` empty
      γn.a0 = []⌝ ∗
    -- (R2d'a A7, A10 item 5, 2026-11-06; DRAFT, approved by 82) no merged snapshot sent at a new
    -- raft term while the replay window is pending (`srvWinPend`; corrected 2026-11-07: false
    -- whenever the restarted member is later elected and snapshots a follower, its `n` free; R2d'b
    -- restates it, R2s removes it; with row 3 false on most restarts, the restart meaning is vacuous
    -- until R2d'b; free at a first start, `srvWinPend_first`)
    "Hwpend" ∷ srvWinPend s γr γn ∗
    -- (2026-10-30, the repair) the apply side's half of the node's running token (`dvRun`), which
    -- `run` gives the raft loop with `raftNode.stop` (`rnStopBag`)
    "Hrunh" ∷ (letI := srvStor (GF := GF) γn.node; nodeRunning γn.nl γn.node.cl srvClusterN (1 : Qp).half) ∗
    -- (2026-10-31) the WAL's open token: the apply side's half (its disk snapshot's `SaveSnap`, which
    -- `run` gives the raft loop with `raftNode.stop`) and the loop's (`raftNode.start`'s); the disk
    -- cooperating (`storage.diskOk`, `NewServer`'s premise)
    "Hwth" ∷ rnWalTokA γn (srvRAddr s) (1 : Qp).half ∗ "Hwtl" ∷ rnWalTokL γn (srvRAddr s) ∗
    "%Hdisk" ∷ ⌜storage.diskOk⌝ ∗
    -- (2026-11-02, the lease-grant plan's D2) in a cluster that grants leases, the open
    -- cases (`srvGrantOpen`, `NewServer`'s precondition); (2026-11-04, the lease-expiry plan's
    -- Part C) as the lease subsystem's sealed premise at some mode (`lease.runCfg`)
    "%Hslg" ∷ ⌜∃ m : lease.Mode, lease.runCfg (GF := GF) γr.kv.lm m⌝ ∗
    "%Hρrd" ∷ ⌜ρ.rd = γr⌝ ∗
    -- (J8b, 2026-11-01) the server's member id is the raft node's (`isServerBuilt`'s)
    "#Hmid" ∷ srvMemberIDAddr s ↦□ γn.id ∗
    -- (2026-11-02, the cluster-rows stage) the member id a voter (the monitors' permission,
    -- `srvMonitorPermitM_of`: its attribute requests name it)
    "%Hmidc" ∷ ⌜γn.id ∈ γr.raft.raft.cfg⌝ ∗
    -- (J8b, 2026-11-01) the meta reads of the backends a snapshot opens (`bootOk`'s `#HmetaSnap`)
    "#HmetaSnap" ∷ srvMetaSnap γ ∗
    "Hloop" ∷ rnLoopTok γn [] ∗ "Hsend" ∷ Er.S ∗ "Happly" ∷ rnApplyTok γn [] ∗ "Hrdone" ∷ rnDoneTok γn (srvRAddr s) ∗
    "#Hcci" ∷ context.isClosedchanInit ∗
    "#Hwci" ∷ waitClosecInit ∗
    "Hw" ∷ (∃ w : GoInterface, srvWAddr s ↦ w) ∗
    "Haw" ∷ (∃ aw : GoInterface, srvApplyWaitAddr s ↦ aw) ∗
    "Hdone" ∷ (∃ c : Loc, srvDoneAddr s ↦ c) ∗
    "Hstop" ∷ (∃ c : Loc, srvStopAddr s ↦ c) ∗
    "Hstopping" ∷ (∃ c : Loc, srvStoppingAddr s ↦ c) ∗
    "Hctx" ∷ (∃ c : GoInterface, srvCtxAddr s ↦ c) ∗
    "Hcancel" ∷ (∃ c : GoFunc, srvCancelAddr s ↦ c) ∗
    "Hread" ∷ (∃ r : Loc, srvReadAddr s ↦ r) ∗
    "Hlc" ∷ (∃ n : Loc, srvLeaderChangedAddr s ↦ n) ∗
    "Hsc" ∷ (∃ n : w64, srvSnapCountAddr s ↦ n) ∗
    -- (2026-10-30, the repair, P10: no run-length premise; until then the receipts' bound at most
    -- the value `start` sets, `5000` for `0`, plus one)
    "Hscu" ∷ (∃ n : w64, srvSnapCatchUpAddr s ↦ n) ∗
    "Hwg" ∷ srvWgAddr s ↦ (zero_val sync.WaitGroup) ∗
    "HwgMu" ∷ srvWgMuAddr s ↦ (zero_val sync.RWMutex) ∗
    "Hcomm" ∷ (∃ c : w64, srvCommittedOwn γr c) ∗
    "Hnot" ∷ (∃ x : Loc × NeedNames, ghostVar γr.notifier 1 x) ∗
    "Happ" ∷ applyBuiltNA s γ ci b E γr ai₀ c₀ x₀ ∗
    "Hlr" ∷ srvLgReader s ∗
    "Hlrl" ∷ srvLgReader s ∗
    "Hfcr" ∷ (∃ n : Loc, srvFirstCommitAddr s ↦□ n ∗ notifyReader n) ∗
    "#Hkv" ∷ (∃ kv : GoInterface, srvKVAddr s ↦□ kv ∗ □ mvcc.api.isMvcc kv E.γ ∗ ⌜kv = E.kv⌝) ∗
    "HWB" ∷ srvWTBudget E ∗
    "#HNR" ∷ □ (|==> idCred ρ.ids 1) ∗
    "#Hcv" ∷ clusterVersionOk s ∗
    -- (the backend-auth-split stage, 2026-11-02) within the backend's pool of readers (`2 ^ 28`;
    -- until then `2 ^ 31`, `GoAttach`'s)
    "%Hbound" ∷ ⌜threadBound GF ≤ backend.rdPoolN⌝ ∗
    -- (revoke-open, 2026-11-06) what `NewServer` built for the revocation
    "#Hrvkb" ∷ srvRevokeBuilt s E ∗
    "Hua" ∷ (∃ ua : GoInterface, srvUberApplyAddr s ↦ ua ∗ apply.applierFor ua E ∗
      apply.applyKV E ua x₀) ∗
    -- (linkv-txn stage B1, 2026-10-20) the member's entry of the registries' map, for `start`
    "Hwtok" ∷ idWaitTok ρ.ids ∗
    -- (2026-10-26, D22 J1a) what the snapshot path takes of the construction (`SnapRO.lean`)
    "Hsnapb" ∷ srvSnapBoot s ci E γr γ)

/-- **The residual** (see the file header): the row of `isServerBuilt` no `NewServer` proof
gives -- the raft storage's snapshot contract `rnSnapOnce` (`notes/STATUS.md`, "srvBuildGap's
rows": the application could not call `MemoryStorage.Snapshot` in the model while raft owns the
storage). Since D17d (2026-10-18) `NewServer.spec` gives it too, from the storage's application
snapshot token (`rnSnapOnce_of_tok`); until then a premise of whoever composed `NewServer` with
`start`. (`srv.kv` as `txn.isKV` with its
read view and the write budget `txn.storeWTs` were rows here until unit N4's `NewServer` proof,
2026-10-17; the uber-applier's `applierFor`/`applyKV` until D14i; `storeSmall`, the id budget,
`clusterVersionOk` and the thread bound until D17, the same day: `srvBuilt`, from
`NewServer.spec`'s workload premises and the cluster's `Version` contract.) -/
def srvBuildGap (s : Loc) (γn : RNNames) (ai₀ at₀ : w64) : IProp GF :=
  iprop("Hsnap" ∷ (∃ ms : Loc, rnRaftStorageAddr (srvRAddr s) ↦□ ms ∗ rnSnapOnce γn.node.reg γn.node.cl γn.key ms γn.γs ai₀ at₀))

end defs

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`srvC` reads only the names** (D13a): two environments that agree on them give the same
raft contract's `E.C`. -/
theorem srvC_agree (ρ : ReqNames) (E E' : apply.AEnv GF) (ai₀ c₀ : w64) (x₀ : apply.ApplyKV)
    (_h : envAgree E E') : srvC ρ E ai₀ c₀ x₀ = srvC ρ E' ai₀ c₀ x₀ := by
  -- (the lease-grant plan's 2.6) the contract reads no name of `E`: a conf change's waiters are
  -- refuted by `reqWaitNone`, free of the environment
  rfl

end lemmas

end EtcdGrove
end Perennial
