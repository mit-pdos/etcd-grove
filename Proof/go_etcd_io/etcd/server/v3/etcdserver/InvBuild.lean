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
  (`issues/etcd-request-id-member-prefix.md`).
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
store's index names, through the results' certificates `idxCert`; its certificate map, `certOk`;
the revisions' tokens, `revMinted`). -/
def envAgree (E E' : apply.AEnv GF) : Prop :=
  E.γ.idx = E'.γ.idx ∧ E.γ.cok = E'.γ.cok ∧ E.γrev = E'.γrev

/-- **The start of a new cluster's apply thread** (`x₀`): `NewStore`'s two empty revisions, the
base chain with auth disabled and no alarm. -/
def bootKV : apply.ApplyKV := ⟨[[], []], apply.alarmChain false false false⟩

/-- **The start with auth on or off** (the auth plan's E2i, 2026-10-26): the base chain's auth
layer enabled when `on` (`NewServer.specM`); `bootKV` is its mode off (`bootKVOf_false`). -/
def bootKVOf (on : Bool) : apply.ApplyKV := ⟨[[], []], apply.alarmChain on false false⟩

theorem bootKVOf_false : bootKVOf false = bootKV := rfl

/-- The bootstrap log as the server's entries. -/
def bootEntries (bootLog : List EntryM) : List EntryModel := bootLog.map EntryModel.ofM

/-- A bootstrap log's entries change no lease table (unit T3, L3a). -/
theorem kvTableOf_boot (c₀ : w64) (ch : apply.Chain) (lt : LeaseTable)
    (ccOk : w32 → List w8 → Prop) (ps : List w64) (bootLog : List EntryM)
    (hb : BootLogOk ccOk ps bootLog) : kvTableOf c₀ ch lt (bootEntries bootLog) = lt := by
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
    (bootLog : List EntryM) (hb : BootLogOk ccOk ps bootLog) :
    kvModelSt γk (bootEntries bootLog) = kvStateOf (kvModel γk (bootEntries bootLog)) := by
  unfold kvModelSt kvLeases
  rw [kvTableOf_boot _ _ _ ccOk ps bootLog hb]

/-- **A message raft hands the server is no `MsgSnap`** (D19p, 2026-10-18; since D21 M3,
2026-10-19, of any cluster in the no-snapshot mode, `RaftNames.reNoSnap`, which `isRaftMsg` says;
until then of a one-member cluster, raft's tracked bound its one node). -/
def srvMsgNoSnap (m : Loc) : IProp GF :=
  iprop(∃ st : MsgSt, msgOwn m DFrac.discard st ∗ ⌜st.msg.Type' ≠ MsgSnap⌝)

/-- **A message raft hands the server, with what its receiver needs** (2026-10-19, D21 stage
M1): read-only, a message raft sent (`isRaftMsg`, its protocol abstraction), at a term the
budget `bud` reached (`termLB`), with its read credit, one for a `MsgReadIndex` (`rdCred`):
what a peer's `node.Step` takes of a network message (`netP`) but the receiver's own facts
(`NetMsgOk`) and a `MsgTimeoutNow`'s tick credit. (2026-10-24, rafthttp stage 6d) Of the member
`id` that sent it (`isRaftMsg`'s sender: a `MsgApp`'s `From`, what the transport's msgappv2 stream
needs). -/
def srvMsgNet (γ : RaftNames) (bud : BudgetNames) (id : w64) (m : Loc) : IProp GF :=
  iprop(∃ st : MsgSt, msgOwn m DFrac.discard st ∗ isRaftMsg γ id st ∗
    termLB bud st.msg.Term' ∗
    rdCred γ (if st.msg.Type' = MsgReadIndex then 1 else 0) ∗
    -- (2026-10-19, D21 M6) a forwarded proposal's tickets
    stTks γ st)

/-- **What the server's messages carry over the network** (D21 M2, 2026-10-19; the network's
payload, `NetPayload`): persistently, the protocol facts and the term bound (`isRaftMsg`, whose
`SentMsgOk` clause gives the receiver's `NetMsgOk`, and `termLB`); once, the read credit of a
`MsgReadIndex`, delivered at most once; any other message may be duplicated, its credit `0` anew.
(2026-10-19, D21 M6, D20 (b)) and a forwarded `MsgProp`'s tickets (`stTks`), delivered at most
once: the transport's at-most-once promise for a `once` message (`Transport.Start`, D21b).
(2026-10-19, D22 S-i) A snapshot's database image carries `srvImage` (`dbImage` at the fresh
cluster's start): what the sender's backend snapshot gives (S-h) and the receiver's
`OpenSnapshotBackend` reads (S-j). -/
def srvNet (γ : RaftNames) (bud : BudgetNames) : NetPayload GF where
  P st := iprop((∃ sid, isRaftMsg γ sid st) ∗ termLB bud st.msg.Term')
  O st := iprop(rdCred γ (if st.msg.Type' = MsgReadIndex then 1 else 0) ∗ stTks γ st)
  once st := st.msg.Type' = MsgReadIndex ∨ st.msg.Type' = MsgProp
  P_pers st := by infer_instance
  dup st h := by
    have h1 : st.msg.Type' ≠ MsgReadIndex := fun e => h (Or.inl e)
    have h2 : st.msg.Type' ≠ MsgProp := fun e => h (Or.inr e)
    simp only [h1, if_false]
    iintro
    imod rdCred_zero_upd γ with Hz
    imodintro
    iframe Hz
    unfold stTks
    rw [if_neg h2]
    iempintro
  img i D := srvImage γ i D
  img_pers i D := by infer_instance

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
none), is one the network takes from its sender (`netBundle`; 2026-10-24, rafthttp stage 6d: in
the no-transfer mode, a `MsgApp` of raft's shape, `SentMsgOk`, from its sender, `AppFrom`). -/
theorem srvMsgNet_bundle (γ : RaftNames) (bud : BudgetNames) (id : w64) (m : Loc)
    (hnx : γ.reNoXfer = true) :
    srvMsgNet (GF := GF) γ bud id m ∗ srvMsgNoSnap m ⊢ netBundle (srvNet γ bud) id m := by
  iintro ⟨H, Hns⟩
  iunfold srvMsgNet at H
  icases H with ⟨%st, #Hm, #Hr, #Ht, Hc, Htk⟩
  ihave #Hr' := Hr
  iunfold isRaftMsg at Hr'
  icases Hr' with ⟨-, %Hsent, -, -, %Hrs⟩
  iunfold srvMsgNoSnap at Hns
  icases Hns with ⟨%st', #Hm', %Hns⟩
  ihave %Hty := msgOwn_type_agree m st st' $$ [Hm Hm']
  · iframe Hm Hm'
  iunfold netBundle
  iexists st
  simp only [srvNet]
  iframe Hm Hc Htk
  isplitr
  · imodintro
    iframe Ht
    iexists id; iexact Hr
  ipureintro
  rw [Hty]
  exact ⟨Hns, Hrs.1, fun ha => ⟨(Hsent hnx).2.2.2.2.2.1 (Hty ▸ ha), Hrs.2 (Hty ▸ ha)⟩⟩

/-- **The server's raft environment** (`RNEnv`): `E.C` the server's (`srvC`), every message raft
hands out but a snapshot (`srvMsgNoSnap`, D19p; until then every message, the transport's
contract, `rafthttp.Transport`, asking nothing of them) with its bundle (`srvMsgNet`, D21 stage
M1), a tick's resource raft's tick credit of the budget `bud`, the read names `ρ.rd`, raft's read
registrations. (2026-10-24, rafthttp stage 6d) Of the member `id` (its messages' sender), the
transport's `Send` borrowing `S` (the server's: the raft loop's key, `srvTrKey`); (D43 M5c) its
`Stop` (D43 M5e, 2026-10-26) asked of no one (`ST := False`: the static server's transport is
frozen, its stop token the apply thread's, `srvApRes`, which M6's stopping server hands over; until
then `True`, a free `Stop`, which Go's `AddPeer` on a stopped transport made unsound). -/
def srvEr (ρ : ReqNames) (E : apply.AEnv GF) (ai₀ c₀ : w64) (x₀ : apply.ApplyKV)
    (bud : BudgetNames) (id : w64) (S : IProp GF) : RNEnv GF :=
  ⟨srvC ρ E ai₀ c₀ x₀, fun m => iprop(srvMsgNet ρ.raft.raft bud id m ∗ srvMsgNoSnap m),
    iprop(True), ρ.rd, srvRQ ρ.rd.raft, S, iprop(False)⟩

/-- The ticker's contract does not read the transport's borrow (`isRNTicker` reads `E.T`). -/
theorem rnTickerOk_srvEr_S (ρ : ReqNames) (E : apply.AEnv GF) (ai₀ c₀ : w64)
    (x₀ : apply.ApplyKV) (bud : BudgetNames) (id : w64) (S S' : IProp GF) :
    rnTickerOk (srvEr ρ E ai₀ c₀ x₀ bud id S) ⊢ rnTickerOk (srvEr ρ E ai₀ c₀ x₀ bud id S') := by
  unfold rnTickerOk isRNTicker srvEr
  exact .rfl

/-- **A cluster in the no-snapshot mode sends no snapshot** (D21 M3, 2026-10-19; `isRaftMsg`'s
clause, from raft's invariant `LogNsOk`). Until then (D19p) of a one-member cluster: with raft's
tracked bound one node, a `MsgSnap`'s sender and receiver would be the same. -/
theorem isRaftMsg_not_snap (γ : RaftNames) (hns : γ.reNoSnap = true) (sid : w64) (st : MsgSt) :
    isRaftMsg (GF := GF) γ sid st ⊢ ⌜st.msg.Type' ≠ MsgSnap⌝ := by
  iintro Hr
  iunfold isRaftMsg at Hr
  icases Hr with ⟨%H, -⟩
  ipureintro; exact H hns

/-- **The server's `msgSnapC` never delivers** (D19p) in raft's no-snapshot mode: what
`processMessages` hands it is an owned `MsgSnap` with its protocol facts (`rnSnapMsg`, D22 S-l
sender, 2026-10-22), which raft never sends in that mode (`isRaftMsg_not_snap`). -/
theorem rnSnapMsg_false (γ : NodeNames) (hns : γ.raft.reNoSnap = true) (m : Loc) :
    rnSnapMsg γ m ⊢ (False : IProp GF) := by
  iintro H
  iunfold rnSnapMsg at H
  icases H with ⟨%st, -, %Hty, #Hrm, -⟩
  ihave %Hne := isRaftMsg_not_snap γ.raft hns γ.id st $$ Hrm
  exact absurd Hty Hne

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
  iprop(□ ∀ L : List EntryModel, srvRLogLb ρ.raft L ={⊤}=∗ ⌜logShape L⌝ ∗ batchWaitOk ρ E L)

instance clusterWorkloadOk_persistent (ρ : ReqNames) (E : apply.AEnv GF) :
    Persistent (clusterWorkloadOk (GF := GF) ρ E) := by
  unfold clusterWorkloadOk; infer_instance

/-! ## The built part and the residual -/

/-- `srvFieldsBuilt` (D22 receiver epochs, S7a, 2026-10-23: the same; until then `srvFieldsBuilt`
had the uber-applier, `srvUberApplyAddr`, `applierFor`, a KV row of `srvBuildGap`). -/
def srvFieldsBuiltNA (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (v : SrvFields) : IProp GF :=
  iprop(srvLgAddr s ↦□ v.lg ∗ ⌜v.lg ≠ null⌝ ∗
      ⌜E.P = batchLockInv γ TM ∧ E.f = v.hook⌝ ∗ ⌜srvEnvOk s γ ci E v.cluster⌝ ∗
      hookSpec γ ci TM v.hook ∗
      srvLessorAddr s ↦□ v.lessor ∗ lessorOk v.lessor ∗
      srvFirstCommitAddr s ↦□ v.firstCommit ∗ srvAlarmStoreAddr s ↦□ v.alarmStore ∗
      srvClusterAddr s ↦□ v.cluster ∗ membership.isRaftCluster v.cluster ∗
      srvQuotaAddr s ↦□ v.quota ∗
      srvLgMuAddr s ↦□ v.lgMu ∗ srvMemberIDAddr s ↦□ v.memberID ∗ srvLeadInv s ∗
      cfgElectionTicksAddr (srvCfgAddr s) ↦□ v.electionTicks ∗
      cfgTickMsAddr (srvCfgAddr s) ↦□ v.tickMs ∗
      isNotifier v.firstCommit ∗ isAlarmStore v.alarmStore)

instance srvFieldsBuiltNA_persistent (s : Loc) (γ : ApplyNames) (ci : Loc)
    (TM : MetaCI → IProp GF) (E : apply.AEnv GF) (v : SrvFields) :
    Persistent (srvFieldsBuiltNA s γ ci TM E v) := by
  unfold srvFieldsBuiltNA; infer_instance

/-- `srvReadBuilt` without the KV rows (`srvKVAddr`, `txn.isKV`, the store's read view,
`storeSmall`: `srvBuildGap`). -/
def srvReadBuiltNK (s : Loc) (E : apply.AEnv GF) (v : ReadFields) : IProp GF :=
  iprop(srvLessorAddr s ↦□ v.lessor ∗ apply.isApplyLessor v.lessor E.s E.γ E.P E.f E.RW ∗
    srvAuthStoreAddr s ↦□ v.auth ∗ apply.isAuthStore v.auth E.γ E.P E.f E.RD E.authMode E.RW ∗
    srvLgAddr s ↦□ v.lg ∗ ⌜v.lg ≠ null⌝ ∗
    srvCfgFieldAddr s go!"WarningApplyDuration" ↦□ v.wad ∗
    inv srvN (∃ t : w64, sync.atomic.ownUint64 (srvTermAddr s) (DFrac.own 1) t) ∗
    (∃ log₀ : mvcc.Log, mvcc.idxCert E.γ.idx log₀ ∗ ⌜2 ≤ log₀.length⌝) ∗
    srvFirstCommitAddr s ↦□ v.fc)

instance srvReadBuiltNK_persistent (s : Loc) (E : apply.AEnv GF) (v : ReadFields) :
    Persistent (srvReadBuiltNK s E v) := by
  unfold srvReadBuiltNK; infer_instance

/-- `applyBuilt` without the applier's KV state (`applyKV`: `srvBuildGap`). -/
def applyBuiltNA (s : Loc) (γ : ApplyNames) (ci : Loc) (b : GoInterface) (E : apply.AEnv GF)
    (γr : ReadNames) (ai₀ c₀ : w64) (x₀ : apply.ApplyKV) : IProp GF :=
  iprop(∃ (st₀ : ApplyState) (a t : w64) (f : Bool),
    applyThread γ st₀ ∗ ⌜loopOk γ st₀ ai₀ ∧ c₀ = ciEff γ st₀.k⌝ ∗ applyBackend γ ci b ∗
    ciApplying ci a t ∗ srvLgReader s ∗ srvBemuReaderAt s E.γbe ∗ srvBeOwn s E ∗
    revAuth E x₀.log ∗ srvAuthApplyRes s E ∗
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
    "#Hsab" ∷ srvApplyAllBuilt s ∗
    "#Hai" ∷ srvAppliedInv s E γr ∗
    "#Hkvi" ∷ srvKVInvs E γr ∗
    "#Hti" ∷ inv srvN (∃ t : w64, sync.atomic.ownUint64 (srvTermAddr s) (DFrac.own 1) t) ∗
    "#Hci'" ∷ srvCommittedInv s γr ∗
    "#Hrn" ∷ isRaftNode Er γn (srvRAddr s) ∗
    -- (D43 M3, 2026-10-25) in raft's dynamic mode a fresh start: no entry replayed
    "%HEr" ∷ ⌜Er.C = srvC ρ E ai₀ c₀ x₀ ∧ Er.γr = γr ∧
      (γn.node.dyn = true → uint.Z c₀ ≤ uint.Z ai₀)⌝ ∗
    "%Hρrd" ∷ ⌜ρ.rd = γr⌝ ∗
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
    -- (2026-10-19, D21 M3) the receipts' bound at most the value `start` sets (`5000`, etcd's
    -- default, for `0`) plus one: `NewServer.spec`'s run bound
    "Hscu" ∷ (∃ n : w64, srvSnapCatchUpAddr s ↦ n ∗
      ⌜receiptBound GF ≤ uint.Z (if n = W64 0 then W64 5000 else n) + 1⌝) ∗
    "Hwg" ∷ srvWgAddr s ↦ (zero_val sync.WaitGroup) ∗
    "HwgMu" ∷ srvWgMuAddr s ↦ (zero_val sync.RWMutex) ∗
    "Hcomm" ∷ (∃ c : w64, srvCommittedOwn γr c) ∗
    "Hnot" ∷ (∃ x : Loc × NeedNames, ghostVar γr.notifier 1 x) ∗
    "Happ" ∷ applyBuiltNA s γ ci b E γr ai₀ c₀ x₀ ∗
    "Hlr" ∷ srvLgReader s ∗
    "Hlrl" ∷ srvLgReader s ∗
    "Hfcr" ∷ (∃ n : Loc, srvFirstCommitAddr s ↦□ n ∗ notifyReader n) ∗
    "#Hkv" ∷ (∃ (kv : GoInterface) (rv : Loc), srvKVAddr s ↦□ kv ∗ txn.isKV kv E.s E.γ ∗
      E.s.[go_etcd_io.etcd.server.v3.storage.mvcc.store, go!"ReadView"] ↦□
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.mvcc.readView.ty)
          #rv : GoInterface) ∗
      mvcc.isReadView rv E.s E.γ) ∗
    "HWB" ∷ srvWTStock E N ∗
    "#Hsmall" ∷ storeSmall E.γ ∗
    "#HNR" ∷ □ (|==> idCred ρ.ids 1) ∗
    "#Hcv" ∷ clusterVersionOk s ∗
    "%Hbound" ∷ ⌜threadBound GF ≤ 2 ^ 31⌝ ∗
    "Hua" ∷ (∃ ua : GoInterface, srvUberApplyAddr s ↦ ua ∗ apply.applierFor ua E ∗
      apply.applyKV E ua x₀) ∗
    -- (linkv-txn stage B1, 2026-10-20) the member's entry of the registries' map, for `start`
    "Hwtok" ∷ idWaitTok ρ.ids ∗
    -- (2026-10-26, D22 J1a) what the snapshot path takes of the construction (`SnapRO.lean`)
    "Hsnapb" ∷ srvSnapBoot s ci E γr)

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
  iprop("Hsnap" ∷ (∃ ms : Loc, rnRaftStorageAddr (srvRAddr s) ↦□ ms ∗ rnSnapOnce ms γn.γs ai₀ at₀))

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
    (h : envAgree E E') : srvC ρ E ai₀ c₀ x₀ = srvC ρ E' ai₀ c₀ x₀ := by
  obtain ⟨hi, hc, hr⟩ := h
  have hres : resultΨ (GF := GF) E = resultΨ E' := by
    funext ρ' rq F x
    unfold resultΨ resultIsW revMinted revTok mvcc.certOk
    rw [hi, hc, hr]
  funext L
  unfold srvC batchWaitOk entryWaitOk reqWaitR
  rw [hres]

end lemmas

end EtcdGrove
end Perennial
