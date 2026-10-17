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
* **The workload clause** `clusterWorkloadOk` (D13c: a premise of `NewServer.spec`): every
  committed log meets the apply premises (`entriesOk`) and its ids are claimed under this
  server's generator (`batchWaitOk`). For several members both are facts about the other members'
  requests (`issues/etcd-request-id-member-prefix.md`); discharging it for one server is unit N3.
* **The built part** `srvBuilt` and **the residual** `srvBuildGap`. The residual's rows: the KV
  rows (`txn.isKV`/`isReadView` of `srv.kv`, the uber-applier's `applierFor`/`applyKV`: true of
  `mvcc.New`'s watchable store since unit N4, `server_kv_watchable`, but given by no `NewServer`
  proof yet), the write budget `txn.storeWTs`, `storeSmall`, the raft storage's
  snapshot contract `rnSnapOnce`, the id budget, `ClusterVersion()`'s contract, the logic's thread
  bound.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvStart
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvNodeStart

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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

/-- The bootstrap log as the server's entries. -/
def bootEntries (bootLog : List EntryM) : List EntryModel := bootLog.map EntryModel.ofM

/-- **The server's raft environment** (`RNEnv`): `E.C` the server's (`srvC`), every message
admitted (the transport's contract, `rafthttp.Transport`, asks nothing of them), a tick's
resource raft's tick credit of the budget `bud`, the read names `ρ.rd`, raft's read
registrations. -/
def srvEr (ρ : ReqNames) (E : apply.AEnv GF) (ai₀ c₀ : w64) (x₀ : apply.ApplyKV)
    (bud : BudgetNames) : RNEnv GF :=
  ⟨srvC ρ E ai₀ c₀ x₀, fun _ => iprop(True), tickCred bud 1, ρ.rd, srvRQ ρ.rd.raft⟩

/-- **The read names, fresh** (the caller's allocation, `srvReadNamesFresh_alloc`): the applied
and committed indices' authorities at `0`, the read loop's notifier variable, the applied logs'
empty map, the pending flag `false`, the KV state's variable at the state of the bootstrap log's
model `σ` (its halves: the KV invariant's and the client's `etcdKV`), the certified length at the
start log's (`hi`). -/
def srvReadNamesFresh (γr : ReadNames) (σ : KVState) : IProp GF :=
  iprop(monoNatAuthOwn γr.applied 1 0 ∗ monoNatAuthOwn γr.committed 1 0 ∗
    (∃ x : Loc × NeedNames, ghostVar γr.notifier 1 x) ∗
    ghostMapAuth γr.logs 1 (∅ : GMap w64 mvcc.Log) ∗ ghostVar γr.pend 1 false ∗
    ghostVar γr.kv.st 1 σ ∗ ghostVar γr.kv.hi 1 γr.kv.log0.length)

/-! ## The workload clause (D13c) -/

/-- **The cluster's workload** (persistent; a premise of `NewServer.spec`): every committed log
`L` (after the server's start) meets the apply premises from `x₀` at the consistent index `c₀`
(`entriesOk`), and every entry's id is claimed under this server's generator (`batchWaitOk`):
what the raft contract's `E.C` asks beyond the KV invariant (`rnEnvOk_of_cluster`). -/
def clusterWorkloadOk (ρ : ReqNames) (E : apply.AEnv GF) (c₀ : w64) (x₀ : apply.ApplyKV) :
    IProp GF :=
  iprop(□ ∀ L : List EntryModel, srvRLogLb ρ.raft L -∗ ⌜entriesOk c₀ L x₀⌝ ∗ batchWaitOk ρ E L)

instance clusterWorkloadOk_persistent (ρ : ReqNames) (E : apply.AEnv GF) (c₀ : w64)
    (x₀ : apply.ApplyKV) : Persistent (clusterWorkloadOk (GF := GF) ρ E c₀ x₀) := by
  unfold clusterWorkloadOk; infer_instance

/-! ## The built part and the residual -/

/-- `srvFieldsBuilt` without the uber-applier (`srvUberApplyAddr`, `applierFor`: a KV row,
`srvBuildGap`). -/
def srvFieldsBuiltNA (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (v : SrvFields) : IProp GF :=
  iprop(srvLgAddr s ↦□ v.lg ∗ ⌜v.lg ≠ null⌝ ∗
      ⌜E.P = batchLockInv γ TM ∧ E.f = v.hook⌝ ∗
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
  iprop(srvLessorAddr s ↦□ v.lessor ∗ apply.isApplyLessor v.lessor E.s E.γ E.P E.f ∗
    srvAuthStoreAddr s ↦□ v.auth ∗ apply.isAuthStore v.auth E.γ E.P E.f E.RD E.authOn ∗
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
    ciApplying ci a t ∗ srvLgReader s ∗ srvBemuReader s ∗ revAuth E x₀.log ∗
    srvAppliedOwn γr ai₀ ∗ appliedLogAt γr ai₀ x₀.log ∗ kvRun γr ai₀ c₀ [] x₀ ∗
    srvForceSnapAddr s ↦ f)

/-- **The built part** (`NewServer.spec`'s postcondition, on success): `isServerBuilt` but the
rows of `srvBuildGap` (named as `isServerBuilt`'s; `#Hfb`, `#Hrdb`, `Happ` without their KV
parts). -/
def srvBuilt (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (Er : RNEnv GF) (γn : RNNames)
    (b : GoInterface) (ai₀ c₀ : w64) (x₀ : apply.ApplyKV) : IProp GF :=
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
    "%HEr" ∷ ⌜Er.C = srvC ρ E ai₀ c₀ x₀ ∧ Er.γr = γr⌝ ∗
    "%Hρrd" ∷ ⌜ρ.rd = γr⌝ ∗
    "Hloop" ∷ rnLoopTok γn [] ∗ "Happly" ∷ rnApplyTok γn [] ∗ "Hrdone" ∷ rnDoneTok γn (srvRAddr s) ∗
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
    "Hscu" ∷ (∃ n : w64, srvSnapCatchUpAddr s ↦ n) ∗
    "Hwg" ∷ srvWgAddr s ↦ (zero_val sync.WaitGroup) ∗
    "HwgMu" ∷ srvWgMuAddr s ↦ (zero_val sync.RWMutex) ∗
    "Hcomm" ∷ (∃ c : w64, srvCommittedOwn γr c) ∗
    "Hnot" ∷ (∃ x : Loc × NeedNames, ghostVar γr.notifier 1 x) ∗
    "Happ" ∷ applyBuiltNA s γ ci b E γr ai₀ c₀ x₀ ∗
    "Hlr" ∷ srvLgReader s ∗
    "Hlrl" ∷ srvLgReader s ∗
    "Hfcr" ∷ (∃ n : Loc, srvFirstCommitAddr s ↦□ n ∗ notifyReader n))

/-- **The residual** (see the file header): the rows of `isServerBuilt` no `NewServer` proof
gives -- the KV rows (the uber-applier's `applierFor` and its KV state `applyKV` at `x₀`,
`srv.kv` as `txn.isKV` with its read view: true of the watchable store since unit N4), `storeSmall`, the write budget,
the raft storage's snapshot contract, the id budget, `ClusterVersion()`'s contract, the logic's
thread bound. A premise of whoever composes `NewServer` with `start`. -/
def srvBuildGap (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ai₀ at₀ : w64)
    (x₀ : apply.ApplyKV) (N : Nat) : IProp GF :=
  iprop("Hua" ∷ (∃ ua : GoInterface, srvUberApplyAddr s ↦□ ua ∗ apply.applierFor ua E ∗
      apply.applyKV E ua x₀) ∗
    "#Hkv" ∷ (∃ (kv : GoInterface) (rv : Loc), srvKVAddr s ↦□ kv ∗ txn.isKV kv E.s E.γ ∗
      E.s.[go_etcd_io.etcd.server.v3.storage.mvcc.store, go!"ReadView"] ↦□
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.mvcc.readView.ty)
          #rv : GoInterface) ∗
      mvcc.isReadView rv E.s E.γ) ∗
    "#Hsmall" ∷ storeSmall E.γ ∗
    "HWB" ∷ txn.storeWTs E.γ N ∗
    "Hsnap" ∷ (∃ ms : Loc, rnRaftStorageAddr (srvRAddr s) ↦□ ms ∗ rnSnapOnce ms ai₀ at₀) ∗
    "#HNR" ∷ □ (|==> idCred ρ.ids 1) ∗
    "#Hcv" ∷ clusterVersionOk s ∗
    "%Hbound" ∷ ⌜threadBound GF ≤ 2 ^ 31⌝)

end defs

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem envAgree_symm {E E' : apply.AEnv GF} (h : envAgree E E') : envAgree E' E :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩

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

/-- The workload clause at agreeing environments. -/
theorem clusterWorkloadOk_agree (ρ : ReqNames) (E E' : apply.AEnv GF) (c₀ : w64)
    (x₀ : apply.ApplyKV) (h : envAgree E E') :
    clusterWorkloadOk (GF := GF) ρ E c₀ x₀ = clusterWorkloadOk ρ E' c₀ x₀ := by
  obtain ⟨hi, hc, hr⟩ := h
  have hres : resultΨ (GF := GF) E = resultΨ E' := by
    funext ρ' rq F x
    unfold resultΨ resultIsW revMinted revTok mvcc.certOk
    rw [hi, hc, hr]
  unfold clusterWorkloadOk batchWaitOk entryWaitOk reqWaitR
  rw [hres]

/-- The server's raft environment at agreeing environments. -/
theorem srvEr_agree (ρ : ReqNames) (E E' : apply.AEnv GF) (ai₀ c₀ : w64) (x₀ : apply.ApplyKV)
    (bud : BudgetNames) (h : envAgree E E') :
    srvEr ρ E ai₀ c₀ x₀ bud = srvEr ρ E' ai₀ c₀ x₀ bud := by
  unfold srvEr; rw [srvC_agree ρ E E' ai₀ c₀ x₀ h]

end lemmas

end EtcdGrove
end Perennial
