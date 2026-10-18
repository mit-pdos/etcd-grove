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
  ⟨srvC ρ E ai₀ c₀ x₀, fun _ => iprop(True), iprop(True), ρ.rd, srvRQ ρ.rd.raft⟩

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

/-- `srvFieldsBuilt` without the uber-applier (`srvUberApplyAddr`, `applierFor`: a KV row,
`srvBuildGap`). -/
def srvFieldsBuiltNA (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (v : SrvFields) : IProp GF :=
  iprop(srvLgAddr s ↦□ v.lg ∗ ⌜v.lg ≠ null⌝ ∗
      ⌜E.P = batchLockInv γ TM ∧ E.f = v.hook⌝ ∗ ⌜srvEnvOk s γ ci E⌝ ∗
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
    "Hfcr" ∷ (∃ n : Loc, srvFirstCommitAddr s ↦□ n ∗ notifyReader n) ∗
    "#Hkv" ∷ (∃ (kv : GoInterface) (rv : Loc), srvKVAddr s ↦□ kv ∗ txn.isKV kv E.s E.γ ∗
      E.s.[go_etcd_io.etcd.server.v3.storage.mvcc.store, go!"ReadView"] ↦□
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.mvcc.readView.ty)
          #rv : GoInterface) ∗
      mvcc.isReadView rv E.s E.γ) ∗
    "HWB" ∷ txn.storeWTs E.γ N ∗
    "#Hsmall" ∷ storeSmall E.γ ∗
    "#HNR" ∷ □ (|==> idCred ρ.ids 1) ∗
    "#Hcv" ∷ clusterVersionOk s ∗
    "%Hbound" ∷ ⌜threadBound GF ≤ 2 ^ 31⌝ ∗
    "Hua" ∷ (∃ ua : GoInterface, srvUberApplyAddr s ↦□ ua ∗ apply.applierFor ua E ∗
      apply.applyKV E ua x₀))

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
def srvBuildGap (s : Loc) (ai₀ at₀ : w64) : IProp GF :=
  iprop("Hsnap" ∷ (∃ ms : Loc, rnRaftStorageAddr (srvRAddr s) ↦□ ms ∗ rnSnapOnce ms ai₀ at₀))

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
theorem clusterWorkloadOk_agree (ρ : ReqNames) (E E' : apply.AEnv GF) (h : envAgree E E') :
    clusterWorkloadOk (GF := GF) ρ E = clusterWorkloadOk ρ E' := by
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
