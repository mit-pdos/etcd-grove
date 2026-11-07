/-
**The server's construction in either auth mode** (the auth plan's E2w, 2026-10-26;
`notes/decisions.md`, "E2w of the auth plan"). `NewServer.specM on` (E2k) took the KV invariant
`kvInv`, whose start chain has the auth layer off, beside a premise putting it on: its
precondition was unsatisfiable at `on = true` (`KVChainOff.lean`, E2p). Here are the mode-indexed
counterparts of what `NewServer`'s proof hands its KV invariant to, so the spec can take
`kvInvM on` (the mode-`on` invariant `kvInvOn`, E2q, at `on = true`) instead:

- `srvAuthSt0`: the auth state the mode-`on` KV model starts from, the store's latest at the
  server's start (`newAuthStore_boot`'s history `[bootState, bump bootState]`, E2e).
- `logShapeM`, `srvCM`, `srvErM`: the raft environment's committed-log clause (`srvC`) with the
  mode's shapes (`logShapeOn` admits the admitted admin requests); `clusterWorkloadOkM`, from
  `kvInvM` (`clusterWorkloadOkM_of`), and the raft wrapper's discharge (`rnEnvOk_of_clusterM`).
- `kvCertInvM`, `srvKVInvsM`, `srvReqBuiltM`, `srvBuiltG`: the built part's rows that hold the
  KV invariant or the certificates' invariant, with the mode's.
- `kvInvOn_alloc_boot`: the mode-`on` invariant allocated at the bootstrap log, as
  `kvInv_alloc_boot` allocates `kvInv`: `NewServer.specM true`'s precondition is satisfiable.

**Additive.** At `on = false` every one of them is today's by definition (`srvCM_false`,
`srvErM_false`, `srvBuiltG_false`, ...: the match reduces), so `NewServer.spec` and every mode-off
statement keep their text; nothing here changes `kvInv`, `srvBuilt`, `srvReqBuilt`, `srvKVInvs`,
`srvC` or `srvEr`. The server's run in the mode `on` (`start`, the apply thread over
`srvKVInvsOn`, the proposers' updates at commit) is not here: it consumes `srvBuiltG true`.

Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ServerOnDefs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ImageOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVApplyOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVModelM
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BuildGap
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BuildAlloc
public import Proof.go_etcd_io.etcd.server.v3.auth.Boot
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.BaseAuth
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.StoreLatest
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthReqDerive
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.ApplyFnKVL
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.ApplyFnAdminL

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

/-- **The server's `E.C` in the auth mode `on`** (`srvC` with the mode's shapes). -/
def srvCM (on : Bool) (ρ : ReqNames) (E : apply.AEnv GF) (ai₀ c₀ : w64) (x₀ : apply.ApplyKV)
    (L : List EntryModel) : IProp GF :=
  iprop(⌜srvIdxOk ai₀ L ∧ logShapeM on ρ.kv.lm L⌝ ∗ batchWaitOk ρ E L ∗ srvRLogLb ρ.raft L)

instance srvCM_persistent (on : Bool) (ρ : ReqNames) (E : apply.AEnv GF) (ai₀ c₀ : w64)
    (x₀ : apply.ApplyKV) (L : List EntryModel) :
    Persistent (srvCM (GF := GF) on ρ E ai₀ c₀ x₀ L) := by
  unfold srvCM; infer_instance

theorem srvCM_false (ρ : ReqNames) (E : apply.AEnv GF) (ai₀ c₀ : w64) (x₀ : apply.ApplyKV) :
    srvCM (GF := GF) false ρ E ai₀ c₀ x₀ = srvC ρ E ai₀ c₀ x₀ := rfl

/-- **The server's raft environment in the auth mode `on`** (`srvEr` with `srvCM`). -/
def srvErM (on : Bool) (ρ : ReqNames) (E : apply.AEnv GF) (ai₀ c₀ : w64) (x₀ : apply.ApplyKV)
    (id : w64) (S ST : IProp GF) : RNEnv GF :=
  ⟨srvCM on ρ E ai₀ c₀ x₀, fun m => iprop(srvMsgNet ρ.raft.raft id m ∗ srvMsgNoSnap m),
    iprop(True), ρ.rd, srvRQ ρ.rd.raft, S, ST⟩

theorem srvErM_false (ρ : ReqNames) (E : apply.AEnv GF) (ai₀ c₀ : w64) (x₀ : apply.ApplyKV)
    (id : w64) (S ST : IProp GF) :
    srvErM (GF := GF) false ρ E ai₀ c₀ x₀ id S ST = srvEr ρ E ai₀ c₀ x₀ id S ST := rfl

/-- **The cluster's workload in the auth mode `on`** (`clusterWorkloadOk` with the mode's
shapes). -/
def clusterWorkloadOkM (on : Bool) (ρ : ReqNames) (E : apply.AEnv GF) : IProp GF :=
  iprop(□ ∀ L : List EntryModel, srvRLogLb ρ.raft L ={⊤}=∗ ⌜logShapeM on ρ.kv.lm L⌝ ∗ batchWaitOk ρ E L)

instance clusterWorkloadOkM_persistent (on : Bool) (ρ : ReqNames) (E : apply.AEnv GF) :
    Persistent (clusterWorkloadOkM (GF := GF) on ρ E) := by
  unfold clusterWorkloadOkM; infer_instance

/-- **`isServerReq`'s fields but `w` and `done`, in the auth mode `on`** (`srvReqBuilt` with the
mode's KV invariant, `kvInvM on`, from `srvAuthSt0`). -/
def srvReqBuiltM (on : Bool) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (v : ReqFields) :
    IProp GF :=
  iprop(structFieldRef EtcdServer go!"reqIDGen" s ↦□ v.gen ∗ idGen ρ.ids v.gen (srvFloorFact E) ∗
    srvRaftNode s ρ.raft ∗
    srvCfgFieldAddr s go!"MaxRequestBytes" ↦□ v.maxReq ∗
    srvCfgFieldAddr s go!"ServerFeatureGate" ↦□ v.fg ∗ isFeatureGate v.fg ∗
    srvCfgFieldAddr s go!"ClientCertAuthEnabled" ↦□ v.cca ∗
    srvCfgFieldAddr s go!"ElectionTicks" ↦□ v.electionTicks ∗
    srvCfgFieldAddr s go!"TickMs" ↦□ v.tickMs ∗
    structFieldRef EtcdServer go!"authStore" s ↦□ v.auth ∗ isReqAuth v.auth E.RD ∗
    structFieldRef EtcdServer go!"memberID" s ↦□ v.memberID ∗
    srvAtomicU64 (structFieldRef EtcdServer go!"lead" s) ∗
    structFieldRef EtcdServer go!"cluster" s ↦□ v.cluster ∗
    structFieldRef raftNodeConfig go!"transport"
      (structFieldRef raftNode go!"raftNodeConfig" (structFieldRef EtcdServer go!"r" s)) ↦□ v.tr ∗
    srvPeersOk v.cluster v.cid v.tr ∗
    srvMintInv ρ ∗ kvInvM on ρ.raft ρ.kv srvAuthSt0 ∗ ⌜structFieldRef EtcdServer go!"Cfg" s ≠ null ∧
      v3rpc.etcdMaxRequestBytesOk (uint.nat v.maxReq)⌝)

instance srvReqBuiltM_persistent (on : Bool) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (v : ReqFields) : Persistent (srvReqBuiltM (GF := GF) on s E ρ v) := by
  unfold srvReqBuiltM; infer_instance

theorem srvReqBuiltM_false (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (v : ReqFields) :
    srvReqBuiltM (GF := GF) false s E ρ v = srvReqBuilt s E ρ v := rfl

/-- **`applyBuiltNA` in the auth mode `on`** (the auth plan's E3c): the apply thread's auth
resource at the store's start state (`srvAuthApplyResB` at `srvAuthSt0`, the latest state of the
store's history `[bootState, bump bootState]`), what ties the apply thread's auth state to the
model's from the start (`applyBuiltOn`); and (C1's A1) the rights to issue tokens at the
consistent index (`srvTokRights`). -/
def applyBuiltNAOn (s : Loc) (γ : ApplyNames) (ci : Loc) (b : GoInterface) (E : apply.AEnv GF)
    (γr : ReadNames) (ai₀ c₀ : w64) (x₀ : apply.ApplyKV) : IProp GF :=
  iprop(∃ (st₀ : ApplyState) (a t : w64) (f : Bool),
    applyThread γ st₀ ∗ ⌜loopOk γ st₀ ai₀ ∧ c₀ = ciEff γ st₀.k⌝ ∗ applyBackend γ ci b ∗
    ciApplying ci a t ∗ srvLgReader s ∗ srvBemuReaderAt s E.γbe ∗ mvcc.api.mvccReaders E.γ 1 ∗
    srvBeOwn s E ∗ revAuth E x₀.log ∗ srvAuthApplyResB s E srvAuthSt0 ∗
    -- (2026-11-04, the lease-expiry plan's step 2) the lessor's range deleter (`mvcc.New`'s; the
    -- merge of `lean`, 2026-11-06: `lease.rdAt` restated over the API's deleter)
    (∃ rd : GoFunc, lease.rdOwn (mvcc.api.mvccLeases E.γ) rd ∗ mvcc.api.mvccDeleter rd E.γ) ∗
    srvAppliedOwn γr ai₀ ∗ appliedLogAt γr ai₀ x₀.log ∗ kvRun γr ai₀ c₀ [] x₀ ∗ srvRest E γr [] ∗
    srvApRes s γr [] ∗ srvForceSnapAddr s ↦ f ∗ srvTokRights E (ciEff γ st₀.k))

/-- **`applyBuiltNA` in the auth mode `on`**: `applyBuiltNA` at `on = false` (by definition),
`applyBuiltNAOn` at `on = true`. -/
def applyBuiltNAM (on : Bool) (s : Loc) (γ : ApplyNames) (ci : Loc) (b : GoInterface)
    (E : apply.AEnv GF) (γr : ReadNames) (ai₀ c₀ : w64) (x₀ : apply.ApplyKV) : IProp GF :=
  match on with
  | false => applyBuiltNA s γ ci b E γr ai₀ c₀ x₀
  | true => applyBuiltNAOn s γ ci b E γr ai₀ c₀ x₀

/-- **The built part's uber-applier row in the auth mode `on`** (E3k): `srvBuilt`'s at `false`
(by definition), with the base applier's auth layer (`srvUberBase`) at `true`. -/
def srvUberRowM (on : Bool) (s : Loc) (E : apply.AEnv GF) (x₀ : apply.ApplyKV) : IProp GF :=
  match on with
  | false => iprop(∃ ua : GoInterface, srvUberApplyAddr s ↦ ua ∗ apply.applierFor ua E ∗
      apply.applyKV E ua x₀)
  | true => iprop(∃ ua : GoInterface, srvUberApplyAddr s ↦ ua ∗ srvUberBase s ua E ∗
      apply.applierFor ua E ∗ apply.applyKV E ua x₀)

/-- **The built part in the auth mode `on`** (`srvBuilt` with `srvReqBuiltM`, `srvKVInvsM` and
`srvCM`; the other rows `srvBuilt`'s). -/
def srvBuiltG (on : Bool) (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (Er : RNEnv GF) (γn : RNNames)
    (b : GoInterface) (ai₀ c₀ : w64) (x₀ : apply.ApplyKV) (N : Nat) : IProp GF :=
  iprop("#Hci" ∷ isServerCI s γ ci ∗
    "#Hfb" ∷ (∃ v : SrvFields, srvFieldsBuiltNA s γ ci TM E v) ∗
    "#Hreqb" ∷ (∃ v : ReqFields, srvReqBuiltM on s E ρ v) ∗
    "#Hrdb" ∷ (∃ v : ReadFields, srvReadBuiltNK s E v) ∗
    "#Hrunb" ∷ (∃ v : RunFields, srvRunBuilt s v) ∗
    -- (M2, S4) the compactor's run, once (`start` spends it)
    "Hcrun" ∷ (∃ c : GoInterface, srvCompactorAddr s ↦□ c ∗ compactorRun s E c) ∗
    "#Hsab" ∷ srvApplyAllBuilt s γr ∗
    "#Hai" ∷ srvAppliedInvM on s E γr ∗
    "#Hkvi" ∷ srvKVInvsM on s E γr ∗
    "#Hti" ∷ inv srvN (∃ t : w64, sync.atomic.ownUint64 (srvTermAddr s) (DFrac.own 1) t) ∗
    "#Hci'" ∷ srvCommittedInv s γr ∗
    "#Hrn" ∷ isRaftNode Er γn (srvRAddr s) ∗
    "%HEr" ∷ ⌜Er.C = srvCM on ρ E ai₀ c₀ x₀ ∧ Er.γr = γr ∧
      (uint.Z c₀ ≤ uint.Z ai₀ ∧ γn.pre = [] ∧ ai₀ = W64 0)⌝ ∗
    -- (2026-10-30, the repair) the apply side's half of the node's running token
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
    -- (J8b, 2026-11-01) the server's member id is the raft node's (`srvBuilt`'s)
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
    "Hscu" ∷ (∃ n : w64, srvSnapCatchUpAddr s ↦ n) ∗
    "Hwg" ∷ srvWgAddr s ↦ (zero_val sync.WaitGroup) ∗
    "HwgMu" ∷ srvWgMuAddr s ↦ (zero_val sync.RWMutex) ∗
    "Hcomm" ∷ (∃ c : w64, srvCommittedOwn γr c) ∗
    "Hnot" ∷ (∃ x : Loc × NeedNames, ghostVar γr.notifier 1 x) ∗
    "Happ" ∷ applyBuiltNAM on s γ ci b E γr ai₀ c₀ x₀ ∗
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
    "Hua" ∷ srvUberRowM on s E x₀ ∗
    "Hwtok" ∷ idWaitTok ρ.ids ∗
    -- (2026-10-26, D22 J1a) what the snapshot path takes of the construction (`SnapRO.lean`)
    "Hsnapb" ∷ srvSnapBoot s ci E γr γ)

theorem srvBuiltG_false (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (Er : RNEnv GF) (γn : RNNames)
    (b : GoInterface) (ai₀ c₀ : w64) (x₀ : apply.ApplyKV) (N : Nat) :
    srvBuiltG (GF := GF) false s γ ci TM E ρ γr Er γn b ai₀ c₀ x₀ N =
      srvBuilt s γ ci TM E ρ γr Er γn b ai₀ c₀ x₀ N := rfl

end defs

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **`applyBuiltNAM` from the mode-`on` row** (E3c): the mode-`on` row is the mode-off one with
the auth resource at its latest state, which the mode-off row forgets (`srvAuthApplyResAt_of_B`, `srvAuthApplyRes_of_At`). -/
theorem srvUberRowM_of_On (on : Bool) (s : Loc) (E : apply.AEnv GF) (x₀ : apply.ApplyKV) :
    (∃ ua : GoInterface, srvUberApplyAddr s ↦ ua ∗ srvUberBase s ua E ∗ apply.applierFor ua E ∗
      apply.applyKV E ua x₀) ⊢ srvUberRowM (GF := GF) on s E x₀ := by
  cases on
  · unfold srvUberRowM
    iintro ⟨%ua, Hua, -, #Hfor, Hakv⟩
    iexists ua
    iframe Hua Hfor Hakv
  · unfold srvUberRowM
    iintro H; iexact H

theorem applyBuiltNAM_of_On (on : Bool) (s : Loc) (γ : ApplyNames) (ci : Loc) (b : GoInterface)
    (E : apply.AEnv GF) (γr : ReadNames) (ai₀ c₀ : w64) (x₀ : apply.ApplyKV) :
    applyBuiltNAOn (GF := GF) s γ ci b E γr ai₀ c₀ x₀ ⊢ applyBuiltNAM on s γ ci b E γr ai₀ c₀ x₀ := by
  cases on
  · unfold applyBuiltNAM applyBuiltNAOn applyBuiltNA
    iintro ⟨%st₀, %a, %t, %f, Hth, %Hok, Hbe, Hca, Hlg, Hbm, Hrdk, Hbo, Hra, Har, Hrdat, Hao, Hal, Hkr, Hrs, Hap, Hfs, -⟩
    iexists st₀, a, t, f
    iframe Hth Hbe Hca Hlg Hbm Hrdk Hbo Hra Hrdat Hao Hal Hkr Hrs Hap Hfs
    isplitr
    · ipureintro; exact Hok
    iapply srvAuthApplyRes_of_At
    iapply srvAuthApplyResAt_of_B $$ Har
  · unfold applyBuiltNAM
    iintro H; iexact H

end lemmas

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The indices' invariants at index `0`, the applied index's in the auth mode `on`**
(`srvIndices_alloc` with `srvAppliedInvM on`, E3k): the start log is the mode's model of the empty
log either way (`kvModelM on γk [] = γk.log0`), so the allocation is `srvIndices_alloc`'s. -/
theorem srvIndices_allocM (on : Bool) (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) (Ec : CoPset)
    (hai : γr.raft.ai0 = W64 0) :
    ⊢ sync.atomic.ownUint64 (srvAppliedIndexAddr s) (DFrac.own 1) (W64 0) -∗
      sync.atomic.ownUint64 (srvCommittedIndexAddr s) (DFrac.own 1) (W64 0) -∗
      sync.atomic.ownUint64 (srvTermAddr s) (DFrac.own 1) (W64 0) -∗
      monoNatAuthOwn γr.applied 1 0 -∗ monoNatAuthOwn γr.committed 1 0 -∗
      ghostMapAuth γr.logs 1 (∅ : GMap w64 mvcc.Log) -∗ ghostVar γr.pend 1 false -∗
      srvApi.kvLogLb E.γs γr.kv.log0 -∗ srvRLogLb γr.raft [] -∗ appliedPubM on E γr (W64 0) ={Ec}=∗
      srvAppliedInvM on s E γr ∗ srvAppliedOwn γr (W64 0) ∗ appliedLogAt γr (W64 0) γr.kv.log0 ∗
      srvCommittedInv s γr ∗ srvCommittedOwn γr (W64 0) ∗
      inv srvN (∃ t : w64, sync.atomic.ownUint64 (srvTermAddr s) (DFrac.own 1) t) := by
  iintro Hai Hci Hti Hap Hcm Hlogs Hpend #Hcert #HL #Hpub0
  have h0 : uint.nat (W64 0) = 0 := rfl
  icases buildMonoNatHalves γr.applied 0 $$ Hap with ⟨Hap1, Hap2⟩
  icases buildMonoNatHalves γr.committed 0 $$ Hcm with ⟨Hcm1, Hcm2⟩
  icases buildGhostVarHalves γr.pend false $$ Hpend with ⟨Hp1, Hp2⟩
  imod ghost_map_insert_persist (W64 0) γr.kv.log0 (GMap.lookup_empty _) $$ Hlogs with ⟨Hlogs, #Hlog0⟩
  imod inv_alloc srvN Ec (iprop(∃ t : w64,
      sync.atomic.ownUint64 (srvTermAddr s) (DFrac.own 1) t)) $$ [Hti] with #Hterm
  · inext; iexists W64 0; iexact Hti
  imod inv_alloc srvN Ec (iprop(∃ v : w64,
      sync.atomic.ownUint64 (srvCommittedIndexAddr s) (DFrac.own 1) v ∗
      monoNatAuthOwn γr.committed (1 : Qp).half (uint.nat v) ∗
      (∃ L : List EntryModel, srvRLogLb γr.raft L ∗ ⌜uint.Z v ≤ uint.Z γr.raft.ai0 + L.length⌝)))
    $$ [Hci Hcm1] with #Hcinv
  · inext
    iexists W64 0
    rw [h0]
    iframe Hci Hcm1
    iexists []
    iframe HL
    ipureintro; rw [hai]; simp
  imod inv_alloc srvN Ec (srvAppliedBodyM on s E γr)
    $$ [Hai Hap1 Hlogs Hp1] with #Hainv
  · inext
    iunfold srvAppliedBodyM
    iexists W64 0, W64 0, γr.kv.log0, (∅ : GMap w64 mvcc.Log).insert (W64 0) γr.kv.log0, false
    rw [h0]
    iframe Hai Hap1 Hlogs Hp1 Hcert
    isplitr
    · ipureintro
      refine ⟨Int.le_refl _, ?_⟩
      constructor
      · intro k L' hk
        rw [GMap.lookup_insert_Some] at hk
        rcases hk with ⟨rfl, -⟩ | ⟨-, hk⟩
        · left; exact Int.le_refl _
        · simp at hk
      · intro k k' L1 L2 h1 h2 _
        rw [GMap.lookup_insert_Some] at h1 h2
        rcases h1 with ⟨-, rfl⟩ | ⟨-, h1⟩
        · rcases h2 with ⟨-, rfl⟩ | ⟨-, h2⟩
          · exact List.prefix_refl _
          · simp at h2
        · simp at h1
    isplitr
    · iunfold appliedLogAt; iexact Hlog0
    iapply (kvLogsPubM_iff on E γr _ _).2
    iframe Hpub0
    iunfold kvLogsOkM
    iexists []
    iframe HL
    ipureintro
    intro k L' hk
    rw [GMap.lookup_insert_Some] at hk
    rcases hk with ⟨rfl, rfl⟩ | ⟨-, hk⟩
    · refine ⟨[], List.prefix_refl _, ?_, by cases on <;> rfl⟩
      rw [hai]; simp
    · simp at hk
  imodintro
  unfold srvAppliedInvM srvCommittedInv srvAppliedOwn srvCommittedOwn
  iframe Hainv Hcinv Hterm
  rw [h0]
  iframe Hap2 Hp2 Hcm2
  iunfold appliedLogAt; iexact Hlog0


open Iris.ProofMode in

/-- `srvCM` does not read the environment's names but through `envAgree` (`srvC_agree`'s). -/
theorem srvCM_agree (on : Bool) (ρ : ReqNames) (E E' : apply.AEnv GF) (ai₀ c₀ : w64)
    (x₀ : apply.ApplyKV) (_h : envAgree E E') :
    srvCM on ρ E ai₀ c₀ x₀ = srvCM on ρ E' ai₀ c₀ x₀ := by
  -- (the lease-grant plan's 2.6) the contract reads no name of `E` (`reqWaitNone`)
  rfl

/-- **The claims give a batch's ids** (`batchWaitOk_of_work`, from the conf changes' ids alone:
what both modes' shapes give, `logShapeM_cc`). -/
theorem batchWaitOk_of_claims (ρ : ReqNames) (E : apply.AEnv GF) (L : List EntryModel)
    (hcc : ∀ m ∈ L, m.typ ≠ W32 0 → ccIdOf m.data = W64 0)
    (hcl : ccLogOk ρ.raft.raft L)
    (ha : attrLogOk ρ.raft.raft.cfg L) :
    ⊢ ([∗list] m ∈ L, entryClaim ρ.ids m) -∗ idNoZero ρ.ids -∗ srvRLogLb ρ.raft L -∗
      batchWaitOk ρ E L := by
  iintro #Hcl #HNZ #HL
  iunfold batchWaitOk
  iintro !> %m %hm
  obtain ⟨n, hn⟩ := List.getElem?_of_mem hm
  ihave #Hc := (BigSepL.bigSepL_lookup (Φ := fun _ m => entryClaim (GF := GF) ρ.ids m) hn) $$ Hcl
  unfold entryWaitOk
  split
  · rename_i ht
    isplitr
    · iintro %rq %id %hrq
      obtain ⟨hd, hdec, hid⟩ := hrq
      iunfold entryClaim at Hc
      icases Hc with (%hc | ⟨%rq', %id', %γf, %k, %hrq', #Hcl', #Hreg⟩)
      · exfalso; rcases hc with hc | hc
        · exact hc ht
        · exact hd hc
      · obtain ⟨hdec', hid'⟩ := hrq'
        rw [hdec] at hdec'
        cases hdec'
        rw [hid] at hid'
        cases hid'
        iexists γf, k
        iframe Hcl' Hreg
    · iexists L
      iframe HL
      ipureintro; exact ⟨hm, ha m hm⟩
  · rename_i ht
    have h0 := hcc m hm ht
    rw [h0]
    isplitr
    rotate_left
    · ipureintro; exact hcl m hm ht
    iunfold reqWaitNone
    iintro !> %d %rq %γf %F #Hc0 - -
    ihave #Hc0a := idClaimAny_of ρ.ids (W64 0) d γf $$ Hc0
    iapply idClaim_noZero ρ.ids d γf $$ HNZ Hc0a

/-- `srv_entry_transfer` for a committed log `A` with no empty `ConfChangeV2` (`srv_committed_noV2`):
`P` need not hold of one. -/
private theorem srv_entry_transfer_nv (ai₀ : w64) (A L : List EntryModel) (P : EntryModel → Prop)
    (hP : ∀ m m', m.toLE = m'.toLE → P m' → P m)
    (hfill : ∀ m : EntryModel, m.typ = W32 0 → m.data = [] → P m)
    (hA : srvIdxOkW ai₀ A) (h : opsOf (A.map EntryModel.toLE) <+: L.map EntryModel.toLE)
    (hL : ∀ m ∈ L, P m) (hnv : ∀ m ∈ A, ¬ (m.typ = W32 2 ∧ m.data = [])) :
    ∀ m ∈ A, P m := by
  have := srv_entry_transfer ai₀ A L (fun m => ¬ (m.typ = W32 2 ∧ m.data = []) → P m)
    (fun m m' he h' hn => by
      have h1 := congrArg LogEntry.type he
      have h2 := congrArg LogEntry.data he
      simp only [EntryModel.toLE] at h1 h2
      exact hP m m' he (h' (by rw [← h1, ← h2]; exact hn)))
    (fun m ht hd _ => hfill m ht hd) (fun m ht hd hn => absurd ⟨ht, hd⟩ hn) hA h
    (fun m hm _ => hL m hm)
  exact fun m hm => this m hm (hnv m hm)

/-- **The workload clause in the mode `on`** (`clusterWorkloadOk_of`'s, from `kvInvOn`). -/
theorem clusterWorkloadOkOn_of (ρ : ReqNames) (E : apply.AEnv GF) (st₀ : auth.AuthState) :
    kvInvOn (GF := GF) ρ.raft ρ.kv st₀ ∗ srvRaftLogInv ρ.raft ∗ idNoZero ρ.ids ⊢
      clusterWorkloadOkM true ρ E := by
  iintro ⟨#Hkv, #Hr, #HNZ⟩
  iunfold clusterWorkloadOkM
  iintro !> %L #HL
  -- (2026-10-30, the repair) no empty `ConfChangeV2` committed (`srv_committed_noV2`)
  ihave #HLc : isCommittedLogLb ρ.raft.raft.cl (srvLE ρ.raft L) $$ []
  · iunfold srvRLogLb at HL; icases HL with ⟨#H, -⟩; iexact H
  imod (srv_committed_noV2 ρ.raft (srvLE ρ.raft L) ⊤ CoPset.subseteq_top CoPset.subseteq_top)
    $$ [] with %Hv2
  · iframe Hr HLc
  have hnv : ∀ m ∈ L, ¬ (m.typ = W32 2 ∧ m.data = []) := by
    rintro m hm ⟨ht, hd⟩
    apply Hv2 m.toLE (by unfold srvLE; exact List.mem_map_of_mem (List.mem_append_right _ hm))
    exact ⟨hd, ht⟩
  iunfold kvInvOn at Hkv
  iinv Hkv with >Hi Hclose
  icases Hi with ⟨%L', HL', Hσ, Hh, %Hok, #Hw⟩
  imod srvRLog_lb ρ.raft (⊤ \ ↑kvN) (mask_ndot_ne' nroot "raft_commit" "server_kv" (by decide))
    L' L $$ Hr HL' HL with ⟨HL', %Hp⟩
  ihave %HLi := srvRLogLb_idx ρ.raft L $$ HL
  imod Hclose $$ [HL' Hσ Hh] with -
  · inext; iexists L'; iframe HL' Hσ Hh Hw; ipureintro; exact Hok
  iunfold kvWorkOn at Hw
  icases Hw with ⟨%Hsh, #Hcl⟩
  obtain ⟨Hsh, Hccl, -, -, Hatt⟩ := Hsh
  -- (2026-10-27) the committed log's entries are the server's log's or fillers
  have HshL : logShapeOn L := srv_entry_transfer_nv _ L L' entryShapeOn
    (fun m m' he h => by
      have h1 := congrArg LogEntry.type he
      have h2 := congrArg LogEntry.data he
      simp only [EntryModel.toLE] at h1 h2
      unfold entryShapeOn at h ⊢; rw [h1, h2]; exact h)
    (fun m ht hd => ⟨fun _ => .inl hd, fun h => absurd ht h⟩) HLi Hp.2.2 Hsh hnv
  have HcclL : ccLogOk ρ.raft.raft L := srv_entry_transfer_nv _ L L'
    (fun m => m.typ ≠ W32 0 → ccPolOk ρ.raft.raft m.data)
    (fun m m' he h => by
      have h1 := congrArg LogEntry.type he
      have h2 := congrArg LogEntry.data he
      simp only [EntryModel.toLE] at h1 h2
      rw [h1, h2]; exact h)
    (fun m ht _ h => absurd ht h) HLi Hp.2.2 Hccl hnv
  -- (2026-11-02, the cluster-rows stage) the attribute requests' members: the fillers ask nothing
  have HatL : attrLogOk ρ.raft.raft.cfg L := srv_entry_transfer_nv _ L L' (attrEntryOk ρ.raft.raft.cfg)
    (fun m m' he h => by
      have h1 := congrArg LogEntry.type he
      have h2 := congrArg LogEntry.data he
      simp only [EntryModel.toLE] at h1 h2
      unfold attrEntryOk at h ⊢; rw [h1, h2]; exact h)
    (fun m _ hd => attrEntryOk_empty _ m hd) HLi Hp.2.2 Hatt hnv
  ihave #HclL := entryClaims_transfer ρ.ids _ L L' HLi Hp.2.2 $$ Hcl
  imodintro
  isplitr
  · ipureintro; exact HshL
  iapply batchWaitOk_of_claims ρ E L (logShapeM_cc true ρ.kv.lm L HshL) HcclL HatL $$ HclL HNZ HL

/-- **The workload clause in the auth mode `on`**, from the mode's KV invariant. -/
theorem clusterWorkloadOkM_of (on : Bool) (ρ : ReqNames) (E : apply.AEnv GF) :
    kvInvM (GF := GF) on ρ.raft ρ.kv srvAuthSt0 ∗ srvRaftLogInv ρ.raft ∗ idNoZero ρ.ids ⊢
      clusterWorkloadOkM on ρ E := by
  cases on
  · exact clusterWorkloadOk_of ρ E
  · exact clusterWorkloadOkOn_of ρ E srvAuthSt0

/-- **The server's raft environment meets the wrapper's discharge in the mode `on`**
(`rnEnvOk_of_cluster`'s, from `kvInvOn`). -/
theorem rnEnvOk_of_clusterOn (ρ : ReqNames) (E : apply.AEnv GF) (ai₀ c₀ : w64)
    (x₀ : apply.ApplyKV) (γw : RNNames) (st₀ : auth.AuthState)
    (hraft : γw.node = ρ.raft.raft) (hpre : γw.pre = ρ.raft.pre)
    (hai : uint.Z ρ.raft.ai0 = γw.pre.length) (hai0 : ρ.raft.ai0 = ai₀)
    -- (2026-10-30, the repair) the cluster at the server's rule (until then, in a dynamic
    -- cluster, its decoder; and the storage's cap)
    (hdec : γw.node.rule = srvRule ρ.rd.kv.c0 γw.node.boot)
    (id : w64) (S ST : IProp GF) (hid : γw.id = id) :
    kvInvOn (GF := GF) ρ.raft ρ.kv st₀ ∗ srvRaftLogInv ρ.raft ∗ clusterWorkloadOkM true ρ E ⊢
      rnEnvOk (srvErM true ρ E ai₀ c₀ x₀ id S ST) γw := by
  iintro ⟨#Hkv, #Hr, #Hwl⟩
  unfold rnEnvOk srvErM
  simp only
  isplitr
  · ipureintro; trivial
  isplitr
  · ipureintro; exact ⟨hraft.symm, hpre.symm, hai⟩
  isplitr
  · ipureintro; exact hdec
  isplitr
  · iexact Hr
  isplitr
  · iintro !> %m %st ⟨#Hmo, #Hrm, Hc, %Hns⟩
    rw [hraft, hid] at *
    isplitl [Hc]
    · iunfold srvMsgNet
      iexists st
      iframe Hmo Hrm Hc
    iunfold srvMsgNoSnap
    iexists st
    iframe Hmo
    ipureintro; exact Hns
  isplitr
  · iintro !> %L #HL %Hfit
    iunfold clusterWorkloadOkM at Hwl
    imod Hwl $$ HL with ⟨%Hent, #Hbw⟩
    ihave %HLi := srvRLogLb_idx ρ.raft L $$ HL
    imodintro
    imodintro
    unfold srvCM
    iframe Hbw HL
    ipureintro
    refine ⟨?_, Hent⟩
    rw [← hai0]
    exact srvIdxOk_of_W _ _ HLi Hfit
  isplitr
  · iintro !> %L #HC
    unfold srvCM
    icases HC with ⟨%Hc, -, #HL⟩
    iframe HL
    ipureintro
    rw [hai0]; exact Hc.1
  · ipureintro; trivial

/-- **The server's raft environment meets the wrapper's discharge in the auth mode `on`**. -/
theorem rnEnvOk_of_clusterM (on : Bool) (ρ : ReqNames) (E : apply.AEnv GF) (ai₀ c₀ : w64)
    (x₀ : apply.ApplyKV) (γw : RNNames)
    (hraft : γw.node = ρ.raft.raft) (hpre : γw.pre = ρ.raft.pre)
    (hai : uint.Z ρ.raft.ai0 = γw.pre.length) (hai0 : ρ.raft.ai0 = ai₀)
    -- (2026-10-30, the repair) the cluster at the server's rule (until then, in a dynamic
    -- cluster, its decoder; and the storage's cap)
    (hdec : γw.node.rule = srvRule ρ.rd.kv.c0 γw.node.boot)
    (id : w64) (S ST : IProp GF) (hid : γw.id = id) :
    kvInvM (GF := GF) on ρ.raft ρ.kv srvAuthSt0 ∗ srvRaftLogInv ρ.raft ∗
        clusterWorkloadOkM on ρ E ⊢
      rnEnvOk (srvErM on ρ E ai₀ c₀ x₀ id S ST) γw := by
  cases on
  · exact rnEnvOk_of_cluster ρ E ai₀ c₀ x₀ γw hraft hpre hai hai0 hdec id S ST hid
  · exact rnEnvOk_of_clusterOn ρ E ai₀ c₀ x₀ γw srvAuthSt0 hraft hpre hai hai0 hdec id S ST hid

/-- **The certificates' invariant in the mode `on`** (`kvCertInv_alloc`'s). -/
theorem kvCertInvOn_alloc (γs : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState)
    (E : CoPset) (h2 : 2 ≤ γk.log0.length) :
    ⊢ ghostMapAuth (GF := GF) γk.cok 1 (∅ : GMap w64 mvcc.Log) -∗
      ghostVar γk.hi (1 : Qp).half γk.log0.length -∗ srvRLogLb γs [] ={E}=∗
      kvCertInvOn γs γk st₀ := by
  iintro HC Hhi #HL
  iunfold kvCertInvOn
  iapply inv_alloc kvcN E
  inext
  iexists ∅, γk.log0.length, []
  iframe HC Hhi HL
  ipureintro
  refine ⟨?_, h2⟩
  intro n l hn
  simp at hn

/-- **The certificates' invariant in the auth mode `on`.** -/
theorem kvCertInvM_alloc (on : Bool) (γs : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState)
    (E : CoPset) (h2 : 2 ≤ γk.log0.length) :
    ⊢ ghostMapAuth (GF := GF) γk.cok 1 (∅ : GMap w64 mvcc.Log) -∗
      ghostVar γk.hi (1 : Qp).half γk.log0.length -∗ srvRLogLb γs [] ={E}=∗
      kvCertInvM on γs γk st₀ := by
  cases on
  · exact kvCertInv_alloc γs γk E h2
  · exact kvCertInvOn_alloc γs γk st₀ E h2

/-- A ghost variable's whole as its two halves. -/
private theorem onGhostVarHalves {A : Type} [Pos.Countable A] (γ : GName) (a : A) :
    ghostVar (GF := GF) γ 1 a ⊢ ghostVar γ (1 : Qp).half a ∗ ghostVar γ (1 : Qp).half a := by
  have h := ghostVar_split (GF := GF) γ a (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at h
  exact wand_entails h

/-- **The mode-`on` KV invariant at the bootstrap log** (`kvInv_alloc_boot`'s: a new cluster, the
server's start log empty, its start index `0`, the consistent index `0`, the base chain with auth
on, a non-empty start log): from the client's half of raft's committed log at `bootLog` and the
KV state's variable at the bootstrap log's mode-`on` model, the invariant and the client's
`etcdKV`. The bootstrap log's entries are conf changes: of the mode-`on` log and determinate
vacuously (both ask of normal entries only). So `NewServer.specM true`'s KV invariant is
satisfiable. (2026-11-05, H-rr1) The start log and the bootstrap log at most `2 ^ 61` long (`hsm`,
as `kvInv_alloc_boot`'s). -/
theorem kvInvOn_alloc_boot (γs : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState)
    (ps : List w64) (E : CoPset)
    (hpre : γs.pre = []) (hai : γs.ai0 = W64 0) (hboot : srvBootLogOk ps γs.raft.boot)
    (hcc : ∀ e ∈ γs.raft.boot, ccIdOf e.Data' = W64 0 ∧ ccBootOk γs.raft.cfg e.Data')
    (hc0 : γk.c0 = W64 0) (hch : γk.ch0 = apply.alarmChain true false false)
    (hlog : γk.log0 ≠ []) (hlk : mvcc.LogPutsLe etcdKeyMax γk.log0)
    (hao : γs.raft.authOn = true)
    (hsm : γk.log0.length ≤ 2 ^ 61 ∧ γs.raft.boot.length ≤ 2 ^ 61) :
    ⊢ srvRLog (GF := GF) γs (bootEntries γs.raft.boot) -∗
      ghostVar γk.st 1 (kvStateOf (kvModelOn γk st₀ (bootEntries γs.raft.boot))) -∗
      monoListAuthOwn γk.hist 1 [st₀] ={E}=∗
      kvInvOn γs γk st₀ ∗
        etcdKV γk (kvStateOf (kvModelOn γk st₀ (bootEntries γs.raft.boot))) ∗
        authHistView γk [st₀] := by
  generalize hbl : γs.raft.boot = bootLog at hboot hcc hsm ⊢
  iintro HL Hv Hh
  icases onGhostVarHalves γk.st _ $$ Hv with ⟨Hv1, Hv2⟩
  icases authHist_split γk [st₀] $$ Hh with ⟨Hhv, Hh⟩
  have hent : ∀ (n : Nat) (m : EntryModel), (bootEntries bootLog)[n]? = some m →
      uint.Z m.index = (n : Int) + 1 ∧ m.typ = W32 1 ∧ isConfChangeEncoding m.data ∧
        ccIdOf m.data = W64 0 := by
    obtain ⟨-, -, hk⟩ := hboot
    intro n m hm
    unfold bootEntries at hm
    rw [List.getElem?_map] at hm
    cases he : bootLog[n]? with
    | none => rw [he] at hm; simp at hm
    | some e =>
      rw [he] at hm
      simp only [Option.map_some, Option.some.injEq] at hm
      subst hm
      obtain ⟨-, hi, ht, ⟨cm, hd, -⟩⟩ := hk n e he
      refine ⟨hi, ht, ?_, (hcc e (List.mem_of_getElem? he)).1⟩
      unfold isConfChangeEncoding
      show (ccDecodeV1 e.Data').isSome = true
      rw [hd]; rfl
  have hty : ∀ m ∈ bootEntries bootLog, m.typ = W32 1 := by
    intro m hm
    obtain ⟨n, hn⟩ := List.getElem?_of_mem hm
    exact (hent n m hn).2.1
  have hok : plainLogOn (bootEntries bootLog) ∧
      detLogOn γk.c0 γk.ch0 (st₀, γk.log0) (bootEntries bootLog) ∧
      srvIdxOkW γs.ai0 (bootEntries bootLog) ∧
      uint.Z γk.c0 ≤ uint.Z γs.ai0 ∧
      γk.ch0 = apply.alarmChain true false false ∧ γk.log0 ≠ [] ∧ γs.raft.authOn = true ∧
      kvLogSmall γk (bootEntries bootLog) := by
    refine ⟨?_, ?_, ?_, ?_, hch, hlog, hao, hsm.1, by unfold bootEntries; simpa using hsm.2⟩
    · intro m hm h0
      rw [hty m hm] at h0
      exact absurd h0 (by decide)
    · intro i m hm h0
      rw [hty m (List.mem_of_getElem? hm)] at h0
      exact absurd h0 (by decide)
    · intro n m hm
      obtain ⟨hi, ht, hc, -⟩ := hent n m hm
      refine ⟨?_, Or.inr ⟨ht, hc⟩⟩
      rw [hai, hi]; word
    · rw [hc0, hai]; word
  have hshape : logShapeOn (bootEntries bootLog) := by
    intro m hm
    obtain ⟨n, hn⟩ := List.getElem?_of_mem hm
    obtain ⟨-, ht, -, hid⟩ := hent n m hn
    refine ⟨fun h0 => ?_, fun _ => hid⟩
    rw [ht] at h0; exact absurd h0 (by decide)
  have hccl : ccLogOk γs.raft (bootEntries bootLog) := by
    intro m hm _
    obtain ⟨n, hn⟩ := List.getElem?_of_mem hm
    obtain ⟨-, -, hk⟩ := hboot
    unfold bootEntries at hn
    rw [List.getElem?_map] at hn
    cases he : bootLog[n]? with
    | none => rw [he] at hn; simp at hn
    | some e =>
      rw [he] at hn
      simp only [Option.map_some, Option.some.injEq] at hn
      subst hn
      exact ccPolOk_of_boot _ _ (hcc e (List.mem_of_getElem? he)).2
  ihave #Hcl := entryClaims_conf (GF := GF) γk.ids (bootEntries bootLog) (fun m hm => by
    rw [hty m hm]; decide)
  iunfold kvInvOn
  imod inv_alloc kvN E (iprop(∃ L : List EntryModel,
      srvRLog γs L ∗ ghostVar γk.st (1 : Qp).half (kvStateOf (kvModelOn γk st₀ L)) ∗
      monoListAuthOwn γk.hist (1 : Qp).half (admStates γk st₀ L) ∗
      ⌜plainLogOn L ∧ detLogOn γk.c0 γk.ch0 (st₀, γk.log0) L ∧ srvIdxOkW γs.ai0 L ∧
        uint.Z γk.c0 ≤ uint.Z γs.ai0 ∧
        γk.ch0 = apply.alarmChain true false false ∧ γk.log0 ≠ [] ∧ γs.raft.authOn = true ∧
        kvLogSmall γk L⌝ ∗
        kvWorkOn γs.raft γk L))
    $$ [HL Hv1 Hh] with #Hinv
  · inext
    iexists bootEntries bootLog
    iframe Hv1
    rw [admStates_conf γk st₀ _ (fun m hm h0 => by rw [hty m hm] at h0; exact absurd h0 (by decide))]
    iframe Hh
    isplitl [HL]
    · iexact HL
    isplitr
    · ipureintro; exact hok
    iunfold kvWorkOn
    iframe Hcl
    ipureintro
    exact ⟨hshape, hccl, fun m hm => entryPutsOk_conf m (by rw [hty m hm]; decide), hlk,
      fun m hm => attrEntryOk_conf _ m (by rw [hty m hm]; decide)⟩
  imodintro
  iframe Hinv Hhv
  iunfold etcdKV; iexact Hv2

end lemmas

end EtcdGrove
end Perennial
