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

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVApplyOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BuildGap
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BuildAlloc
public import Proof.go_etcd_io.etcd.server.v3.auth.Boot
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.BaseAuth
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.StoreLatest

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

/-- **The auth state the mode-`on` KV model starts from**: the store's latest at the server's
start (`newAuthStore_boot`: the history `[bootState, bump bootState]`, the revision committed
once). -/
def srvAuthSt0 : auth.AuthState := auth.bump auth.bootState

section pure
variable [GooseExts]

/-- **The committed log's shapes in the auth mode `on`**: `logShape` off, `logShapeOn` on. -/
def logShapeM (on : Bool) (L : List EntryModel) : Prop :=
  match on with
  | false => logShape L
  | true => logShapeOn L

/-- The shapes of either mode give a conf change's id `0`. -/
theorem logShapeM_cc (on : Bool) (L : List EntryModel) (h : logShapeM on L) :
    ∀ m ∈ L, m.typ ≠ W32 0 → ccIdOf m.data = W64 0 := by
  cases on
  · exact fun m hm => (h m hm).2
  · exact fun m hm => (h m hm).2

theorem logShapeM_append (on : Bool) (A B : List EntryModel) (h : logShapeM on (A ++ B)) :
    logShapeM on A := by
  cases on
  · exact fun m hm => h m (List.mem_append_left _ hm)
  · exact fun m hm => h m (List.mem_append_left _ hm)

/-- **The KV model of the committed log `L` in the auth mode `on`**: `kvModel` off, the mode-`on`
model from the server's start state (`kvModelOn … srvAuthSt0`) on. -/
def kvModelM (on : Bool) (γk : KVNames) (L : List EntryModel) : mvcc.Log :=
  match on with
  | false => kvModel γk L
  | true => kvModelOn γk srvAuthSt0 L

theorem kvModelM_false (γk : KVNames) (L : List EntryModel) :
    kvModelM false γk L = kvModel γk L := rfl

theorem kvModelM_true (γk : KVNames) (L : List EntryModel) :
    kvModelM true γk L = kvModelOn γk srvAuthSt0 L := rfl

end pure

section appliedM
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The KV log `L` applied through the index `i` is the mode's KV model of a committed raft
log** (persistent; `kvLogAt` at `false`). -/
def kvLogAtM (on : Bool) (γr : ReadNames) (i : w64) (L : mvcc.Log) : IProp GF :=
  iprop(∃ A : List EntryModel, srvRLogLb γr.raft A ∗
    ⌜uint.Z i = uint.Z γr.raft.ai0 + A.length ∧ L = kvModelM on γr.kv A⌝)

instance kvLogAtM_persistent (on : Bool) (γr : ReadNames) (i : w64) (L : mvcc.Log) :
    Persistent (kvLogAtM (GF := GF) on γr i L) := by
  unfold kvLogAtM; infer_instance

theorem kvLogAtM_false (γr : ReadNames) (i : w64) (L : mvcc.Log) :
    kvLogAtM (GF := GF) false γr i L = kvLogAt γr i L := rfl

/-- **The applied logs are the mode's KV models of committed raft logs** (`kvLogsOk` at
`false`). -/
def kvLogsOkM (on : Bool) (γr : ReadNames) (M : GMap w64 mvcc.Log) : IProp GF :=
  iprop(∃ Lb : List EntryModel, srvRLogLb γr.raft Lb ∗
    ⌜∀ k L, M.lookup k = some L → ∃ A, A <+: Lb ∧
      uint.Z k = uint.Z γr.raft.ai0 + A.length ∧ L = kvModelM on γr.kv A⌝)

instance kvLogsOkM_persistent (on : Bool) (γr : ReadNames) (M : GMap w64 mvcc.Log) :
    Persistent (kvLogsOkM (GF := GF) on γr M) := by
  unfold kvLogsOkM; infer_instance

instance kvLogsOkM_timeless (on : Bool) (γr : ReadNames) (M : GMap w64 mvcc.Log) :
    Timeless (kvLogsOkM (GF := GF) on γr M) := by
  unfold kvLogsOkM; infer_instance

theorem kvLogsOkM_false (γr : ReadNames) (M : GMap w64 mvcc.Log) :
    kvLogsOkM (GF := GF) false γr M = kvLogsOk γr M := rfl

/-- **The applied index's invariant's body in the mode `on`** (`srvAppliedBody` at `false`): its
applied logs the mode's KV models (`kvLogsOkM`). -/
def srvAppliedBodyM (on : Bool) (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) : IProp GF :=
  iprop(∃ (v a : w64) (L : mvcc.Log) (M : GMap w64 mvcc.Log) (p : Bool),
    sync.atomic.ownUint64 (srvAppliedIndexAddr s) (DFrac.own 1) v ∗
    monoNatAuthOwn γr.applied (1 : Qp).half (uint.nat a) ∗
    ghostMapAuth γr.logs 1 M ∗ ghostVar γr.pend (1 : Qp).half p ∗
    ⌜uint.Z v ≤ uint.Z a ∧ appliedKeysOk M a p ∧ appliedMonoMap M⌝ ∗
    appliedLogAt γr a L ∗ mvcc.idxCert E.γ.idx L ∗ kvLogsOkM on γr M)

theorem srvAppliedBodyM_false (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) :
    srvAppliedBodyM (GF := GF) false s E γr = srvAppliedBody s E γr := rfl

/-- **The applied index's invariant in the mode `on`** (`srvAppliedInv` at `false`). -/
def srvAppliedInvM (on : Bool) (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) : IProp GF :=
  inv srvN (srvAppliedBodyM on s E γr)

instance srvAppliedInvM_persistent (on : Bool) (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) :
    Persistent (srvAppliedInvM on s E γr) := by
  unfold srvAppliedInvM; infer_instance

theorem srvAppliedInvM_false (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) :
    srvAppliedInvM (GF := GF) false s E γr = srvAppliedInv s E γr := rfl

end appliedM

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The certificates' invariant in the auth mode `on`**: `kvCertInv` off, `kvCertInvOn` on. -/
def kvCertInvM (on : Bool) (γ : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState) :
    IProp GF :=
  match on with
  | false => kvCertInv γ γk
  | true => kvCertInvOn γ γk st₀

instance kvCertInvM_persistent (on : Bool) (γ : ServerRaftNames) (γk : KVNames)
    (st₀ : auth.AuthState) : Persistent (kvCertInvM (GF := GF) on γ γk st₀) := by
  cases on <;> unfold kvCertInvM <;> infer_instance

/-- **The server's `E.C` in the auth mode `on`** (`srvC` with the mode's shapes). -/
def srvCM (on : Bool) (ρ : ReqNames) (E : apply.AEnv GF) (ai₀ c₀ : w64) (x₀ : apply.ApplyKV)
    (L : List EntryModel) : IProp GF :=
  iprop(⌜srvIdxOk ai₀ L ∧ logShapeM on L⌝ ∗ batchWaitOk ρ E L ∗ srvRLogLb ρ.raft L)

instance srvCM_persistent (on : Bool) (ρ : ReqNames) (E : apply.AEnv GF) (ai₀ c₀ : w64)
    (x₀ : apply.ApplyKV) (L : List EntryModel) :
    Persistent (srvCM (GF := GF) on ρ E ai₀ c₀ x₀ L) := by
  unfold srvCM; infer_instance

theorem srvCM_false (ρ : ReqNames) (E : apply.AEnv GF) (ai₀ c₀ : w64) (x₀ : apply.ApplyKV) :
    srvCM (GF := GF) false ρ E ai₀ c₀ x₀ = srvC ρ E ai₀ c₀ x₀ := rfl

/-- **The server's raft environment in the auth mode `on`** (`srvEr` with `srvCM`). -/
def srvErM (on : Bool) (ρ : ReqNames) (E : apply.AEnv GF) (ai₀ c₀ : w64) (x₀ : apply.ApplyKV)
    (id : w64) (S : IProp GF) : RNEnv GF :=
  ⟨srvCM on ρ E ai₀ c₀ x₀, fun m => iprop(srvMsgNet ρ.raft.raft id m ∗ srvMsgNoSnap m),
    iprop(True), ρ.rd, srvRQ ρ.rd.raft, S, iprop(False)⟩

theorem srvErM_false (ρ : ReqNames) (E : apply.AEnv GF) (ai₀ c₀ : w64) (x₀ : apply.ApplyKV)
    (id : w64) (S : IProp GF) :
    srvErM (GF := GF) false ρ E ai₀ c₀ x₀ id S = srvEr ρ E ai₀ c₀ x₀ id S := rfl

/-- **The cluster's workload in the auth mode `on`** (`clusterWorkloadOk` with the mode's
shapes). -/
def clusterWorkloadOkM (on : Bool) (ρ : ReqNames) (E : apply.AEnv GF) : IProp GF :=
  iprop(□ ∀ L : List EntryModel, srvRLogLb ρ.raft L ={⊤}=∗ ⌜logShapeM on L⌝ ∗ batchWaitOk ρ E L)

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
    srvMintInv ρ ∗ kvInvM on ρ.raft ρ.kv srvAuthSt0 ∗ ⌜structFieldRef EtcdServer go!"Cfg" s ≠ null⌝)

instance srvReqBuiltM_persistent (on : Bool) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (v : ReqFields) : Persistent (srvReqBuiltM (GF := GF) on s E ρ v) := by
  unfold srvReqBuiltM; infer_instance

theorem srvReqBuiltM_false (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (v : ReqFields) :
    srvReqBuiltM (GF := GF) false s E ρ v = srvReqBuilt s E ρ v := rfl

/-- **The apply thread's KV invariants in the auth mode `on`** (`srvKVInvs` with the mode's KV
and certificates' invariants, from `srvAuthSt0`; at `on = true` `srvKVInvsOn`'s rows). -/
def srvKVInvsM (on : Bool) (E : apply.AEnv GF) (γr : ReadNames) : IProp GF :=
  iprop(kvInvM on γr.raft γr.kv srvAuthSt0 ∗ kvCertInvM on γr.raft γr.kv srvAuthSt0 ∗
    srvRaftLogInv γr.raft ∗ ⌜E.γ.cok = γr.kv.cok⌝)

instance srvKVInvsM_persistent (on : Bool) (E : apply.AEnv GF) (γr : ReadNames) :
    Persistent (srvKVInvsM (GF := GF) on E γr) := by
  unfold srvKVInvsM; infer_instance

theorem srvKVInvsM_false (E : apply.AEnv GF) (γr : ReadNames) :
    srvKVInvsM (GF := GF) false E γr = srvKVInvs E γr := rfl

theorem srvKVInvsM_true (E : apply.AEnv GF) (γr : ReadNames) :
    srvKVInvsM (GF := GF) true E γr = srvKVInvsOn E γr srvAuthSt0 := rfl

/-- **`applyBuiltNA` in the auth mode `on`** (the auth plan's E3c): the apply thread's auth
resource at the store's start state (`srvAuthApplyResB` at `srvAuthSt0`, the latest state of the
store's history `[bootState, bump bootState]`), what ties the apply thread's auth state to the
model's from the start (`applyBuiltOn`). -/
def applyBuiltNAOn (s : Loc) (γ : ApplyNames) (ci : Loc) (b : GoInterface) (E : apply.AEnv GF)
    (γr : ReadNames) (ai₀ c₀ : w64) (x₀ : apply.ApplyKV) : IProp GF :=
  iprop(∃ (st₀ : ApplyState) (a t : w64) (f : Bool),
    applyThread γ st₀ ∗ ⌜loopOk γ st₀ ai₀ ∧ c₀ = ciEff γ st₀.k⌝ ∗ applyBackend γ ci b ∗
    ciApplying ci a t ∗ srvLgReader s ∗ srvBemuReaderAt s E.γbe ∗ srvBeOwn s E ∗
    revAuth E x₀.log ∗ srvAuthApplyResB s E srvAuthSt0 ∗
    srvAppliedOwn γr ai₀ ∗ appliedLogAt γr ai₀ x₀.log ∗ kvRun γr ai₀ c₀ [] x₀ ∗ srvRest E γr [] ∗
    srvApRes s γr [] ∗ srvForceSnapAddr s ↦ f)

/-- **`applyBuiltNA` in the auth mode `on`**: `applyBuiltNA` at `on = false` (by definition),
`applyBuiltNAOn` at `on = true`. -/
def applyBuiltNAM (on : Bool) (s : Loc) (γ : ApplyNames) (ci : Loc) (b : GoInterface)
    (E : apply.AEnv GF) (γr : ReadNames) (ai₀ c₀ : w64) (x₀ : apply.ApplyKV) : IProp GF :=
  match on with
  | false => applyBuiltNA s γ ci b E γr ai₀ c₀ x₀
  | true => applyBuiltNAOn s γ ci b E γr ai₀ c₀ x₀

/-- **The server's uber-applier's base applier's auth layer** (the auth plan's E3k; persistent):
its store and lessor the server's `authStore` and `lessor` fields' (`apply.uberBaseAuth`), what the
apply thread's latest-state KV triples come from (`apply.uberKVL_of_base`); with the store's
checks at the latest state in the environment's mode (`authStoreLatestM`, E3l: with auth on, of the
store's invariant). -/
def srvUberBase (s : Loc) (ua : GoInterface) (E : apply.AEnv GF) : IProp GF :=
  iprop(∃ au le : GoInterface, srvAuthStoreAddr s ↦□ au ∗ srvLessorAddr s ↦□ le ∗
    apply.uberBaseAuth ua E au le ∗
    ∃ stl : Loc, ⌜au = auth.authIface stl⌝ ∗ authStoreLatestM E.authMode au E.RD stl)

instance srvUberBase_persistent (s : Loc) (ua : GoInterface) (E : apply.AEnv GF) :
    Persistent (srvUberBase s ua E) := by
  unfold srvUberBase; infer_instance

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
    "#Hsab" ∷ srvApplyAllBuilt s ∗
    "#Hai" ∷ srvAppliedInvM on s E γr ∗
    "#Hkvi" ∷ srvKVInvsM on E γr ∗
    "#Hti" ∷ inv srvN (∃ t : w64, sync.atomic.ownUint64 (srvTermAddr s) (DFrac.own 1) t) ∗
    "#Hci'" ∷ srvCommittedInv s γr ∗
    "#Hrn" ∷ isRaftNode Er γn (srvRAddr s) ∗
    "%HEr" ∷ ⌜Er.C = srvCM on ρ E ai₀ c₀ x₀ ∧ Er.γr = γr ∧
      (γn.node.dyn = true → uint.Z c₀ ≤ uint.Z ai₀ ∧ γn.pre = [] ∧ ai₀ = W64 0)⌝ ∗
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
    "Hscu" ∷ (∃ n : w64, srvSnapCatchUpAddr s ↦ n ∗
      ⌜receiptBound GF ≤ uint.Z (if n = W64 0 then W64 5000 else n) + 1⌝) ∗
    "Hwg" ∷ srvWgAddr s ↦ (zero_val sync.WaitGroup) ∗
    "HwgMu" ∷ srvWgMuAddr s ↦ (zero_val sync.RWMutex) ∗
    "Hcomm" ∷ (∃ c : w64, srvCommittedOwn γr c) ∗
    "Hnot" ∷ (∃ x : Loc × NeedNames, ghostVar γr.notifier 1 x) ∗
    "Happ" ∷ applyBuiltNAM on s γ ci b E γr ai₀ c₀ x₀ ∗
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
    "Hua" ∷ srvUberRowM on s E x₀ ∗
    "Hwtok" ∷ idWaitTok ρ.ids ∗
    -- (2026-10-26, D22 J1a) what the snapshot path takes of the construction (`SnapRO.lean`)
    "Hsnapb" ∷ srvSnapBoot s ci E γr)

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
    iintro ⟨%st₀, %a, %t, %f, Hth, %Hok, Hbe, Hca, Hlg, Hbm, Hbo, Hra, Har, Hao, Hal, Hkr, Hrs, Hap, Hfs⟩
    iexists st₀, a, t, f
    iframe Hth Hbe Hca Hlg Hbm Hbo Hra Hao Hal Hkr Hrs Hap Hfs
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
      mvcc.idxCert E.γ.idx γr.kv.log0 -∗ srvRLogLb γr.raft [] ={Ec}=∗
      srvAppliedInvM on s E γr ∗ srvAppliedOwn γr (W64 0) ∗ appliedLogAt γr (W64 0) γr.kv.log0 ∗
      srvCommittedInv s γr ∗ srvCommittedOwn γr (W64 0) ∗
      inv srvN (∃ t : w64, sync.atomic.ownUint64 (srvTermAddr s) (DFrac.own 1) t) := by
  iintro Hai Hci Hti Hap Hcm Hlogs Hpend #Hcert #HL
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
    (x₀ : apply.ApplyKV) (h : envAgree E E') :
    srvCM on ρ E ai₀ c₀ x₀ = srvCM on ρ E' ai₀ c₀ x₀ := by
  obtain ⟨hi, hc, hr⟩ := h
  have hres : resultΨ (GF := GF) E = resultΨ E' := by
    funext ρ' rq F x
    unfold resultΨ resultIsW revMinted revTok mvcc.certOk
    rw [hi, hc, hr]
  funext L
  unfold srvCM batchWaitOk entryWaitOk reqWaitR
  rw [hres]

/-- The ticker's contract does not read the transport's borrow (`rnTickerOk_srvEr_S`'s). -/
theorem rnTickerOk_srvErM_S (on : Bool) (ρ : ReqNames) (E : apply.AEnv GF) (ai₀ c₀ : w64)
    (x₀ : apply.ApplyKV) (id : w64) (S S' : IProp GF) :
    rnTickerOk (srvErM on ρ E ai₀ c₀ x₀ id S) ⊢
      rnTickerOk (srvErM on ρ E ai₀ c₀ x₀ id S') := by
  unfold rnTickerOk isRNTicker srvErM
  exact .rfl

/-- **The claims give a batch's ids** (`batchWaitOk_of_work`, from the conf changes' ids alone:
what both modes' shapes give, `logShapeM_cc`). -/
theorem batchWaitOk_of_claims (ρ : ReqNames) (E : apply.AEnv GF) (L : List EntryModel)
    (hcc : ∀ m ∈ L, m.typ ≠ W32 0 → ccIdOf m.data = W64 0)
    (hcl : ccLogOk ρ.raft.raft L) :
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
      icases Hc with (%hc | ⟨%rq', %id', %γf, %hrq', #Hcl', #Hreg⟩)
      · exfalso; rcases hc with hc | hc
        · exact hc ht
        · exact hd hc
      · obtain ⟨hdec', hid'⟩ := hrq'
        rw [hdec] at hdec'
        cases hdec'
        rw [hid] at hid'
        cases hid'
        iframe Hreg
        iexists γf
        iexact Hcl'
    · iexists L
      iframe HL
      ipureintro; exact hm
  · rename_i ht
    have h0 := hcc m hm ht
    rw [h0]
    isplitr
    rotate_left
    · ipureintro; exact hcl m hm ht
    iintro !> %Ψ HR
    iunfold reqWaitR at HR
    icases HR with ⟨%d, %rq, %γf, %F, #Hc0, -, -⟩
    iapply idClaim_noZero ρ.ids d γf $$ HNZ Hc0

/-- **The workload clause in the mode `on`** (`clusterWorkloadOk_of`'s, from `kvInvOn`). -/
theorem clusterWorkloadOkOn_of (ρ : ReqNames) (E : apply.AEnv GF) (st₀ : auth.AuthState) :
    kvInvOn (GF := GF) ρ.raft ρ.kv st₀ ∗ srvRaftLogInv ρ.raft ∗ idNoZero ρ.ids ⊢
      clusterWorkloadOkM true ρ E := by
  iintro ⟨#Hkv, #Hr, #HNZ⟩
  iunfold clusterWorkloadOkM
  iintro !> %L #HL
  iunfold kvInvOn at Hkv
  iinv Hkv with >Hi Hclose
  icases Hi with ⟨%L', HL', Hσ, %Hok, #Hw⟩
  imod srvRLog_lb ρ.raft (⊤ \ ↑kvN) (mask_ndot_ne' nroot "raft_commit" "server_kv" (by decide))
    L' L $$ Hr HL' HL with ⟨HL', %Hp⟩
  ihave %HLi := srvRLogLb_idx ρ.raft L $$ HL
  imod Hclose $$ [HL' Hσ] with -
  · inext; iexists L'; iframe HL' Hσ Hw; ipureintro; exact Hok
  iunfold kvWorkOn at Hw
  icases Hw with ⟨%Hsh, #Hcl⟩
  obtain ⟨Hsh, Hccl⟩ := Hsh
  -- (2026-10-27) the committed log's entries are the server's log's or fillers
  have HshL : logShapeOn L := srv_entry_transfer _ L L' entryShapeOn
    (fun m m' he h => by
      have h1 := congrArg Draft.LogEntry.type he
      have h2 := congrArg Draft.LogEntry.data he
      simp only [EntryModel.toLE] at h1 h2
      unfold entryShapeOn at h ⊢; rw [h1, h2]; exact h)
    (fun m ht hd => ⟨fun _ => .inl hd, fun h => absurd ht h⟩) HLi Hp.2.2 Hsh
  have HcclL : ccLogOk ρ.raft.raft L := srv_entry_transfer _ L L'
    (fun m => m.typ ≠ W32 0 → ccPolOk ρ.raft.raft m.data)
    (fun m m' he h => by
      have h1 := congrArg Draft.LogEntry.type he
      have h2 := congrArg Draft.LogEntry.data he
      simp only [EntryModel.toLE] at h1 h2
      rw [h1, h2]; exact h)
    (fun m ht _ h => absurd ht h) HLi Hp.2.2 Hccl
  ihave #HclL := entryClaims_transfer ρ.ids _ L L' HLi Hp.2.2 $$ Hcl
  imodintro
  isplitr
  · ipureintro; exact HshL
  iapply batchWaitOk_of_claims ρ E L (logShapeM_cc true L HshL) HcclL $$ HclL HNZ HL

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
    (hdec : γw.node.dyn = true → γw.node.dec = srvDec ρ.rd.kv.c0 γw.node.boot)
    (hcap : 1 ≤ γw.γs.cap)
    (id : w64) (S : IProp GF) (hid : γw.id = id) :
    kvInvOn (GF := GF) ρ.raft ρ.kv st₀ ∗ srvRaftLogInv ρ.raft ∗ clusterWorkloadOkM true ρ E ⊢
      rnEnvOk (srvErM true ρ E ai₀ c₀ x₀ id S) γw := by
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
  · ipureintro; exact hcap
  isplitr
  · iexact Hr
  isplitr
  · iintro !> %m %st ⟨#Hmo, #Hrm, Hc⟩
    ihave #Hcl : srvClusterOk ρ.raft $$ []
    · iunfold srvRaftLogInv at Hr; icases Hr with ⟨-, #H, -⟩; iexact H
    rw [hraft, hid] at *
    ihave %Hns := srv_sentMsg_notSnap ρ.raft id st $$ [Hcl Hrm]
    · iframe Hcl Hrm
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
    (hdec : γw.node.dyn = true → γw.node.dec = srvDec ρ.rd.kv.c0 γw.node.boot)
    (hcap : 1 ≤ γw.γs.cap)
    (id : w64) (S : IProp GF) (hid : γw.id = id) :
    kvInvM (GF := GF) on ρ.raft ρ.kv srvAuthSt0 ∗ srvRaftLogInv ρ.raft ∗
        clusterWorkloadOkM on ρ E ⊢
      rnEnvOk (srvErM on ρ E ai₀ c₀ x₀ id S) γw := by
  cases on
  · exact rnEnvOk_of_cluster ρ E ai₀ c₀ x₀ γw hraft hpre hai hai0 hdec hcap id S hid
  · exact rnEnvOk_of_clusterOn ρ E ai₀ c₀ x₀ γw srvAuthSt0 hraft hpre hai hai0 hdec hcap id S hid

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
satisfiable. -/
theorem kvInvOn_alloc_boot (γs : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState)
    (ps : List w64) (E : CoPset)
    (hpre : γs.pre = []) (hai : γs.ai0 = W64 0) (hboot : srvBootLogOk ps γs.raft.boot)
    (hcc : ∀ e ∈ γs.raft.boot, ccIdOf e.Data' = W64 0 ∧ ccBootOk γs.raft.cfg e.Data')
    (hc0 : γk.c0 = W64 0) (hch : γk.ch0 = apply.alarmChain true false false)
    (hlog : γk.log0 ≠ []) :
    ⊢ srvRLog (GF := GF) γs (bootEntries γs.raft.boot) -∗
      ghostVar γk.st 1 (kvStateOf (kvModelOn γk st₀ (bootEntries γs.raft.boot))) ={E}=∗
      kvInvOn γs γk st₀ ∗
        etcdKV γk (kvStateOf (kvModelOn γk st₀ (bootEntries γs.raft.boot))) := by
  generalize hbl : γs.raft.boot = bootLog at hboot hcc ⊢
  iintro HL Hv
  icases onGhostVarHalves γk.st _ $$ Hv with ⟨Hv1, Hv2⟩
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
      γk.ch0 = apply.alarmChain true false false ∧ γk.log0 ≠ [] := by
    refine ⟨?_, ?_, ?_, ?_, hch, hlog⟩
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
      ⌜plainLogOn L ∧ detLogOn γk.c0 γk.ch0 (st₀, γk.log0) L ∧ srvIdxOkW γs.ai0 L ∧
        uint.Z γk.c0 ≤ uint.Z γs.ai0 ∧
        γk.ch0 = apply.alarmChain true false false ∧ γk.log0 ≠ []⌝ ∗ kvWorkOn γs.raft γk L))
    $$ [HL Hv1] with #Hinv
  · inext
    iexists bootEntries bootLog
    iframe Hv1
    isplitl [HL]
    · iexact HL
    isplitr
    · ipureintro; exact hok
    iunfold kvWorkOn
    iframe Hcl
    ipureintro; exact ⟨hshape, hccl⟩
  imodintro
  iframe Hinv
  iunfold etcdKV; iexact Hv2

end lemmas

end EtcdGrove
end Perennial
