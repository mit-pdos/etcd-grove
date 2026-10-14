/-
**The construction premise** (`isServerBuilt`): what the server's `start` (`server.go`) needs of
the server `NewServer` built, clause by clause, and what `start` hands to `run`, to the request
path and to `Start`'s goroutines. Lean-first (the request path's unit 4c, 2026-10-13); see
`notes/decisions.md`, "The server's goroutines: the FIFO scheduler as a chain of saved
postconditions, the construction premise".

`start` sets the fields `w` (`wait.New`), `applyWait` (`wait.NewTimeList`), `done`, `stop`,
`stopping` (fresh channels), `ctx`/`cancel` (`context.WithCancel(Background())`), `read`
(`read.NewRead`), `leaderChanged` (`notify.NewNotifier`) and the snapshot defaults of `s.Cfg`, and
starts `run`. Everything else is `NewServer`'s, and is stated here as it is when `start` begins:

* the server's views but the fields `start` sets (`srvFieldsBuilt`, `srvReqBuilt`, `srvReadBuilt`,
  `srvRunBuilt`, `srvApplyAllBuilt`: the persistent views `isServer`, `isServerReq`,
  `isServerRead`, `srvRunFieldsAt`, `isServerApplyAll` without those fields);
* the read names `γr` with the applied and committed indices' invariants: `NewServer` allocates
  them, as the raft node's contract (`isRaftNode Er γn`, `Er.γr = γr`) is stated over them;
* the raft wrapper (its node contract over the server's `E.C`, `srvC`), its tokens at the empty
  log, the raft storage's snapshot contract (`rnSnapOnce`);
* the apply thread's resources at the snapshot's index `ai₀` (`applyBuilt`: `applyStart` but the
  `wgMu` slot and the wait `start` makes), with the authority of the revisions' tokens at the
  KV's log (`revAuth E x₀.log`: a ghost allocation at `E.γrev`, an empty map does, `revAuth_empty`;
  the vertical slice's unit V1);
* the contracts of the names-only parts (`clusterVersionOk`: `ClusterVersion()`, monotone from
  `nil` to non-`nil`; `□ |==> idCred ρ.ids 1`: the read loop's ids; `□ |==> Er.T`: the ticks);
* the fields `start` sets (any values), `wg` and `wgMu` at their zero values;
* the reader slots `start` hands on: `s.lgMu`'s for `run` and for the read loop, and
  `s.firstCommitInTerm`'s for the read loop;
* the write budget `txn.storeWTs E.γ N` (the backend's unit 6: the store's write tokens, one per
  applied entry; `start`'s callers take `2 ^ 64 ≤ N`, every index's).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRun
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRead
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.read.Inv

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

/-- `uint64` is not an interface type (as `apply/BackendLemmas2.lean`'s: `start` calls `String()`
on the server's `types.ID`, whose underlying type is `uint64`). -/
instance notInterface_uint64_start [FfiSyntax] : go.NotInterface go.uint64 :=
  ⟨by unfold go.uint64; trivial⟩

section addrs
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]
abbrev srvSnapCountAddr (s : Loc) : Loc := srvCfgFieldAddr s go!"SnapshotCount"
abbrev srvSnapCatchUpAddr (s : Loc) : Loc := srvCfgFieldAddr s go!"SnapshotCatchUpEntries"
end addrs

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`isServer`'s fields but `w`** (persistent): `srvFieldsAt` without `s.w` (which `start` sets). -/
def srvFieldsBuilt (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (v : SrvFields) : IProp GF :=
  iprop(srvLgAddr s ↦□ v.lg ∗ ⌜v.lg ≠ null⌝ ∗
      srvUberApplyAddr s ↦□ v.ua ∗ apply.applierFor v.ua E ∗
      ⌜E.P = batchLockInv γ TM ∧ E.f = v.hook⌝ ∗
      hookSpec γ ci TM v.hook ∗
      srvLessorAddr s ↦□ v.lessor ∗ lessorOk v.lessor ∗
      srvFirstCommitAddr s ↦□ v.firstCommit ∗ srvAlarmStoreAddr s ↦□ v.alarmStore ∗
      srvClusterAddr s ↦□ v.cluster ∗ srvQuotaAddr s ↦□ v.quota ∗
      srvLgMuAddr s ↦□ v.lgMu ∗ srvMemberIDAddr s ↦□ v.memberID ∗ srvLeadInv s ∗
      cfgElectionTicksAddr (srvCfgAddr s) ↦□ v.electionTicks ∗
      cfgTickMsAddr (srvCfgAddr s) ↦□ v.tickMs ∗
      isNotifier v.firstCommit ∗ isAlarmStore v.alarmStore)

instance srvFieldsBuilt_persistent (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (v : SrvFields) : Persistent (srvFieldsBuilt s γ ci TM E v) := by
  unfold srvFieldsBuilt; infer_instance

/-- **`isServerReq`'s fields but `w` and `done`** (persistent; `srvReqFieldsAt` without them and
without the indices' invariants, which `isServerBuilt` states once). -/
def srvReqBuilt (s : Loc) (ρ : ReqNames) (v : ReqFields) : IProp GF :=
  iprop(structFieldRef EtcdServer go!"reqIDGen" s ↦□ v.gen ∗ idGen ρ.ids v.gen ∗
    srvRaftNode s ρ.raft ∗
    srvCfgFieldAddr s go!"MaxRequestBytes" ↦□ v.maxReq ∗
    srvCfgFieldAddr s go!"ServerFeatureGate" ↦□ v.fg ∗ isFeatureGate v.fg ∗
    srvCfgFieldAddr s go!"ClientCertAuthEnabled" ↦□ v.cca ∗
    srvCfgFieldAddr s go!"ElectionTicks" ↦□ v.electionTicks ∗
    srvCfgFieldAddr s go!"TickMs" ↦□ v.tickMs ∗
    structFieldRef EtcdServer go!"authStore" s ↦□ v.auth ∗ isReqAuth v.auth ∗
    structFieldRef EtcdServer go!"memberID" s ↦□ v.memberID ∗
    srvAtomicU64 (structFieldRef EtcdServer go!"lead" s) ∗
    structFieldRef EtcdServer go!"cluster" s ↦□ v.cluster ∗
    structFieldRef raftNodeConfig go!"transport"
      (structFieldRef raftNode go!"raftNodeConfig" (structFieldRef EtcdServer go!"r" s)) ↦□ v.tr ∗
    srvMintInv ρ ∗ srvCLogInv ρ.raft ∗ ⌜structFieldRef EtcdServer go!"Cfg" s ≠ null⌝)

instance srvReqBuilt_persistent (s : Loc) (ρ : ReqNames) (v : ReqFields) :
    Persistent (srvReqBuilt (GF := GF) s ρ v) := by
  unfold srvReqBuilt; infer_instance

/-- **`isServerRead`'s fields but `read`, `applyWait`, `leaderChanged`, `stopping`** (persistent;
`srvReadFieldsAt` without them and without the indices' invariants). -/
def srvReadBuilt (s : Loc) (E : apply.AEnv GF) (v : ReadFields) : IProp GF :=
  iprop(srvKVAddr s ↦□ v.kv ∗ txn.isKV v.kv E.s E.γ ∗
    E.s.[go_etcd_io.etcd.server.v3.storage.mvcc.store, go!"ReadView"] ↦□
      (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.mvcc.readView.ty)
        #v.rv : GoInterface) ∗
    mvcc.isReadView v.rv E.s E.γ ∗
    srvLessorAddr s ↦□ v.lessor ∗ apply.isApplyLessor v.lessor E.γ E.P E.f ∗
    srvAuthStoreAddr s ↦□ v.auth ∗ apply.isAuthStore v.auth E.P E.f ∗
    srvLgAddr s ↦□ v.lg ∗ ⌜v.lg ≠ null⌝ ∗
    srvCfgFieldAddr s go!"WarningApplyDuration" ↦□ v.wad ∗
    inv srvN (∃ t : w64, sync.atomic.ownUint64 (srvTermAddr s) (DFrac.own 1) t) ∗
    storeSmall E.γ ∗
    (∃ log₀ : mvcc.Log, mvcc.idxCert E.γ.idx log₀ ∗ ⌜2 ≤ log₀.length⌝) ∗
    srvFirstCommitAddr s ↦□ v.fc)

instance srvReadBuilt_persistent (s : Loc) (E : apply.AEnv GF) (v : ReadFields) :
    Persistent (srvReadBuilt s E v) := by
  unfold srvReadBuilt; infer_instance

/-- **`run`'s fields but those `start` sets** (persistent; `srvRunFieldsAt`'s `errorc`, compactor,
stats and `leadTimeMu`). -/
def srvRunBuilt (s : Loc) (v : RunFields) : IProp GF :=
  iprop(srvErrorcAddr s ↦□ v.errorc ∗
      (∃ γe : ChanNames, isChanBag γe v.errorc (V := GoInterface) (fun _ => iprop(True))) ∗
    srvCompactorAddr s ↦□ v.compactor ∗ compactorOk v.compactor ∗
    srvStatsAddr s ↦□ v.stats ∗
    sync.isRWMutexGuard (srvLeadTimeMuAddr s) (leadTimeP s))

instance srvRunBuilt_persistent (s : Loc) (v : RunFields) : Persistent (srvRunBuilt (GF := GF) s v) := by
  unfold srvRunBuilt; infer_instance

/-- **`isServerApplyAll`'s raft field** (persistent): the raft wrapper's `msgSnapC`. -/
def srvApplyAllBuilt (s : Loc) : IProp GF :=
  iprop(∃ msc : Loc, rnMsgSnapCAddr (srvRAddr s) ↦□ msc ∗
    (∃ (γc : ChanNames) (P : Loc → IProp GF), isChanBag γc msc (V := Loc) P))

instance srvApplyAllBuilt_persistent (s : Loc) : Persistent (srvApplyAllBuilt (GF := GF) s) := by
  unfold srvApplyAllBuilt; infer_instance

/-- **`s.ClusterVersion()`** (names-only: a trust-boundary contract, in the premise as the
lessor's): some `*semver.Version`, `nil` until the cluster's version is known, and non-`nil` from
then on (the ghost witness `monoNatLbOwn γcv 1`: `start` calls it three times and dereferences the
last two results when the first was non-`nil`). -/
def clusterVersionOk (s : Loc) : IProp GF :=
  iprop(∃ γcv : GName, □ (∀ known : Bool,
    {{ if known then monoNatLbOwn γcv 1 else True }}
      (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"ClusterVersion")) (Val #()))
    {{ (v : Loc), RET #v; ⌜v = null ∧ known = false⌝ ∨ ⌜v ≠ null⌝ ∗ monoNatLbOwn γcv 1 }}))

instance clusterVersionOk_persistent (s : Loc) : Persistent (clusterVersionOk (GF := GF) s) := by
  unfold clusterVersionOk; infer_instance

/-- **The apply thread's resources when `start` begins** (`applyStart` but the `wgMu` reader slot,
of the protocol `start` sets up, and the server's wait, which `start` makes: the applier's KV
state at `x₀`). -/
def applyBuilt (s : Loc) (γ : ApplyNames) (ci : Loc) (b : GoInterface) (E : apply.AEnv GF)
    (γr : ReadNames) (ai₀ c₀ : w64) (x₀ : apply.ApplyKV) : IProp GF :=
  iprop(∃ (st₀ : ApplyState) (a t : w64) (f : Bool),
    applyThread γ st₀ ∗ ⌜loopOk γ st₀ ai₀ ∧ c₀ = ciEff γ st₀.k⌝ ∗ applyBackend γ ci b ∗
    ciApplying ci a t ∗ srvLgReader s ∗ srvBemuReader s ∗
    (∃ ua : GoInterface, srvUberApplyAddr s ↦□ ua ∗ apply.applyKV E ua x₀) ∗ revAuth E x₀.log ∗
    srvAppliedOwn γr ai₀ ∗ appliedLogAt γr ai₀ x₀.log ∗ srvForceSnapAddr s ↦ f)

/-- **The construction premise** (see the file header; named conjuncts, what a `NewServer` proof
discharges). -/
def isServerBuilt (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (Er : RNEnv GF) (γn : RNNames)
    (b : GoInterface) (ai₀ at₀ c₀ : w64) (x₀ : apply.ApplyKV) (N : Nat) :
    IProp GF :=
  iprop(-- the server's views but the fields `start` sets
    "#Hci" ∷ isServerCI s γ ci ∗
    "#Hfb" ∷ (∃ v : SrvFields, srvFieldsBuilt s γ ci TM E v) ∗
    "#Hreqb" ∷ (∃ v : ReqFields, srvReqBuilt s ρ v) ∗
    "#Hrdb" ∷ (∃ v : ReadFields, srvReadBuilt s E v) ∗
    "#Hrunb" ∷ (∃ v : RunFields, srvRunBuilt s v) ∗
    "#Hsab" ∷ srvApplyAllBuilt s ∗
    -- the indices' invariants at the read names
    "#Hai" ∷ srvAppliedInv s E γr ∗
    "#Hti" ∷ inv srvN (∃ t : w64, sync.atomic.ownUint64 (srvTermAddr s) (DFrac.own 1) t) ∗
    "#Hci'" ∷ srvCommittedInv s γr ∗
    -- the raft wrapper over the server's `E.C`
    "#Hrn" ∷ isRaftNode Er γn (srvRAddr s) ∗
    "%HEr" ∷ ⌜Er.C = srvC ρ E ai₀ c₀ x₀ ∧ Er.γr = γr⌝ ∗
    "#HT" ∷ □ (|==> Er.T) ∗
    "Hsnap" ∷ (∃ ms : Loc, rnRaftStorageAddr (srvRAddr s) ↦□ ms ∗ rnSnapOnce ms ai₀ at₀) ∗
    "Hloop" ∷ rnLoopTok γn [] ∗ "Happly" ∷ rnApplyTok γn [] ∗ "Hrdone" ∷ rnDoneTok γn (srvRAddr s) ∗
    -- the names-only parts' contracts and the packages' ghost facts
    "#HNR" ∷ □ (|==> idCred ρ.ids 1) ∗
    "#Hcv" ∷ clusterVersionOk s ∗
    "#Hcci" ∷ context.isClosedchanInit ∗
    "#Hwci" ∷ waitClosecInit ∗
    "%Hbound" ∷ ⌜threadBound GF ≤ 2 ^ 31⌝ ∗
    -- the fields `start` sets
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
    -- the ghost state `start` hands on
    "Hcomm" ∷ (∃ c : w64, srvCommittedOwn γr c) ∗
    "Hnot" ∷ (∃ x : Loc × GName, ghostVar γr.notifier 1 x) ∗
    "Happ" ∷ applyBuilt s γ ci b E γr ai₀ c₀ x₀ ∗
    -- the reader slots `start` hands on: `run`'s and the read loop's
    "Hlr" ∷ srvLgReader s ∗
    "Hlrl" ∷ srvLgReader s ∗
    "Hfcr" ∷ (∃ n : Loc, srvFirstCommitAddr s ↦□ n ∗ notifyReader n) ∗
    -- the write budget
    "HWB" ∷ txn.storeWTs E.γ N)

/-- **What `start` hands to `Start`'s goroutines** (not persistent): a reader slot of `wgMu` (for
`Start`'s `GoAttach`es), the read loop's precondition with its resources (`srvReadLR`), and the
reader slots left over for request goroutines: `s.read.mux`'s (`srvReadReader`), `s.wgMu`'s
(`srvWgReader`), `s.leaderChanged`'s. -/
def srvStarted (s : Loc) (γr : ReadNames) (ρ : ReqNames) (RQ : w64 → w64 → IProp GF) : IProp GF :=
  iprop("Hgo" ∷ srvWgReader s ∗
    "Hrl" ∷ (∃ r : Loc, srvReadAddr s ↦□ r ∗
      isReadLoopPre r γr RQ (srvReadLR s) (idCred ρ.ids 1)) ∗
    "HLR" ∷ srvReadLR s ∗
    "#HNR" ∷ □ (|==> idCred ρ.ids 1) ∗
    "Hrds" ∷ ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
      srvReadReader s γr) ∗
    "Hwgs" ∷ ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders - 2) (),
      srvWgReader s) ∗
    "Hlcs" ∷ ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders - 1) (),
      ∃ n : Loc, srvLeaderChangedAddr s ↦□ n ∗ notifyReader n))

end defs

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- Perennial's `RWMutex` admits at least two readers. -/
theorem maxReaders_ge2 : 2 ≤ Int.toNat sync.rwmutex.actualMaxReaders := by
  rw [sync.rwmutex.actualMaxReaders_unseal]; decide

/-- One of `M ≥ 1` copies of `P`. -/
theorem replicate_take1 (P : IProp GF) (M : Nat) (h : 1 ≤ M) :
    ([∗list] _x ∈ List.replicate M (), P) ⊢ P ∗ [∗list] _x ∈ List.replicate (M - 1) (), P := by
  obtain ⟨m, rfl⟩ : ∃ m, M = m + 1 := ⟨M - 1, by omega⟩
  rw [List.replicate_succ, Nat.add_sub_cancel]
  iintro H
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H1, Hs⟩
  iframe H1 Hs

/-- Two of `M ≥ 2` copies of `P`. -/
theorem replicate_take2 (P : IProp GF) (M : Nat) (h : 2 ≤ M) :
    ([∗list] _x ∈ List.replicate M (), P) ⊢
      P ∗ P ∗ [∗list] _x ∈ List.replicate (M - 2) (), P := by
  obtain ⟨m, rfl⟩ : ∃ m, M = m + 2 := ⟨M - 2, by omega⟩
  rw [List.replicate_succ, List.replicate_succ, Nat.add_sub_cancel]
  iintro H
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H1, Hs⟩
  icases BigSepL.bigSepL_cons.1 $$ Hs with ⟨H2, Hs⟩
  iframe H1 H2 Hs

/-- Copies of `P` as copies of `Q`, given a persistent `R` with which `P` gives `Q`. -/
theorem replicate_map (P Q R : IProp GF) [Persistent R] (M : Nat) (h : R ∗ P ⊢ Q) :
    R ∗ ([∗list] _x ∈ List.replicate M (), P) ⊢ [∗list] _x ∈ List.replicate M (), Q := by
  iintro ⟨#HR, Hs⟩
  iapply BigSepL.bigSepL_impl $$ Hs
  iintro !> %k %x %_ HP
  iapply h
  iframe HR HP

/-- **`GoAttach`'s protocol, set up** (`start`): from the `stopping` channel's closer view, the
zero `wg` and `wgMu`, and the fields the protocol reads, the protocol (`srvGoAttachOk`), the
closer's token (`run`'s shutdown's) and the reader slots of `wgMu`. -/
theorem goAttach_init (s ch : Loc) (γch : ChanNames) (c : GoInterface) (l : Loc)
    (hbound : threadBound GF ≤ 2 ^ 31) (hl : l ≠ null) :
    ⊢ srvStoppingAddr' s ↦□ ch -∗ ownStopChan ch γch iprop(True) .Pending -∗
      srvWgAddr s ↦ (zero_val sync.WaitGroup) -∗ srvWgMuAddr s ↦ (zero_val sync.RWMutex) -∗
      srvCtxAddr s ↦□ c -∗ srvLgAddr s ↦□ l ={⊤}=∗
      ∃ γ : GoNames, srvGoAttachOk s γ ∗ token γ.close ∗
        [∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (), srvWgReader s := by
  iintro #Hchf Hch Hwg HwgMu #Hctx #Hlg
  unfold ownStopChan
  icases Hch with ⟨%γchi, #Hint, Hflag⟩
  imod sync.init_WaitGroup goAttachWGN (srvWgAddr s) $$ Hwg with ⟨%γwg, #Hiswg, Hctr, Hwait⟩
  imod ghostVar_alloc true with ⟨%γb, Hb⟩
  icases (read_ghostVar_halves γb true).1 $$ Hb with ⟨Hb1, Hb2⟩
  imod token_alloc with ⟨%γclose, Hclose⟩
  imod ownTokAuth_alloc with ⟨%γrun, Hrun⟩
  ihave H0 := threadToks_zero (GF := GF)
  let γ : GoNames := ⟨γb, γclose, γwg, γrun, γch, γchi⟩
  imod inv_alloc goAttachN ⊤ (goAttachInv γ) $$ [Hb2 Hctr Hrun H0 Hwait] with #Hinv
  · inext
    iunfold goAttachInv
    iexists true, (W32 0), 0
    iframe Hb2 Hctr Hrun H0
    isplitr
    · ipureintro; constructor <;> simp
    iright
    iframe Hwait
    ipureintro; rfl
  imod sync.init_RWMutex (wgMuP γ) (srvWgMuAddr s) $$ [Hb1 Hflag] HwgMu with Hslots
  · inext
    iunfold wgMuP
    iexists true
    iframe Hb1
    iunfold stopPart
    simp only [↓reduceIte]
    iexact Hflag
  icases read_guard_of_slots _ _ $$ Hslots with ⟨Hslots, #Hguard⟩
  ihave #Hok : srvGoAttachOk s γ $$ []
  · iunfold srvGoAttachOk
    iexists ch, c
    iframe #
    isplitr
    · ipureintro; exact hl
    ipureintro; exact hbound
  imodintro
  iexists γ
  iframe Hok Hclose
  iapply replicate_map _ _ (srvGoAttachOk s γ) $$ [$Hok $Hslots]
  iintro ⟨#Hok', Hslot⟩
  iunfold srvWgReader
  iexists γ
  iframe Hok' Hslot

end lemmas

end EtcdGrove
end Perennial
