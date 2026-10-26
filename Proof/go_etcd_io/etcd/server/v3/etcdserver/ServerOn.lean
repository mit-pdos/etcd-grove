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

end pure

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
    (bud : BudgetNames) (id : w64) (S : IProp GF) : RNEnv GF :=
  ⟨srvCM on ρ E ai₀ c₀ x₀, fun m => iprop(srvMsgNet ρ.raft.raft bud id m ∗ srvMsgNoSnap m),
    iprop(True), ρ.rd, srvRQ ρ.rd.raft, S⟩

theorem srvErM_false (ρ : ReqNames) (E : apply.AEnv GF) (ai₀ c₀ : w64) (x₀ : apply.ApplyKV)
    (bud : BudgetNames) (id : w64) (S : IProp GF) :
    srvErM (GF := GF) false ρ E ai₀ c₀ x₀ bud id S = srvEr ρ E ai₀ c₀ x₀ bud id S := rfl

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
resource at the store's start state (`srvAuthApplyResAt` at `srvAuthSt0`, the latest state of the
store's history `[bootState, bump bootState]`), what ties the apply thread's auth state to the
model's from the start (`applyBuiltOn`). -/
def applyBuiltNAOn (s : Loc) (γ : ApplyNames) (ci : Loc) (b : GoInterface) (E : apply.AEnv GF)
    (γr : ReadNames) (ai₀ c₀ : w64) (x₀ : apply.ApplyKV) : IProp GF :=
  iprop(∃ (st₀ : ApplyState) (a t : w64) (f : Bool),
    applyThread γ st₀ ∗ ⌜loopOk γ st₀ ai₀ ∧ c₀ = ciEff γ st₀.k⌝ ∗ applyBackend γ ci b ∗
    ciApplying ci a t ∗ srvLgReader s ∗ srvBemuReaderAt s E.γbe ∗ srvBeOwn s E ∗
    revAuth E x₀.log ∗ srvAuthApplyResAt s E srvAuthSt0 ∗
    srvAppliedOwn γr ai₀ ∗ appliedLogAt γr ai₀ x₀.log ∗ kvRun γr ai₀ c₀ [] x₀ ∗ srvRest E γr [] ∗
    srvForceSnapAddr s ↦ f)

/-- **`applyBuiltNA` in the auth mode `on`**: `applyBuiltNA` at `on = false` (by definition),
`applyBuiltNAOn` at `on = true`. -/
def applyBuiltNAM (on : Bool) (s : Loc) (γ : ApplyNames) (ci : Loc) (b : GoInterface)
    (E : apply.AEnv GF) (γr : ReadNames) (ai₀ c₀ : w64) (x₀ : apply.ApplyKV) : IProp GF :=
  match on with
  | false => applyBuiltNA s γ ci b E γr ai₀ c₀ x₀
  | true => applyBuiltNAOn s γ ci b E γr ai₀ c₀ x₀

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
    "#Hai" ∷ srvAppliedInv s E γr ∗
    "#Hkvi" ∷ srvKVInvsM on E γr ∗
    "#Hti" ∷ inv srvN (∃ t : w64, sync.atomic.ownUint64 (srvTermAddr s) (DFrac.own 1) t) ∗
    "#Hci'" ∷ srvCommittedInv s γr ∗
    "#Hrn" ∷ isRaftNode Er γn (srvRAddr s) ∗
    "%HEr" ∷ ⌜Er.C = srvCM on ρ E ai₀ c₀ x₀ ∧ Er.γr = γr ∧
      (γn.node.mode.isDyn = true → uint.Z c₀ ≤ uint.Z ai₀)⌝ ∗
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
    "Hua" ∷ (∃ ua : GoInterface, srvUberApplyAddr s ↦ ua ∗ apply.applierFor ua E ∗
      apply.applyKV E ua x₀) ∗
    "Hwtok" ∷ idWaitTok ρ.ids)

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

open Iris.ProofMode in
/-- **`applyBuiltNAM` from the mode-`on` row** (E3c): the mode-`on` row is the mode-off one with
the auth resource at its latest state, which the mode-off row forgets (`srvAuthApplyRes_of_At`). -/
theorem applyBuiltNAM_of_On (on : Bool) (s : Loc) (γ : ApplyNames) (ci : Loc) (b : GoInterface)
    (E : apply.AEnv GF) (γr : ReadNames) (ai₀ c₀ : w64) (x₀ : apply.ApplyKV) :
    applyBuiltNAOn (GF := GF) s γ ci b E γr ai₀ c₀ x₀ ⊢ applyBuiltNAM on s γ ci b E γr ai₀ c₀ x₀ := by
  cases on
  · unfold applyBuiltNAM applyBuiltNAOn applyBuiltNA
    iintro ⟨%st₀, %a, %t, %f, Hth, %Hok, Hbe, Hca, Hlg, Hbm, Hbo, Hra, Har, Hao, Hal, Hkr, Hrs, Hfs⟩
    iexists st₀, a, t, f
    iframe Hth Hbe Hca Hlg Hbm Hbo Hra Hao Hal Hkr Hrs Hfs
    isplitr
    · ipureintro; exact Hok
    iapply srvAuthApplyRes_of_At $$ Har
  · unfold applyBuiltNAM
    iintro H; iexact H

end lemmas

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

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
    (x₀ : apply.ApplyKV) (bud : BudgetNames) (id : w64) (S S' : IProp GF) :
    rnTickerOk (srvErM on ρ E ai₀ c₀ x₀ bud id S) ⊢
      rnTickerOk (srvErM on ρ E ai₀ c₀ x₀ bud id S') := by
  unfold rnTickerOk isRNTicker srvErM
  exact .rfl

/-- **The claims give a batch's ids** (`batchWaitOk_of_work`, from the conf changes' ids alone:
what both modes' shapes give, `logShapeM_cc`). -/
theorem batchWaitOk_of_claims (ρ : ReqNames) (E : apply.AEnv GF) (L : List EntryModel)
    (hcc : ∀ m ∈ L, m.typ ≠ W32 0 → ccIdOf m.data = W64 0)
    (hcl : ccLogOk ρ.raft.raft.reCfg L) :
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
    L' L $$ Hr HL' HL with ⟨HL', -, %Hp⟩
  imod Hclose $$ [HL' Hσ] with -
  · inext; iexists L'; iframe HL' Hσ Hw; ipureintro; exact Hok
  iunfold kvWorkOn at Hw
  icases Hw with ⟨%Hsh, #Hcl⟩
  obtain ⟨Hsh, Hccl⟩ := Hsh
  obtain ⟨R, rfl⟩ := Hp
  icases BigSepL.bigSepL_append.1 $$ Hcl with ⟨#HclL, -⟩
  have HshL : logShapeOn L := fun m hm => Hsh m (List.mem_append_left _ hm)
  imodintro
  isplitr
  · ipureintro; exact HshL
  iapply batchWaitOk_of_claims ρ E L (logShapeM_cc true L HshL)
    (fun m hm => Hccl m (List.mem_append_left _ hm)) $$ HclL HNZ HL

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
    (x₀ : apply.ApplyKV) (bud : BudgetNames) (γw : RNNames) (st₀ : auth.AuthState)
    (hraft : γw.node.raft = ρ.raft.raft) (hpre : γw.pre = ρ.raft.pre)
    (hai : uint.Z ρ.raft.ai0 = γw.pre.length) (hai0 : ρ.raft.ai0 = ai₀)
    (hmode : γw.node.mode = RNMode.static ↔ γw.node.raft.reDyn = none)
    (hdec : ∀ dec c0 h0 h1, γw.node.mode = .dyn dec c0 h0 h1 → dec = srvDec)
    (hstor : γw.node.stor = memStorIface γw.ms)
    (hbud : γw.node.bud = bud)
    (hns : ρ.raft.raft.reNoSnap = true)
    (hcap : 1 ≤ γw.γs.cap)
    (id : w64) (S : IProp GF) (hid : γw.node.id = id) :
    kvInvOn (GF := GF) ρ.raft ρ.kv st₀ ∗ srvRaftLogInv ρ.raft ∗ clusterWorkloadOkM true ρ E ⊢
      rnEnvOk (srvErM true ρ E ai₀ c₀ x₀ bud id S) γw := by
  iintro ⟨#Hkv, #Hr, #Hwl⟩
  unfold rnEnvOk srvErM
  simp only
  isplitr
  · ipureintro; trivial
  isplitr
  · ipureintro; exact ⟨hraft.symm, hpre.symm, hai⟩
  isplitr
  · ipureintro; exact ⟨hmode, hdec, hstor, by rw [hraft]; exact hns⟩
  isplitr
  · ipureintro; exact hcap
  isplitr
  · iintro !> %m %st ⟨#Hmo, #Hrm, #Htl, Hc, Htk⟩
    rw [hraft, hbud] at *
    isplitl [Hc Htk]
    · iunfold srvMsgNet
      iexists st
      iframe Hmo Htl Hc Htk
      rw [← hid]; iexact Hrm
    iunfold srvMsgNoSnap
    iexists st
    iframe Hmo
    iapply isRaftMsg_not_snap ρ.raft.raft hns _ st $$ Hrm
  isplitr
  · iintro !> %L #HL %Hfit
    iunfold clusterWorkloadOkM at Hwl
    imod Hwl $$ HL with ⟨%Hent, #Hbw⟩
    iunfold kvInvOn at Hkv
    iinv Hkv with >Hi Hclose
    icases Hi with ⟨%L', HL', Hσ, %Hok, #Hw⟩
    imod srvRLog_lb ρ.raft (⊤ \ ↑kvN) (mask_ndot_ne' nroot "raft_commit" "server_kv" (by decide))
      L' L $$ Hr HL' HL with ⟨HL', -, %Hp⟩
    imod Hclose $$ [HL' Hσ] with -
    · inext; iexists L'; iframe HL' Hσ Hw; ipureintro; exact Hok
    imodintro
    imodintro
    unfold srvCM
    iframe Hbw HL
    ipureintro
    refine ⟨?_, Hent⟩
    rw [← hai0]
    exact srvIdxOk_of_W _ _ (srvIdxOkW_prefix _ _ _ Hok.2.2.1 Hp) Hfit
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
    (x₀ : apply.ApplyKV) (bud : BudgetNames) (γw : RNNames)
    (hraft : γw.node.raft = ρ.raft.raft) (hpre : γw.pre = ρ.raft.pre)
    (hai : uint.Z ρ.raft.ai0 = γw.pre.length) (hai0 : ρ.raft.ai0 = ai₀)
    (hmode : γw.node.mode = RNMode.static ↔ γw.node.raft.reDyn = none)
    (hdec : ∀ dec c0 h0 h1, γw.node.mode = .dyn dec c0 h0 h1 → dec = srvDec)
    (hstor : γw.node.stor = memStorIface γw.ms)
    (hbud : γw.node.bud = bud)
    (hns : ρ.raft.raft.reNoSnap = true)
    (hcap : 1 ≤ γw.γs.cap)
    (id : w64) (S : IProp GF) (hid : γw.node.id = id) :
    kvInvM (GF := GF) on ρ.raft ρ.kv srvAuthSt0 ∗ srvRaftLogInv ρ.raft ∗
        clusterWorkloadOkM on ρ E ⊢
      rnEnvOk (srvErM on ρ E ai₀ c₀ x₀ bud id S) γw := by
  cases on
  · exact rnEnvOk_of_cluster ρ E ai₀ c₀ x₀ bud γw hraft hpre hai hai0 hmode hdec hstor hbud hns
      hcap id S hid
  · exact rnEnvOk_of_clusterOn ρ E ai₀ c₀ x₀ bud γw srvAuthSt0 hraft hpre hai hai0 hmode hdec
      hstor hbud hns hcap id S hid

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
    (ccOk : w32 → List w8 → Prop) (ps : List w64) (bootLog : List EntryM) (E : CoPset)
    (hpre : γs.pre = []) (hai : γs.ai0 = W64 0) (hboot : BootLogOk ccOk ps bootLog)
    (hcc : ∀ ty d, ccOk ty d → ccIdOf d = W64 0 ∧ ccBootOk γs.raft.reCfg d)
    (hc0 : γk.c0 = W64 0) (hch : γk.ch0 = apply.alarmChain true false false)
    (hlog : γk.log0 ≠ []) :
    ⊢ rLog (GF := GF) γs.raft bootLog -∗
      ghostVar γk.st 1 (kvStateOf (kvModelOn γk st₀ (bootEntries bootLog))) ={E}=∗
      kvInvOn γs γk st₀ ∗ etcdKV γk (kvStateOf (kvModelOn γk st₀ (bootEntries bootLog))) := by
  iintro HL Hv
  icases onGhostVarHalves γk.st _ $$ Hv with ⟨Hv1, Hv2⟩
  have hsl : srvLogOf γs (bootEntries bootLog) = bootLog := by
    unfold srvLogOf bootEntries; rw [hpre, List.nil_append, EntryModel.map_toM_ofM]
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
      obtain ⟨-, hi, ht, ⟨cm, hd, -⟩, hok⟩ := hk n e he
      refine ⟨hi, ht, ?_, (hcc _ _ hok).1⟩
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
      uint.Z γk.c0 ≤ uint.Z γs.ai0 + (bootEntries bootLog).length ∧
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
  have hccl : ccLogOk γs.raft.reCfg (bootEntries bootLog) := by
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
      obtain ⟨-, -, -, -, hok⟩ := hk n e he
      exact (hcc _ _ hok).2
  ihave #Hcl := entryClaims_conf (GF := GF) γk.ids (bootEntries bootLog) (fun m hm => by
    rw [hty m hm]; decide)
  iunfold kvInvOn
  imod inv_alloc kvN E (iprop(∃ L : List EntryModel,
      srvRLog γs L ∗ ghostVar γk.st (1 : Qp).half (kvStateOf (kvModelOn γk st₀ L)) ∗
      ⌜plainLogOn L ∧ detLogOn γk.c0 γk.ch0 (st₀, γk.log0) L ∧ srvIdxOkW γs.ai0 L ∧
        uint.Z γk.c0 ≤ uint.Z γs.ai0 + L.length ∧
        γk.ch0 = apply.alarmChain true false false ∧ γk.log0 ≠ []⌝ ∗ kvWorkOn γs.raft.reCfg γk L))
    $$ [HL Hv1] with #Hinv
  · inext
    iexists bootEntries bootLog
    iframe Hv1
    isplitl [HL]
    · iunfold srvRLog; rw [hsl]; iexact HL
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
