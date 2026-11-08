/-
**The server's rows over the auth component** (the auth-component refactor's stage 2, 2026-11-04; the
statements frozen by the user, 2026-11-04, `notes/decisions.md`, "The auth component, stage 2"):
the rows the five merged linked specs (`run`, `start`, `Start`, `applyAll.specBatch`;
`AppliedIndex` is over a model row) are written over, indexed by the slot `C : AuthC` (`AuthComp`)
where today's are indexed by `on : Bool` or split into off/on twins, each with its bridge to
today's rows (under `hC : E.authMode = C.mode` where a row reads the environment's mode).

* model and flag rows stay `Bool`, used at `C.isOn` (`kvInvM`, `srvAppliedInvM`, `srvCM`, ...;
  `kvRunM`, new here, joins them);
* resource rows and their containers: `srvApplyKVC`, `srvKVInvsC`, `srvAtomicsC`, `isServerC`,
  `applyBuiltC`, `isServerBuiltC`, `applyStartC`, `isServerRunC`.

Today's rows stay until their last spec moves (stage 3). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthComp
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.StartOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.StopApi

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

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

/-- **The KV names' ties to the environment with auth off** (`srvKVInvs`'s): the compaction mode
and retention, and the lease-granting mode, the environment's. Nothing with auth on, where they
have no producer (`kvTieM`, ReqOn, is a different row: the request side's). -/
def kvNameTiesM (on : Bool) (E : apply.AEnv GF) (γr : ReadNames) : Prop :=
  match on with
  | false => γr.kv.cmp = E.cmp ∧ (γr.kv.cret = E.cret ∧ γr.kv.lm = E.lm)
  | true => True

/-- **The store's witness in the auth mode `on`** (R6, 2026-11-07, the `lean` merge: `srvKVInvs`'
`kvNxOff`, `srvKVInvsOn`'s `kvNxOn` from `srvAuthSt0`). -/
def kvNxM (on : Bool) (γr : ReadNames) : mvcc.Log → IProp GF :=
  match on with
  | false => kvNxOff γr.raft γr.kv
  | true => kvNxOn γr.raft γr.kv srvAuthSt0

/-- **The apply thread's KV ghost state at `A`** (a model row): `kvRun` off (the auth state `st`
unused), `kvRunAtOn` at `st` on. -/
def kvRunM (on : Bool) (γr : ReadNames) (ai₀ c₀ : w64) (A : List EntryModel) (x : apply.ApplyKV)
    (st : auth.AuthState) : IProp GF :=
  match on with
  | false => kvRun γr ai₀ c₀ A x
  | true => kvRunAtOn γr ai₀ c₀ A x st

/-- **The apply thread's applier state** at `x` and the model's auth state `st` (`srvApplyKV`
off, `srvApplyKVOn` on: `srvApplyKVM`'s, with the auth part the component's). -/
def srvApplyKVC (C : AuthC) (s : Loc) (E : apply.AEnv GF) (γw : GName) (x : apply.ApplyKV)
    (st : auth.AuthState) : IProp GF :=
  iprop(∃ ua : GoInterface, srvUberApplyAddr s ↦ ua ∗ apply.applierFor ua E ∗ apply.applyKV E ua x ∗
    srvBeOwn s E ∗ revAuth E x.log ∗ acRes C s E ua st ∗
    (∃ (w : GoInterface) (RD : IProp GF), srvWAddr s ↦□ w ∗
      waitOk w RD (fun ot id => waitRegdOpt γw id ot) (fun ot id => waitGoneOpt γw id ot) ∗ RD) ∗
    -- (the lease-expiry merge) the lessor's range deleter (`srvApplyKV`'s, `srvApplyKVOn`'s)
    (∃ rd : GoFunc, lease.rdOwn (mvcc.api.mvccLeases E.γ) rd ∗ mvcc.api.mvccDeleter rd E.γ))

/-- **The apply thread's KV invariants** (`srvKVInvsM`'s): the mode's KV and certificates'
invariants from `srvAuthSt0`, the raft log's, the KV names' ties (off's, `kvNameTiesM`), the modes
the component needs (`acModesOk`: on, compaction and lease grants off), and the component's
invariants (`acInv`). (R6, 2026-11-07, the `lean` merge: `lean`'s tie `E.γ.cok = γr.kv.cok` and
mvcc's permit invariant `crevPermIs` replaced, as in `srvKVInvs`/`srvKVInvsOn`, by the store
invariant at the chain's witness and permit, `envWitOk`, the permit `kvCpOk` and the witness the
mode's model's, `kvNxM`; `acModesOk` at the KV names' compaction mode, `srvKVInvsOn`'s.) -/
def srvKVInvsC (C : AuthC) (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) : IProp GF :=
  iprop(kvInvM C.isOn γr.raft γr.kv srvAuthSt0 ∗ kvCertInvM C.isOn γr.raft γr.kv srvAuthSt0 ∗
    srvRaftLogInv γr.raft ∗ □ srvApi.kvStoreInvG E.kv E.γ E.Nx E.Cp E.γs ∗
    ⌜envWitOk E ∧ E.Cp = kvCpOk γr.kv⌝ ∗ ⌜E.Nx = kvNxM C.isOn γr⌝ ∗
    ⌜kvNameTiesM C.isOn E γr⌝ ∗ ⌜acModesOk C γr.kv.cmp γr.kv.lg⌝ ∗ acInv C s E γr)

instance srvKVInvsC_persistent (C : AuthC) (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) :
    Persistent (srvKVInvsC (GF := GF) C s E γr) := by
  unfold srvKVInvsC; infer_instance

/-- **The server's atomics** (`srvAtomicsM`'s). -/
def srvAtomicsC (C : AuthC) (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) : IProp GF :=
  iprop(srvAppliedInvM C.isOn s E γr ∗
    inv srvN (∃ v : w64, sync.atomic.ownUint64 (srvTermAddr s) (DFrac.own 1) v) ∗
    srvKVInvsC C s E γr)

instance srvAtomicsC_persistent (C : AuthC) (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) :
    Persistent (srvAtomicsC (GF := GF) C s E γr) := by
  unfold srvAtomicsC; infer_instance

/-- **The apply thread's view of the server** (`isServerM`'s). -/
def isServerC (C : AuthC) (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) : IProp GF :=
  iprop(⌜ρ.rd = γr⌝ ∗ isServerCI s γ ci ∗ (∃ v : SrvFields, srvFieldsAtM C.isOn s γ ci TM E ρ v) ∗
    srvAtomicsC C s E γr ∗ srvGenAt s E ρ ∗ srvRaftNode s ρ.raft ∗
    ⌜threadBound GF ≤ backend.rdPoolN⌝)

instance isServerC_persistent (C : AuthC) (s : Loc) (γ : ApplyNames) (ci : Loc)
    (TM : MetaCI → IProp GF) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) :
    Persistent (isServerC C s γ ci TM E ρ γr) := by
  unfold isServerC; infer_instance

/-- **The apply thread's resources when `start` begins** (`applyBuilt` off, `applyBuiltOn` on,
with `kvRunOn []`'s auth state named: `srvAuthSt0`). -/
def applyBuiltC (C : AuthC) (s : Loc) (γ : ApplyNames) (ci : Loc) (b : GoInterface)
    (E : apply.AEnv GF) (γr : ReadNames) (ai₀ c₀ : w64) (x₀ : apply.ApplyKV) : IProp GF :=
  iprop(∃ (st₀ : ApplyState) (a t : w64) (f : Bool),
    applyThread γ st₀ ∗ ⌜loopOk γ st₀ ai₀ ∧ c₀ = ciEff γ st₀.k⌝ ∗ applyBackend γ ci b ∗
    ciApplying ci a t ∗ srvLgReader s ∗ srvBemuReaderAt s E.γbe ∗ mvcc.api.mvccReaders E.γ 1 ∗ srvBeOwn s E ∗
    (∃ ua : GoInterface, srvUberApplyAddr s ↦ ua ∗ acRes C s E ua srvAuthSt0 ∗
      apply.applierFor ua E ∗ apply.applyKV E ua x₀) ∗
    revAuth E x₀.log ∗
    -- (the lease-expiry merge) the lessor's range deleter (`applyBuilt`'s, `applyBuiltOn`'s)
    (∃ rd : GoFunc, lease.rdOwn (mvcc.api.mvccLeases E.γ) rd ∗ mvcc.api.mvccDeleter rd E.γ) ∗
    srvAppliedOwn γr ai₀ ∗ appliedLogAt γr ai₀ x₀.log ∗ kvRunM C.isOn γr ai₀ c₀ [] x₀ srvAuthSt0 ∗
    srvRest E γr [] ∗ srvApRes s γr [] ∗ srvForceSnapAddr s ↦ f ∗ acTok C (ciEff γ st₀.k))

/-- **`start`'s construction premise** (`isServerBuilt` off, `isServerBuiltOn` on: the
model rows at `C.isOn`, the KV invariants and the apply thread's resources the component's). -/
def isServerBuiltC (C : AuthC) (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (Er : RNEnv GF) (γn : RNNames)
    (b : GoInterface) (ai₀ at₀ c₀ : w64) (x₀ : apply.ApplyKV) (N : Nat) :
    IProp GF :=
  iprop("#Hci" ∷ isServerCI s γ ci ∗
    "#Hfb" ∷ (∃ v : SrvFields, srvFieldsBuilt s γ ci TM E v) ∗
    "#Hreqb" ∷ (∃ v : ReqFields, srvReqBuiltM C.isOn s E ρ v) ∗
    "#Hrdb" ∷ (∃ v : ReadFields, srvReadBuilt s E v) ∗
    "#Hrunb" ∷ (∃ v : RunFields, srvRunBuilt s v) ∗
    -- (M2, S4) the compactor's run, once (`start` spends it)
    "Hcrun" ∷ (∃ c : GoInterface, srvCompactorAddr s ↦□ c ∗ compactorRun s E c) ∗
    "#Hsab" ∷ srvApplyAllBuilt s γr ∗
    "#Hai" ∷ srvAppliedInvM C.isOn s E γr ∗
    "#Hkvi" ∷ srvKVInvsC C s E γr ∗
    "#Hti" ∷ inv srvN (∃ t : w64, sync.atomic.ownUint64 (srvTermAddr s) (DFrac.own 1) t) ∗
    "#Hci'" ∷ srvCommittedInv s γr ∗
    "#Hrn" ∷ isRaftNode Er γn (srvRAddr s) ∗
    "%HEr" ∷ ⌜Er.C = srvCM C.isOn ρ E ai₀ c₀ x₀ ∧ Er.γr = γr ∧
      (uint.Z c₀ ≤ uint.Z ai₀ ∧ γn.pre = [] ∧ ai₀ = W64 0) ∧
      -- (R2d'a A6, DRAFT) a first start: the restart point's backend log `γn.a0` empty
      γn.a0 = []⌝ ∗
    -- (R2d'a A7, A10 item 5, 2026-11-06; DRAFT, approved by 82) no merged snapshot sent at a new
    -- raft term while the replay window is pending (`srvWinPend`; corrected 2026-11-07: false
    -- whenever the restarted member is later elected and snapshots a follower, its `n` free; R2d'b
    -- restates it, R2s removes it; with row 3 false on most restarts, the restart meaning is vacuous
    -- until R2d'b; free at a first start, `srvWinPend_first`)
    "Hwpend" ∷ srvWinPend s γr γn ∗
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
    -- (J8b, 2026-11-01) the server's member id is the raft node's (`applyAll.specSnapM`'s member id
    -- against the snapshot payload's `nodeSnapLocal … γn.id`)
    "#Hmid" ∷ srvMemberIDAddr s ↦□ γn.id ∗
    -- (2026-11-02, the cluster-rows stage) the member id a voter (the monitors' permission,
    -- `srvMonitorPermitM_of`: its attribute requests name it)
    "%Hmidc" ∷ ⌜γn.id ∈ γr.raft.raft.cfg⌝ ∗
    -- (J8b, 2026-11-01) the meta reads of the backends a snapshot opens (`bootOk`'s `#HmetaSnap`)
    "#HmetaSnap" ∷ srvMetaSnap γ ∗
    "Hsnap" ∷ (∃ ms : Loc, rnRaftStorageAddr (srvRAddr s) ↦□ ms ∗ rnSnapOnce γn.node.reg γn.node.cl γn.key ms γn.γs ai₀ at₀) ∗
    "Hloop" ∷ rnLoopTok γn [] ∗ "Hsend" ∷ Er.S ∗ "Happly" ∷ rnApplyTok γn [] ∗
    "Hrdone" ∷ rnDoneTok γn (srvRAddr s) ∗
    "#HNR" ∷ □ (|==> idCred ρ.ids 1) ∗
    "#Hcv" ∷ clusterVersionOk s ∗
    "#Hcci" ∷ context.isClosedchanInit ∗
    "#Hwci" ∷ waitClosecInit ∗
    -- (the backend-auth-split stage, 2026-11-02) within the backend's pool of readers (`2 ^ 28`;
    -- until then `2 ^ 31`, `GoAttach`'s)
    "%Hbound" ∷ ⌜threadBound GF ≤ backend.rdPoolN⌝ ∗
    -- (revoke-open, 2026-11-06) what `NewServer` built for the revocation
    "#Hrvkb" ∷ srvRevokeBuilt s E ∗
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
    "Happ" ∷ applyBuiltC C s γ ci b E γr ai₀ c₀ x₀ ∗
    "Hlr" ∷ srvLgReader s ∗
    "Hlrl" ∷ srvLgReader s ∗
    "Hfcr" ∷ (∃ n : Loc, srvFirstCommitAddr s ↦□ n ∗ notifyReader n) ∗
    "HWB" ∷ srvWTBudget E ∗
    "Hwtok" ∷ idWaitTok ρ.ids ∗
    -- (2026-10-26, D22 J1a) what the snapshot path takes of the construction (`SnapRO.lean`)
    "Hsnapb" ∷ srvSnapBoot s ci E γr γ ∗
    -- (2026-11-05, the restart plan's R2c-3) what `NewServer` kept for the stop, which `start`
    -- hands `run` (`srvStop.slot`)
    "Hskeep" ∷ srvStop.slot s E γn Er)

/-- **The apply thread's resources when `run` starts** (`applyStart` off, `applyStartOn` on). -/
def applyStartC (C : AuthC) (s : Loc) (γ : ApplyNames) (ci : Loc) (b : GoInterface) (E : apply.AEnv GF)
    (γr : ReadNames) (ai₀ c₀ : w64) (x₀ : apply.ApplyKV) (γw : GName) : IProp GF :=
  iprop(∃ (st₀ : ApplyState) (a t : w64) (f : Bool),
    applyThread γ st₀ ∗ ⌜loopOk γ st₀ ai₀ ∧ c₀ = ciEff γ st₀.k⌝ ∗ applyBackend γ ci b ∗
    ciApplying ci a t ∗ srvLgReader s ∗ srvBemuReaderAt s E.γbe ∗ srvWgReader s ∗ mvcc.api.mvccReaders E.γ 1 ∗ srvApplyKVC C s E γw x₀ srvAuthSt0 ∗
    srvAppliedOwn γr ai₀ ∗ appliedLogAt γr ai₀ x₀.log ∗ kvRunM C.isOn γr ai₀ c₀ [] x₀ srvAuthSt0 ∗ srvRest E γr [] ∗
    srvApRes s γr [] ∗ srvForceSnapAddr s ↦ f ∗ acTok C (ciEff γ st₀.k) ∗
    -- (D22 J1b, 2026-10-31) what each snapshot install takes and gives back
    srvSnapOwn s ci E γr γ ai₀)

/-- **`Hsnap`'s restart form** (R2d'a A9; `rnSnapOnce`'s, `InvRunRes.lean:334`): `run`'s one call of
the raft storage's `Snapshot()` (`server.go:760` at `673da07c8`) answers a snapshot at index `i` and
term `t` whose conf state is read-only and reports the voters after the ghost log `A₀` (`epCsAt γ A₀`:
at a restart the WAL snapshot's `ConfState`, `bootstrap.go:449-478`; nothing at `A₀ = []`), with a
lower bound of the storage's snapshot (`memSnapLb γs 0`, the writers' handle; a first start's from
`memSnapNone`) and the storage's invariant. -/
def rnSnapOnceR (rg : GName) (cl : Cluster) (nk : GName) (ms : Loc) (γs : MemStorNames) (i t : w64)
    (γ : ServerRaftNames) (A₀ : List EntryModel) : IProp GF :=
  iprop(∀ Φ : val → IProp GF,
    ▷ (∀ (sn pm cs : Loc) (sv : SnapshotM),
      ⌜sv.Metadata'.Index' = i ∧ sv.Metadata'.Term' = t ∧ pm ≠ null ∧ cs ≠ null⌝ -∗
      ownSnapM sn DFrac.discard sv -∗
      sn.[go_etcd_io.raft.v3.raftpb.Snapshot, go!"Metadata"] ↦□ pm -∗
      pm.[go_etcd_io.raft.v3.raftpb.SnapshotMetadata, go!"ConfState"] ↦□ cs -∗
      epCsOk cs -∗ epCsAt γ A₀ cs -∗ (|==> memSnapLb γs 0) -∗
      (letI : MemStorReg GF := ⟨rg⟩; memStorInv ms γs cl nk) -∗
      Φ (PairV #sn #(GoInterface.nil))) -∗
    WP (App (Val (ms @!! go.GoType.PointerType go_etcd_io.raft.v3.MemoryStorage.ty @!! go!"Snapshot"))
      (Val #())) {{ Φ }})

/-- **`applyStartC`'s restart form** (R2d'a A9): the apply thread's resources when `run` starts at Go's
index `ai` (`ep.appliedi`'s first value, the WAL snapshot's index), with the backend's ghost log
`A₀`: the ghost rows at `A₀` (the applied index `g₀ = ai₀ + |A₀|`, `kvRunM`, `srvRest`, `srvApRes`,
the consistent index `ciEff` at `g₀`, `bootstrap.go:255-273`), Go's at `ai` (`loopOk`, the snapshot
resources). The auth state `sa₀` is the one after `A₀` (`kvRunM`'s, with auth on the state
`A₀`'s admin entries leave, which Go's auth store recovers from the backend at the consistent
index), existential so that an auth-on restart whose log changed auth meets it; a first start's is
`srvAuthSt0` (`srvRestartAtR_first`). -/
def srvRestartAtR (C : AuthC) (s : Loc) (γ : ApplyNames) (ci : Loc) (b : GoInterface)
    (E : apply.AEnv GF) (γr : ReadNames) (ai₀ c₀ : w64) (x₀ : apply.ApplyKV) (γw : GName)
    (A₀ : List EntryModel) (ai : w64) : IProp GF :=
  iprop(∃ (st₀ : ApplyState) (a t : w64) (f : Bool) (g₀ : w64) (sa₀ : auth.AuthState),
    applyThread γ st₀ ∗
    ⌜loopOk γ st₀ ai ∧ g₀ = ciEff γ st₀.k ∧ uint.Z g₀ = uint.Z ai₀ + A₀.length⌝ ∗
    applyBackend γ ci b ∗ ciApplying ci a t ∗ srvLgReader s ∗ srvBemuReaderAt s E.γbe ∗
    srvWgReader s ∗ mvcc.api.mvccReaders E.γ 1 ∗ srvApplyKVC C s E γw x₀ sa₀ ∗
    srvAppliedOwn γr g₀ ∗ appliedLogAt γr g₀ x₀.log ∗ kvRunM C.isOn γr ai₀ c₀ A₀ x₀ sa₀ ∗
    srvRest E γr A₀ ∗ srvApRes s γr A₀ ∗ srvForceSnapAddr s ↦ f ∗ acTok C (ciEff γ st₀.k) ∗
    srvSnapOwn s ci E γr γ ai)

/-- **A9's texts for `isServerRunC`** (R2d'a A9, Q24 (c); in the hub since swap batch 5, 2026-11-07,
with `run.wp_proof`'s restart proof). Three of `isServerRunC`'s conjuncts at a restart, **`σ.b = 0` only**: a restart before the member's first WAL snapshot, so that nothing was
handed before the start (`γn.pre = []`, `ai₀ = 0`: `rnEnvOk` unchanged), Go's log restarts at index 0
and the backend's ghost log `A₀` (`γn.a0`, A6's field) is replayed through the window `(0, |A₀|]`.
`σ.b > 0` is R2d'b's, with the raft side's restart data (Q24 (a)).
- `%HEr`: today's conjuncts with `γn.a0 = A₀` for some `A₀` (was `γn.a0 = []`), `A₀`'s entries
  normal or conf changes, and room past it (`ai₀ + |A₀| + 1 < 2^64`); the last two are restart-only
  premises 6 and 7 of the eight (`notes/restart-plan.md`, "R2d'a restart-only premises"; R2d'b
  produces both; 7 holds of etcd's logs because etcd proposes only v1 `ConfChange`s);
- `Hsnap`: `rnSnapOnceR` at index `ai₀` (`= 0`), the conf state at `A₀`;
- `Hstart`: `srvRestartAtR` at `A₀`, Go's index `ai₀`.
At `A₀ = []` they are today's (`srvRunRestartR_first`). -/
def srvRunRestartR (C : AuthC) (s : Loc) (γ : ApplyNames) (ci : Loc) (b : GoInterface)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (Er : RNEnv GF) (γn : RNNames)
    (ai₀ at₀ c₀ : w64) (x₀ : apply.ApplyKV) (γw : GName) : IProp GF :=
  iprop(∃ A₀ : List EntryModel,
    ⌜Er.C = srvCM C.isOn ρ E ai₀ c₀ x₀ ∧ Er.γr = γr ∧
      (uint.Z c₀ ≤ uint.Z ai₀ ∧ γn.pre = [] ∧ ai₀ = W64 0) ∧
      γn.a0 = A₀ ∧ (∀ m ∈ A₀, m.typ = W32 0 ∨ m.typ = W32 1) ∧
      uint.Z ai₀ + A₀.length + 1 < 2 ^ 64⌝ ∗
    (∃ ms : Loc, rnRaftStorageAddr (srvRAddr s) ↦□ ms ∗
      rnSnapOnceR γn.node.reg γn.node.cl γn.key ms γn.γs ai₀ at₀ γr.raft A₀) ∗
    srvRestartAtR C s γ ci b E γr ai₀ c₀ x₀ γw A₀ ai₀)

/-- **What `run` needs**, at a first start or a restart at `σ.b = 0` (R2d'a swap batch 5,
2026-11-07: the start's conjuncts are `HRr ∷ srvRunRestartR`, the backend's ghost log `A₀ = γn.a0`;
until then `InvRun.lean`'s `isServerRun` off and `RunOn.lean`'s `isServerRunOn` on, both deleted
2026-11-07). The stop
requests' `SP` and the done channel's `DQ`, and (R2c-4) the stop's slot, `srvStop.slot`. -/
def isServerRunC (C : AuthC) (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (Er : RNEnv GF) (γn : RNNames)
    (γg : GoNames) (γcx : context.ContextNames) (γd : ChanNames) (v : RunFields)
    (b : GoInterface) (ai₀ at₀ c₀ : w64) (x₀ : apply.ApplyKV)
    (SP : IProp GF := iprop(False)) (DQ : IProp GF := iprop(True)) : IProp GF :=
  iprop("#Hsrv" ∷ isServerC C s γ ci TM E ρ γr ∗
    "#Hlnil" ∷ acLessor C s ∗
    "#Hsa" ∷ isServerApplyAll s γr ∗
    -- (J8b, 2026-11-01) the server's member id is the raft node's (`isServerBuilt`'s)
    "#Hmid" ∷ srvMemberIDAddr s ↦□ γn.id ∗
    -- (J8b, 2026-11-01) the meta reads of the backends a snapshot opens (`bootOk`'s `#HmetaSnap`)
    "#HmetaSnap" ∷ srvMetaSnap γ ∗
    "#Hrn" ∷ isRaftNode Er γn (srvRAddr s) ∗
    -- (R2d'a A9, swap batch 5, 2026-11-07; until then `%HEr` with `γn.a0 = []`, `Hsnap` (`rnSnapOnce`)
    -- and `Hstart` (`applyStartC`), a first start's, which give it: `srvRunRestartR_first`) a start
    -- or a restart at `σ.b = 0`: the backend's ghost log `A₀ = γn.a0`, the storage's snapshot's conf
    -- state at it, the apply thread's ghost rows at it
    "HRr" ∷ srvRunRestartR C s γ ci b E ρ γr Er γn ai₀ at₀ c₀ x₀ ρ.wait ∗
    -- (R2d'a A7, A10 item 5, 2026-11-06; DRAFT, approved by 82) no merged snapshot sent at a new
    -- raft term while the replay window is pending (`srvWinPend`; corrected 2026-11-07: false
    -- whenever the restarted member is later elected and snapshots a follower, its `n` free; R2d'b
    -- restates it, R2s removes it; with row 3 false on most restarts, the restart meaning is vacuous
    -- until R2d'b; free at a first start, `srvWinPend_first`)
    "Hwpend" ∷ srvWinPend s γr γn ∗
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
    -- (2026-10-31, #11) the KV the snapshot commits (`start`'s `srvReadBuilt`)
    "#Hkvf" ∷ (∃ kv : GoInterface, srvKVAddr s ↦□ kv ∗ □ mvcc.api.isMvcc kv E.γ ∗ ⌜kv = E.kv⌝) ∗
    "#Hrf" ∷ srvRunFieldsAt s γr γg γcx v SP ∗
    -- (revoke-open, 2026-11-06) the revocation's bundle (`run`'s expiry arm, revocable mode)
    "#Hrvk" ∷ srvRevokeCtx s E ρ γr γg ∗
    "Hloop" ∷ rnLoopTok γn [] ∗ "Hsend" ∷ Er.S ∗ "Happly" ∷ rnApplyTok γn [] ∗ "Hrdone" ∷ rnDoneTok γn (srvRAddr s) ∗
    "Hcomm" ∷ (∃ c : w64, srvCommittedOwn γr c) ∗
    "Hdc" ∷ ownBroadcastChan v.done γd DQ .Pending ∗
    "Hclose" ∷ token γg.close ∗
    "Hlr" ∷ srvLgReader s ∗
    -- (2026-10-19, D21 M3) with its counter, the apply thread's tokens taken through `ai₀`
    -- (H2, 2026-11-05) and its register at `GoAttach`'s receipts' name (`start` set it)
    "#HWB" ∷ (∃ γp : WTNames, srvWTPool E γp ∗ srvWTAt γp.cnt ai₀ ∗
      dghostVar γp.reg DFrac.discard (some γg.run)) ∗
    -- (2026-10-26, D22 J1a) what the snapshot path takes of the construction (`SnapRO.lean`): its
    -- persistent bundle; (D22 J1b, 2026-10-31) the counter's authority and the stocks in `applyStart`
    "#Hsnapb" ∷ (∃ γt : GName, srvSnapRO s ci E γr γt) ∗
    -- (J8a-3, 2026-11-01) the two configuration fields `start` writes, read-only from then on:
    -- with `srvSnapRO`'s rebuild, the whole configuration read-only (`specSnapM`'s `srvCfgAddr s ↦□`)
    "#Hsncfg" ∷ (∃ sc scu : w64, srvCfgFieldAddr s go!"SnapshotCount" ↦□ sc ∗
      srvCfgFieldAddr s go!"SnapshotCatchUpEntries" ↦□ scu) ∗
    -- (R2c-4) the stop's slot (`srvStop.slot`), from `start`'s construction premise, for the
    -- deferred shutdown
    "Hskeep" ∷ srvStop.slot s E γn Er)

end defs

section bridges
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-! ### Bridges to today's rows (stage 3 deletes today's rows, then these) -/

theorem kvRunM_nil_on (γr : ReadNames) (ai₀ c₀ : w64) (x : apply.ApplyKV) :
    kvRunOn (GF := GF) γr ai₀ c₀ [] x ⊣⊢ kvRunM true γr ai₀ c₀ [] x srvAuthSt0 := by
  constructor
  · exact kvRunOn_nil_at γr ai₀ c₀ x
  · unfold kvRunM kvRunOn kvRunAtOn
    iintro ⟨H, %h⟩
    isplitl
    · iexists srvAuthSt0; iexact H
    · ipureintro; exact h

theorem srvApplyKVM_C (C : AuthC) (s : Loc) (E : apply.AEnv GF) (γw : GName) (x : apply.ApplyKV)
    (st : auth.AuthState) :
    srvApplyKVM (GF := GF) C.isOn s E γw x st ⊣⊢ srvApplyKVC C s E γw x st := by
  refine (srvApplyKVM_open C.isOn s E γw x st).trans ?_
  simp only [kvAuthM_eq]
  exact .rfl

theorem srvKVInvsM_C (C : AuthC) (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) :
    srvKVInvsM (GF := GF) C.isOn s E γr ⊣⊢ srvKVInvsC C s E γr := by
  cases C with
  | off =>
    dsimp only [AuthC.isOn, srvKVInvsM, srvKVInvsC, srvKVInvs, kvInvM, kvCertInvM, kvNameTiesM,
      acModesOk, kvNxM]
    constructor
    · iintro ⟨#H1, #H2, #H3, #Hs, %Hc, %HNx, %Hlm⟩
      iframe H1 H2 H3 Hs
      isplitr
      · ipureintro; exact ⟨Hc.2.2.1, Hc.2.2.2⟩
      isplitr
      · ipureintro; exact HNx
      isplitr
      · ipureintro; exact ⟨Hc.1, Hc.2.1, Hlm⟩
      isplitr
      · ipureintro; trivial
      iapply acInv_off
    · iintro ⟨#H1, #H2, #H3, #Hs, %Hc, %HNx, %Ht, -, -⟩
      iframe H1 H2 H3 Hs
      isplitr
      · ipureintro; exact ⟨Ht.1, Ht.2.1, Hc.1, Hc.2⟩
      isplitr
      · ipureintro; exact HNx
      ipureintro; exact Ht.2.2
  | on γa =>
    dsimp only [AuthC.isOn, srvKVInvsM, srvKVInvsC, srvKVInvsOn, kvInvM, kvCertInvM, kvNameTiesM,
      acModesOk, kvNxM]
    constructor
    · iintro ⟨⟨#H1, #H2, #H3, #Htie, #Hs, %Hc, %HNx, %Hm⟩, #Hu⟩
      iframe H1 H2 H3 Hs
      isplitr
      · ipureintro; exact Hc
      isplitr
      · ipureintro; exact HNx
      isplitr
      · ipureintro; trivial
      isplitr
      · ipureintro; exact Hm
      iapply (acInv_on (.on γa) γa rfl s E γr).2
      iframe Htie Hu
    · iintro ⟨#H1, #H2, #H3, #Hs, %Hc, %HNx, -, %Hm, #Hi⟩
      ihave ⟨#Htie, #Hu⟩ := (acInv_on (.on γa) γa rfl s E γr).1 $$ Hi
      iframe H1 H2 H3 Hs Htie Hu
      isplitr
      · ipureintro; exact Hc
      isplitr
      · ipureintro; exact HNx
      ipureintro; exact Hm

theorem srvAtomicsM_C (C : AuthC) (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) :
    srvAtomicsM (GF := GF) C.isOn s E γr ⊣⊢ srvAtomicsC C s E γr := by
  unfold srvAtomicsM srvAtomicsC
  constructor
  · iintro ⟨#Ha, #Ht, #Hk⟩
    iframe Ha Ht
    iapply (srvKVInvsM_C C s E γr).1 $$ Hk
  · iintro ⟨#Ha, #Ht, #Hk⟩
    iframe Ha Ht
    iapply (srvKVInvsM_C C s E γr).2 $$ Hk

theorem isServerM_C (C : AuthC) (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) :
    isServerM (GF := GF) C.isOn s γ ci TM E ρ γr ⊣⊢ isServerC C s γ ci TM E ρ γr := by
  unfold isServerM isServerC
  constructor
  · iintro ⟨%Hr, #Hci, #Hf, #Ha, #Hg, #Hn, %Hb⟩
    iframe Hci Hf Hg Hn
    isplitr
    · ipureintro; exact Hr
    isplitr
    · iapply (srvAtomicsM_C C s E γr).1 $$ Ha
    ipureintro; exact Hb
  · iintro ⟨%Hr, #Hci, #Hf, #Ha, #Hg, #Hn, %Hb⟩
    iframe Hci Hf Hg Hn
    isplitr
    · ipureintro; exact Hr
    isplitr
    · iapply (srvAtomicsM_C C s E γr).2 $$ Ha
    ipureintro; exact Hb

/-- `applyBuilt` is the off component's (`hC`: `acTok .off` is `True`). -/
theorem applyBuilt_C (s : Loc) (γ : ApplyNames) (ci : Loc) (b : GoInterface) (E : apply.AEnv GF)
    (γr : ReadNames) (ai₀ c₀ : w64) (x₀ : apply.ApplyKV) (hC : E.authMode = AuthC.off.mode) :
    applyBuilt (GF := GF) s γ ci b E γr ai₀ c₀ x₀ ⊣⊢ applyBuiltC .off s γ ci b E γr ai₀ c₀ x₀ := by
  have hT : ∀ k, srvTokRights E k = acTok (GF := GF) .off k := fun k => srvTokRights_eq .off E k hC
  unfold applyBuilt applyBuiltC
  simp only [← hT, ← kvAuthM_eq]
  dsimp only [AuthC.isOn, AuthC.mode, kvAuthM, kvRunM] at hC ⊢
  simp only [srvTokRights, hC]
  constructor
  · iintro ⟨%st₀, %a, %t, %f, Hth, %Hok, Hbe, Hca, Hlg, Hbm, Hrdk, Hbo, ⟨%ua, Hua, Hfor, Hakv⟩, Hra,
      Har, Hrdat, Hao, Hal, Hkr, Hrest, Hap, Hfs⟩
    iexists st₀, a, t, f
    iframe Hth Hbe Hca Hlg Hbm Hrdk Hbo Hra Hrdat Hao Hal Hkr Hrest Hap Hfs
    isplitr
    · ipureintro; exact Hok
    iexists ua; iframe Hua Har Hfor Hakv
  · iintro ⟨%st₀, %a, %t, %f, Hth, %Hok, Hbe, Hca, Hlg, Hbm, Hrdk, Hbo, ⟨%ua, Hua, Har, Hfor, Hakv⟩, Hra,
      Hrdat, Hao, Hal, Hkr, Hrest, Hap, Hfs, -⟩
    iexists st₀, a, t, f
    iframe Hth Hbe Hca Hlg Hbm Hrdk Hbo Hra Har Hrdat Hao Hal Hkr Hrest Hap Hfs
    isplitr
    · ipureintro; exact Hok
    iexists ua; iframe Hua Hfor Hakv

/-- `applyBuiltOn` is the on component's (`kvRunOn []` at `srvAuthSt0`). -/
theorem applyBuiltOn_C (γa : auth.AuthNames) (s : Loc) (γ : ApplyNames) (ci : Loc)
    (b : GoInterface) (E : apply.AEnv GF) (γr : ReadNames) (ai₀ c₀ : w64) (x₀ : apply.ApplyKV)
    (hC : E.authMode = (AuthC.on γa).mode) :
    applyBuiltOn (GF := GF) s γ ci b E γr ai₀ c₀ x₀ ⊣⊢
      applyBuiltC (.on γa) s γ ci b E γr ai₀ c₀ x₀ := by
  have hT : ∀ k, srvTokRights E k = acTok (GF := GF) (.on γa) k :=
    fun k => srvTokRights_eq (.on γa) E k hC
  unfold applyBuiltOn applyBuiltC
  simp only [← hT, ← kvAuthM_eq]
  dsimp only [AuthC.isOn, kvAuthM]
  constructor
  · iintro ⟨%st₀, %a, %t, %f, Hth, %Hok, Hbe, Hca, Hlg, Hbm, Hrdk, Hbo, ⟨%ua, Hua, Hub, Hfor, Hakv⟩, Hra,
      Har, Hrdat, Hao, Hal, Hkr, Hrest, Hap, Hfs, Htok⟩
    iexists st₀, a, t, f
    iframe Hth Hbe Hca Hlg Hbm Hrdk Hbo Hra Hrdat Hao Hal Hrest Hap Hfs Htok
    isplitr
    · ipureintro; exact Hok
    isplitl [Hua Hub Har Hfor Hakv]
    · iexists ua; iframe Hua Hub Har Hfor Hakv
    iapply (kvRunM_nil_on γr ai₀ c₀ x₀).1 $$ Hkr
  · iintro ⟨%st₀, %a, %t, %f, Hth, %Hok, Hbe, Hca, Hlg, Hbm, Hrdk, Hbo, ⟨%ua, Hua, ⟨Hub, Har⟩, Hfor, Hakv⟩,
      Hra, Hrdat, Hao, Hal, Hkr, Hrest, Hap, Hfs, Htok⟩
    iexists st₀, a, t, f
    iframe Hth Hbe Hca Hlg Hbm Hrdk Hbo Hra Har Hrdat Hao Hal Hrest Hap Hfs Htok
    isplitr
    · ipureintro; exact Hok
    isplitl [Hua Hub Hfor Hakv]
    · iexists ua; iframe Hua Hub Hfor Hakv
    iapply (kvRunM_nil_on γr ai₀ c₀ x₀).2 $$ Hkr

/-- **`start`'s construction premise is the component's** (`isServerBuilt` off,
`isServerBuiltOn` on). -/
theorem isServerBuiltM_C (C : AuthC) (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (Er : RNEnv GF) (γn : RNNames)
    (b : GoInterface) (ai₀ at₀ c₀ : w64) (x₀ : apply.ApplyKV) (N : Nat)
    (hC : E.authMode = C.mode) :
    isServerBuiltM (GF := GF) C.isOn s γ ci TM E ρ γr Er γn b ai₀ at₀ c₀ x₀ N ∗
        srvStop.slot s E γn Er ⊣⊢
      isServerBuiltC C s γ ci TM E ρ γr Er γn b ai₀ at₀ c₀ x₀ N := by
  have hK := srvKVInvsM_C (GF := GF) C s E γr
  cases C with
  | off =>
    have hA := applyBuilt_C (GF := GF) s γ ci b E γr ai₀ c₀ x₀ hC
    dsimp only [AuthC.isOn, srvKVInvsM] at hK
    unfold isServerBuiltM isServerBuilt isServerBuiltC
    simp only [AuthC.isOn, srvReqBuiltM_false, srvAppliedInvM_false, srvCM_false]
    constructor
    · iintro ⟨⟨#Hci, #Hfb, #Hreqb, #Hrdb, #Hrunb, Hcrun, #Hsab, #Hai, #Hkvi, #Hti, #Hci', #Hrn, #HEr, Hwpend, Hrunh, Hwth, Hwtl, #Hdisk, #Hslg, #Hρrd, #Hmid, #Hmidc, #HmetaSnap, Hsnap, Hloop, Hsend, Happly, Hrdone, #HNR, #Hcv, #Hcci, #Hwci, #Hbound, #Hrvkb, Hw, Haw, Hdone, Hstop, Hstopping, Hctx, Hcancel, Hread, Hlc, Hsc, Hscu, Hwg, HwgMu, Hcomm, Hnot, Happ, Hlr, Hlrl, Hfcr, HWB, Hwtok, Hsnapb⟩, Hsk⟩
      iframe Hci Hfb Hreqb Hrdb Hrunb Hcrun Hsab Hai Hti Hci' Hrn HEr Hwpend Hrunh Hwth Hwtl Hdisk Hslg Hρrd Hmid Hmidc HmetaSnap Hsnap Hloop Hsend Happly Hrdone HNR Hcv Hcci Hwci Hbound Hrvkb Hw Haw Hdone Hstop Hstopping Hctx Hcancel Hread Hlc Hsc Hscu Hwg HwgMu Hcomm Hnot Hlr Hlrl Hfcr HWB Hwtok Hsnapb Hsk
      isplitr
      · iapply hK.1 $$ Hkvi
      iapply hA.1 $$ Happ
    · iintro ⟨#Hci, #Hfb, #Hreqb, #Hrdb, #Hrunb, Hcrun, #Hsab, #Hai, #Hkvi, #Hti, #Hci', #Hrn, #HEr, Hwpend, Hrunh, Hwth, Hwtl, #Hdisk, #Hslg, #Hρrd, #Hmid, #Hmidc, #HmetaSnap, Hsnap, Hloop, Hsend, Happly, Hrdone, #HNR, #Hcv, #Hcci, #Hwci, #Hbound, #Hrvkb, Hw, Haw, Hdone, Hstop, Hstopping, Hctx, Hcancel, Hread, Hlc, Hsc, Hscu, Hwg, HwgMu, Hcomm, Hnot, Happ, Hlr, Hlrl, Hfcr, HWB, Hwtok, Hsnapb, Hsk⟩
      iframe Hci Hfb Hreqb Hrdb Hrunb Hcrun Hsab Hai Hti Hci' Hrn HEr Hwpend Hrunh Hwth Hwtl Hdisk Hslg Hρrd Hmid Hmidc HmetaSnap Hsnap Hloop Hsend Happly Hrdone HNR Hcv Hcci Hwci Hbound Hrvkb Hw Haw Hdone Hstop Hstopping Hctx Hcancel Hread Hlc Hsc Hscu Hwg HwgMu Hcomm Hnot Hlr Hlrl Hfcr HWB Hwtok Hsnapb Hsk
      isplitr
      · iapply hK.2 $$ Hkvi
      iapply hA.2 $$ Happ
  | on γa =>
    have hA := applyBuiltOn_C (GF := GF) γa s γ ci b E γr ai₀ c₀ x₀ hC
    dsimp only [AuthC.isOn] at hK
    unfold isServerBuiltM isServerBuiltOn isServerBuiltC
    simp only [AuthC.isOn]
    constructor
    · iintro ⟨⟨#Hci, #Hfb, #Hreqb, #Hrdb, #Hrunb, Hcrun, #Hsab, #Hai, #Hkvi, #Hti, #Hci', #Hrn, #HEr, Hwpend, Hrunh, Hwth, Hwtl, #Hdisk, #Hslg, #Hρrd, #Hmid, #Hmidc, #HmetaSnap, Hsnap, Hloop, Hsend, Happly, Hrdone, #HNR, #Hcv, #Hcci, #Hwci, #Hbound, #Hrvkb, Hw, Haw, Hdone, Hstop, Hstopping, Hctx, Hcancel, Hread, Hlc, Hsc, Hscu, Hwg, HwgMu, Hcomm, Hnot, Happ, Hlr, Hlrl, Hfcr, HWB, Hwtok, Hsnapb⟩, Hsk⟩
      iframe Hci Hfb Hreqb Hrdb Hrunb Hcrun Hsab Hai Hti Hci' Hrn HEr Hwpend Hrunh Hwth Hwtl Hdisk Hslg Hρrd Hmid Hmidc HmetaSnap Hsnap Hloop Hsend Happly Hrdone HNR Hcv Hcci Hwci Hbound Hrvkb Hw Haw Hdone Hstop Hstopping Hctx Hcancel Hread Hlc Hsc Hscu Hwg HwgMu Hcomm Hnot Hlr Hlrl Hfcr HWB Hwtok Hsnapb Hsk
      isplitr
      · iapply hK.1 $$ Hkvi
      iapply hA.1 $$ Happ
    · iintro ⟨#Hci, #Hfb, #Hreqb, #Hrdb, #Hrunb, Hcrun, #Hsab, #Hai, #Hkvi, #Hti, #Hci', #Hrn, #HEr, Hwpend, Hrunh, Hwth, Hwtl, #Hdisk, #Hslg, #Hρrd, #Hmid, #Hmidc, #HmetaSnap, Hsnap, Hloop, Hsend, Happly, Hrdone, #HNR, #Hcv, #Hcci, #Hwci, #Hbound, #Hrvkb, Hw, Haw, Hdone, Hstop, Hstopping, Hctx, Hcancel, Hread, Hlc, Hsc, Hscu, Hwg, HwgMu, Hcomm, Hnot, Happ, Hlr, Hlrl, Hfcr, HWB, Hwtok, Hsnapb, Hsk⟩
      iframe Hci Hfb Hreqb Hrdb Hrunb Hcrun Hsab Hai Hti Hci' Hrn HEr Hwpend Hrunh Hwth Hwtl Hdisk Hslg Hρrd Hmid Hmidc HmetaSnap Hsnap Hloop Hsend Happly Hrdone HNR Hcv Hcci Hwci Hbound Hrvkb Hw Haw Hdone Hstop Hstopping Hctx Hcancel Hread Hlc Hsc Hscu Hwg HwgMu Hcomm Hnot Hlr Hlrl Hfcr HWB Hwtok Hsnapb Hsk
      isplitr
      · iapply hK.2 $$ Hkvi
      iapply hA.2 $$ Happ

/-- `applyStart` is the off component's. -/
theorem applyStart_C (s : Loc) (γ : ApplyNames) (ci : Loc) (b : GoInterface) (E : apply.AEnv GF)
    (γr : ReadNames) (ai₀ c₀ : w64) (x₀ : apply.ApplyKV) (γw : GName)
    (hC : E.authMode = AuthC.off.mode) :
    applyStart (GF := GF) s γ ci b E γr ai₀ c₀ x₀ γw ⊣⊢
      applyStartC .off s γ ci b E γr ai₀ c₀ x₀ γw := by
  have hT : ∀ k, srvTokRights E k = acTok (GF := GF) .off k := fun k => srvTokRights_eq .off E k hC
  have hK := srvApplyKVM_C (GF := GF) .off s E γw x₀ srvAuthSt0
  dsimp only [AuthC.isOn, AuthC.mode, srvApplyKVM] at hK hC
  unfold applyStart applyStartC
  simp only [← hT]
  dsimp only [AuthC.isOn, kvRunM]
  simp only [srvTokRights, hC]
  constructor
  · iintro ⟨%st₀, %a, %t, %f, Hth, %Hok, Hbe, Hca, Hlg, Hbm, Hwg, Hrdk, Hkv, Hao, Hal, Hkr, Hrest, Hap,
      Hfs, Hso⟩
    iexists st₀, a, t, f
    iframe Hth Hbe Hca Hlg Hbm Hwg Hrdk Hao Hal Hkr Hrest Hap Hfs Hso
    isplitr
    · ipureintro; exact Hok
    iapply hK.1 $$ Hkv
  · iintro ⟨%st₀, %a, %t, %f, Hth, %Hok, Hbe, Hca, Hlg, Hbm, Hwg, Hrdk, Hkv, Hao, Hal, Hkr, Hrest, Hap,
      Hfs, -, Hso⟩
    iexists st₀, a, t, f
    iframe Hth Hbe Hca Hlg Hbm Hwg Hrdk Hao Hal Hkr Hrest Hap Hfs Hso
    isplitr
    · ipureintro; exact Hok
    iapply hK.2 $$ Hkv

/-- `applyStartOn` is the on component's. -/
theorem applyStartOn_C (γa : auth.AuthNames) (s : Loc) (γ : ApplyNames) (ci : Loc)
    (b : GoInterface) (E : apply.AEnv GF) (γr : ReadNames) (ai₀ c₀ : w64) (x₀ : apply.ApplyKV)
    (γw : GName) (hC : E.authMode = (AuthC.on γa).mode) :
    applyStartOn (GF := GF) s γ ci b E γr ai₀ c₀ x₀ γw ⊣⊢
      applyStartC (.on γa) s γ ci b E γr ai₀ c₀ x₀ γw := by
  have hT : ∀ k, srvTokRights E k = acTok (GF := GF) (.on γa) k :=
    fun k => srvTokRights_eq (.on γa) E k hC
  have hK := srvApplyKVM_C (GF := GF) (.on γa) s E γw x₀ srvAuthSt0
  dsimp only [AuthC.isOn, srvApplyKVM] at hK
  unfold applyStartOn applyStartC
  simp only [← hT]
  dsimp only [AuthC.isOn, kvRunM]
  constructor
  · iintro ⟨%st₀, %a, %t, %f, Hth, %Hok, Hbe, Hca, Hlg, Hbm, Hwg, Hrdk, Hkv, Hao, Hal, Hkr, Hrest, Hap,
      Hfs, Htok, Hso⟩
    iexists st₀, a, t, f
    iframe Hth Hbe Hca Hlg Hbm Hwg Hrdk Hao Hal Hkr Hrest Hap Hfs Htok Hso
    isplitr
    · ipureintro; exact Hok
    iapply hK.1 $$ Hkv
  · iintro ⟨%st₀, %a, %t, %f, Hth, %Hok, Hbe, Hca, Hlg, Hbm, Hwg, Hrdk, Hkv, Hao, Hal, Hkr, Hrest, Hap,
      Hfs, Htok, Hso⟩
    iexists st₀, a, t, f
    iframe Hth Hbe Hca Hlg Hbm Hwg Hrdk Hao Hal Hkr Hrest Hap Hfs Htok Hso
    isplitr
    · ipureintro; exact Hok
    iapply hK.2 $$ Hkv

/-- `isServerBuilt_mid`'s, over the component: the member id field, a voter. -/
theorem isServerBuiltC_mid (C : AuthC) (s : Loc) (γ : ApplyNames) (ci : Loc)
    (TM : MetaCI → IProp GF) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (Er : RNEnv GF)
    (γn : RNNames) (b : GoInterface) (ai₀ at₀ c₀ : w64) (x₀ : apply.ApplyKV) (N : Nat) :
    isServerBuiltC (GF := GF) C s γ ci TM E ρ γr Er γn b ai₀ at₀ c₀ x₀ N ⊢
      isServerBuiltC C s γ ci TM E ρ γr Er γn b ai₀ at₀ c₀ x₀ N ∗
        srvMemberIDAddr s ↦□ γn.id ∗ ⌜γn.id ∈ ρ.raft.raft.cfg⌝ := by
  iintro H
  iunfold isServerBuiltC at H
  iNamed H
  have hm : γn.id ∈ ρ.raft.raft.cfg := by rw [ReqNames.raft, Hρrd]; exact Hmidc
  iframe Hmid
  isplitl
  · iunfold isServerBuiltC
    iframe % # ∗
  ipureintro; exact hm

/-- **`start`'s construction premise from `NewServer`'s built part**, the component's
(`isServerBuilt_of_gapM` and the bridge). -/
theorem isServerBuiltC_of_gap (C : AuthC) (s : Loc) (γ : ApplyNames) (ci : Loc)
    (TM : MetaCI → IProp GF) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (Er : RNEnv GF)
    (γn : RNNames) (b : GoInterface) (ai₀ at₀ c₀ : w64) (x₀ : apply.ApplyKV) (N : Nat)
    (hC : E.authMode = C.mode) :
    srvBuiltG C.isOn s γ ci TM E ρ γr Er γn b ai₀ c₀ x₀ N ∗ srvBuildGap s γn ai₀ at₀ ∗
        srvStop.slot s E γn Er ⊢
      isServerBuiltC C s γ ci TM E ρ γr Er γn b ai₀ at₀ c₀ x₀ N := by
  iintro ⟨Hb, Hg, Hsk⟩
  iapply (isServerBuiltM_C C s γ ci TM E ρ γr Er γn b ai₀ at₀ c₀ x₀ N hC).1
  iframe Hsk
  iapply isServerBuilt_of_gapM C.isOn s γ ci TM E ρ γr Er γn b ai₀ at₀ c₀ x₀ N
  iframe Hb Hg

/-! ### The views `start` makes (the auth component's 2c) -/

/-- **The request view's bound request side**, from the read side. -/
theorem srvAuthBoundM_of_read (C : AuthC) (s : Loc) (E : apply.AEnv GF)
    (hC : E.authMode = C.mode) : acRead (GF := GF) C s E ⊢ srvAuthBoundM C.isOn s E := by
  cases C with
  | off =>
    iintro -
    dsimp only [AuthC.isOn, srvAuthBoundM]
    ipureintro; rw [apply.AEnv.authOn_eq, hC]; rfl
  | on γa =>
    iintro #H
    dsimp only [AuthC.isOn, srvAuthBoundM]
    isplitl
    · iapply acRead_bound (GF := GF) (.on γa) γa rfl s E $$ H
    ipureintro; rw [apply.AEnv.authOn_eq, hC]; rfl

/-- **The read view's request-side bound** at the store field's value `au`, from the read side. -/
theorem readBound_of_read (C : AuthC) (s : Loc) (E : apply.AEnv GF) (au : GoInterface)
    (hC : E.authMode = C.mode) :
    acRead (GF := GF) C s E ∗ srvAuthStoreAddr s ↦□ au ⊢
      □ (⌜E.authMode.isOn = true⌝ → isReqAuthBound au E.RD E.authMode) := by
  cases C with
  | off =>
    iintro -
    iintro !> %h
    simp [hC, AuthC.mode, auth.AuthMode.isOn] at h
  | on γa =>
    iintro ⟨#H, #Ha⟩
    ihave #Hb := acRead_bound (GF := GF) (.on γa) γa rfl s E $$ H
    iunfold srvAuthBound at Hb
    icases Hb with ⟨%st, #Hst, #HB⟩
    ihave #Hst' : srvAuthStoreAddr s ↦□ st $$ []
    · iexact Hst
    icombine Ha Hst' gives %Heq
    iintro !> %_
    rw [Heq]
    iexact HB

/-- **The read loop's composition** at the mode's model state, from the KV invariants. -/
theorem readCompose_C (C : AuthC) (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) :
    srvKVInvsC (GF := GF) C s E γr ⊢ readCompose γr (kvStM C.isOn γr.kv) := by
  iintro #H
  ihave #H' := (srvKVInvsM_C (GF := GF) C s E γr).2 $$ H
  cases C with
  | off =>
    dsimp only [AuthC.isOn] at *
    rw [kvStM_false]
    rw [srvKVInvsM_false] at *
    iunfold readCompose
    iintro !> %gs #Hgs
    iunfold srvKVInvs at H'
    icases H' with ⟨#HkvI, -⟩
    iapply kv_read_compose γr.raft γr.kv gs $$ HkvI Hgs
  | on γa =>
    dsimp only [AuthC.isOn] at *
    iapply readCompose_on s E γr $$ H'

/-- The KV names' tie gives the request view's (`kvTieM`). -/
theorem kvTieM_of_names (on : Bool) (E : apply.AEnv GF) (γr : ReadNames)
    (h : kvNameTiesM (GF := GF) on E γr) : kvTieM (GF := GF) on γr.kv.cmp E := by
  cases on
  · exact h.1
  · trivial

/-! ### What `applyAll`'s merged-snapshot window takes of the rows (the auth component's 2c) -/

/-- **The applier row lends its core and the component's part** (`srvApplyKV_core` off,
`srvApplyKVOn_coreA` on). -/
theorem srvApplyKVC_coreA (C : AuthC) (s : Loc) (E : apply.AEnv GF) (γw : GName) (x : apply.ApplyKV)
    (st : auth.AuthState) :
    srvApplyKVC (GF := GF) C s E γw x st ⊢
      ∃ ua, srvApplyKVCore s E γw x ua ∗ acRes C s E ua st ∗
        (srvApplyKVCore s E γw x ua -∗ acRes C s E ua st -∗ srvApplyKVC C s E γw x st) := by
  iintro H
  iunfold srvApplyKVC at H
  icases H with ⟨%ua, Hua, #Hap, Hkv, Hbo, Hra, Har, Hw, Hrd⟩
  iexists ua
  isplitl [Hua Hkv Hbo Hra Hw]
  · iunfold srvApplyKVCore
    isplitl [Hua]
    · iexact Hua
    isplitr
    · iexact Hap
    isplitl [Hkv]
    · iexact Hkv
    isplitl [Hbo]
    · iexact Hbo
    isplitl [Hra]
    · iexact Hra
    iexact Hw
  isplitl [Har]
  · iexact Har
  iintro Hc Har
  iunfold srvApplyKVCore at Hc
  icases Hc with ⟨Hua, -, Hkv, Hbo, Hra, Hw⟩
  iunfold srvApplyKVC
  iexists ua
  isplitl [Hua]
  · iexact Hua
  isplitr
  · iexact Hap
  isplitl [Hkv]
  · iexact Hkv
  isplitl [Hbo]
  · iexact Hbo
  isplitl [Hra]
  · iexact Hra
  isplitl [Har]
  · iexact Har
  isplitl [Hw]
  · iexact Hw
  iexact Hrd

/-- **The apply thread's compaction revision is `-1` with auth on** (R6, 2026-11-07:
`srvApplyKVOn_crev` at the component; `merged_imageC`'s `hcr`). -/
theorem srvApplyKVC_crev (C : AuthC) (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (γw : GName) (x : apply.ApplyKV)
    (sa : auth.AuthState) :
    isServerM (GF := GF) C.isOn s γ ci TM E ρ γr ⊢ srvApplyKVC C s E γw x sa ={⊤}=∗
      srvApplyKVC C s E γw x sa ∗ ⌜C.isOn = true → x.crev = -1⌝ := by
  cases C with
  | off =>
    iintro - H
    iframe H
    ipureintro; intro h; cases h
  | on γa =>
    have hK := srvApplyKVM_C (GF := GF) (.on γa) s E γw x sa
    simp only [AuthC.isOn, srvApplyKVM_true] at hK
    dsimp only [AuthC.isOn]
    iintro #Hsrv H
    ihave H : srvApplyKVOn s E γw x sa $$ [H]
    · iapply hK.2 $$ H
    iunfold isServerM at Hsrv
    icases Hsrv with ⟨-, -, -, Hat, -, -⟩
    iunfold srvAtomicsM at Hat
    icases Hat with ⟨-, -, Hki⟩
    ihave #Hinvs := srvKVInvsM_true s E γr $$ Hki
    imod srvApplyKVOn_crev s E γr srvAuthSt0 γw x sa $$ Hinvs H with ⟨H, %hc⟩
    imodintro
    isplitl [H]
    · iapply hK.1 $$ H
    ipureintro; intro _; exact hc

/-- **The merged image's certificate** (`merged_image` off, `merged_imageOn` on): the window's
image (`mergedImgM`, R4, 2026-11-07: until then the observation `mergedObsM` and the KV log's
receipt), with the component's buckets at its image (`acImg`, `acBkts`). With auth on, the apply
thread's compaction revision `-1` (`hcr`: `merged_imageOn`'s, `srvApplyKVOn_crev`). -/
theorem merged_imageC (C : AuthC) (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (ai : w64) (A : List EntryModel)
    (x : apply.ApplyKV) (sa : auth.AuthState) (D : backend.Data) (hC : E.authMode = C.mode)
    (hlen : uint.Z ai = A.length) (h0 : γr.kv.c0 = W64 0 ∧ γr.kv.log0 = [[], []])
    (hcr : C.isOn = true → x.crev = -1) :
    mergedImgM E.authMode E.lg γr ai A x.log x.crev D ∗
      ⌜∃ r, acImg C sa r ∧ ∀ n, acBkts C n → D.lookup n = r.lookup n⌝ ∗
      isServerM C.isOn s γ ci TM E ρ γr ∗
      kvAppliedM C.isOn γr.raft γr.kv srvAuthSt0 A x sa ⊢
      |={⊤}=> kvAppliedM C.isOn γr.raft γr.kv srvAuthSt0 A x sa ∗
        □ (srvNet (GF := GF) γr.raft.raft).img ai D := by
  cases C with
  | off =>
    dsimp only [AuthC.isOn]
    rw [kvAppliedM_false, isServerM_false]
    iintro ⟨#Hmi, -, #Hsrv, Hka⟩
    iapply (merged_image s γ ci TM E ρ γr ai A x D (by simpa [AuthC.mode] using hC) hlen h0)
    iframe Hmi Hsrv Hka
  | on γa =>
    dsimp only [AuthC.isOn]
    rw [kvAppliedM_true]
    iintro ⟨#Hmi, %hobs, #Hsrv, Hka⟩
    iapply (merged_imageOn s γ ci TM E ρ γr γa ai A x sa D (by simpa [AuthC.mode] using hC) hlen h0
      (hcr rfl))
    iframe Hmi Hsrv Hka
    ipureintro
    obtain ⟨r, hQ, hr⟩ := hobs
    exact authBucketsAt_congr sa D r hr hQ

/-- `kvRunM`'s parts: the KV's ghost state at the mode's and the start's indices. -/
theorem kvRunM_split (on : Bool) (γr : ReadNames) (ai₀ c₀ : w64) (A : List EntryModel)
    (x : apply.ApplyKV) (st : auth.AuthState) :
    kvRunM (GF := GF) on γr ai₀ c₀ A x st =
      iprop(kvAppliedM on γr.raft γr.kv srvAuthSt0 A x st ∗ ⌜γr.kv.c0 = c₀ ∧ γr.raft.ai0 = ai₀⌝) := by
  cases on <;> rfl

theorem kvRunM_false (γr : ReadNames) (ai₀ c₀ : w64) (A : List EntryModel) (x : apply.ApplyKV)
    (st : auth.AuthState) : kvRunM (GF := GF) false γr ai₀ c₀ A x st = kvRun γr ai₀ c₀ A x := rfl

theorem kvRunM_true (γr : ReadNames) (ai₀ c₀ : w64) (A : List EntryModel) (x : apply.ApplyKV)
    (st : auth.AuthState) : kvRunM (GF := GF) true γr ai₀ c₀ A x st = kvRunAtOn γr ai₀ c₀ A x st :=
  rfl

/-- **The server's view's names** (`isServer_lg`'s): the request names' reads the view's, and off
the KV names' lease mode the environment's. -/
theorem isServerC_lg (K : AuthC) (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) :
    isServerC (GF := GF) K s γ ci TM E ρ γr ⊢ ⌜ρ.rd = γr ∧ (K.isOn = false → γr.kv.lg = E.lg)⌝ := by
  refine (isServerM_C (GF := GF) K s γ ci TM E ρ γr).2.trans ?_
  cases K with
  | off =>
    refine (isServer_lg s γ ci TM E ρ γr).trans ?_
    iintro %h; ipureintro; exact ⟨h.1, fun _ => h.2⟩
  | on γa =>
    iintro H
    iunfold isServerM at H
    icases H with ⟨%h, -⟩
    ipureintro; exact ⟨h, fun h' => by cases h'⟩

theorem isServerC_lm (K : AuthC) (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) :
    isServerC (GF := GF) K s γ ci TM E ρ γr ⊢ ⌜ρ.rd = γr ∧ (K.isOn = false → γr.kv.lm = E.lm)⌝ := by
  refine (isServerM_C (GF := GF) K s γ ci TM E ρ γr).2.trans ?_
  cases K with
  | off =>
    refine (isServer_lm s γ ci TM E ρ γr).trans ?_
    iintro %h; ipureintro; exact ⟨h.1, fun _ => h.2⟩
  | on γa =>
    iintro H
    iunfold isServerM at H
    icases H with ⟨%h, -⟩
    ipureintro; exact ⟨h, fun h' => by cases h'⟩

/-- **A first start's `Hsnap` gives the restart form at `A₀ = []`**. -/
theorem rnSnapOnceR_first (rg : GName) (cl : Cluster) (nk : GName) (ms : Loc) (γs : MemStorNames)
    (i t : w64) (γ : ServerRaftNames) :
    rnSnapOnce (GF := GF) rg cl nk ms γs i t ⊢ rnSnapOnceR rg cl nk ms γs i t γ [] := by
  iintro H
  iunfold rnSnapOnceR
  iintro %Φ HΦ
  iunfold rnSnapOnce at H
  iapply H
  inext
  iintro %sn %pm %cs %sv %h Hsn Hpm Hcs #Hok Hnone Hinv
  ihave #Hca : epCsAt γ [] cs $$ []
  · iunfold epCsAt; ileft; ipureintro; rfl
  ihave Hlb : iprop(|==> memSnapLb γs 0) $$ [Hnone]
  · iapply (memSnapNone_open (GF := GF) γs) $$ Hnone
  iapply HΦ $$ %sn %pm %cs %sv %h Hsn Hpm Hcs Hok Hca Hlb Hinv

/-- **A first start's `applyStartC` is the restart form at `A₀ = []`** (Go's index `ai₀`). -/
theorem srvRestartAtR_first (C : AuthC) (s : Loc) (γ : ApplyNames) (ci : Loc) (b : GoInterface)
    (E : apply.AEnv GF) (γr : ReadNames) (ai₀ c₀ : w64) (x₀ : apply.ApplyKV) (γw : GName) :
    applyStartC (GF := GF) C s γ ci b E γr ai₀ c₀ x₀ γw ∗ ⌜c₀ = ai₀⌝ ⊢
      srvRestartAtR C s γ ci b E γr ai₀ c₀ x₀ γw [] ai₀ := by
  iintro ⟨H, %hc⟩
  iunfold applyStartC at H
  icases H with ⟨%st₀, %a, %t, %f, Hth, %Hok, Hbe, Hca, Hlg, Hbm, Hwg, Hrdk, Hkv, Hao, Hal, Hkr, Hrest,
    Hap, Hfs, Htok, Hso⟩
  iunfold srvRestartAtR
  iexists st₀, a, t, f, ai₀, srvAuthSt0
  iframe Hth Hbe Hca Hlg Hbm Hwg Hrdk Hkv Hao Hal Hkr Hrest Hap Hfs Htok Hso
  ipureintro
  exact ⟨Hok.1, by rw [← hc]; exact Hok.2, by simp⟩


/-- **A first start's conjuncts give A9's** (`A₀ = []`): today's `%HEr` (with A6's `γn.a0 = []`),
`Hsnap` and `Hstart`. -/
theorem srvRunRestartR_first (C : AuthC) (s : Loc) (γ : ApplyNames) (ci : Loc) (b : GoInterface)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (Er : RNEnv GF) (γn : RNNames)
    (ai₀ at₀ c₀ : w64) (x₀ : apply.ApplyKV) (γw : GName)
    (hEr : Er.C = srvCM C.isOn ρ E ai₀ c₀ x₀ ∧ Er.γr = γr ∧
      (uint.Z c₀ ≤ uint.Z ai₀ ∧ γn.pre = [] ∧ ai₀ = W64 0) ∧ γn.a0 = []) :
    (∃ ms : Loc, rnRaftStorageAddr (srvRAddr s) ↦□ ms ∗
        rnSnapOnce (GF := GF) γn.node.reg γn.node.cl γn.key ms γn.γs ai₀ at₀) ∗
      applyStartC C s γ ci b E γr ai₀ c₀ x₀ γw ⊢
    srvRunRestartR C s γ ci b E ρ γr Er γn ai₀ at₀ c₀ x₀ γw := by
  obtain ⟨h1, h2, ⟨hc, hp, ha⟩, h4⟩ := hEr
  have hc0 : c₀ = ai₀ := by subst ha; word
  iintro ⟨⟨%ms, #Hms, Hsnap⟩, Hst⟩
  iunfold srvRunRestartR
  iexists []
  isplitr
  · ipureintro
    refine ⟨h1, h2, ⟨hc, hp, ha⟩, h4, by simp, ?_⟩
    subst ha; simp <;> word
  isplitl [Hsnap]
  · iexists ms
    iframe Hms
    iapply rnSnapOnceR_first $$ Hsnap
  iapply srvRestartAtR_first $$ [Hst]
  iframe Hst
  ipureintro; exact hc0

end bridges

end EtcdGrove
end Perennial
