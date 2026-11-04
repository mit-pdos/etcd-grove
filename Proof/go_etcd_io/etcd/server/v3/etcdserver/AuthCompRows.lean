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
  | false => (γr.kv.cmp = E.cmp ∧ (mvcc.kbCmpM E.γ.kb ↔ E.cmp = true)) ∧
             (γr.kv.cret = E.cret ∧ γr.kv.lg = E.lg)
  | true => True

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
    ∃ (w : GoInterface) (RD : IProp GF), srvWAddr s ↦□ w ∗
      waitOk w RD (fun ot id => waitRegdOpt γw id ot) (fun ot id => waitGoneOpt γw id ot) ∗ RD)

/-- **The apply thread's KV invariants** (`srvKVInvsM`'s): the mode's KV and certificates'
invariants from `srvAuthSt0`, the raft log's, the KV names' ties (off's, `kvNameTiesM`), the modes
the component needs (`acModesOk`: on, compaction and lease grants off), and the component's
invariants (`acInv`). -/
def srvKVInvsC (C : AuthC) (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) : IProp GF :=
  iprop(kvInvM C.isOn γr.raft γr.kv srvAuthSt0 ∗ kvCertInvM C.isOn γr.raft γr.kv srvAuthSt0 ∗
    srvRaftLogInv γr.raft ∗ ⌜E.γ.cok = γr.kv.cok⌝ ∗ mvcc.crevPermIs E.γ (kvCmpPermit γr.kv) ∗
    ⌜kvNameTiesM C.isOn E γr⌝ ∗ ⌜acModesOk C E.cmp γr.kv.lg⌝ ∗ acInv C s E γr)

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
    ciApplying ci a t ∗ srvLgReader s ∗ srvBemuReaderAt s E.γbe ∗ srvBeOwn s E ∗
    (∃ ua : GoInterface, srvUberApplyAddr s ↦ ua ∗ acRes C s E ua srvAuthSt0 ∗
      apply.applierFor ua E ∗ apply.applyKV E ua x₀) ∗
    revAuth E x₀.log ∗
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
      (uint.Z c₀ ≤ uint.Z ai₀ ∧ γn.pre = [] ∧ ai₀ = W64 0)⌝ ∗
    -- (2026-10-30, the repair) the apply side's half of the node's running token
    "Hrunh" ∷ (letI := srvStor (GF := GF) γn.node; nodeRunning γn.nl γn.node.cl srvClusterN (1 : Qp).half) ∗
    -- (2026-10-31) the WAL's open token: the apply side's half (its disk snapshot's `SaveSnap`, which
    -- `run` gives the raft loop with `raftNode.stop`) and the loop's (`raftNode.start`'s); the disk
    -- cooperating (`storage.diskOk`, `NewServer`'s premise)
    "Hwth" ∷ rnWalTokA γn (srvRAddr s) (1 : Qp).half ∗ "Hwtl" ∷ rnWalTokL γn (srvRAddr s) ∗
    "%Hdisk" ∷ ⌜storage.diskOk⌝ ∗
    -- (2026-11-02, the lease-grant plan's D2) in a cluster that grants leases, the open
    -- cases (`srvGrantOpen`, `NewServer`'s precondition)
    "%Hslg" ∷ ⌜γr.kv.lg = true → lease.leasesNoExpiry ∧ srvGrantOpen (GF := GF)⌝ ∗
    "%Hρrd" ∷ ⌜ρ.rd = γr⌝ ∗
    -- (J8b, 2026-11-01) the server's member id is the raft node's (`applyAll.specSnap`'s member id
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
    "Hsnapb" ∷ srvSnapBoot s ci E γr)

/-- **The apply thread's resources when `run` starts** (`applyStart` off, `applyStartOn` on). -/
def applyStartC (C : AuthC) (s : Loc) (γ : ApplyNames) (ci : Loc) (b : GoInterface) (E : apply.AEnv GF)
    (γr : ReadNames) (ai₀ c₀ : w64) (x₀ : apply.ApplyKV) (γw : GName) : IProp GF :=
  iprop(∃ (st₀ : ApplyState) (a t : w64) (f : Bool),
    applyThread γ st₀ ∗ ⌜loopOk γ st₀ ai₀ ∧ c₀ = ciEff γ st₀.k⌝ ∗ applyBackend γ ci b ∗
    ciApplying ci a t ∗ srvLgReader s ∗ srvBemuReaderAt s E.γbe ∗ srvWgReader s ∗ srvApplyKVC C s E γw x₀ srvAuthSt0 ∗
    srvAppliedOwn γr ai₀ ∗ appliedLogAt γr ai₀ x₀.log ∗ kvRunM C.isOn γr ai₀ c₀ [] x₀ srvAuthSt0 ∗ srvRest E γr [] ∗
    srvApRes s γr [] ∗ srvForceSnapAddr s ↦ f ∗ acTok C (ciEff γ st₀.k) ∗
    -- (D22 J1b, 2026-10-31) what each snapshot install takes and gives back
    srvSnapOwn s ci E γr ai₀)

/-- **What `run` needs** (`isServerRun` off, `isServerRunOn` on; the stop requests' `SP` and the
done channel's `DQ` as `isServerRun`'s). -/
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
    -- (D43 M3, 2026-10-25) in raft's dynamic mode a fresh start: no entry replayed
    "%HEr" ∷ ⌜Er.C = srvCM C.isOn ρ E ai₀ c₀ x₀ ∧ Er.γr = γr ∧
      (uint.Z c₀ ≤ uint.Z ai₀ ∧ γn.pre = [] ∧ ai₀ = W64 0)⌝ ∗
    -- (2026-10-30, the repair) the apply side's half of the node's running token
    "Hrunh" ∷ (letI := srvStor (GF := GF) γn.node; nodeRunning γn.nl γn.node.cl srvClusterN (1 : Qp).half) ∗
    -- (2026-10-31) the WAL's open token: the apply side's half (its disk snapshot's `SaveSnap`, which
    -- `run` gives the raft loop with `raftNode.stop`) and the loop's (`raftNode.start`'s); the disk
    -- cooperating (`storage.diskOk`, `NewServer`'s premise)
    "Hwth" ∷ rnWalTokA γn (srvRAddr s) (1 : Qp).half ∗ "Hwtl" ∷ rnWalTokL γn (srvRAddr s) ∗
    "%Hdisk" ∷ ⌜storage.diskOk⌝ ∗
    -- (2026-11-02, the lease-grant plan's D2) in a cluster that grants leases, the open
    -- cases (`srvGrantOpen`, `NewServer`'s precondition)
    "%Hslg" ∷ ⌜γr.kv.lg = true → lease.leasesNoExpiry ∧ srvGrantOpen (GF := GF)⌝ ∗
    -- (2026-10-31, #11) the KV the snapshot commits (`start`'s `srvReadBuilt`)
    "#Hkvf" ∷ (∃ kv : GoInterface, srvKVAddr s ↦□ kv ∗ txn.isKV kv E.s E.γ) ∗
    "#Hrf" ∷ srvRunFieldsAt s γr γg γcx v SP ∗
    "Hsnap" ∷ (∃ ms : Loc, rnRaftStorageAddr (srvRAddr s) ↦□ ms ∗ rnSnapOnce γn.node.reg γn.node.cl γn.key ms γn.γs ai₀ at₀) ∗
    "Hloop" ∷ rnLoopTok γn [] ∗ "Hsend" ∷ Er.S ∗ "Happly" ∷ rnApplyTok γn [] ∗ "Hrdone" ∷ rnDoneTok γn (srvRAddr s) ∗
    "Hcomm" ∷ (∃ c : w64, srvCommittedOwn γr c) ∗
    "Hdc" ∷ ownBroadcastChan v.done γd DQ .Pending ∗
    "Hclose" ∷ token γg.close ∗
    "Hstart" ∷ applyStartC C s γ ci b E γr ai₀ c₀ x₀ ρ.wait ∗
    "Hlr" ∷ srvLgReader s ∗
    -- (2026-10-19, D21 M3) with its counter, the apply thread's tokens taken through `ai₀`
    "#HWB" ∷ (∃ γp : GName, srvWTPool E γp ∗ srvWTAt γp ai₀) ∗
    -- (2026-10-26, D22 J1a) what the snapshot path takes of the construction (`SnapRO.lean`): its
    -- persistent bundle; (D22 J1b, 2026-10-31) the counter's authority and the stocks in `applyStart`
    "#Hsnapb" ∷ (∃ γt : GName, srvSnapRO s ci E γr γt) ∗
    -- (J8a-3, 2026-11-01) the two configuration fields `start` writes, read-only from then on:
    -- with `srvSnapRO`'s rebuild, the whole configuration read-only (`specSnap`'s `srvCfgAddr s ↦□`)
    "#Hsncfg" ∷ (∃ sc scu : w64, srvCfgFieldAddr s go!"SnapshotCount" ↦□ sc ∗
      srvCfgFieldAddr s go!"SnapshotCatchUpEntries" ↦□ scu))

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
      acModesOk]
    constructor
    · iintro ⟨#H1, #H2, #H3, %Hc, %Ht1, %Ht2, #Hp⟩
      iframe H1 H2 H3 Hp
      isplitr
      · ipureintro; exact Hc
      isplitr
      · ipureintro; exact ⟨Ht1, Ht2⟩
      isplitr
      · ipureintro; trivial
      iapply acInv_off
    · iintro ⟨#H1, #H2, #H3, %Hc, #Hp, %Ht, -, -⟩
      iframe H1 H2 H3 Hp
      isplitr
      · ipureintro; exact Hc
      isplitr
      · ipureintro; exact Ht.1
      ipureintro; exact Ht.2
  | on γa =>
    dsimp only [AuthC.isOn, srvKVInvsM, srvKVInvsC, srvKVInvsOn, kvInvM, kvCertInvM, kvNameTiesM,
      acModesOk]
    constructor
    · iintro ⟨⟨#H1, #H2, #H3, #Htie, %Hc, #Hp, %Hm⟩, #Hu⟩
      iframe H1 H2 H3 Hp
      isplitr
      · ipureintro; exact Hc
      isplitr
      · ipureintro; trivial
      isplitr
      · ipureintro; exact Hm
      iapply (acInv_on (.on γa) γa rfl s E γr).2
      iframe Htie Hu
    · iintro ⟨#H1, #H2, #H3, %Hc, #Hp, -, %Hm, #Hi⟩
      ihave ⟨#Htie, #Hu⟩ := (acInv_on (.on γa) γa rfl s E γr).1 $$ Hi
      iframe H1 H2 H3 Hp Htie Hu
      isplitr
      · ipureintro; exact Hc
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
  · iintro ⟨%st₀, %a, %t, %f, Hth, %Hok, Hbe, Hca, Hlg, Hbm, Hbo, ⟨%ua, Hua, Hfor, Hakv⟩, Hra,
      Har, Hao, Hal, Hkr, Hrest, Hap, Hfs⟩
    iexists st₀, a, t, f
    iframe Hth Hbe Hca Hlg Hbm Hbo Hra Hao Hal Hkr Hrest Hap Hfs
    isplitr
    · ipureintro; exact Hok
    iexists ua; iframe Hua Har Hfor Hakv
  · iintro ⟨%st₀, %a, %t, %f, Hth, %Hok, Hbe, Hca, Hlg, Hbm, Hbo, ⟨%ua, Hua, Har, Hfor, Hakv⟩, Hra,
      Hao, Hal, Hkr, Hrest, Hap, Hfs, -⟩
    iexists st₀, a, t, f
    iframe Hth Hbe Hca Hlg Hbm Hbo Hra Har Hao Hal Hkr Hrest Hap Hfs
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
  · iintro ⟨%st₀, %a, %t, %f, Hth, %Hok, Hbe, Hca, Hlg, Hbm, Hbo, ⟨%ua, Hua, Hub, Hfor, Hakv⟩, Hra,
      Har, Hao, Hal, Hkr, Hrest, Hap, Hfs, Htok⟩
    iexists st₀, a, t, f
    iframe Hth Hbe Hca Hlg Hbm Hbo Hra Hao Hal Hrest Hap Hfs Htok
    isplitr
    · ipureintro; exact Hok
    isplitl [Hua Hub Har Hfor Hakv]
    · iexists ua; iframe Hua Hub Har Hfor Hakv
    iapply (kvRunM_nil_on γr ai₀ c₀ x₀).1 $$ Hkr
  · iintro ⟨%st₀, %a, %t, %f, Hth, %Hok, Hbe, Hca, Hlg, Hbm, Hbo, ⟨%ua, Hua, ⟨Hub, Har⟩, Hfor, Hakv⟩,
      Hra, Hao, Hal, Hkr, Hrest, Hap, Hfs, Htok⟩
    iexists st₀, a, t, f
    iframe Hth Hbe Hca Hlg Hbm Hbo Hra Har Hao Hal Hrest Hap Hfs Htok
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
    isServerBuiltM (GF := GF) C.isOn s γ ci TM E ρ γr Er γn b ai₀ at₀ c₀ x₀ N ⊣⊢
      isServerBuiltC C s γ ci TM E ρ γr Er γn b ai₀ at₀ c₀ x₀ N := by
  have hK := srvKVInvsM_C (GF := GF) C s E γr
  cases C with
  | off =>
    have hA := applyBuilt_C (GF := GF) s γ ci b E γr ai₀ c₀ x₀ hC
    dsimp only [AuthC.isOn, srvKVInvsM] at hK
    unfold isServerBuiltM isServerBuilt isServerBuiltC
    simp only [AuthC.isOn, srvReqBuiltM_false, srvAppliedInvM_false, srvCM_false]
    constructor
    · iintro ⟨#Hci, #Hfb, #Hreqb, #Hrdb, #Hrunb, Hcrun, #Hsab, #Hai, #Hkvi, #Hti, #Hci', #Hrn, #HEr, Hrunh, Hwth, Hwtl, #Hdisk, #Hslg, #Hρrd, #Hmid, #Hmidc, #HmetaSnap, Hsnap, Hloop, Hsend, Happly, Hrdone, #HNR, #Hcv, #Hcci, #Hwci, #Hbound, Hw, Haw, Hdone, Hstop, Hstopping, Hctx, Hcancel, Hread, Hlc, Hsc, Hscu, Hwg, HwgMu, Hcomm, Hnot, Happ, Hlr, Hlrl, Hfcr, HWB, Hwtok, Hsnapb⟩
      iframe Hci Hfb Hreqb Hrdb Hrunb Hcrun Hsab Hai Hti Hci' Hrn HEr Hrunh Hwth Hwtl Hdisk Hslg Hρrd Hmid Hmidc HmetaSnap Hsnap Hloop Hsend Happly Hrdone HNR Hcv Hcci Hwci Hbound Hw Haw Hdone Hstop Hstopping Hctx Hcancel Hread Hlc Hsc Hscu Hwg HwgMu Hcomm Hnot Hlr Hlrl Hfcr HWB Hwtok Hsnapb
      isplitr
      · iapply hK.1 $$ Hkvi
      iapply hA.1 $$ Happ
    · iintro ⟨#Hci, #Hfb, #Hreqb, #Hrdb, #Hrunb, Hcrun, #Hsab, #Hai, #Hkvi, #Hti, #Hci', #Hrn, #HEr, Hrunh, Hwth, Hwtl, #Hdisk, #Hslg, #Hρrd, #Hmid, #Hmidc, #HmetaSnap, Hsnap, Hloop, Hsend, Happly, Hrdone, #HNR, #Hcv, #Hcci, #Hwci, #Hbound, Hw, Haw, Hdone, Hstop, Hstopping, Hctx, Hcancel, Hread, Hlc, Hsc, Hscu, Hwg, HwgMu, Hcomm, Hnot, Happ, Hlr, Hlrl, Hfcr, HWB, Hwtok, Hsnapb⟩
      iframe Hci Hfb Hreqb Hrdb Hrunb Hcrun Hsab Hai Hti Hci' Hrn HEr Hrunh Hwth Hwtl Hdisk Hslg Hρrd Hmid Hmidc HmetaSnap Hsnap Hloop Hsend Happly Hrdone HNR Hcv Hcci Hwci Hbound Hw Haw Hdone Hstop Hstopping Hctx Hcancel Hread Hlc Hsc Hscu Hwg HwgMu Hcomm Hnot Hlr Hlrl Hfcr HWB Hwtok Hsnapb
      isplitr
      · iapply hK.2 $$ Hkvi
      iapply hA.2 $$ Happ
  | on γa =>
    have hA := applyBuiltOn_C (GF := GF) γa s γ ci b E γr ai₀ c₀ x₀ hC
    dsimp only [AuthC.isOn] at hK
    unfold isServerBuiltM isServerBuiltOn isServerBuiltC
    simp only [AuthC.isOn]
    constructor
    · iintro ⟨#Hci, #Hfb, #Hreqb, #Hrdb, #Hrunb, Hcrun, #Hsab, #Hai, #Hkvi, #Hti, #Hci', #Hrn, #HEr, Hrunh, Hwth, Hwtl, #Hdisk, #Hslg, #Hρrd, #Hmid, #Hmidc, #HmetaSnap, Hsnap, Hloop, Hsend, Happly, Hrdone, #HNR, #Hcv, #Hcci, #Hwci, #Hbound, Hw, Haw, Hdone, Hstop, Hstopping, Hctx, Hcancel, Hread, Hlc, Hsc, Hscu, Hwg, HwgMu, Hcomm, Hnot, Happ, Hlr, Hlrl, Hfcr, HWB, Hwtok, Hsnapb⟩
      iframe Hci Hfb Hreqb Hrdb Hrunb Hcrun Hsab Hai Hti Hci' Hrn HEr Hrunh Hwth Hwtl Hdisk Hslg Hρrd Hmid Hmidc HmetaSnap Hsnap Hloop Hsend Happly Hrdone HNR Hcv Hcci Hwci Hbound Hw Haw Hdone Hstop Hstopping Hctx Hcancel Hread Hlc Hsc Hscu Hwg HwgMu Hcomm Hnot Hlr Hlrl Hfcr HWB Hwtok Hsnapb
      isplitr
      · iapply hK.1 $$ Hkvi
      iapply hA.1 $$ Happ
    · iintro ⟨#Hci, #Hfb, #Hreqb, #Hrdb, #Hrunb, Hcrun, #Hsab, #Hai, #Hkvi, #Hti, #Hci', #Hrn, #HEr, Hrunh, Hwth, Hwtl, #Hdisk, #Hslg, #Hρrd, #Hmid, #Hmidc, #HmetaSnap, Hsnap, Hloop, Hsend, Happly, Hrdone, #HNR, #Hcv, #Hcci, #Hwci, #Hbound, Hw, Haw, Hdone, Hstop, Hstopping, Hctx, Hcancel, Hread, Hlc, Hsc, Hscu, Hwg, HwgMu, Hcomm, Hnot, Happ, Hlr, Hlrl, Hfcr, HWB, Hwtok, Hsnapb⟩
      iframe Hci Hfb Hreqb Hrdb Hrunb Hcrun Hsab Hai Hti Hci' Hrn HEr Hrunh Hwth Hwtl Hdisk Hslg Hρrd Hmid Hmidc HmetaSnap Hsnap Hloop Hsend Happly Hrdone HNR Hcv Hcci Hwci Hbound Hw Haw Hdone Hstop Hstopping Hctx Hcancel Hread Hlc Hsc Hscu Hwg HwgMu Hcomm Hnot Hlr Hlrl Hfcr HWB Hwtok Hsnapb
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
  · iintro ⟨%st₀, %a, %t, %f, Hth, %Hok, Hbe, Hca, Hlg, Hbm, Hwg, Hkv, Hao, Hal, Hkr, Hrest, Hap,
      Hfs, Hso⟩
    iexists st₀, a, t, f
    iframe Hth Hbe Hca Hlg Hbm Hwg Hao Hal Hkr Hrest Hap Hfs Hso
    isplitr
    · ipureintro; exact Hok
    iapply hK.1 $$ Hkv
  · iintro ⟨%st₀, %a, %t, %f, Hth, %Hok, Hbe, Hca, Hlg, Hbm, Hwg, Hkv, Hao, Hal, Hkr, Hrest, Hap,
      Hfs, -, Hso⟩
    iexists st₀, a, t, f
    iframe Hth Hbe Hca Hlg Hbm Hwg Hao Hal Hkr Hrest Hap Hfs Hso
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
  · iintro ⟨%st₀, %a, %t, %f, Hth, %Hok, Hbe, Hca, Hlg, Hbm, Hwg, Hkv, Hao, Hal, Hkr, Hrest, Hap,
      Hfs, Htok, Hso⟩
    iexists st₀, a, t, f
    iframe Hth Hbe Hca Hlg Hbm Hwg Hao Hal Hkr Hrest Hap Hfs Htok Hso
    isplitr
    · ipureintro; exact Hok
    iapply hK.1 $$ Hkv
  · iintro ⟨%st₀, %a, %t, %f, Hth, %Hok, Hbe, Hca, Hlg, Hbm, Hwg, Hkv, Hao, Hal, Hkr, Hrest, Hap,
      Hfs, Htok, Hso⟩
    iexists st₀, a, t, f
    iframe Hth Hbe Hca Hlg Hbm Hwg Hao Hal Hkr Hrest Hap Hfs Htok Hso
    isplitr
    · ipureintro; exact Hok
    iapply hK.2 $$ Hkv

/-- **What `run` needs, off, is the off component's.** -/
theorem isServerRun_C (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (Er : RNEnv GF) (γn : RNNames)
    (γg : GoNames) (γcx : context.ContextNames) (γd : ChanNames) (v : RunFields)
    (b : GoInterface) (ai₀ at₀ c₀ : w64) (x₀ : apply.ApplyKV) (SP DQ : IProp GF)
    (hC : E.authMode = AuthC.off.mode) :
    isServerRun (GF := GF) s γ ci TM E ρ γr Er γn γg γcx γd v b ai₀ at₀ c₀ x₀ SP DQ ⊣⊢
      isServerRunC .off s γ ci TM E ρ γr Er γn γg γcx γd v b ai₀ at₀ c₀ x₀ SP DQ := by
  have hS := isServerM_C (GF := GF) .off s γ ci TM E ρ γr
  have hA := applyStart_C (GF := GF) s γ ci b E γr ai₀ c₀ x₀ ρ.wait hC
  dsimp only [AuthC.isOn] at hS
  rw [isServerM_false] at hS
  unfold isServerRun isServerRunC
  simp only [AuthC.isOn, srvCM_false]
  constructor
  · iintro ⟨#Hsrv, #Hsa, #Hmid, #HmetaSnap, #Hrn, #HEr, Hrunh, Hwth, Hwtl, #Hdisk, #Hslg, #Hkvf, #Hrf, Hsnap, Hloop, Hsend, Happly, Hrdone, Hcomm, Hdc, Hclose, Hstart, Hlr, #HWB, #Hsnapb, #Hsncfg⟩
    iframe Hsa Hmid HmetaSnap Hrn HEr Hrunh Hwth Hwtl Hdisk Hslg Hkvf Hrf Hsnap Hloop Hsend Happly Hrdone Hcomm Hdc Hclose Hlr HWB Hsnapb Hsncfg
    isplitr
    · iapply hS.1 $$ Hsrv
    isplitr
    · iapply acLessor_off
    iapply hA.1 $$ Hstart
  · iintro ⟨#Hsrv, #Hlnil, #Hsa, #Hmid, #HmetaSnap, #Hrn, #HEr, Hrunh, Hwth, Hwtl, #Hdisk, #Hslg, #Hkvf, #Hrf, Hsnap, Hloop, Hsend, Happly, Hrdone, Hcomm, Hdc, Hclose, Hstart, Hlr, #HWB, #Hsnapb, #Hsncfg⟩
    iframe Hsa Hmid HmetaSnap Hrn HEr Hrunh Hwth Hwtl Hdisk Hslg Hkvf Hrf Hsnap Hloop Hsend Happly Hrdone Hcomm Hdc Hclose Hlr HWB Hsnapb Hsncfg
    isplitr
    · iapply hS.2 $$ Hsrv
    iapply hA.2 $$ Hstart

/-- **What `run` needs, on, is the on component's** (`isServerRunOn` at `isServerRun`'s default
`SP`, `DQ`). -/
theorem isServerRunOn_C (γa : auth.AuthNames) (s : Loc) (γ : ApplyNames) (ci : Loc)
    (TM : MetaCI → IProp GF) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (Er : RNEnv GF)
    (γn : RNNames) (γg : GoNames) (γcx : context.ContextNames) (γd : ChanNames) (v : RunFields)
    (b : GoInterface) (ai₀ at₀ c₀ : w64) (x₀ : apply.ApplyKV)
    (hC : E.authMode = (AuthC.on γa).mode) :
    isServerRunOn (GF := GF) s γ ci TM E ρ γr Er γn γg γcx γd v b ai₀ at₀ c₀ x₀ ⊣⊢
      isServerRunC (.on γa) s γ ci TM E ρ γr Er γn γg γcx γd v b ai₀ at₀ c₀ x₀ := by
  have hS := isServerM_C (GF := GF) (.on γa) s γ ci TM E ρ γr
  have hA := applyStartOn_C (GF := GF) γa s γ ci b E γr ai₀ c₀ x₀ ρ.wait hC
  have hL := acLessor_on (GF := GF) (.on γa) γa rfl s
  dsimp only [AuthC.isOn] at hS
  unfold isServerRunOn isServerRunC
  simp only [AuthC.isOn]
  constructor
  · iintro ⟨#Hsrv, #Hlnil, #Hsa, #Hmid, #HmetaSnap, #Hrn, #HEr, Hrunh, Hwth, Hwtl, #Hdisk, #Hslg, #Hkvf, #Hrf, Hsnap, Hloop, Hsend, Happly, Hrdone, Hcomm, Hdc, Hclose, Hstart, Hlr, #HWB, #Hsnapb, #Hsncfg⟩
    iframe Hsa Hmid HmetaSnap Hrn HEr Hrunh Hwth Hwtl Hdisk Hslg Hkvf Hrf Hsnap Hloop Hsend Happly Hrdone Hcomm Hdc Hclose Hlr HWB Hsnapb Hsncfg
    isplitr
    · iapply hS.1 $$ Hsrv
    isplitr
    · iapply hL.2 $$ Hlnil
    iapply hA.1 $$ Hstart
  · iintro ⟨#Hsrv, #Hlnil, #Hsa, #Hmid, #HmetaSnap, #Hrn, #HEr, Hrunh, Hwth, Hwtl, #Hdisk, #Hslg, #Hkvf, #Hrf, Hsnap, Hloop, Hsend, Happly, Hrdone, Hcomm, Hdc, Hclose, Hstart, Hlr, #HWB, #Hsnapb, #Hsncfg⟩
    iframe Hsa Hmid HmetaSnap Hrn HEr Hrunh Hwth Hwtl Hdisk Hslg Hkvf Hrf Hsnap Hloop Hsend Happly Hrdone Hcomm Hdc Hclose Hlr HWB Hsnapb Hsncfg
    isplitr
    · iapply hS.2 $$ Hsrv
    isplitr
    · iapply hL.1 $$ Hlnil
    iapply hA.2 $$ Hstart

/-- **`start`'s construction premise from `NewServer`'s built part**, the component's
(`isServerBuilt_of_gapM` and the bridge). -/
theorem isServerBuiltC_of_gap (C : AuthC) (s : Loc) (γ : ApplyNames) (ci : Loc)
    (TM : MetaCI → IProp GF) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (Er : RNEnv GF)
    (γn : RNNames) (b : GoInterface) (ai₀ at₀ c₀ : w64) (x₀ : apply.ApplyKV) (N : Nat)
    (hC : E.authMode = C.mode) :
    srvBuiltG C.isOn s γ ci TM E ρ γr Er γn b ai₀ c₀ x₀ N ∗ srvBuildGap s γn ai₀ at₀ ⊢
      isServerBuiltC C s γ ci TM E ρ γr Er γn b ai₀ at₀ c₀ x₀ N :=
  (isServerBuilt_of_gapM C.isOn s γ ci TM E ρ γr Er γn b ai₀ at₀ c₀ x₀ N).trans
    (isServerBuiltM_C C s γ ci TM E ρ γr Er γn b ai₀ at₀ c₀ x₀ N hC).1

end bridges

end EtcdGrove
end Perennial
