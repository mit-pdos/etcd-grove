/-
**The built part at a restart** (restart S6, 2026-11-13; `/shared/tmp/restart-s56/plan.md` §2.1, D1):
`srvBuiltR`, what `NewServer.specR` (a restart's construction, auth off, no compaction) gives `start`,
with its law to `start`'s construction premise (`srvBuiltR_C`); the restart's apply state `restartKV`;
and the restart's pure facts for `NodeStartSpecR` (probe P6) and `bootstrap`'s restart contract (the
cluster version, `restart_clusterVerLogOk`). Lean-first (no Rocq counterpart).

`srvBuiltR` is `isServerBuiltC .off`'s rows less the stop's slot (`srvStop.slot`, which the post's
`srvStop.keep` gives, as at a first start): a first start's `srvBuiltG false` and `srvBuildGap` reach
`isServerBuiltC` only through `isServerBuiltC_of_gap`, which completes their KV rows (the
uber-applier's field into `#Hfb`, `srv.kv` into `#Hrdb`) and moves the first-start snapshot and
token rows into `HBr` at `P = []`; at a restart the construction gives the completed rows and `HBr`
at the restart point (`srvBuiltRestartR`, restart S4) directly.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthCompRows
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRestart
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapRecvFacts

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

/-- **The apply thread's KV state at a restart** (pure): the KV model of the image's applied log
`A` at the restarted names `γk`, the start's chain, the log's compaction revision: what `kvApplied`
asks of the state at `A` (`x.log = kvModel γk A`, `x.chain = γk.ch0`, `x.crev = crevOf γk A`). -/
def restartKV (γk : KVNames) (A : List EntryModel) : apply.ApplyKV :=
  ⟨kvModel γk A, γk.ch0, crevOf γk A⟩

set_option linter.unusedVariables false in
/-- **The built part at a restart** (see the file header): `isServerBuiltC .off`'s rows but the
stop's slot, the restart point `HBr` (`srvBuiltRestartR .off`: the storage's snapshot at Go's
`|P|`, the loop's and the apply side's tokens at `P`, the apply thread's resources at the backend's
log `γn.a0`) in place of a first start's `Hsnap`/`Hloop`/`Happly`/`Happ`, `HEr` without `γn.a0 = []`,
and `Hwpend` from `srvRestartRows`. (`N`, unused, as `isServerBuiltC`'s.) -/
def srvBuiltR (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (Er : RNEnv GF) (γn : RNNames)
    (b : GoInterface) (ai₀ at₀ c₀ : w64) (x₀ : apply.ApplyKV) (N : Nat) : IProp GF :=
  iprop("#Hci" ∷ isServerCI s γ ci ∗
    "#Hfb" ∷ (∃ v : SrvFields, srvFieldsBuilt s γ ci TM E v) ∗
    "#Hreqb" ∷ (∃ v : ReqFields, srvReqBuiltM false s E ρ v) ∗
    "#Hrdb" ∷ (∃ v : ReadFields, srvReadBuilt s E v) ∗
    "#Hrunb" ∷ (∃ v : RunFields, srvRunBuilt s v) ∗
    -- (M2, S4) the compactor's run, once (`start` spends it)
    "Hcrun" ∷ (∃ c : GoInterface, srvCompactorAddr s ↦□ c ∗ compactorRun s E c) ∗
    "#Hsab" ∷ srvApplyAllBuilt s γr ∗
    "#Hai" ∷ srvAppliedInvM false s E γr ∗
    "#Hkvi" ∷ srvKVInvsC .off s E γr ∗
    "#Hti" ∷ inv srvN (∃ t : w64, sync.atomic.ownUint64 (srvTermAddr s) (DFrac.own 1) t) ∗
    "#Hci'" ∷ srvCommittedInv s γr ∗
    "#Hrn" ∷ isRaftNode Er γn (srvRAddr s) ∗
    -- (restart S4, 2026-11-12: R2d'a A6's `γn.a0 = []`, a first start, dropped; the restart point's
    -- conjuncts are `HBr`'s)
    "%HEr" ∷ ⌜Er.C = srvCM false ρ E ai₀ c₀ x₀ ∧ Er.γr = γr ∧
      (uint.Z c₀ ≤ uint.Z ai₀ ∧ γn.pre = [] ∧ ai₀ = W64 0)⌝ ∗
    -- (R2d'a A7, A10 item 5, 2026-11-06; DRAFT, approved by 82) no merged snapshot sent at a new
    -- raft term while the replay window is pending (`srvWinPend`; corrected 2026-11-07: false
    -- whenever the restarted member is later elected and snapshots a follower, its `n` free; R2s
    -- (restart S7) removes it; S1 removed row 3, so the restart meaning is limited by this premise
    -- and by `rnRestartOk`'s graceful-only `|a0| ≤ commit0`; free at a first start, `srvWinPend_first`)
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
    -- (restart S4, 2026-11-12) the restart point: the storage's snapshot, the loop's and the apply
    -- side's tokens at `P`, the apply thread's resources at `γn.a0` (until then `Hsnap` (`rnSnapOnce`
    -- at `ai₀`), `Hloop`/`Happly` at `[]` and `Happ` (`applyBuiltC`), a first start's)
    "HBr" ∷ srvBuiltRestartR .off s γ ci b E γr γn ai₀ at₀ c₀ x₀ ∗
    "Hsend" ∷ Er.S ∗
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
    -- (auth-schema-fix S1 option A) the right to fire the token provider's readiness
    "Htpp" ∷ srvTpPend s E.authMode ∗
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
    "Hlr" ∷ srvLgReader s ∗
    "Hlrl" ∷ srvLgReader s ∗
    "Hfcr" ∷ (∃ n : Loc, srvFirstCommitAddr s ↦□ n ∗ notifyReader n) ∗
    "HWB" ∷ srvWTBudget E ∗
    "Hwtok" ∷ idWaitTok ρ.ids ∗
    -- (2026-10-26, D22 J1a) what the snapshot path takes of the construction (`SnapRO.lean`)
    "Hsnapb" ∷ srvSnapBoot s ci E γr γ)

end defs

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`start`'s construction premise from the restart's built part** and the stop's slot. -/
theorem srvBuiltR_C (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (Er : RNEnv GF) (γn : RNNames)
    (b : GoInterface) (ai₀ at₀ c₀ : w64) (x₀ : apply.ApplyKV) (N : Nat) :
    srvBuiltR (GF := GF) s γ ci TM E ρ γr Er γn b ai₀ at₀ c₀ x₀ N ∗ srvStop.slot s E γn Er ⊢
      isServerBuiltC .off s γ ci TM E ρ γr Er γn b ai₀ at₀ c₀ x₀ N := by
  iintro ⟨H, Hskeep⟩
  iunfold srvBuiltR at H
  iNamed H
  iunfold isServerBuiltC
  simp only [AuthC.isOn]
  iframe % # ∗

/-- (Probe P6) **The backend's conf state is within raft's bounds** (`NodeStartSpecR`'s size
premise): a conf state of the simple membership of `vs`, with fewer than `2^62` voters. -/
theorem restart_cs_bound (cs : ConfStateM) (vs : GSet w64) (h : confStateIs cs (Membership.simple vs))
    (hs : GMap.size vs < 2 ^ 62) :
    (cs.Voters'.length + cs.Learners'.length + cs.VotersOutgoing'.length +
      cs.LearnersNext'.length : Int) ≤ 2 ^ 62 := by
  obtain ⟨hv, hvo, hl, hln, -⟩ := h
  simp only [hv.length_eq, hvo.length_eq, hl.length_eq, hln.length_eq, GMap.length_elements,
    Membership.simple, GMap.size_empty]
  omega

/-- (Probe P6) **The node's index facts at `A₀ := A`** (`NodeStartSpecR`'s): from the image's
`σ.b ≤ i ≤ σ.commit` (`wal.stopImage`), `bootLen ≤ i` and `i = |A|` (its start index `0`): `σ.b ≤ |A|`,
`|A| ≤ σ.commit` (graceful-only: it feeds `rnRestartOk`'s marked conjunct only) and
`bootLen ≤ σ.commit` (through the same fact). -/
theorem restart_idx (σ : StorContents) (i ai0 : w64) (A : List EntryModel) (bl : Nat)
    (hi : uint.Z i = uint.Z ai0 + A.length) (h0 : ai0 = W64 0)
    (hb : σ.b ≤ uint.nat i) (hc : uint.nat i ≤ σ.commit) (hbl : bl ≤ uint.nat i) :
    σ.b ≤ A.length ∧ A.length ≤ σ.commit ∧ bl ≤ σ.commit := by
  subst h0
  have : uint.nat i = A.length := by simp at hi; word
  omega

/-- **The image's committed log passes `Recover`'s version check** (restart S6, CP2: the restart
contract's `clusterVerLogOk L` at the image's `L = pre ++ A`, from the stopped incarnation's KV
invariant, `kv_log_verOk`; see `bootstrapRestartContract`'s docstring, "The cluster version"). -/
theorem restart_clusterVerLogOk (γ : ServerRaftNames) (γk : KVNames) (A : List EntryModel)
    (hpre : γ.pre = []) :
    ⊢ kvInv (GF := GF) γ γk -∗ srvRaftLogInv γ -∗ srvRLogLb γ A ={⊤}=∗
      ⌜clusterVerLogOk (γ.pre ++ A)⌝ := by
  iintro #HkI #HrI #HA
  rw [hpre, List.nil_append]
  iapply kv_log_verOk γ γk A $$ HkI HrI HA

end lemmas

end EtcdGrove
end Perennial
