/-
`(*Replica).executeCommands()` (epaxos.go), the executor goroutine: its spec (the one the run
loop's `ExecuteCommandsSpec`, `Epaxos/Proof/epaxos/RunSpec.lean` on branch prove-epaxos, takes as
hypothesis), and `ExecWf_of_inv`, the facts of the model's invariant a scan pass needs.

Status: `ExecWf_of_inv` proved (from the model's `execWf_of_inv`, MODEL-REQUEST exec-M1 resolved:
new conjunct `InvAux.execLo`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.FindSCC
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.GhostExec
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.GhostDeliver
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.ExecWfInv

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs
open model epaxosProof

attribute [local instance] GooseGlobalGS.gooseInvGS

variable [GooseExts]

/-- The ops' premise (`opsPre`, from `epInv`'s ops list) gives the model's `OpsOk`. -/
theorem opsOk_of_pre [GooseExts] [GoGlobalContext] {S : Sys} (h : opsPre S) : OpsOk S := by
  intro o ho
  obtain ⟨inp, hpre, hc⟩ := h o ho
  rw [hc]
  exact opCmdOk_of_pre inp hpre

/-- What a scan pass needs of the replica's state, from the model's invariant and the ops'
premise (the executor is idle when it takes the lock): the model's `execWf_of_inv`
(`Epaxos/Model/Proof/ExecWfInv.lean`). -/
theorem ExecWf_of_inv [GooseExts] [GoGlobalContext] (S : Sys) (hS : Inv S) (hops : opsPre S) (i : Nat)
    (hi : i < nR) : ExecWf (S.rep i) :=
  execWf_of_inv S hS (opsOk_of_pre hops) i hi

/-- What a scan pass relies on: the executor's facts and the rows' `crtInstance` in range
(`Inv.wf`). -/
def ScanOk (σ : RState) : Prop :=
  ExecWf σ ∧ ∀ q < nR, -1 ≤ zz (σ.crtInstance q) ∧ toN (σ.crtInstance q) + 1 < MAX_INSTANCE

theorem scanOk_of_inv [GooseExts] [GoGlobalContext] (S : Sys) (hS : Inv S) (hops : opsPre S) (i : Nat)
    (hi : i < nR) : ScanOk (S.rep i) :=
  ⟨ExecWf_of_inv S hS hops i hi, fun q hq => hS.1.1.2.2.1 i hi q hq⟩

/-- `execBump` keeps the executor's facts. -/
theorem execWf_bump {σ : RState} (h : ExecWf σ) {q : Nat} (hq : q < nR)
    (he : σ.executed ⟨q, toN (σ.execedUpTo q + 1)⟩) : ExecWf (model.execBump σ q) := by
  obtain ⟨w, hw, hst⟩ := he
  have hlo := h.exLo q hq
  have hid : toN (σ.execedUpTo q + 1) + 1 < MAX_INSTANCE := (h.ids _ w hw).2
  have hsucc : zz (σ.execedUpTo q + 1) = zz (σ.execedUpTo q) + 1 := by
    have := hlo.2; unfold MAX_INSTANCE at this
    simp only [zz] at *; word
  have hn : (toN (σ.execedUpTo q + 1) : Int) = zz (σ.execedUpTo q) + 1 := by
    simp only [toN, zz] at *; omega
  refine ⟨h.ids, h.deps, fun q' hq' n hn' => ?_, fun q' hq' => ?_, h.cmdsOk, h.props, h.store⟩
  · simp only [model.execBump, upd_apply] at hn' ⊢
    show RState.executed σ _
    by_cases e : q' = q
    · subst e; simp only [ite_true] at hn'
      rcases Int.lt_or_eq_of_le (show (n : Int) ≤ zz (σ.execedUpTo q') + 1 by rw [← hsucc]; exact hn')
        with h1 | h1
      · exact h.exUp q' hq' n (by omega)
      · have : n = toN (σ.execedUpTo q' + 1) := by omega
        subst this; exact ⟨w, hw, hst⟩
    · simp only [if_neg e] at hn' ⊢; exact h.exUp q' hq' n hn'
  · simp only [model.execBump, upd_apply]
    by_cases e : q' = q
    · subst e; simp only [ite_true]; rw [hsucc]; constructor <;> omega
    · simp only [if_neg e]; exact h.exLo q' hq'

/-- The state during a scan pass: the state at the lock with other instances, store and
executed-up-to row (the executor's writes). -/
def ScanRel (σ0 σ : RState) : Prop :=
  ∃ (I : InstId → Option InstRec) (st : w64 → Option (List w8)) (eu : Nat → w32),
    σ = { σ0 with inst := I, store := st, execedUpTo := eu }

theorem ScanRel.refl (σ : RState) : ScanRel σ σ := ⟨σ.inst, σ.store, σ.execedUpTo, rfl⟩

theorem ScanRel.exRel {σ0 σ σ' : RState} (h : ScanRel σ0 σ) (h' : ExRel σ σ') : ScanRel σ0 σ' := by
  obtain ⟨I, st, eu, rfl⟩ := h
  obtain ⟨⟨I', st', e'⟩, -⟩ := h'
  exact ⟨I', st', eu, by rw [e']⟩

theorem ScanRel.bump {σ0 σ : RState} (h : ScanRel σ0 σ) (q : Nat) :
    ScanRel σ0 (model.execBump σ q) := by
  obtain ⟨I, st, eu, rfl⟩ := h
  exact ⟨I, st, _, rfl⟩

theorem ScanRel.crt {σ0 σ : RState} (h : ScanRel σ0 σ) : σ.crtInstance = σ0.crtInstance := by
  obtain ⟨I, st, eu, rfl⟩ := h; rfl

theorem ScanOk.exRel {σ σ' : RState} (h : ScanOk σ) (h' : ExRel σ σ') (hw : ExecWf σ') :
    ScanOk σ' := by
  obtain ⟨⟨I', st', e'⟩, -⟩ := h'
  exact ⟨hw, by rw [e']; exact h.2⟩

theorem ScanOk.bump {σ : RState} (h : ScanOk σ) {q : Nat} (hq : q < nR)
    (he : σ.executed ⟨q, toN (σ.execedUpTo q + 1)⟩) : ScanOk (model.execBump σ q) :=
  ⟨execWf_bump h.1 hq he, h.2⟩

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF] [π : NetProtoGS]

/-- At the lock: the scan's facts, from `epInv` (one credit; nothing changes). -/
theorem ep_scanOk (γ : EpNames) (E : CoPset) (i : Nat) (σ : RState) (hE : ↑protoN ⊆ E)
    (hi : i < nR) :
    ⊢ inv protoN (epInv (GF := GF) γ) -∗ repFrag γ i σ -∗ £ 1 ={E}=∗ repFrag γ i σ ∗ ⌜ScanOk σ⌝ := by
  rw [epInv_unseal, epInvDef_eq]
  unfold repFrag
  iintro #Hinv Hf Hlc
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := E \ ↑protoN) $$ Hlc Hi with Hi
  iunfold epInvB at Hi
  icases Hi with ⟨%S, Ha, %hS, %hX, Hkv, HF, Hsents, Hdel, Hops⟩
  ihave %hσ := sysAuthB_rep γ S i σ hi $$ Ha Hf
  ihave %hops := ops_pre γ S $$ Hops
  imod Hclose $$ [Ha Hkv HF Hsents Hdel Hops] with -
  · inext
    iunfold epInvB
    iexists S
    iframe
    ipureintro; exact ⟨hS, hX⟩
  imodintro
  iframe
  ipureintro
  rw [← hσ]; exact scanOk_of_inv S hS hops i hi

end ghost

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS]
variable [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions] [TH : StateTreemap GF]

/-- A recovery request the executor sends on `instancesToRecover` (as `recoverReq` of the run
loop's RunSpec.lean, prove-epaxos). -/
def exRecoverReq (γ : EpNames) (i : Nat) (iid : Loc) : IProp GF :=
  iprop(∃ (q k : Nat) (n : w32), iid ↦ epaxos.instanceId.mk (W32 q) (W32 k) ∗ crtLb γ i q n ∗
    ⌜q < nR ∧ (k : Int) ≤ zz n⌝)

/-- **`executeCommands()`** (never returns), in the form of the run loop's
`ExecuteCommandsSpec` (its `hctx` unfolded: the package, the handle, the framework's handle). -/
def ExecuteCommandsSpecX : Prop :=
  ∀ (γ : EpNames) (i : Nat) (r rr : Loc) (L : List GoString) (p : FwPtrs) (Rext : IProp GF)
    (e : Loc) (ch : GoChan) (γc : ChanNames),
  {{ pkgInit_epaxos (GF := GF) ∗ isReplica γ i r ∗ efld r go!"Replica" ↦□ rr ∗
      isReplicaFw γ rr i L p Rext ∗ efld r go!"exec" ↦□ e ∗
      structFieldRef epaxos.Exec go!"r" e ↦□ r ∗ efld r go!"instancesToRecover" ↦□ ch ∗
      isChanBag γc ch (exRecoverReq γ i) }}
    (App (Val (r @!! go.GoType.PointerType epaxos.Replica.ty @!! go!"executeCommands")) (Val #()))
  {{ RET #(); False }}

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
