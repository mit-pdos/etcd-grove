/-
The heap image of `startRecoveryForInstance`'s instance (the new bookkeeping with the replica's
own PrepareReply), from the pieces the handler holds.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.RecModel
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.HCtx

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs
open model epaxosProof

attribute [local instance] GooseGlobalGS.gooseInvGS

variable [GooseExts]

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS]
variable [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions] [TH : StateTreemap GF]

/-- The proposals `startRecoveryForInstance` carries over (`inst.lb.clientProposals`). -/
def recCp (γ : EpNames) (i : Nat) (σ : RState) (x : InstId) (pv : GoSlice) : IProp GF :=
  match (recW0 σ x).lb.bind (·.clientProposals) with
  | none => iprop(⌜pv = slice.nil⌝)
  | some ps => iprop(∃ gs : List Loc, ⌜pv ≠ slice.nil ∧ gs.length = ps.length⌝ ∗ pv ↦*□ gs ∗
      [∗list] k ↦ g ∈ gs, propHeld γ i (decide ((recW0 σ x).status = stEXECUTED)) g
        (ps.getD k default))

theorem cmdsRep_dup2 (sl : GoSlice) (o : Option (List WCmd)) :
    cmdsRep (GF := GF) sl o ⊢ cmdsRep sl o ∗ cmdsRep sl o := by
  rcases o with _ | cs
  · unfold cmdsRep; iintro %H; isplitl [] <;> ipureintro <;> exact H
  · unfold cmdsRep; iintro ⟨%H, #Hc⟩
    isplitl []
    · isplitl []
      · ipureintro; exact H
      · iexact Hc
    · isplitl []
      · ipureintro; exact H
      · iexact Hc

theorem ownInst_rec (γ : EpNames) (i : Nat) (σ : RState) (x : InstId) (hid : σ.id = i)
    (p' lbp rp : Loc) (y : epaxos.Instance) (pv od cd prsl pq : GoSlice) (lr : Bool)
    (hlr : lr = decide (σ.id = x.q)) (hlbp : lbp ≠ null)
    (Hyf : y.bal' = (recW0 σ x).bal ∧ y.vbal' = (recW0 σ x).vbal ∧ y.Status' = (recW0 σ x).status ∧
      y.Seq' = (recW0 σ x).seq ∧ ((recW0 σ x).status ≠ stEXECUTED → y.Index' = W64 0)) :
    p' ↦ epaxos.Instance.mk y.Cmds' (recN σ x) y.vbal' y.Status' y.Seq' y.Deps' lbp y.Index'
        y.Lowlink' y.bfilter' y.proposeTime' y.id' ∗
      y.id' ↦□ epaxos.instanceId.mk (W32 x.q) (W32 x.i) ∗
      cmdsRep (GF := GF) y.Cmds' (recW0 σ x).cmds ∗ cmdsRep y.Cmds' (recW0 σ x).cmds ∗
      cmdsRep y.Cmds' (recW0 σ x).cmds ∗ y.Deps' ↦*□ (recW0 σ x).deps ∗
      lbp ↦ epaxos.LeaderBookkeeping.mk pv y.vbal' true (W64 0) (W64 0) (W64 0) od cd prsl true
        false pq (W64 0) false (recN σ x) y.Cmds' y.Status' y.Seq' y.Deps' lr (W64 0) ∗
      (prsl ↦* [rp] ∗ ownSliceCap Loc prsl (DFrac.own 1)) ∗
      rp ↦□ epaxos.PrepareReply.mk (W32 (i : Int)) (W32 (x.q : Int)) (W32 (x.i : Int)) (recN σ x)
        y.vbal' y.Status' y.Cmds' y.Seq' y.Deps' ∗
      recCp γ i σ x pv ⊢
    ownInst γ i x p' (recInst σ x) := by
  iintro ⟨Hy, #Hyid, Hc1, Hc2, Hc3, #Hd, Hlbp, Hprsl, #Hrp, Hcp⟩
  unfold ownInst
  rw [show (recInst σ x).status = (recW0 σ x).status from rfl]
  iexists epaxos.Instance.mk y.Cmds' (recN σ x) y.vbal' y.Status' y.Seq' y.Deps' lbp y.Index'
    y.Lowlink' y.bfilter' y.proposeTime' y.id'
  simp only [recInst]
  iframe Hy
  isplitr
  · ipureintro; exact ⟨trivial, Hyf.2.1, Hyf.2.2.1, Hyf.2.2.2.1, Hyf.2.2.2.2⟩
  isplitr
  · iexact Hyid
  isplitl [Hc1]
  · iexact Hc1
  isplitr
  · iexists DFrac.discard; iexact Hd
  isplitr
  · ipureintro; exact hlbp
  unfold ownLb
  have hdo : lbDepsOwned (recLb σ x) = false := by simp [lbDepsOwned, recLb]
  rw [hdo]
  unfold recCp
  rcases hcp : (recW0 σ x).lb.bind (·.clientProposals) with _ | ps
  · iexists epaxos.LeaderBookkeeping.mk pv y.vbal' true (W64 0) (W64 0) (W64 0) od cd prsl true false pq (W64 0) false (recN σ x) y.Cmds' y.Status' y.Seq' y.Deps' lr (W64 0), [], [rp]
    simp only [recLb, hcp]
    iframe Hlbp Hprsl
    isplitr
    · ipureintro
      simp [Hyf.2.1, Hyf.2.2.1, Hyf.2.2.2.1, hlr]
    isplitl [Hcp]
    · icases Hcp with %Hpv; ipureintro; exact Hpv
    isplitl [Hc2]
    · iexact Hc2
    isplitr
    · simp only [Bool.false_eq_true, ite_false]; iexists DFrac.discard; iexact Hd
    isplitr
    · ipureintro; rfl
    iapply Iris.BI.BigSepL.bigSepL_cons.2
    isplitl [Hc3]
    · simp only [List.getD_cons_zero]
      unfold ownPReply
      iexists y.Cmds', y.Deps', DFrac.discard
      simp only [recReply, hid]
      rw [← Hyf.2.1, ← Hyf.2.2.1, ← Hyf.2.2.2.1]
      iframe Hrp Hd
      iapply prCmds_of_cmdsRep $$ Hc3
    iapply Iris.BI.BigSepL.bigSepL_nil.2
    iempintro
  · icases Hcp with ⟨%gs, %Hgs, #Hgs, Hheld⟩
    iexists epaxos.LeaderBookkeeping.mk pv y.vbal' true (W64 0) (W64 0) (W64 0) od cd prsl true false pq (W64 0) false (recN σ x) y.Cmds' y.Status' y.Seq' y.Deps' lr (W64 0), gs, [rp]
    simp only [recLb, hcp]
    iframe Hlbp Hprsl
    isplitr
    · ipureintro
      simp [Hyf.2.1, Hyf.2.2.1, Hyf.2.2.2.1, hlr]
    isplitl [Hheld]
    · iframe Hheld
      isplitr
      · ipureintro; exact Hgs
      iexact Hgs
    isplitl [Hc2]
    · iexact Hc2
    isplitr
    · simp only [Bool.false_eq_true, ite_false]; iexists DFrac.discard; iexact Hd
    isplitr
    · ipureintro; rfl
    iapply Iris.BI.BigSepL.bigSepL_cons.2
    isplitl [Hc3]
    · simp only [List.getD_cons_zero]
      unfold ownPReply
      iexists y.Cmds', y.Deps', DFrac.discard
      simp only [recReply, hid]
      rw [← Hyf.2.1, ← Hyf.2.2.1, ← Hyf.2.2.2.1]
      iframe Hrp Hd
      iapply prCmds_of_cmdsRep $$ Hc3
    iapply Iris.BI.BigSepL.bigSepL_nil.2
    iempintro

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
