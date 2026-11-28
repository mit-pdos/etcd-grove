/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__runFSM.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).runFSM`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__runFSM
public import Dsverify.Spec.github_com.hashicorp.raft.deferError__respond
public import Dsverify.Proof.github_com.hashicorp.raft.DeferRespond
public import Dsverify.Proof.github_com.hashicorp.raft.FsmBase
public import Dsverify.Proof.github_com.hashicorp.raft.FutBase
public import Dsverify.Proof.github_com.hashicorp.raft.gprot.Snap
public import Dsverify.Proof.github_com.hashicorp.raft.InstallBase
public import Dsverify.Proof.github_com.hashicorp.raft.SnapFut
public import Dsverify.Spec.github_com.hashicorp.raft.fsmRestoreAndMeasure
public import Dsverify.Spec.github_com.hashicorp.raft.DecodeConfiguration

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]
variable [hRB : ReceiptBoundLe GF (2 ^ 62)]

open github_com.hashicorp.raft proto gprot github_com.hashicorp.raft.fsmProof

namespace github_com.hashicorp.raft.fsmProof

/-- The FSM goroutine's last applied command `k0` (`0`: none) has a (persistent) response fact. -/
def lastR (rc : RCtx GF) (k0 : Nat) : IProp GF :=
  iprop(⌜k0 = 0⌝ ∨ ∃ r : GoInterface, □ rc.respP k0 r)

instance lastR_persistent rc k0 : Persistent (lastR (GF := GF) rc k0) := by
  unfold lastR; infer_instance

/-- (stage 3) What the FSM goroutine's `lastIndex`/`lastTerm` mean: nothing applied yet, or the end of
an item it processed (`batchEnd`), a committed entry of that term, past the last command `k0`. -/
def lastF (γ : GNames) (rc : RCtx GF) (k0 : Nat) (li lt : w64) : IProp GF :=
  iprop(⌜li = W64 0⌝ ∨ (⌜k0 ≤ uint.nat li ∧ 1 ≤ uint.nat li⌝ ∗ (∃ m, batchEnd rc m (uint.nat li)) ∗
    ∃ e : Entry, CIdx γ (uint.nat li) e ∗ ⌜e.term = uint.nat lt⌝))

instance lastF_persistent γ rc k0 li lt : Persistent (lastF (GF := GF) γ rc k0 li lt) := by
  unfold lastF; infer_instance

theorem noCmdBetween_prefix (γ : GNames) (k0 a b : Nat) (h1 : k0 < b) (h : b ≤ a) :
    noCmdBetween (GF := GF) γ k0 a ⊢ noCmdBetween γ k0 b := by
  unfold noCmdBetween
  have : a - (k0 + 1) = (b - (k0 + 1)) + (a - b) := by omega
  rw [this, ← List.range'_append]
  iintro H
  ihave ⟨H1, -⟩ := BigSepL.bigSepL_append.1 $$ H
  iexact H1

theorem itemRes_CIdx (γ : GNames) (rc : RCtx GF) (i : SID) (it : BatchItem) :
    itemRes (GF := GF) γ rc i it ⊢ CIdx γ it.k it.e := by
  simp only [itemRes]
  iintro ⟨-, -, #HC, -⟩
  iexact HC

/-- `fsmAt` from the loop's last-command fact (`iface.fsmAt_intro`). -/
theorem fsmAt_of_lastR (γ : GNames) (rc : RCtx GF) (i : SID) (k0 s : Nat) (h : k0 ≤ s) :
    lastR rc k0 ∗ noCmdBetween γ k0 (s + 1) ∗ durLb γ i s ⊢ fsmAt γ rc.respP i s := by
  unfold lastR
  iintro ⟨#HR, #Hnc, #Hd⟩
  icases HR with (%H0 | ⟨%r, #Hr⟩)
  · iapply github_com.hashicorp.raft.fsmAt_intro γ rc.respP i k0 s interface.nil h
    iframe #
    ileft; ipureintro; exact H0
  · iapply github_com.hashicorp.raft.fsmAt_intro γ rc.respP i k0 s r h
    iframe #

instance barrierDisp_persistent γ i sc b e : Persistent (barrierDisp (GF := GF) γ i sc b e) := by
  unfold barrierDisp; infer_instance

instance verifyItem_persistent γ i sc a : Persistent (verifyItem (GF := GF) γ i sc a) := by
  unfold verifyItem; infer_instance

/-- The barrier bound at the FSM goroutine: the committed barrier `e` at `b` (dispatched after the
client's snapshot `sc`, `barrierDisp`) is above every voter's durable prefix at `sc`
(`gprot.barrier_bound`). -/
theorem barrier_voters (γ : GNames) (i : SID) (sc : Snap) (b : Nat) (e : Entry) :
    Inv (GF := GF) γ ∗ barrierDisp γ i sc b e ∗ CIdx γ b e ⊢ |={⊤}=>
      ⌜∀ i' ∈ γ.srvs, sc.dur i' < b⌝ := by
  unfold barrierDisp
  iintro ⟨#HInv, ⟨%n0, %st, -, -, -, #Hsc, %Hd⟩, #HC⟩
  iapply barrier_bound γ ⊤ (by simp) sc b e Hd.2.1 $$ [$HInv $Hsc $HC]

end github_com.hashicorp.raft.fsmProof

theorem github_com.hashicorp.raft.Raft.runFSM.wp_proof
    (wp_respond : github_com.hashicorp.raft.deferError.respond.spec (GF := GF) (hG := hG))
    (wp_fsmRestoreAndMeasure :
      github_com.hashicorp.raft.fsmRestoreAndMeasure.spec (GF := GF) (hG := hG))
    (wp_DecodeConfiguration : github_com.hashicorp.raft.DecodeConfiguration.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.runFSM.spec (GF := GF) (hG := hG) := by
  sorry -- hraft_robust L0: re-proved by its stage (HANDOFF.md)

end proof

end Perennial
