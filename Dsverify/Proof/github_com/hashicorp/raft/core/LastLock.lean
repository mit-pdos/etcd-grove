/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/core/LastLock.lean (241f27e).
-/
/-
Helper lemmas of package CORE (stage 3, not part of the frozen interface): `lastApplied`'s lower
bounds against its authority, and the main goroutine's bound on the last snapshot (`lastLockInv`'s
snapshot is within the log: `si ≤ lastApplied ≤ dur ≤ |log|`; review T1-1, check N1).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.core.Helpers

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.hashicorp.raft

open proto gprot

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

/-- A lower bound of `lastApplied` is at most its authority's value. -/
theorem applLb_le (rc : RCtx GF) (q : Qp) (a x : Nat) :
    monoNatAuthOwn rc.names.applied q a ∗ applLb rc x ⊢ ⌜x ≤ a⌝ := by
  iintro ⟨Ha, Hlb⟩
  iunfold applLb at Hlb
  ihave %h := monoNatLbOwn_valid _ _ _ _ $$ Ha Hlb
  ipureintro; exact h.2

/-- The two halves of `lastApplied`'s authority agree, and together move up to `x`. -/
theorem applied_halves_update (rc : RCtx GF) (a b x : Nat) (h : a ≤ x) :
    monoNatAuthOwn rc.names.applied (1 : Qp).half a ∗ monoNatAuthOwn rc.names.applied (1 : Qp).half b ⊢
      |==> (⌜a = b⌝ ∗ monoNatAuthOwn rc.names.applied (1 : Qp).half x ∗
        monoNatAuthOwn rc.names.applied (1 : Qp).half x) := by
  iintro ⟨Ha, Hb⟩
  ihave %hab := monoNatAuthOwn_agree _ _ _ _ _ $$ Ha Hb
  obtain ⟨-, rfl⟩ := hab
  have hc := (monoNatAuthOwn_fractional (GF := GF) rc.names.applied a).fractional (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at hc
  ihave H1 := hc.2 $$ [$Ha $Hb]
  imod mono_nat_own_update x h $$ H1 with ⟨H1, -⟩
  have hs := (monoNatAuthOwn_fractional (GF := GF) rc.names.applied x).fractional (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at hs
  icases hs.1 $$ H1 with ⟨H1, H2⟩
  imodintro
  iframe
  ipureintro; rfl

section rb
variable [hRB : ReceiptBoundLe GF (2 ^ 62)]

/-- The main goroutine's bound on `lastLockInv`'s snapshot: within its log. -/
theorem lastLock_snap_le (E : CoPset) (hE : ↑gprotN ⊆ E) (γ : GNames) (rc : RCtx GF) (i : SID)
    (s : SState) (q : Qp) (a : Nat) (si st : w64) :
    Inv (GF := GF) γ ∗ srvOwn γ i s ∗ monoNatAuthOwn rc.names.applied q a ∗ ⌜a ≤ s.dur.1⌝ ∗
      (⌜si = W64 0⌝ ∨ ∃ e : Entry, CIdx γ (uint.nat si) e ∗ ⌜e.term = uint.nat st⌝ ∗
        applLb rc (uint.nat si) ∗
        (durLb γ i (uint.nat si) ∨ snapFollow γ i (uint.nat si) (uint.nat st))) ⊢ |={E}=>
      srvOwn γ i s ∗ monoNatAuthOwn rc.names.applied q a ∗ ⌜uint.nat si ≤ s.log.length⌝ := by
  iintro ⟨#HI, Hs, Ha, %Hle, Hsn⟩
  imod srvOwn_facts γ E hE i s $$ [$HI $Hs] with ⟨Hs, -, %Hf⟩
  icases Hsn with (%H0 | ⟨%e, -, -, Hlb, -⟩)
  · imodintro; iframe; ipureintro; subst H0; simp
  · ihave %h := applLb_le rc q a (uint.nat si) $$ [$Ha $Hlb]
    imodintro; iframe; ipureintro; omega

end rb

end lemmas

end github_com.hashicorp.raft

end Perennial
