/-
Package `proxy`: the slot bound of `handleClientBatch` — the ghost step issuing the init token of
`proposeIndex` (`lastProposedIndex + 1`, then past decided slots), paid by the client batch's
credit.
-/
module

public import Dsverify.Proof.raxos.Proxy.Defs
public import Dsverify.Proof.raxos.Cons.Laws

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.raxos


open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.raxos.pure Perennial.raxos.msg

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable {GF : BundledGFunctors} [G : GooseGlobalGS HasLC.hasLC GF] [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

instance spentLb_persistent_px (γ : QNames) (m : Int) : Persistent (spentLb (GF := GF) γ m) := by
  unfold spentLb; infer_instance

instance decided_persistent'' (γ : QNames) (i : Int) (ids : List GoString) :
    Persistent (decided (GF := GF) γ i ids) := by
  unfold decided; infer_instance

/-- `handleClientBatch` issues slot `p`: either the frontier `n` itself, or past it, when slot
`p - 1` is decided (the loop skipped decided slots). The credit pays; the slot is in `[1, 600]`
(so `instanceTimeouts[p]` is in bounds). -/
theorem issue_ghost (γ : QNames) (E : CoPset) (hE : ↑consN ⊆ E) (k : Int) (n p : Int) (t : Ticket)
    (ids : List GoString) (hnp : n ≤ p) :
    ⊢@{IProp GF} inv consN (consInv γ) -∗ spentLb γ 0 -∗ initFront γ k n -∗ credit γ t -∗
      (⌜p = n⌝ ∨ decided γ (p - 1) ids) ={E}=∗
      initFront γ k (p + 1) ∗ initTok γ k p ∗ ⌜1 ≤ p ∧ p ≤ 600⌝ := by
  iintro #Hcons #Hsp0 Hfr Hcr Hcase
  icases Hcase with (%Hpn | #Hdec)
  · subst Hpn
    iapply (init_issue γ E hE k p 0 p t ⟨Int.le_refl _, Int.le_max_left _ _⟩) $$ Hcons Hfr Hcr Hsp0
  · iunfold decided at Hdec
    imod (evIn_bound γ E hE (.decide (p - 1) ids)) $$ Hcons Hdec with ⟨#Hsp, %-⟩
    simp only [Ev.slot]
    iapply (init_issue γ E hE k n (p - 1) p t ⟨hnp, by omega⟩) $$ Hcons Hfr Hcr Hsp

end proofs

end Perennial.raxos
