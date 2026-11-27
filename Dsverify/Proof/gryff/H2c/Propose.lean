/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H2c/Propose.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit H2c: re-proposals (`e.R.ProposeChan <- p` under the lock)

`proposeOwn` holds `ProposeChan`'s exclusive `ownChan` (buffered; only the lock holder sends to it
and receives from it): a send appends the proposal (a send on a full buffer blocks forever, which
a WP admits: `sendAu`'s buffered case).
-/
module

public import Dsverify.Proof.gryff.H2c.SlotOpen

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.replica2

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto
open Perennial.gryff.model (RState Copy LB Proposal Msg Ev Out Cmd Deps)

attribute [local instance] GooseGlobalGS.gooseInvGS

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]


instance proposalRep_persistent (ρ : Repl2Names) (pp : Loc) (pr : Proposal) :
    Persistent (proposalRep ρ pp pr : IProp GF) := by
  unfold proposalRep writerIs; infer_instance

theorem proposeOwn_open (ρ : Repl2Names) (gR : Loc) (ps : List Proposal) :
    proposeOwn (GF := GF) ρ gR ps ⊣⊢ ∃ (ch : Loc) (pps : List Loc),
      gR.[src.genericsmr.Replica, go!"ProposeChan"] ↦□ ch ∗
      isChan ch (ρ.chans "propose") Loc ∗ ownChan (ρ.chans "propose") Loc (.Buffered pps) ∗
      ⌜pps.length = ps.length⌝ ∗
      [∗list] i ↦ pp ∈ pps, ∃ pr, ⌜ps[i]? = some pr⌝ ∗ proposalRep ρ pp pr := by
  unfold proposeOwn; exact .rfl

/-- `ProposeChan`'s handle (persistent). -/
theorem proposeOwn_chan (ρ : Repl2Names) (gR : Loc) (ps : List Proposal) :
    proposeOwn (GF := GF) ρ gR ps ⊢ proposeOwn ρ gR ps ∗ ∃ ch : Loc,
      gR.[src.genericsmr.Replica, go!"ProposeChan"] ↦□ ch := by
  iintro H
  icases (proposeOwn_open ..).1 $$ H with ⟨%ch, %pps, #Hch, #Hic, Hoc, %Hl, Hps⟩
  isplitl
  · iapply (proposeOwn_open ..).2
    iexists ch, pps
    iframe # ∗
    ipureintro; exact Hl
  · iexists ch; iexact Hch

/-- **`ProposeChan <- pp`**: the proposal is queued. -/
theorem wp_propose_send (ρ : Repl2Names) (gR ch pp : Loc) (ps : List Proposal) (pr : Proposal) :
    {{ proposeOwn (GF := GF) ρ gR ps ∗ gR.[src.genericsmr.Replica, go!"ProposeChan"] ↦□ ch ∗
        proposalRep ρ pp pr }}
      (App (App (Val (chan.send (go.GoType.PointerType src.genericsmr.Propose.ty))) (Val #ch))
        (Val #pp))
    {{ RET #(); proposeOwn ρ gR (ps ++ [pr]) }} := by
  iintro %Φ ⟨Hown, #Hch, #Hpr⟩ HΦ
  icases (proposeOwn_open ..).1 $$ Hown with ⟨%ch', %pps, #Hch', #Hic, Hoc, %Hl, Hps⟩
  icombine Hch Hch' gives %Hce
  subst Hce
  wp_apply (chan.wp_send (V := Loc) (t := go.GoType.PointerType src.genericsmr.Propose.ty) ch pp (ρ.chans "propose")) $$ Hic
  iintro -
  unfold sendAu
  iapply ncfupd_of_fupd
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists .Buffered pps
  iframe Hoc
  dsimp only
  iintro Hoc
  imod Hmask with -
  imodintro
  iapply HΦ
  iapply (proposeOwn_open ..).2
  iexists ch, pps ++ [pp]
  iframe # Hoc
  isplitr
  · ipureintro; simp [Hl]
  isplitl [Hps]
  · iapply BigSepL.bigSepL_mono (fun {i x} hi => ?_) $$ Hps
    iintro ⟨%pr', %Hpr', Hx⟩
    iexists pr'
    iframe Hx
    ipureintro
    have : i < ps.length := by
      have := (List.getElem?_eq_some_iff.1 hi).1; omega
    rw [List.getElem?_append_left this]; exact Hpr'
  isplitr
  · ipureintro; rw [Nat.zero_add, Hl, List.getElem?_append_right (Nat.le_refl _)]; simp
  · iapply BigSepL.bigSepL_nil.2; itrivial

end

end Perennial.gryff.replica2
