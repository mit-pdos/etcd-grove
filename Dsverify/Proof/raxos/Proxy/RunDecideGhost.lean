/-
Package `proxy`: the ghost steps of the decision handlers: a decided slot's ids are nonempty
valid strings (`rd_decided_ok`); a slot this proxy proposed (`evIn (.init idx k _)`) is in the
log (`rd_init_in_log`: below the init frontier, and not pending, its init token being spent).
-/
module

public import Dsverify.Proof.raxos.Proxy.RunSmrHelpers

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Perennial.raxos


open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.raxos.pure Perennial.raxos.msg
open raxos.replica.src

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]

attribute [local instance] HeapGS.goose_globalGS

instance rd_decided_persistent (γ : QNames) (i : Int) (ids : List GoString) :
    Persistent (decided (GF := GF) γ i ids) := by
  unfold decided; infer_instance

theorem rd_reg_strOk (γ : QNames) (ids : List GoString) :
    ⊢@{IProp GF} ([∗list] x ∈ ids, ∃ b, batchReg γ x b) -∗ ⌜∀ x ∈ ids, strOk x⌝ := by
  induction ids with
  | nil => iintro -; ipureintro; simp
  | cons y ys ih =>
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨⟨%b, Hb⟩, H⟩
    ihave %Hs := batchReg_shape γ y b $$ Hb
    ihave %Hr := ih $$ H
    ipureintro
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact rd_ascii_strOk x Hs.1
    · exact Hr x hx

theorem rd_decided_ok (γ : QNames) (E : CoPset) (hE : ↑consN ⊆ E) (i : Int) (ids : List GoString) :
    ⊢@{IProp GF} inv consN (consInv γ) -∗ decided γ i ids ={E}=∗
      ⌜ids ≠ [] ∧ (∀ x ∈ ids, strOk x) ∧ 1 ≤ i ∧ i ≤ 600⌝ := by
  iintro #Hinv #Hd
  imod (decided_nonempty γ E hE i ids) $$ Hinv Hd with %Hne
  imod (decided_registered γ E hE i ids) $$ Hinv Hd with Hreg
  ihave %Hok := rd_reg_strOk γ ids $$ Hreg
  iunfold decided at Hd
  imod (evIn_bound γ E hE (.decide i ids)) $$ Hinv Hd with ⟨-, %Hb⟩
  imodintro
  ipureintro
  exact ⟨Hne, Hok, Hb⟩

theorem rd_init_in_log (γ : QNames) (E : CoPset) (hE : ↑consN ⊆ E) (k : Nat)
    (Pm : GMap Int Unit) (lp : Int) (n : Nat) (idx : Int) (ids0 : List GoString) (lead : Bool)
    (hPm : ∀ i, 1 ≤ i → i ≤ lp → i < n ∨ (Pm !! i).isSome) :
    ⊢@{IProp GF} inv consN (consInv γ) -∗ evIn γ (.init idx k ids0 lead) -∗ initFront γ k (lp + 1) -∗
      ([∗map] i ↦ _u ∈ Pm, initTok γ k i) ={E}=∗
      initFront γ k (lp + 1) ∗ ([∗map] i ↦ _u ∈ Pm, initTok γ k i) ∗
      ⌜1 ≤ idx ∧ idx ≤ 600 ∧ idx < n⌝ := by
  iintro #Hinv #Hev Hfr Htoks
  imod (evIn_bound γ E hE (.init idx k ids0 lead)) $$ Hinv Hev with ⟨-, %Hb⟩
  imod (init_lt_front γ E hE k (lp + 1) idx ids0 lead) $$ Hinv Hev Hfr with ⟨Hfr, %Hlt⟩
  simp only [Ev.slot] at Hb
  rcases hPm idx Hb.1 (by omega) with hn | hp
  · imodintro
    iframe Hfr Htoks
    ipureintro; exact ⟨Hb.1, Hb.2, hn⟩
  · obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 hp
    icases (BigSepM.bigSepM_lookup_acc (Φ := fun i _ => initTok (GF := GF) γ k i)
      (show PartialMap.get? Pm idx = some u from hu)).1 $$ Htoks with ⟨Htok, -⟩
    imod (init_tok_spent γ E hE k idx ids0 lead) $$ Hinv Hev Htok with %Hf
    exact Hf.elim

end proofs

end Perennial.raxos
