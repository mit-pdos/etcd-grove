/-
Package `proposer`: persisting the owned representation of a decoded `DecideResponse`.
-/
module

public import Dsverify.Proof.raxos.Proposer.Defs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.raxos


open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Net
open Perennial.raxos.pure Perennial.raxos.msg
open raxos.replica.src

namespace prop

section persist
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]

theorem bigSepL_fupd' {A : Type} (E : CoPset) (Φ : Nat → A → IProp GF) (l : List A) :
    ⊢ ([∗list] k ↦ x ∈ l, |={E}=> Φ k x) -∗ |={E}=> [∗list] k ↦ x ∈ l, Φ k x := by
  induction l generalizing Φ with
  | nil => iintro -; imodintro; iapply BigSepL.bigSepL_nil.2; iempintro
  | cons a l ih =>
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨H1, H2⟩
    imod H1 with H1
    imod ih (fun k x => Φ (k + 1) x) $$ H2 with H2
    imodintro
    iapply BigSepL.bigSepL_cons.2
    iframe

theorem repList_persist {A : Type} (E : CoPset) (rep : Loc → DFrac → A → IProp GF) (ps : List Loc)
    (xs : List A) (H : ∀ l a, ⊢ rep l (DFrac.own 1) a -∗ |={E}=> rep l .discard a) :
    ⊢ repList rep ps (DFrac.own 1) xs -∗ |={E}=> repList rep ps .discard xs := by
  unfold repList
  iintro ⟨%Hl, H1⟩
  ihave H1 := BigSepL.bigSepL_mono (Ψ := fun k p => iprop(|={E}=> ∃ x, ⌜xs[k]? = some x⌝ ∗
    rep p .discard x)) (fun {k p} _ => by
      iintro ⟨%x, %Hx, Hr⟩
      imod H p x $$ Hr with Hr
      imodintro
      iexists x
      iframe
      ipureintro; exact Hx) $$ H1
  imod bigSepL_fupd' E _ _ $$ H1 with H1
  imodintro
  isplitr
  · ipureintro; exact Hl
  iexact H1

theorem repDRSingle_persist (E : CoPset) (l : Loc) (m : GoString) :
    ⊢@{IProp GF} repDRSingle l (DFrac.own 1) m -∗ |={E}=> repDRSingle l .discard m := by
  unfold repDRSingle
  iintro ⟨%x, Hx, %Hm⟩
  imod ptDRSingle_persist E _ _ _ $$ Hx with #Hx
  imodintro
  iexists x
  iframe #
  ipureintro; exact Hm

theorem repDRBatch_persist (E : CoPset) (l : Loc) (b : Batch) :
    ⊢@{IProp GF} repDRBatch l (DFrac.own 1) b -∗ |={E}=> repDRBatch l .discard b := by
  unfold repDRBatch
  iintro ⟨%x, %ps, Hx, %Hu, %Hf, Hps, Hr⟩
  imod ptDRBatch_persist E _ _ _ $$ Hx with #Hx
  ipersist Hps
  imod repList_persist E _ _ _ (repDRSingle_persist E) $$ Hr with Hr
  imodintro
  iexists x, ps
  iframe
  iframe #
  ipureintro; exact ⟨Hu, Hf⟩

theorem repDResp_persist (E : CoPset) (l : Loc) (bs : List Batch) :
    ⊢@{IProp GF} repDResp l (DFrac.own 1) bs -∗ |={E}=> repDResp l .discard bs := by
  unfold repDResp
  iintro ⟨%x, %ps, Hx, %Hu, Hps, Hr⟩
  imod ptDResp_persist E _ _ _ $$ Hx with #Hx
  ipersist Hps
  imod repList_persist E _ _ _ (repDRBatch_persist E) $$ Hr with Hr
  imodintro
  iexists x, ps
  iframe
  iframe #
  ipureintro; exact Hu

end persist

end prop

end Perennial.raxos
