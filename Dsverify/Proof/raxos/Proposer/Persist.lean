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

theorem bigSepL_bupd' {A : Type} (Φ : Nat → A → IProp GF) (l : List A) :
    ⊢ ([∗list] k ↦ x ∈ l, |==> Φ k x) -∗ |==> [∗list] k ↦ x ∈ l, Φ k x := by
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

theorem repList_persist {A : Type} (rep : Loc → DFrac → A → IProp GF) (ps : List Loc) (xs : List A)
    (H : ∀ l a, ⊢ rep l (DFrac.own 1) a -∗ |==> rep l .discard a) :
    ⊢ repList rep ps (DFrac.own 1) xs -∗ |==> repList rep ps .discard xs := by
  unfold repList
  iintro ⟨%Hl, H1⟩
  iapply bupd_mono (P := iprop([∗list] k ↦ p ∈ ps, ∃ x, ⌜xs[k]? = some x⌝ ∗ rep p .discard x))
  · iintro H2; isplitr; · ipureintro; exact Hl
    iexact H2
  iapply bigSepL_bupd'
  iapply BigSepL.bigSepL_mono_of_forall (Φ := fun k p => iprop(∃ x, ⌜xs[k]? = some x⌝ ∗
    rep p (DFrac.own 1) x)) ?_ $$ H1
  intro k p
  iintro ⟨%x, %Hx, Hr⟩
  imod H p x $$ Hr with Hr
  imodintro
  iexists x
  iframe
  ipureintro; exact Hx

theorem repDRSingle_persist (l : Loc) (m : GoString) :
    ⊢@{IProp GF} repDRSingle l (DFrac.own 1) m -∗ |==> repDRSingle l .discard m := by
  unfold repDRSingle
  iintro ⟨%x, Hx, %Hm⟩
  ipersist Hx
  imodintro
  iexists x
  iframe #
  ipureintro; exact Hm

theorem repDRBatch_persist (l : Loc) (b : Batch) :
    ⊢@{IProp GF} repDRBatch l (DFrac.own 1) b -∗ |==> repDRBatch l .discard b := by
  unfold repDRBatch
  iintro ⟨%x, %ps, Hx, %Hf, Hps, Hr⟩
  ipersist Hx
  ipersist Hps
  imod repList_persist _ _ _ repDRSingle_persist $$ Hr with Hr
  imodintro
  iexists x, ps
  iframe
  iframe #
  ipureintro; exact Hf

theorem repDResp_persist (l : Loc) (bs : List Batch) :
    ⊢@{IProp GF} repDResp l (DFrac.own 1) bs -∗ |==> repDResp l .discard bs := by
  unfold repDResp
  iintro ⟨%x, %ps, Hx, Hps, Hr⟩
  ipersist Hx
  ipersist Hps
  imod repList_persist _ _ _ repDRBatch_persist $$ Hr with Hr
  imodintro
  iexists x, ps
  iframe
  iframe #

end persist

end prop

end Perennial.raxos
