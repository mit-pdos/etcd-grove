/-
`os.WriteFile`'s lemmas (`os.osAU_triv`: the update of a caller holding all of its precondition;
`os.crTr_false`, `os.crOut_join`), moved unchanged out of the proof file `WriteFile.lean` (import
tiers, 2026-11-19: `fileutil`'s `IsDirWriteable` proofs use them, and a proof file is imported by
linking modules only).
-/
module

public import Spec.os.WriteFile
public import Spec.os.File__Close
public import Proof.os.OffLong
public import Proof.os.OpenFileTruncLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions]

omit [os.Assumptions] in
/-- **The trivial update** of a caller holding all of `α`: it commits with whatever the step gives. -/
theorem os.osAU_triv {A : Type} (α : IProp GF) (β : A → IProp GF) : α ⊢ osAU α β β := by
  unfold osAU
  refine (BI.and_intro BI.true_intro .rfl).trans (aupd_intro ?_)
  iintro ⟨-, Hα⟩
  unfold atomic_acc
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hclose
  isimp only [texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iframe Hα
  isplit
  · iintro Hα
    imod Hclose
    imodintro
    iexact Hα
  · iintro %o Hβ
    imod Hclose
    imodintro
    iexact Hβ

/-- The file a create made, held whole, forgetting the success's facts. -/
theorem os.crTr_false (P : Prop) (o : Option (Nat × Nat × Ino)) :
    crTr (GF := GF) P o ⊢ crTr False o := by
  rcases o with _ | ⟨x, s, i⟩
  · dsimp only [crTr]; iintro H; iexact H
  · dsimp only [crTr]; exact trFile_mono i P False False.elim

omit [os.Assumptions] in
/-- Two halves of a create's outcome on a claim make the whole. -/
theorem os.crOut_join (j : Ino) (b : GoString) (h : NamesH) (o : Option (Nat × Nat × Ino)) :
    crOut (GF := GF) j b h (DFrac.own (1 : Qp).half) o ∗ crOut (GF := GF) j b h (DFrac.own (1 : Qp).half) o ⊢
      crOut (GF := GF) j b h (DFrac.own 1) o := by
  rcases o with _ | ⟨x, s, i⟩
  · dsimp only [crOut]
    iintro ⟨H1, H2⟩
    iapply (osNames_join j _ _ _ h (Qp.half_add_half 1)).1
    iframe
  · dsimp only [crOut]
    iintro ⟨⟨%hc, Hl, H1⟩, ⟨-, -, H2⟩⟩
    iframe Hl
    isplitr
    · ipureintro; exact hc
    iapply (osNames_join j _ _ _ _ (Qp.half_add_half 1)).1
    iframe

end proof

end EtcdGrove
end Perennial
