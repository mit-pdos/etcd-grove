/-
`typed.validatingObjectWalker.finishDescent`: not proved yet (`sorry`): the stage's Prove step, after the freeze
(notes/smd-plan.md). Draft (2026-11-19).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.validatingObjectWalker__finishDescent

public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsA

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : typed.Assumptions]

theorem typed.validatingObjectWalker.finishDescent.wp_proof :
    typed.validatingObjectWalker.finishDescent.spec (GF := GF) :=
    fun w w2 sc S st st2 sp a => by
  wp_start as ⟨Hcore, Hcore2, Hsp, %Hspn⟩
  iunfold vwCore at Hcore Hcore2
  icases Hcore with ⟨%tr0, Hw, #Htr0, #Hsc, %Hwf⟩
  icases Hcore2 with ⟨%tr2, Hw2, -, -, -⟩
  iunfold spareWalkers at Hsp
  icases Hsp with (%h | ⟨%sl, %ws, Hsp, Hsl, Hcap, Hws⟩)
  · contradiction
  wp_auto
  wp_apply (wp_slice_literal (V := Loc) [w2])
  isplitr
  · ipureintro; rfl
  iintro %slp ⟨Hl, Hlcap⟩
  wp_auto
  wp_apply (wp_slice_append (V := Loc) sl ws _ [w2] (DFrac.own 1)) $$ [Hsl Hcap Hl] as %sl' ⟨Hsl, Hcap, -⟩
  · iframe
  try wp_auto
  iapply HΦ
  iunfold vwCore
  isplitl [Hw]
  · iexists tr0; iframe Hw; iframe #; ipureintro; exact Hwf
  iunfold spareWalkers
  iright
  iexists sl', ws ++ [w2]
  iframe Hsp Hsl Hcap
  iapply BigSepL.bigSepL_snoc.2
  iframe Hws
  iexists _; iexact Hw2

end proof

end smd
end EtcdGrove
end Perennial
