/-
`typed.toFieldSetWalker.finishDescent`: proved (Prove phase, 2026-11-20): as
`mergingWalker.finishDescent` (the parent's path is the child's less its last element, `ownPath_pop`;
the child goes back to the spare list).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.toFieldSetWalker__finishDescent
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsBPers

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

theorem typed.toFieldSetWalker.finishDescent.wp_proof :
    typed.toFieldSetWalker.finishDescent.spec (GF := GF) :=
    fun w w2 sc S st st2 ps ps2 s sp a pe => by
  wp_start as ⟨Hcore, Hcore2, Hps2, Hsp, %Hspnn⟩
  unfold twCore
  icases Hcore with ⟨%tr0, Hw, #Htr, #Hsc, %HWF⟩
  icases Hcore2 with ⟨%tr2, Hw2, -⟩
  unfold spareWalkers
  icases Hsp with (%Hn | ⟨%sl, %ws, Hspp, Hws, Hwsc, Hwl⟩)
  · exact absurd Hn Hspnn
  ihave ⟨Hps2, %Hl2⟩ := ownPath_len _ _ $$ Hps2
  ihave Hps' := ownPath_pop ps2 st.path pe $$ Hps2
  wp_auto
  have hb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (ps2.len - W64 1) ∧
      sint.Z (ps2.len - W64 1) ≤ sint.Z ps2.cap := by
    simp only [List.length_append, List.length_singleton] at Hl2
    word
  simp only [hb, and_self, ↓reduceIte]
  wp_auto
  wp_apply (wp_slice_literal (V := Loc) [w2])
  isplitr
  · ipureintro; rfl
  iintro %sl2 ⟨Hsl2, -⟩
  (try wp_auto)
  wp_apply (wp_slice_append (V := Loc) sl ws _ [w2] (DFrac.own 1))
    $$ [$Hws $Hwsc $Hsl2] as %sl' ⟨Hws, Hwsc, -⟩
  iapply HΦ
  iexists _
  iframe
  simp only
  isplitr [Hw2 Hwl Hws Hwsc Hspp]
  · isplitr; iexact Htr
    isplitr; iexact Hsc
    ipureintro; exact HWF
  iright
  iexists sl', ws ++ [w2]
  iframe
  iapply (BigSepL.bigSepL_nil_intro (P := iprop(True)))
  ipureintro; trivial

end proof

end smd
end EtcdGrove
end Perennial
