/-
`bufio.NewWriterSize`, generic (see `Spec/bufio/NewWriterSizeRep.lean`). Ported from dsverify-lab's
`Harness/Proof/bufio/Writer.lean` (`wp_NewWriter`).
-/
module

public import Spec.bufio.NewWriterSizeRep

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.bufio.Assumptions]

set_option goose.wp.extras true

theorem bufio.NewWriterSize.wp_proofRep : bufio.NewWriterSize.specRep (GF := GF) (hG := hG) := by
  intro wi Ew size
  wp_start as ⟨%hty, #Hpkg⟩
  wp_auto
  simp only [ite_eq_right_of_eq_false _ _ (eq_false hty), decide_eq_false hty]
  wp_auto
  have h0 : sint.Z (W64 0) = 0 := rfl
  wp_if_destruct
  all_goals
    try wp_auto
    wp_apply (wp_slice_make2 (V := w8) _) as %buf ⟨Hbuf, -⟩
    · ipureintro; first | decide | omega
    try wp_auto
    iapply HΦ
    unfold bufio.writerRep
    iexists buf, 0, _
    simp only [List.nil_append, List.length_nil]
    iframe «$r0» Hbuf
    isplitr
    · ipureintro
      refine ⟨rfl, ?_, ?_⟩
      · simp only [List.length_replicate]; first | (show 0 < (sint.Z _).toNat; omega) | decide
      · simp only [List.length_replicate, bufio.writerSize]
        split <;> first | rfl | omega
    unfold io.werrAt
    ileft; ipureintro; rfl

end proof

end EtcdGrove
end Perennial
