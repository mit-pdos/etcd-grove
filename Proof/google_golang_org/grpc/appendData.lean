/-
The proof of `Spec/google_golang_org/grpc/appendData.lean`: three appends.
-/
module

public import Spec.google_golang_org.grpc.appendData

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : google_golang_org.grpc.Assumptions]

theorem grpc.appendData.wp_proof :
    grpc.appendData.spec (GF := GF) (hG := hG) := by
  intro b vs hdr hd dqh pl ps dqp
  wp_start as ⟨Hb, Hcap, Hh, Hp⟩
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := w8) (t := go.byte) [frameData]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  wp_apply wp_slice_append (V := w8) b vs _ [frameData] (DFrac.own 1) $$ [$Hb $Hcap $Hsl]
    as %b1 ⟨Hb1, Hcap1, -⟩
  wp_apply wp_slice_append (V := w8) b1 _ hdr hd dqh $$ [$Hb1 $Hcap1 $Hh]
    as %b2 ⟨Hb2, Hcap2, Hh⟩
  wp_apply wp_slice_append (V := w8) b2 _ pl ps dqp $$ [$Hb2 $Hcap2 $Hp]
    as %b3 ⟨Hb3, Hcap3, Hp⟩
  iapply HΦ
  simp only [List.append_assoc, List.singleton_append]
  iframe

end proof

end EtcdGrove
end Perennial
