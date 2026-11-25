/-
The proof of `Spec/google_golang_org/grpc/appendOversizedBlock.lean`: the kind byte appended, then
the four bytes of the length `maxHeaderBlock + 1` (`binary.BigEndian.AppendUint32`, whose bytes are
`be32`: `u32Le_reverse`).
-/
module

public import Spec.google_golang_org.grpc.appendOversizedBlock
public import Spec.encoding.binary.bigEndian__AppendUint32

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
variable [binary_sem : encoding.binary.Assumptions]

theorem grpc.appendOversizedBlock.wp_proof
    (wp_AppendUint32 : binary.bigEndian.AppendUint32.spec (GF := GF) (hG := hG)) :
    grpc.appendOversizedBlock.spec (GF := GF) (hG := hG) := by
  intro b vs kind
  wp_start as ⟨Hb, Hcap⟩
  ihave #Hpkg : isPkgInit (PROP := IProp GF) pkg_id.encoding.binary $$ []
  · iPkgInit
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := w8) (t := go.byte) [kind]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  wp_apply wp_slice_append (V := w8) b vs _ [kind] (DFrac.own 1) $$ [$Hb $Hcap $Hsl]
    as %b1 ⟨Hb1, Hcap1, -⟩
  wp_apply wp_AppendUint32 b1 _ (W32 16777217) $$ [$Hpkg $Hb1 $Hcap1] as %r ⟨Hr, Hrcap⟩
  iapply HΦ
  rw [u32Le_reverse]
  simp only [srvFrameBytes, List.append_assoc, List.singleton_append]
  iframe

end proof

end EtcdGrove
end Perennial
