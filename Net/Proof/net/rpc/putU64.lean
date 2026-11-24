/-
The proof of `putU64` (`Net/Spec/net/rpc/putU64.lean`): the 8-byte slice literal appended;
dsverify's `wp_putU64`.
-/
module

public import Net.Spec.net.rpc.putU64

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace net.rpc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions]

open encoding.binary in
theorem putU64.wp_proof : putU64.spec (GF := GF) (hG := hG) := by
  intro b vs x
  wp_start as ⟨Hb, Hcap⟩
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := w8) (t := go.byte) (u64Le x)
  wp_auto
  isplitl []
  · ipureintro; rw [u64Le_8]; rfl
  iintro %sl_ptr ⟨Hsl, -⟩
  wp_apply wp_slice_append (V := w8) b vs _ (u64Le x) (DFrac.own 1) $$ [$Hb $Hcap $Hsl]
    as %r ⟨Hr, Hrcap, -⟩
  iapply HΦ
  iframe

end proof

end net.rpc
end Perennial
