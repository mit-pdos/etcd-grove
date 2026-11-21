/-
The proof of `putFrame` (`Net/Spec/net/rpc/putFrame.lean`): `putU64` of the payload's length,
then the payload appended.
-/
module

public import Net.Spec.net.rpc.putFrame
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

theorem putFrame.wp_proof (wp_putU64 : putU64.spec (GF := GF) (hG := hG)) :
    putFrame.spec (GF := GF) (hG := hG) := by
  intro b vs pl dq p
  wp_start as ⟨Hb, Hcap, Hp⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hp
  wp_auto
  wp_apply wp_putU64 b vs _ $$ [$Hb $Hcap] as %b1 ⟨Hb1, Hb1cap⟩
  wp_apply wp_slice_append (V := w8) _ _ _ _ _ $$ [$Hb1 $Hb1cap $Hp] as %b2 ⟨Hb2, Hcap2, Hp⟩
  iapply HΦ
  have hl : (W64 p.length : w64) = pl.len := by rw [Hlen.1]; word
  rw [List.append_assoc, show u64Le pl.len ++ p = frameOf p by rw [frameOf, hl]]
  iframe

end proof

end net.rpc
end Perennial
