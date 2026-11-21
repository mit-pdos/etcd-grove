/-
The proof of `putString` (`Net/Spec/net/rpc/putString.lean`): `putU64` of the length, then
the string's bytes appended.
-/
module

public import Net.Spec.net.rpc.putString
public import Net.Spec.net.rpc.putU64
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

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

theorem putString.wp_proof (wp_putU64 : putU64.spec (GF := GF) (hG := hG)) :
    putString.spec (GF := GF) (hG := hG) := by
  intro b vs s
  wp_start as ⟨Hb, Hcap⟩
  wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hslen
  wp_apply wp_putU64 b vs _ $$ [$Hb $Hcap] as %b1 ⟨Hb1, Hb1cap⟩
  wp_apply wp_string_to_bytes as %sl ⟨Hsl, -⟩
  wp_apply wp_slice_append (V := w8) _ _ _ _ _ $$ [$Hb1 $Hb1cap $Hsl] as %b2 ⟨Hb2, Hcap2, -⟩
  iapply HΦ
  rw [List.append_assoc]
  iframe

end proof

end net.rpc
end Perennial
