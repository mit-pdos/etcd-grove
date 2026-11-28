/-
The proof of `rpctransport.hdrBound`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.hdrBound
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.BytesBound

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.rpctransport.Assumptions]

open github_com.hashicorp.raft.examples.hraftnet.rpctransport

theorem github_com.hashicorp.raft.examples.hraftnet.rpctransport.hdrBound.wp_proof
    (wp_BytesBound : github_com.hashicorp.raft.examples.hraftnet.rpctransport.BytesBound.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.hraftnet.rpctransport.hdrBound.spec (GF := GF) (hG := hG) := by
  intro h dq hv dq1 dq2 id ad
  wp_start as ⟨Hh, Hid, Had⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hh
  iStructNamed Hh
  wp_auto
  wp_apply wp_BytesBound $$ [$Hid] as %r1 ⟨%Hr1, Hid⟩
  wp_apply wp_BytesBound $$ [$Had] as %r2 ⟨%Hr2, Had⟩
  have b1 := bytesBoundN_le id.length
  have b2 := bytesBoundN_le ad.length
  iapply HΦ
  iframe Hid Had
  isplitr
  · ipureintro
    unfold hdrBoundN
    have h16 : uint.nat (W64 16) = 16 := by rfl
    rw [w64_add_nat _ _ (by rw [w64_add_nat _ _ (by omega), h16]; omega), w64_add_nat _ _ (by omega), h16]
    omega
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef]
  iframe

end proof

end Perennial
