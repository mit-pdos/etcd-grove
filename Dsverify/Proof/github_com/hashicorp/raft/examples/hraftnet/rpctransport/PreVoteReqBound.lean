/-
The proof of `rpctransport.PreVoteReqBound`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.PreVoteReqBound
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.BytesBound
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.hdrBound

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

theorem github_com.hashicorp.raft.examples.hraftnet.rpctransport.PreVoteReqBound.wp_proof
    (wp_BytesBound : github_com.hashicorp.raft.examples.hraftnet.rpctransport.BytesBound.spec (GF := GF) (hG := hG))
    (wp_hdrBound : github_com.hashicorp.raft.examples.hraftnet.rpctransport.hdrBound.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.hraftnet.rpctransport.PreVoteReqBound.spec (GF := GF) (hG := hG) := by
  intro a dq w dq1 id ad 
  wp_start as ⟨Ha, Hid, Had⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ha
  iStructNamed Ha
  (try (irename : ("_" ∷ True : IProp GF) => Hjunk; iclear Hjunk))
  (try wp_auto)
  wp_apply wp_hdrBound $$ [$Hdr $Hid $Had] as %r1 ⟨%Hr1, Hdr, Hid, Had⟩
  have hh : hdrBoundN id ad ≤ 16 + 2 * (17 + 8 * 2 ^ 30) := by
    unfold hdrBoundN; have := bytesBoundN_le id.length; have := bytesBoundN_le ad.length; omega
  have h128 : uint.nat (W64 128) = 128 := by rfl
  have h64 : uint.nat (W64 64) = 64 := by rfl
  iapply HΦ
  iframe
  isplitr
  · ipureintro
    unfold preVoteBoundN
    have e1 := w64_add_eq h128 Hr1 (by omega)
    have e2 := w64_add_eq e1 h64 (by omega)
    rw [e2]
    (try omega)
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef]
  iframe

end proof

end Perennial
