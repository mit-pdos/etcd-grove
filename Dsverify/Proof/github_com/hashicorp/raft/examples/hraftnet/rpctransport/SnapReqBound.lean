/-
The proof of `rpctransport.SnapReqBound`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.SnapReqBound
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

theorem github_com.hashicorp.raft.examples.hraftnet.rpctransport.SnapReqBound.wp_proof
    (wp_BytesBound : github_com.hashicorp.raft.examples.hraftnet.rpctransport.BytesBound.spec (GF := GF) (hG := hG))
    (wp_hdrBound : github_com.hashicorp.raft.examples.hraftnet.rpctransport.hdrBound.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.hraftnet.rpctransport.SnapReqBound.spec (GF := GF) (hG := hG) := by
  intro a dq w dq1 id ad s0 s1 s2 s3
  wp_start as ⟨Ha, Hid, Had, H0, H1, H2, H3⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ha
  iStructNamed Ha
  (try (irename : ("_" ∷ True : IProp GF) => Hjunk; iclear Hjunk))
  (try wp_auto)
  wp_apply wp_hdrBound $$ [$Hdr $Hid $Had] as %r1 ⟨%Hr1, Hdr, Hid, Had⟩
  wp_apply wp_BytesBound $$ [$H0] as %q0 ⟨%Hq0, H0⟩
  wp_apply wp_BytesBound $$ [$H1] as %q1 ⟨%Hq1, H1⟩
  wp_apply wp_BytesBound $$ [$H2] as %q2 ⟨%Hq2, H2⟩
  wp_apply wp_BytesBound $$ [$H3] as %q3 ⟨%Hq3, H3⟩
  have hh : hdrBoundN id ad ≤ 16 + 2 * (17 + 8 * 2 ^ 30) := by
    unfold hdrBoundN; have := bytesBoundN_le id.length; have := bytesBoundN_le ad.length; omega
  have bq0 := bytesBoundN_le s0.length
  have bq1 := bytesBoundN_le s1.length
  have bq2 := bytesBoundN_le s2.length
  have bq3 := bytesBoundN_le s3.length
  have h128 : uint.nat (W64 128) = 128 := by rfl
  have h64 : uint.nat (W64 64) = 64 := by rfl
  iapply HΦ
  iframe
  isplitr
  · ipureintro
    unfold snapBoundN
    have e1 := w64_add_eq h128 Hr1 (by omega)
    have e2 := w64_add_eq e1 Hq0 (by omega)
    have e3 := w64_add_eq e2 Hq1 (by omega)
    have e4 := w64_add_eq e3 Hq2 (by omega)
    have e5 := w64_add_eq e4 Hq3 (by omega)
    have e6 := w64_add_eq e5 h128 (by omega)
    rw [e6]
    (try omega)
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef]
  iframe

end proof

end Perennial
