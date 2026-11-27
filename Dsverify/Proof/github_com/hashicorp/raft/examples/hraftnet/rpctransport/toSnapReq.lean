/-
The proof of `rpctransport.toSnapReq`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.toSnapReq
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.copyBytes
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.toHeader

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

theorem github_com.hashicorp.raft.examples.hraftnet.rpctransport.toSnapReq.wp_proof
    (wp_copyBytes : github_com.hashicorp.raft.examples.hraftnet.rpctransport.copyBytes.spec (GF := GF) (hG := hG))
    (wp_toHeader : github_com.hashicorp.raft.examples.hraftnet.rpctransport.toHeader.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.hraftnet.rpctransport.toSnapReq.spec (GF := GF) (hG := hG) := by
  intro a dq rq dq1 id ad b0 b1 b2 data
  wp_start as ⟨Ha, Hid, Had, Hb0, Hb1, Hb2⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ha
  iStructNamed Ha
  (try (irename : ("_" ∷ True : IProp GF) => Hjunk; iclear Hjunk))
  wp_auto
  wp_apply wp_toHeader $$ [$Hid $Had] as %i %d ⟨Hid, Had, Hi, Hd⟩
  wp_apply wp_copyBytes $$ [$Hb0] as %c0 ⟨Hb0, Hc0⟩
  wp_apply wp_copyBytes $$ [$Hb1] as %c1 ⟨Hb1, Hc1⟩
  wp_apply wp_copyBytes $$ [$Hb2] as %c2 ⟨Hb2, Hc2⟩
  irename «$r0» => Hp
  iapply HΦ
  iframe Hid Had Hb0 Hb1 Hb2
  isplitr [Hp Hi Hd Hc0 Hc1 Hc2]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  iexists i, d, c0, c1, c2
  iframe

end proof

end Perennial
