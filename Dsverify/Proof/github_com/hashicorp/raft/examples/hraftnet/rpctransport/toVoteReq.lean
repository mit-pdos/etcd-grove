/-
The proof of `rpctransport.toVoteReq`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.toVoteReq
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

theorem github_com.hashicorp.raft.examples.hraftnet.rpctransport.toVoteReq.wp_proof
    (wp_copyBytes : github_com.hashicorp.raft.examples.hraftnet.rpctransport.copyBytes.spec (GF := GF) (hG := hG))
    (wp_toHeader : github_com.hashicorp.raft.examples.hraftnet.rpctransport.toHeader.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.hraftnet.rpctransport.toVoteReq.spec (GF := GF) (hG := hG) := by
  intro a dq rq dq1 id ad b0
  wp_start as ⟨Ha, Hid, Had, Hb0⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ha
  iStructNamed Ha
  (try (irename : ("_" ∷ True : IProp GF) => Hjunk; iclear Hjunk))
  wp_auto
  wp_apply wp_toHeader $$ [$Hid $Had] as %i %d ⟨Hid, Had, Hi, Hd⟩
  wp_apply wp_copyBytes $$ [$Hb0] as %c0 ⟨Hb0, Hc0⟩
  irename «$r0» => Hp
  iapply HΦ
  iframe Hid Had Hb0
  isplitr [Hp Hi Hd Hc0]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  iexists i, d, c0
  iframe

end proof

end Perennial
