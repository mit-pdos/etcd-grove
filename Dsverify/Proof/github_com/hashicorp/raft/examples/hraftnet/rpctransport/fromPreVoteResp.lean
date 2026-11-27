/-
The proof of `rpctransport.fromPreVoteResp`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.fromPreVoteResp
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.fromHeader

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

theorem github_com.hashicorp.raft.examples.hraftnet.rpctransport.fromPreVoteResp.wp_proof
    (wp_fromHeader : github_com.hashicorp.raft.examples.hraftnet.rpctransport.fromHeader.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.hraftnet.rpctransport.fromPreVoteResp.spec (GF := GF) (hG := hG) := by
  intro a dq rq dq1 id ad 
  wp_start as ⟨Ha, Hid, Had⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ha
  iStructNamed Ha
  (try (irename : ("_" ∷ True : IProp GF) => Hjunk; iclear Hjunk))
  wp_auto
  wp_apply wp_fromHeader $$ [$Hid $Had] as %i %d ⟨Hid, Had, Hi, Hd⟩
  (try wp_auto)
  iapply HΦ
  iframe Hid Had Hi Hd
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef]
  iframe

end proof

end Perennial
