/-
The proof of `rpctransport.toHeader`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.toHeader
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.copyBytes

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

theorem github_com.hashicorp.raft.examples.hraftnet.rpctransport.toHeader.wp_proof
    (wp_copyBytes : github_com.hashicorp.raft.examples.hraftnet.rpctransport.copyBytes.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.hraftnet.rpctransport.toHeader.spec (GF := GF) (hG := hG) := by
  intro h dq1 dq2 id ad
  wp_start as ⟨Hid, Had⟩
  wp_auto
  wp_apply wp_copyBytes $$ [$Hid] as %c1 ⟨Hid, Hc1⟩
  wp_apply wp_copyBytes $$ [$Had] as %c2 ⟨Had, Hc2⟩
  wp_end

end proof

end Perennial
