/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/countingReader__Read.lean (241f27e).
-/
/-
The proof of `raft.(*countingReader).Read` (stage 3, snap).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.countingReader__Read
public import Perennial.Proof.sync.Link

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

open github_com.hashicorp.raft proto gprot

theorem github_com.hashicorp.raft.countingReader.Read.wp_proof :
    github_com.hashicorp.raft.countingReader.Read.spec (GF := GF) (hG := hG) := by
  intro cr src R eof p buf cs
  wp_start as ⟨#Hcr, #HRd, %Hbuf, HR, Hp⟩
  unfold countingReaderIs
  icases Hcr with ⟨#Hrd, #Hmu⟩
  unfold streamReaderOk
  wp_auto
  wp_apply HRd $$ %p %buf %cs [] HR Hp as %n %err %Hn Hp HR
  · ipureintro; exact Hbuf
  wp_apply (sync.Mutex.wp_Lock _ _) $$ [$Hmu] with ⟨Hown, ⟨%nb, Hb⟩⟩
  wp_apply (sync.Mutex.wp_Unlock _ _) $$ [Hmu Hown Hb]
  · iframe #; iframe
  iapply HΦ
  iframe
  ipureintro; exact Hn

end proof

end Perennial
