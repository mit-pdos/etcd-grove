/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/commitment__getCommitIndex.lean (241f27e).
-/
/-
The proof of `commitment__getCommitIndex` (replication subsystem).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.commitment__getCommitIndex
public import Dsverify.Proof.github_com.hashicorp.raft.ReplBase

@[expose] public section

set_option linter.unusedVariables false
set_option linter.deprecated false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]
variable [hRB : ReceiptBoundLe GF (2 ^ 62)]

open github_com.hashicorp.raft github_com.hashicorp.raft.gprot proto

theorem github_com.hashicorp.raft.commitment.getCommitIndex.wp_proof :
    github_com.hashicorp.raft.commitment.getCommitIndex.spec (GF := GF) (hG := hG) :=
  fun γ i T cm => by
  wp_start as #Hcm
  wp_auto
  wp_apply wp_with_defer as %defer Hdefer
  unfold isCommitment
  icases Hcm with ⟨-, #Hcm⟩
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Lock $$ [$Hcm] as ⟨Hlocked, Hinv⟩
  unfold commitInv
  icases Hinv with ⟨%ch, %mi, %mm, %ci, %si, %n0, %p, %e, Hch, #Hchn, Hmi, Hmm, Hcc, #He, %Hdom, Hacks, Hci, #Hcio, #Hsip, #Hn0, %Hsi, #Hl, #HInv⟩
  wp_auto
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Unlock $$ [$Hcm $Hlocked Hch Hmi Hmm Hacks Hci Hcc]
  · iexists ch, mi, mm, ci, si, n0, p, e
    iframe
    iframe #
    ipureintro; exact ⟨Hdom, Hsi⟩
  iapply HΦ
  icases Hcio with (%H0 | ⟨%Hlt, %k, %pk, %Hk, #Hc⟩)
  · ileft; ipureintro; exact H0
  · iright; iexists n0, k, pk; iframe #; ipureintro; exact ⟨Hlt, Hk⟩

end proof

end Perennial
