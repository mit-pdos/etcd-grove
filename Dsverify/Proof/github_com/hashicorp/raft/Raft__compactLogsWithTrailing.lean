/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__compactLogsWithTrailing.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).compactLogsWithTrailing` (stage 3).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__compactLogsWithTrailing
public import Dsverify.Proof.github_com.hashicorp.raft.InstallBase
public import Dsverify.Spec.github_com.hashicorp.raft.min

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
variable [hRB : ReceiptBoundLe GF (2 ^ 62)]

open github_com.hashicorp.raft proto gprot

theorem github_com.hashicorp.raft.Raft.compactLogsWithTrailing.wp_proof
    (wp_min : github_com.hashicorp.raft.min.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.compactLogsWithTrailing.spec (GF := GF) (hG := hG) :=
  fun r γ rc i x li tl tid => by
  wp_start as ⟨#Hr, #Hcx, %Hx, Htok⟩
  ihave ⟨%lsx, #Hlsf, #Hls, -⟩ := isRaft_logStore r γ rc i $$ Hr
  ihave #HlogC := isRaft_durInv r γ rc i $$ Hr
  unfold isLogStore
  icases Hls with ⟨-, #HFirst, -, -, -, #HDel⟩
  wp_auto
  wp_apply HFirst $$ Htok as %mn Htok
  wp_if_destruct
  · iapply HΦ; iframe; ipureintro; rfl
  wp_apply wp_min
  obtain ⟨mx, Hmx⟩ : ∃ mx : w64, mx = (if uint.Z x ≤ uint.Z (li - tl) then x else li - tl) := ⟨_, rfl⟩
  rw [← Hmx]
  have Hmxx : uint.nat mx ≤ uint.nat x := by
    rw [Hmx]; split <;> word
  wp_if_destruct
  · iapply HΦ; iframe; ipureintro; rfl
  wp_bind
  iapply HDel $$ %mn %mx %_ []
  · ipureintro; omega
  iapply (snapProof.logCell_compact γ rc i (uint.nat mn) (uint.nat mx) (uint.nat x) Hmxx _)
  iframe HlogC Hcx
  wp_auto
  iapply HΦ; iframe; ipureintro; rfl

end proof

end Perennial
