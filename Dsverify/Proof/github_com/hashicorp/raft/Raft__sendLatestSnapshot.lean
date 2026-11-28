/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__sendLatestSnapshot.lean (241f27e).
-/
/-
The proof of `Raft__sendLatestSnapshot` (replication subsystem).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__sendLatestSnapshot
public import Perennial.Spec.fmt.Errorf
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__getRPCHeader
public import Dsverify.Spec.github_com.hashicorp.raft.EncodeConfiguration
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__getCurrentTerm
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__handleStaleTerm
public import Dsverify.Spec.github_com.hashicorp.raft.followerReplication__setLastContact
public import Dsverify.Spec.github_com.hashicorp.raft.commitment__match
public import Dsverify.Proof.github_com.hashicorp.raft.ReplSnap

@[expose] public section

set_option linter.unusedVariables false

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

theorem github_com.hashicorp.raft.Raft.sendLatestSnapshot.wp_proof
    (wp_Errorf : fmt.Errorf.spec (GF := GF) (hG := hG))
    (wp_StoreUint64 : sync.atomic.StoreUint64.spec (GF := GF) (hG := hG))
    (wp_getRPCHeader : github_com.hashicorp.raft.Raft.getRPCHeader.spec (GF := GF) (hG := hG))
    (wp_EncodeConfiguration : github_com.hashicorp.raft.EncodeConfiguration.spec (GF := GF) (hG := hG))
    (wp_getCurrentTerm : github_com.hashicorp.raft.raftState.getCurrentTerm.spec (GF := GF) (hG := hG))
    (wp_handleStaleTerm : github_com.hashicorp.raft.Raft.handleStaleTerm.spec (GF := GF) (hG := hG))
    (wp_setLastContact : github_com.hashicorp.raft.followerReplication.setLastContact.spec (GF := GF) (hG := hG))
    (wp_match : github_com.hashicorp.raft.commitment.match.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.sendLatestSnapshot.spec (GF := GF) (hG := hG) := by
  sorry -- hraft_robust L0: re-proved by its stage (HANDOFF.md)
/- stage-3 broken proof, kept (stage 2: no snapshots):
  fun r γ rc i s tid => by
  wp_start as ⟨#Hr, Htok⟩
  ihave ⟨%x, #Hsnaps, #Hss⟩ := isRaft_snapshotStore r γ rc i $$ Hr
  wp_auto
  wp_apply wp_with_defer as %defer Hdefer
  unfold isSnapshotStore
  wp_bind (App (Val #(methods x.ty _ x.v)) _)
  iapply Hss $$ Htok
  iintro %sl Hsl Htok
  ihave %Hlen := ownSlice_len $$ Hsl
  wp_auto
  wp_if_destruct
  · wp_apply (wp_Errorf _ slice.nil [] (DFrac.own 1)) as %e ⟨-, %s, -, He⟩
    · isplitl
      · iapply ownSlice_nil
      · iapply (fmt.argsOk_of_argsWf (by intro ii h; simp at h))
    iapply HΦ
    iframe Htok
    ipureintro; exact ⟨rfl, by simp⟩
  exfalso; apply Hif; simp at Hlen; word
  -/

end proof

end Perennial
