/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/verifyFuture__vote.lean (241f27e).
-/
/-
The proof of `verifyFuture__vote` (replication subsystem, stage 2).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.verifyFuture__vote
public import Dsverify.Proof.github_com.hashicorp.raft.ReplNotify

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

theorem github_com.hashicorp.raft.verifyFuture.vote.wp_proof :
    github_com.hashicorp.raft.verifyFuture.vote.spec (GF := GF) (hG := hG) :=
  fun r γ rc i T sv L vch j v b => by
  wp_start as ⟨#Hr, #Hvch, #Hreg, #Hvj, Hb⟩
  ihave ⟨%vch', %γv, #Hvch', #Hbag⟩ := isRaft_verifyCh r γ rc i $$ Hr
  icombine Hvch Hvch' gives %Heq
  subst vch'
  wp_apply wp_with_defer as %defer Hdefer
  unfold verifyReg
  icases Hreg with ⟨%q, #Hvreg, #Hq, #Hpre, #Hwi, #Hn0, %Hqb, #Hmu⟩
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
  iunfold voteInv at Hinv
  icases Hinv with ⟨%nc, Hnc, (%Hnil | ⟨%Hvc, Hback, %n, %Q, Hvotes, %HQ, HQl⟩)⟩
  · -- already notified: nothing
    subst Hnil
    wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hnc]
    · inext; unfold voteInv; iexists chan.nil; iframe; ileft; ipureintro; rfl
    iapply HΦ; itrivial
  subst nc
  obtain ⟨Hn, HQnd, HQv⟩ := HQ
  wp_auto
  wp_if_destruct
  · -- `vch` is nil: nothing (not the case in practice; no fact needed)
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hnc Hback Hvotes HQl]
    · inext; unfold voteInv; iexists _; iframe; iright
      isplitr; · ipureintro; rfl
      iframe Hback
      iexists n, Q; iframe; ipureintro; exact ⟨Hn, HQnd, HQv⟩
    iapply HΦ; itrivial
  cases b with
  | false =>
    -- a `false` vote: send `v` back (short of the quorum, or with the quorum it already had)
    wp_auto
    wp_apply (wp_bag_send γv vch v (verifyP γ rc i vch)) $$ [Hback Hvotes HQl]
    · iframe #
      unfold verifyP verifyVoted
      iright
      iexists T, sv, L, n, q
      iframe; iframe #
      isplitr
      · unfold verifyReg; iexists q; iframe #; ipureintro; exact Hqb
      by_cases hq : uint.nat n < uint.nat q
      · ileft; ipureintro; exact hq
      · iright; iexists Q
        isplitr; · ipureintro; exact ⟨by omega, HQnd, HQv⟩
        iapply (BigSepL.bigSepL_mono (fun {k x} _ => ?_)) $$ HQl
        iintro ⟨-, H⟩; iexact H
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hnc]
    · inext; unfold voteInv; iexists chan.nil; iframe; ileft; ipureintro; rfl
    iapply HΦ; itrivial
  | true =>
    icases Hb with (%Hf | ⟨Htok, #Hwit, %Hj⟩)
    · cases Hf
    -- `j` has not voted yet (its token is exclusive)
    by_cases hjQ : j ∈ Q
    · iexfalso
      iapply voteTok_excl rc v j Q (fun j' => respWit γ j' T sv) hjQ $$ [Htok HQl]
      iframe
    have hlen : (j :: Q).length ≤ (cfgOfC γ.cv L).length := by
      apply List.Nodup.length_le_of_subset (List.nodup_cons.mpr ⟨hjQ, HQnd⟩)
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Hj
      · exact HQv x hx
    have hn1 : uint.nat (n + 1) = Q.length + 1 := by
      simp only [List.length_cons] at hlen
      word
    wp_auto
    wp_if_destruct
    · -- a quorum (as the code compares): send `v` back
      wp_apply (wp_bag_send γv vch v (verifyP γ rc i vch)) $$ [Hback Hvotes HQl Htok]
      · iframe #
        unfold verifyP verifyVoted
        iright
        iexists T, sv, L, (n + 1), q
        iframe; iframe #
        isplitr
        · unfold verifyReg; iexists q; iframe #; ipureintro; exact Hqb
        by_cases hq : uint.nat (n + 1) < uint.nat q
        · ileft; ipureintro; exact hq
        · iright; iexists (j :: Q)
          isplitr
          · ipureintro
            refine ⟨by simp only [List.length_cons]; omega, List.nodup_cons.mpr ⟨hjQ, HQnd⟩, ?_⟩
            intro x hx
            rcases List.mem_cons.mp hx with rfl | hx
            · exact Hj
            · exact HQv x hx
          iapply BigSepL.bigSepL_cons.2
          isplitr; · iexact Hwit
          iapply (BigSepL.bigSepL_mono (fun {k x} _ => ?_)) $$ HQl
          iintro ⟨-, H⟩; iexact H
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hnc]
      · inext; unfold voteInv; iexists chan.nil; iframe; ileft; ipureintro; rfl
      iapply HΦ; itrivial
    · -- not yet a quorum: count the vote
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hnc Hback Hvotes HQl Htok]
      · inext; unfold voteInv; iexists vch; iframe; iright
        isplitr; · ipureintro; rfl
        iframe Hback
        iexists (n + 1), (j :: Q)
        iframe
        isplitr
        · ipureintro
          refine ⟨by simp only [List.length_cons]; omega, List.nodup_cons.mpr ⟨hjQ, HQnd⟩, ?_⟩
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact Hj
          · exact HQv x hx
        iframe #
      iapply HΦ; itrivial

end proof

end Perennial
