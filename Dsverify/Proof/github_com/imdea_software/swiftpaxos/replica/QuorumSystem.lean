/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/replica/QuorumSystem.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`NewQuorumsFromFile("")`, `NewQuorumSystem` (no quorum file), and the `QuorumSystem` methods
`BallotAt`, `NumAQ`, `AQ`, `SameHigher`: proofs.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.QuorumSet
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section proofs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF]
variable [sem : go.Semantics] [replica.Assumptions] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]

set_option goose.wp.extras true

open replica.quorum

theorem replica.NewQuorumsFromFile.wp_proof : replica.NewQuorumsFromFile.spec := by
  intro r msg
  wp_start as #Hv
  iunfold errors.newVar at Hv
  icases Hv with ⟨%x, #Hx, -⟩
  wp_auto
  wp_apply wp_with_defer as %defer Hdefer
  iapply HΦ
  iframe Hx
  ipureintro; exact ⟨x, rfl⟩

theorem replica.NewQuorumSystem.wp_proof (wp_File : replica.NewQuorumsFromFile.spec)
    (wp_NewQuorumSet : replica.NewQuorumSet.spec) : replica.NewQuorumSystem.spec := by
  intro r dq N msg
  wp_start as ⟨#Hv, Hr, %HN⟩
  wp_auto
  wp_apply wp_File $$ [$Hv] as %e ⟨%He, #He⟩
  obtain ⟨x, rfl⟩ := He
  wp_auto
  wp_apply +noauto wp_NewQuorumSet as %qs #Hqs
  · ipureintro; exact HN
  wp_pures
  wp_alloc sp as Hs
  ipersist Hs
  wp_auto
  iapply HΦ
  iframe Hr
  iunfold isQS
  iexists qs
  iframe Hs Hqs

theorem replica.QuorumSystem.BallotAt.wp_proof : replica.QuorumSystem.BallotAt.spec := by
  intro sys N i
  wp_start as ⟨#Hs, %Hi⟩
  iunfold isQS at Hs
  icases Hs with ⟨%qs, #Hs, #Hqs⟩
  iStructNamed Hs
  wp_auto
  rw [show decide (sint.Z i < sint.Z (0 : w64)) = false from
    decide_eq_false (by have : sint.Z (0 : w64) = 0 := rfl; omega)]
  wp_auto
  iapply HΦ; itrivial

theorem replica.QuorumSystem.NumAQ.wp_proof : replica.QuorumSystem.NumAQ.spec := by
  intro sys N l
  wp_start as ⟨#Hs, %Hl⟩
  iunfold isQS at Hs
  icases Hs with ⟨%qs, #Hs, #Hqs⟩
  wp_auto
  wp_method_call
  wp_auto
  iunfold qsIs at Hqs
  icases Hqs with ⟨%HN, #Hqs⟩
  have hl : (sint.Z l).toNat < N := by omega
  ihave Hacc := qsOwn_acc qs N (lqs N) DFrac.discard _ hl $$ Hqs
  icases Hacc with ⟨%m, %p, #Hm, %Hp, %Hdom, #Hl, -⟩
  have hl32 : w32n (sint.Z l).toNat = l := by
    unfold w32n; rw [Int.toNat_of_nonneg Hl.1]; word
  rw [hl32] at Hp
  wp_apply (wp_map_lookup1 (K := w32) (V := Loc)) $$ [$Hm] as -
  rw [Hp]
  simp only [Option.getD_some]
  iunfold lqsOwn at Hl
  icases Hl with ⟨%mi, #Hmi, %Hdomi, -⟩
  wp_apply (wp_map_len (K := w32) (V := Loc) (t := replica.QuorumsOfLeader.ty)) $$ [$Hmi] as -
  rw [lqs_size mi _ Hdomi.1 Hdomi.2]
  unfold numAQ
  iapply HΦ; itrivial

theorem replica.QuorumSystem.AQ.wp_proof (wp_AQ : replica.QuorumSet.AQ.spec) :
    replica.QuorumSystem.AQ.spec := by
  intro sys N b
  wp_start as ⟨#Hs, %Hb⟩
  iunfold isQS at Hs
  icases Hs with ⟨%qs, #Hs, #Hqs⟩
  wp_auto
  wp_method_call
  wp_auto
  wp_method_call
  wp_auto
  rw [show ({ qs' := qs, ballots' := slice.nil } : replica.QuorumSystem).qs' = qs from rfl]
  wp_apply (wp_AQ qs N b) $$ [$Hqs] as %q #Hq
  · ipureintro; exact Hb
  iapply HΦ $$ Hq

theorem replica.QuorumSystem.SameHigher.wp_proof (wp_Leader : replica.Leader.spec) :
    replica.QuorumSystem.SameHigher.spec := by
  intro sys N sameAs higherThan
  wp_start as ⟨#Hs, %Hb⟩
  iunfold isQS at Hs
  icases Hs with ⟨%qs, #Hs, #Hqs⟩
  iStructNamed Hs
  wp_auto
  iunfold qsIs at Hqs
  icases Hqs with ⟨%HN, #Hqs⟩
  generalize hbn : (sint.Z sameAs).toNat = bn
  have hl : bn % N < N := Nat.mod_lt _ (by omega)
  ihave Hacc := qsOwn_acc qs N (lqs N) DFrac.discard _ hl $$ Hqs
  icases Hacc with ⟨%m, %p, #Hm, %Hp, %Hdom, #Hl, -⟩
  iunfold lqsOwn at Hl
  icases Hl with ⟨%mi, #Hmi, %Hdomi, -⟩
  have hN64 : sint.Z (W64 (N : Int)) = N := sint_W64 _ (by omega) (by omega)
  obtain ⟨hpos, h35⟩ := numAQ_pos N (bn % N) HN hl
  unfold numAQ at hpos h35
  have hL64 : sint.Z (W64 ((lqs N (bn % N)).length : Int)) = (lqs N (bn % N)).length :=
    sint_W64 _ (by omega) (by omega)
  have hL32 : sint.Z (W32 ((lqs N (bn % N)).length : Int)) = (lqs N (bn % N)).length :=
    sint_W32 _ (by omega) (by omega)
  wp_apply (wp_map_len (K := w32) (V := Loc) (t := replica.QuorumSet.ty)) $$ [$Hm] as -
  rw [lqs_size m N (by omega) Hdom]
  wp_apply wp_Leader
  · ipureintro; omega
  rw [hN64, srem_nat sameAs N (by omega) Hb, hbn]
  wp_apply (wp_map_lookup1 (K := w32) (V := Loc)) $$ [$Hm] as -
  rw [Hp]
  simp only [Option.getD_some]
  wp_apply (wp_map_len (K := w32) (V := Loc) (t := replica.QuorumsOfLeader.ty)) $$ [$Hmi] as -
  rw [lqs_size mi _ Hdomi.1 Hdomi.2, hL64]
  rw [if_neg (by omega)]
  wp_auto
  wp_apply (wp_map_lookup1 (K := w32) (V := Loc)) $$ [$Hm] as -
  rw [Hp]
  simp only [Option.getD_some]
  wp_apply (wp_map_len (K := w32) (V := Loc) (t := replica.QuorumsOfLeader.ty)) $$ [$Hmi] as -
  rw [lqs_size mi _ Hdomi.1 Hdomi.2, hL64]
  wp_apply (wp_map_len (K := w32) (V := Loc) (t := replica.QuorumSet.ty)) $$ [$Hm] as -
  rw [lqs_size m N (by omega) Hdom, hN64]
  unfold numAQ
  iapply HΦ; itrivial

end proofs

end Perennial.github_com.imdea_software.swiftpaxos

end
