/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__persistVote.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).persistVote`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__persistVote
public import Dsverify.Proof.github_com.hashicorp.raft.handlers.Base
public import Dsverify.Proof.github_com.hashicorp.raft.DurHelpers

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

theorem github_com.hashicorp.raft.Raft.persistVote.wp_proof :
    github_com.hashicorp.raft.Raft.persistVote.spec (GF := GF) (hG := hG) :=
  fun r γ rc i s sst t cs c li lt => by
  wp_start as ⟨#Hr, Hs, Hst, #Hcs, #Hci, %Hpre⟩
  ihave #Hg := pkgGlobals_access $$ Hpkg
  unfold pkgGlobals
  icases Hg with ⟨-, -, ⟨%k1, #Hk1, #Hk1s⟩, ⟨%k2, #Hk2, #Hk2s⟩, -⟩
  ihave ⟨%x, #Hstx, #Hss⟩ := isRaft_stableStore r γ rc i $$ Hr
  ihave #Hdur := isRaft_durInv r γ rc i $$ Hr
  ihave ⟨#HInv, -⟩ := isRaft_proto r γ rc i $$ Hr
  unfold isStableStore
  icases Hss with ⟨#HgetU, #HsetU, #Hget, #Hset⟩
  rw [stV_eq rc sst]
  icases Hst with ⟨%g, Hst⟩
  obtain ⟨Ht, Hv, Hup⟩ := Hpre
  have Hwt : (W64 (s.term : Int)) = t := by rw [← Ht]; word
  -- the first write: `Set(LastVoteCand, c)`, no step
  ihave Hwin := set_voteCand_win γ rc i s sst g c Hv
    iprop(srvV rc s ∗ stVS rc { sst with bytes := sst.bytes.insert (go!"LastVoteCand" : List w8) c } g)
    $$ Hdur Hs Hst
  ihave ⟨HW, HAU⟩ := Hwin $$ []
  · iintro Hs Hst; imodintro; iframe
  wp_auto
  wp_apply_core Hset $$ Hk2s Hcs HW
  iintro HW Hnc
  imod HAU $$ HW Hnc with ⟨Hnc, HAU⟩
  iframe Hnc
  imodintro
  inext
  icases HAU with ⟨%D0, Hown, Hcl⟩
  iexists D0
  iframe Hown
  iintro Hown
  imod Hcl $$ Hown with ⟨Hs, Hst⟩
  imodintro
  wp_auto
  -- the second write: `SetUint64(LastVoteTerm, t)`, the vote
  have Hc : ({ sst with bytes := sst.bytes.insert (go!"LastVoteCand" : List w8) c } : StableAbs).bytes.lookup
      (go!"LastVoteCand" : List w8) = some c := by
    simp only [GMap.lookup_insert]
  ihave Hwin := setUint64_vote_win γ rc i s c li lt
    { sst with bytes := sst.bytes.insert (go!"LastVoteCand" : List w8) c } g ⟨Hv, Hup⟩ Hc
    iprop(srvV rc { s with vterm := s.term, vcand := c } ∗ voteIs γ i s.term c ∗
      stVS rc { ({ sst with bytes := sst.bytes.insert (go!"LastVoteCand" : List w8) c } : StableAbs) with
        ints := sst.ints.insert (go!"LastVoteTerm" : List w8) (W64 s.term) } g)
    $$ HInv Hdur Hs Hst Hci
  ihave ⟨HW, HAU⟩ := Hwin $$ []
  · iintro Hs Hst Hvo; imodintro; iframe
  rw [Hwt]
  wp_apply_core HsetU $$ Hk1s HW
  iintro HW Hnc
  imod HAU $$ HW Hnc with ⟨Hnc, HAU⟩
  iframe Hnc
  imodintro
  inext
  icases HAU with ⟨%D0, Hown, Hcl⟩
  iexists D0
  iframe Hown
  iintro Hown
  imod Hcl $$ Hown with ⟨Hs, #Hvo, Hst⟩
  imodintro
  wp_auto
  iapply HΦ
  iframe; iframe #
  rw [stV_eq]
  iexists g
  iexact Hst
