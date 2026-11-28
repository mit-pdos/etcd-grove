/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__setCurrentTerm.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).setCurrentTerm`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__setCurrentTerm
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__setCurrentTerm
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

open github_com.hashicorp.raft proto gprot

theorem github_com.hashicorp.raft.Raft.setCurrentTerm.wp_proof
    (wp_rs_setCurrentTerm : github_com.hashicorp.raft.raftState.setCurrentTerm.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.setCurrentTerm.spec (GF := GF) (hG := hG) := by
  fun r γ rc i s sst t tp => by
  wp_start as ⟨#Hr, Hs, Hst, Htp, %Htp⟩
  ihave #Hg := pkgGlobals_access $$ Hpkg
  unfold pkgGlobals
  icases Hg with ⟨-, ⟨%k0, #Hk0, #Hk0s⟩, -, -, -⟩
  ihave ⟨%x, #Hstx, #Hss⟩ := isRaft_stableStore r γ rc i $$ Hr
  ihave #Htc := isRaft_termCell r γ rc i $$ Hr
  ihave #Hdur := isRaft_durInv r γ rc i $$ Hr
  ihave ⟨#HInv, -⟩ := isRaft_proto r γ rc i $$ Hr
  unfold isStableStore
  icases Hss with ⟨#HgetU, #HsetU, #Hget, #Hset⟩
  unfold stV
  icases Hst with ⟨%g, Hst⟩
  have Ht64 : uint.nat t < 2 ^ 64 := by word
  have Hwt : (W64 (uint.nat t : Int)) = t := by word
  ihave Hwin := setUint64_term_win γ rc i s tp (uint.nat t) sst g Htp Ht64
    iprop(srvVP rc s (some tp) none ∗
      stVS rc { sst with ints := sst.ints.insert (go!"CurrentTerm" : List w8) (W64 (uint.nat t)) } g)
    $$ Hdur Hs Hst Htp
  ihave ⟨HW, HAU⟩ := Hwin $$ [] 
  · iintro Hs Hst; imodintro; iframe
  rw [Hwt]
  wp_auto
  wp_apply_core HsetU $$ Hk0s HW
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
  rcases Htp with ⟨rfl, Hle⟩ | ⟨rfl, Hel⟩
  · wp_apply wp_rs_setCurrentTerm r γ rc i t
      iprop(srvV rc { s with term := uint.nat t } ∗ termLb γ i (uint.nat t)) $$ [$Htc Hs] as ⟨Hs, #Hlb⟩
    · iintro %t0 Hc
      iapply ncfupd_wand
      isplitl [Hs Hc]
      · iapply setTerm_R γ rc i gd_diff_termN s (uint.nat t) t0 $$ [$HInv $Hdur $Hs $Hc]
      iintro ⟨Hs, Hc, #Hlb⟩
      iframe; iframe #
    iapply HΦ
    iframe; iframe #
    unfold stV; iexists g; iexact Hst
  · wp_apply wp_rs_setCurrentTerm r γ rc i t
      iprop(srvV rc { s with term := s.term + 1 } ∗ termLb γ i (s.term + 1) ∗
        candIs γ i (s.term + 1) s.log.length (lastTerm s.log) ∗
        pubOwn γ i (s.term + 1) 0 ∗ ccfgOwn γ i (s.term + 1) 0 ∗ ccfgOwn γ i (s.term + 1) 0)
      $$ [$Htc Hs] as ⟨Hs, #Hlb, Hrest⟩
    · iintro %t0 Hc
      iapply ncfupd_wand
      isplitl [Hs Hc]
      · iapply electTerm_R γ rc i gd_diff_termN s t0 $$ [$HInv $Hdur $Hs $Hc]
      iintro ⟨Hs, Hc, Hrest⟩
      rw [Hel]
      iframe
    iapply HΦ
    rw [Hel]
    iframe; iframe #
    unfold stV; iexists g; iexact Hst
