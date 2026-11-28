/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/HasExistingState.lean (241f27e).
-/
/-
The proof of `raft.HasExistingState`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.HasExistingState
public import Dsverify.Proof.github_com.hashicorp.raft.EncodingLemmas

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

open github_com.hashicorp.raft proto

theorem github_com.hashicorp.raft.HasExistingState.wp_proof :
    github_com.hashicorp.raft.HasExistingState.spec (GF := GF) (hG := hG) := by
  intro Wl Ws Qc logsI stableI snapsI γ i ownL ownS ownSS eof sst tid
  wp_start as ⟨#Hlog, #Hst, #Hsn, HL, HS, %Hct, HSS, Htok⟩
  ihave #Hglob := pkgGlobals_of_isPkgInit $$ Hpkg
  unfold pkgGlobals
  icases Hglob with ⟨-, ⟨%kCT, #HkCT, #HkCTs⟩, -, -, -⟩
  unfold isStableStore
  icases Hst with ⟨#HGetU, -, -, -⟩
  unfold isLogStore
  icases Hlog with ⟨#HLastIdx, -⟩
  unfold isSnapStore
  icases Hsn with ⟨-, #HList, -⟩
  wp_auto
  wp_bind (App (Val #(methods _ _ _)) _)
  iapply HGetU $$ HkCTs Htok
  iapply ncfupd_of_fupd
  iapply fupd_mask_intro (by simp)
  iintro Hclose
  inext
  iexists sst
  iframe HS
  iintro HS
  imod Hclose
  imodintro
  iintro Htok
  wp_auto
  rw [show (sst.ints !! (go!"CurrentTerm" : List w8)).getD (W64 0) = W64 0 from Hct]
  wp_auto
  wp_bind (App (Val #(methods _ _ _)) _)
  iapply HLastIdx $$ Htok
  iapply ncfupd_of_fupd
  iapply fupd_mask_intro (by simp)
  iintro Hclose
  inext
  iexists LogAbs.empty
  iframe HL
  iintro HL
  imod Hclose
  imodintro
  iintro Htok
  wp_auto
  wp_bind (App (Val #(methods _ _ _)) _)
  iapply HList $$ Htok
  iapply ncfupd_of_fupd
  iapply fupd_mask_intro (by simp)
  iintro Hclose
  inext
  iexists none
  iframe HSS
  iintro HSS
  imod Hclose
  imodintro
  iintro %sl %ps Hsl %Hps Htok
  subst Hps
  ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
  wp_auto
  rw [decide_eq_false (by simp at Hsll; word)]
  wp_auto
  iapply HΦ
  iframe

end proof

end Perennial
