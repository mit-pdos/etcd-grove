/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/overrideNotifyBool.lean (241f27e).
-/
/-
The proof of `raft.overrideNotifyBool`: with the buffered-1 channel owned exclusively, either the
send fits the (empty) buffer, or the receive takes the old value and the inner non-blocking send
then fits (its `default: panic` is unreachable).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.overrideNotifyBool

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

open github_com.hashicorp.raft

theorem github_com.hashicorp.raft.overrideNotifyBool.wp_proof :
    github_com.hashicorp.raft.overrideNotifyBool.spec (GF := GF) (hG := hG) :=
  fun γc ch bs v => by
  wp_start as ⟨#Hch, Hoc, %Hcap⟩
  wp_auto
  obtain ⟨hcap, hlen⟩ := Hcap
  rcases bs with _ | ⟨x, _ | ⟨y, rest⟩⟩
  rotate_left 2
  · simp at hlen
  · -- empty buffer: the send fires
    wp_apply_core chan.wp_select_blocking
    iapply BigAndL.bigAndL_cons.2
    isplit
    · dsimp only [chan.blockingClausePre]
      iexists Bool, inferInstance, inferInstance, inferInstance, inferInstance, ch, γc, v
      isplitr
      · ipureintro; exact ⟨rfl, rfl⟩
      iframe Hch
      unfold sendAu
      iapply ncfupd_of_fupd
      iapply fupd_mask_intro Std.LawfulSet.empty_subset
      iintro Hmask
      inext
      iexists _
      iframe Hoc
      dsimp only
      iintro Hoc
      imod Hmask with -
      imodintro
      wp_auto
      simp only [List.nil_append]
      iapply HΦ $$ Hoc
    iapply BigAndL.bigAndL_singleton.2
    dsimp only [chan.blockingClausePre]
    iexists Bool, inferInstance, inferInstance, inferInstance, inferInstance, ch, γc
    isplitr
    · ipureintro; rfl
    iframe Hch
    unfold recvAu
    iapply ncfupd_of_fupd
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    iexists _
    iframe Hoc
  · -- full buffer: the receive fires, then the inner send fits
    wp_apply_core chan.wp_select_blocking
    iapply BigAndL.bigAndL_cons.2
    isplit
    · dsimp only [chan.blockingClausePre]
      iexists Bool, inferInstance, inferInstance, inferInstance, inferInstance, ch, γc, v
      isplitr
      · ipureintro; exact ⟨rfl, rfl⟩
      iframe Hch
      unfold sendAu
      iapply ncfupd_of_fupd
      iapply fupd_mask_intro Std.LawfulSet.empty_subset
      iintro Hmask
      inext
      iexists _
      iframe Hoc
      dsimp only
      iintro Hoc
      rw [ownChan_unseal]; unfold ownChanDef
      icases Hoc with ⟨-, %Hv⟩
      simp [ChanCapValid] at Hv
      omega
    iapply BigAndL.bigAndL_singleton.2
    dsimp only [chan.blockingClausePre]
    iexists Bool, inferInstance, inferInstance, inferInstance, inferInstance, ch, γc
    isplitr
    · ipureintro; rfl
    iframe Hch
    unfold recvAu
    iapply ncfupd_of_fupd
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    iexists _
    iframe Hoc
    dsimp only
    iintro Hoc
    imod Hmask with -
    imodintro
    wp_auto
    wp_apply_core chan.wp_select_nonblocking_alt [iprop(False)] (ownChan γc Bool (.Buffered [])) $$ [HΦ] Hoc []
    · iapply BigSepL2.bigSepL2_singleton.2
      iintro Hoc
      simp only [chan.nonblockingAltClausePre]
      iexists Bool, inferInstance, inferInstance, inferInstance, inferInstance, ch, γc, v
      isplitr
      · ipureintro; exact ⟨rfl, rfl⟩
      iframe Hch
      unfold nonblockingSendAuAlt
      iapply ncfupd_of_fupd
      iapply fupd_mask_intro Std.LawfulSet.empty_subset
      iintro Hmask
      inext
      iexists _
      iframe Hoc
      dsimp only
      rw [ite_cond_eq_true _ _ (by simp; omega)]
      iintro Hoc
      imod Hmask with -
      imodintro
      wp_auto
      simp only [List.nil_append]
      iapply HΦ $$ Hoc
    · iintro - Hnr
      icases BigSepL.bigSepL_singleton.1 $$ Hnr with Hf
      iexfalso; iexact Hf

end proof

end Perennial
