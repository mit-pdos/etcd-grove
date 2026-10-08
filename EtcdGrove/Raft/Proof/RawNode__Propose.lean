/- Port of election_proof/proof_RawNode__Propose.v.

Lean notes: like its spec, the section fixes `hlc := HasLC.hasLC` and has `[AllG GF]`.
-/
import EtcdGrove.Raft.Spec.RawNode__Propose
import EtcdGrove.Raft.Spec.raft__Step

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
variable [AllG GF]

/-- A premise of `Step` about another message type: `MsgProp` (`W32 2`) is not it. -/
local macro "msg_ne" : tactic => `(tactic| (intro Hc; simp [MsgHup, MsgVote, MsgVoteResp,
  MsgPreVote, MsgPreVoteResp, MsgApp, MsgHeartbeat, MsgAppResp, MsgHeartbeatResp, MsgSnap,
  MsgBeat, MsgStorageAppendResp, MsgStorageApplyResp] at Hc))

/-- `Step` on the literal message: `Type: MsgProp`, `From: r.id`, the one-entry batch;
every other field zero. Its `MsgProp` arm, at the singleton batch, is the
postcondition. -/
theorem RawNode.Propose.wp_proof
    (wp_raft_Step : raft.Step.spec (GF := GF) (hG := hG)) :
    RawNode.Propose.spec (GF := GF) (hG := hG) := by
  intro cfg γ rn id ps ⟨s, rsoft, rhard, rsteps⟩ data_sl data Q Hcfg Hin Hrel
  dsimp only at Hrel ⊢
  wp_start as H
  iNamed H
  unfold ownRawNode
  icases Hrn with ⟨%rnv, %sv, %steps, Hrn⟩
  iNamed Hrn
  wp_auto
  wp_apply raft.wp_load_id $$ Hphys as Hphys
  wp_apply wp_slice_literal (l := [propEntry data_sl])
  isplitr
  · ipureintro; rfl
  iintro %sl_ptr ⟨Hes, Hcap⟩
  wp_auto
  wp_apply wp_raft_Step cfg γ _ id s ps _ [propEntry data_sl] [Q] Hcfg
    (by simp [StepMsg, stepMsgTypes, MsgProp]) Hin
    (by msg_ne) (by msg_ne)
    (by msg_ne) (by msg_ne)
    (by msg_ne) (by msg_ne)
    (by msg_ne) (by msg_ne)
    (by msg_ne) (by msg_ne)
    (by msg_ne)
    (fun _ => ⟨rfl, .inr rfl⟩) (by msg_ne) (by msg_ne) Hrel
    $$ [$Hphys $Hghost Hes Hcap Hau]
  · -- the message: its one-entry batch, owned; `Context` nil
    simp only [MsgProp, ite_true]
    isplitl [Hes Hcap]
    · simp only [named]
      isplitl [Hes]
      · iexact Hes
      isplitl [Hcap]
      · iexact Hcap
      isplitr
      · ipureintro
        intro _
        refine ⟨List.cons_ne_nil _ _, ?_, by simp⟩
        intro e He
        simp only [List.mem_singleton] at He
        subst He
        rfl
      isplitr
      · ipureintro
        intro Hc
        simp [MsgStorageApplyResp] at Hc
      · imodintro
        iintro %ty %Hty _
        rw [show mtypeOf (W32 2) = some .propose from rfl] at Hty
        cases Hty
        unfold isMessage absMsg absMsgFrom
        itrivial
    isplitl [Hau]
    · simp only [named]
      iapply (BigSepL2.bigSepL2_singleton (Φ := fun _ e Q' => propAu γ e Q')).2
      iexact Hau
    isplitr
    · iexists []
      isplitr
      · iapply ownSlice_nil
      · ipureintro
        refine ⟨?_, fun Hc => ?_⟩
        · intro Hc; unfold campaignTransfer at Hc; simp at Hc
        · simp [MsgHeartbeatResp] at Hc
    · imodintro
      iintro %Hc
      simp [MsgSnap] at Hc
  simp only [MsgProp, ite_true]
  iintro %err %s' %ps' ⟨Hphys, Hghost, %Hrel', %Href, Herr, Hprops⟩
  wp_auto
  iapply HΦ
  simp only [named]
  iframe Hghost
  isplitl [Hrn Hphys Hsteps Hsteps_cap Hpown]
  · iexists rnv, sv, steps
    iframe Hrn Hphys Hsoft Hsteps Hsteps_cap Hpend Hpown
    ipureintro
    exact ⟨Hasync, Hsoftv, Hhard⟩
  isplitr
  · ipureintro; exact Hrel'
  isplitr
  · ipureintro; exact Href
  icases Hprops with (⟨%Hok, Hout⟩ | Hau)
  · ileft
    isplitr
    · ipureintro; exact Hok
    icases (BigSepL.bigSepL_singleton (Φ := fun k Q' => iprop(∃ γp,
        isProp γ ps.term (plastIndex ps + W64 1 + W64 (k : Int)) γp Q' ∗ propTok γp))).1 $$ Hout
      with ⟨%γp, Hp, Ht⟩
    iexists γp
    iframe Ht
    -- the index `last + 1 + 0`
    rw [show plastIndex ps + W64 1 + W64 ((0 : Nat) : Int) = plastIndex ps + W64 1 by word] at *
    iexact Hp
  · iright
    icases (BigSepL2.bigSepL2_singleton (Φ := fun _ e Q' => propAu γ e Q')).1 $$ Hau with Hau
    iframe Hau
    icases Herr with (%Herr | ⟨-, #Hd⟩)
    · ileft; ipureintro; exact Herr
    · iright; iexact Hd

end proof

end EtcdGrove
end Perennial
