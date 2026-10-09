/- Port of election_proof/proof_RawNode__Propose.v.

Lean notes: like its spec, the section fixes `hlc := HasLC.hasLC` and has `[AllG GF]`.
-/
module

public import Spec.go_etcd_io.raft.v3.RawNode__Propose
public import Spec.go_etcd_io.raft.v3.raft__Step
-- `Step.commit_mono`
public import Proof.go_etcd_io.raft.v3.Protocol.Facts

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
variable [AllG GF]

/-- A premise of `Step` about another message type: `MsgProp` (`W32 2`) is not it. -/
local macro "msg_ne" : tactic => `(tactic| (intro Hc; simp [MsgHup, MsgVote, MsgVoteResp,
  MsgPreVote, MsgPreVoteResp, MsgApp, MsgHeartbeat, MsgAppResp, MsgHeartbeatResp, MsgSnap,
  MsgBeat, MsgStorageAppendResp, MsgStorageApplyResp] at Hc))

/-- `Step` on the literal message: `Type: MsgProp`, `From: r.id`, the one-entry batch;
every other field zero. Its `MsgProp` arm, at the singleton batch, is the
postcondition; `LocalStepOk` and `Step.commit_mono` keep `ownRawNode` at `rs`. -/
theorem RawNode.Propose.wp_proof
    (wp_raft_Step : raft.Step.spec (GF := GF) (hG := hG)) :
    RawNode.Propose.spec (GF := GF) (hG := hG) := by
  intro γ rn id rs data_sl data Q
  wp_start as H
  iNamed H
  iNamed Hrn
  wp_auto
  wp_apply raft.wp_load_id $$ Hphys as Hphys
  wp_apply wp_slice_literal (l := [propEntry data_sl])
  isplitr
  · ipureintro; rfl
  iintro %sl_ptr ⟨Hes, Hcap⟩
  wp_auto
  wp_apply wp_raft_Step γ.reCfg γ _ id s ps _ [propEntry data_sl] [Q] rfl
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
  iintro %err %s' %ps' ⟨Hphys, Hghost, %Hrel', %Href, %Hloc, %_, %_, Herr, Hprops⟩
  wp_auto
  -- what the `RawNode` tracks is kept: `LocalStepOk`, and the commit index does not move
  -- back (`Step.commit_mono`)
  obtain ⟨Hfr, Hap⟩ := Hloc (.inl rfl)
  have Hap' := Hap (fun Hc => absurd Hc (by msg_ne))
  have Hc : uint.Z s.logst.committed ≤ uint.Z s'.logst.committed := by
    obtain ⟨recv, Hst⟩ := Href
    have H := Step.commit_mono Hst
    rw [← Hrel.1, ← Hrel'.1] at H
    exact H
  iapply HΦ
  simp only [named]
  isplitl [Hrn Hphys Hghost Hsteps Hsteps_cap Hpown]
  · iapply ownRawNode_intro γ rn id rs s' ps' rnv sv steps Hrel' Hin Hasync
      (by rw [Hap']; exact Hdlen) (by rw [Hfr.2.2.1]; exact Hunp) (by rw [Hfr.2.2.2]; exact Hsnap)
      (fun h => stepsOk_mono s s' _ Hfr.1 Hfr.2.1 Hc Hap' (Hadv h)) (by rw [Hfr.1]; exact Htrm)
      $$ Hrn Hphys Hghost Hsoft Hsteps Hsteps_cap Hpend Hpown Hdeliv
  icases Hprops with (⟨%Hok, Hout⟩ | Hau)
  · ileft
    isplitr
    · ipureintro; exact Hok.1
    icases (BigSepL.bigSepL_singleton (Φ := fun k Q' => iprop(∃ γp,
        isProp γ ps.term (plastIndex ps + W64 1 + W64 (k : Int)) γp Q' ∗ propTok γp))).1 $$ Hout
      with ⟨%γp, Hp, Ht⟩
    iexists ps.term, plastIndex ps + W64 1 + W64 ((0 : Nat) : Int), γp
    iframe Hp Ht
  · iright
    icases (BigSepL2.bigSepL2_singleton (Φ := fun _ e Q' => propAu γ e Q')).1 $$ Hau with Hau
    iframe Hau
    icases Herr with (%Herr | ⟨-, #Hd⟩)
    · ileft; ipureintro; exact Herr
    · iright; iexact Hd

end proof

end EtcdGrove
end Perennial
