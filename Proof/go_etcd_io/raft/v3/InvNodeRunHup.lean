/- Lean-first (no Rocq counterpart).

# `run`'s step of `Campaign`'s `MsgHup` (2026-10-29, stage U7)

`node.Campaign` puts `pb.Message{Type: MsgHup}` on `recvc` (`netP`'s second disjunct, `hupP`),
and `run` steps it with `r.Step(m)`, as `RawNode.Campaign` does: `wp_rn_raft_Step_hup` is
`RawNode.Campaign`'s proof with the message given (read-only, `hupSt`) instead of built. The term
ceiling must cover the campaign's term (`run` raises it with the message's tick credit,
`budget_spend`).
-/
module

public import Spec.go_etcd_io.raft.v3.raft__Step
public import Proof.go_etcd_io.raft.v3.InvRawnode
public import Proof.go_etcd_io.raft.v3.LemmasRawnodeR
public import Proof.go_etcd_io.raft.v3.InvNodeChan
-- `Step.commit_mono`
public import Proof.go_etcd_io.raft.v3.Protocol.Facts

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3
open RawNodeOwnAccess

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- A premise of `Step` about another message type: `MsgHup` (`W32 0`) is not it. -/
local macro "msg_ne" : tactic => `(tactic| (intro Hc; simp [MsgHup, MsgVote, MsgVoteResp,
  MsgPreVote, MsgPreVoteResp, MsgApp, MsgHeartbeat, MsgAppResp, MsgHeartbeatResp,MsgCheckQuorum, MsgSnap,
  MsgBeat, MsgProp, MsgStorageAppendResp, MsgStorageApplyResp, MsgReadIndex,
  MsgReadIndexResp, MsgForgetLeader, MsgUnreachable, MsgSnapStatus, MsgTimeoutNow, MsgTransferLeader] at Hc))

/-- `r.Step(m)` on `Campaign`'s `MsgHup` (`hupSt`), `r` the node's raft struct: as
`RawNode.Campaign`, the term moves up by at most one, within the ceiling. -/
theorem wp_rn_raft_Step_hup (wp_raft_Step : raft.Step.spec (GF := GF) (hG := hG))
    (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (r : Loc) (ml : Loc) (st : MsgSt)
    (Hst : st = hupSt) (Hterm : uint.Z rs.term + 1 ≤ uint.Z rs.tc) (Hflw : rs.flw = false) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        ownRawNode γ rn id rs ∗ rn.[RawNode, go!"raft"] ↦□ r ∗
        msgIn ml DFrac.discard st ∗ £ 1 }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #ml))
    {{ (err : GoInterface) (t : w64), RET #err;
        ownRawNode γ rn id { rs with term := t } ∗
        ⌜uint.Z rs.term ≤ uint.Z t ∧ uint.Z t ≤ uint.Z rs.term + 1⌝ }} := by
  sorry -- PHASE1
  /- PHASE1-OLD
 by
  subst Hst
  iintro %Φ ⟨#Hpkg, Hrn, #Hr, Hm, Hlc1⟩ HΦ
  unfold hupSt
  iNamed Hrn
  ihave #Hr' := rawNodeOwn_raft rn rnv $$ Hrn
  icombine Hr Hr' gives %Heq
  subst Heq
  have Htc1 : uint.Z s.term + 1 ≤ uint.Z s.gh.tc := by rw [← Htrm, ← Hpvoff.2.1]; exact Hterm
  have Hnw : uint.Z s.term + 1 < 2 ^ 64 := by have : uint.Z s.gh.tc < 2 ^ 64 := by word
                                              omega
  imod rdCred_zero_upd (GF := GF) γ with Hcr
  icases ownRaftPhysC_preFacts cf rnv.raft' id s (Hpvoff.guard rs.capplied rs.cfg (ds := ds)) $$ Hphys with ⟨%Hpf, Hphys⟩
  have hP : (W32 0 : w32) ≠ MsgProp := by simp [MsgProp]
  wp_apply wp_raft_Step cf _ γ _ id s ml ({ (zero_val MessageM) with Type' := W32 0 } : MessageM)
    [] [] none []
    (by simp [StepMsg, stepMsgTypes, MsgHup])
    (fun _ => ⟨rfl, Hnw, fun _ => Htc1, Hrnfl.1 Hflw⟩)
    (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
    (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
    (by msg_ne) (by msg_ne) (by msg_ne)
    (RestMsgOk.of_ne ⟨by msg_ne, by msg_ne, by msg_ne, by msg_ne, by msg_ne⟩) Hwf
    (GMode.Pre.of_facts Hpf (by msg_ne) (by msg_ne)) (fun h => absurd h (by msg_ne))
    $$ [$Hphys $Hghost $Hlc1 Hcr Hm]
  · -- the message: no entries, no `Context`, no snapshot
    simp only [hP, ↓reduceIte, named]
    isplitl [Hm]
    · iframe Hm
      repeat (isplitr; · first | iempintro | (ipureintro; simp) | (ipureintro; msg_ne))
      imodintro
      iintro %ty %Hty
      rw [show mtypeOf (W32 0) = none from rfl] at Hty
      cases Hty
    isplitl [Hcr]
    · rw [ite_eq_right (by msg_ne)]; iexact Hcr
    imodintro
    iintro %Hc
    simp [MsgSnap] at Hc
  simp only [hP]
  iintro %err %s' %c' %md' ⟨Hphys, Hghost, %Hwf', %Href, %Hcc, -, %Hfr, %Htm, -, -, -, -⟩
  have Hc := Href.commit_mono
  have e1 := Href.keep (by msg_ne) (by msg_ne) (fun h => absurd h (by msg_ne)); subst e1
  have e2 := Hcc (by msg_ne); subst c'
  obtain ⟨Ha, Hsn, Hu, Hpv, Hsd, Hsg, Hpre, Hgh, Hfl', Hap'⟩ := Hfr (by msg_ne) (by msg_ne) (fun h => absurd h (by msg_ne))
  obtain ⟨Ht1, Ht2, -, Hip4, -, Hpcs⟩ := Htm (by msg_ne)
  have Ht2' := Ht2 rfl
  ihave #Hstr' := ackInv_keep (rs' := rs) γ rfl Hstok Ht1 Hpv Hsn (logStoreRec_stored Hsd) (Hip4 (by msg_ne)) $$ Hstrecs
  iapply HΦ $$ %err %s'.term
  isplitl [Hrn Hphys Hghost Hsteps Hsteps_cap Hpend]
  ihave #Hsloc' := snapLocOk_keep γ id (.inl Hsn) $$ Hsloc
  · iapply ownRawNode_intro γ rn id { rs with term := s'.term } s' cf fp rnv sv hprev steps Hwf' Hin
      Hasync (by rw [Ha]; exact Hdlen) (by rw [Hu]; exact Hunp) (by rw [Hsn]; exact Hsnap)
      (stepsOk_mono_le s s' _ Ht1 ⟨Hpv, (logStoreRec_stored Hsd)⟩ Hc Ha (tc_le_of_gh Hgh) Hstok) rfl (by rw [Hsg]; exact Hstor)
      (Hpvoff.step rfl rfl Hpre Hgh (by have := Ht2 rfl; omega) Hpcs (fun _ => Htc1))
      (by rw [Hgh]; exact Hrs_out) (by rw [Hgh]; exact Hrs_unst) (Int.le_trans Hrs_clb Hc)
      (RNFl.keep Hrnfl Hfl' Hap' Ha) (Hloan.keep Hgh Hsn Hfl' (logStoreRec_stored Hsd) Hu Ha Hc)
      (Hsdt.ofRec Hsn Hsd) $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstr' Hloanc Hsloc'
  ipureintro
  rw [Htrm]
  exact ⟨Ht1, Ht2'⟩
  -/

end proof

end EtcdGrove
end Perennial
