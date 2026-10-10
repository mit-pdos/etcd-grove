/- Port of election_proof/proof_RawNode__HasReady.v (857d09190).

Since 2026-10-09 the spec pins nothing about the answer, so every path returns the same
way: close the raft struct's view unchanged (`close_view`) and refold `ownRawNode`
(`finish`).

Lean notes: Rocq's `nstate_set_same` is not needed (the record update closing the view
is definitionally `s`). Rocq's `close_view`/`finish_true` are the local macros
`close_view`/`finish`; the tail after the hard-state test, which falls through in two
ways, is the local macro `rest`. -/
module

public import Spec.go_etcd_io.raft.v3.RawNode__HasReady
public import Spec.go_etcd_io.raft.v3.SoftState__equal
public import Spec.go_etcd_io.raft.v3.IsEmptyHardState
public import Spec.go_etcd_io.raft.v3.isHardStateEqual
public import Spec.go_etcd_io.raft.v3.raftLog__hasNextUnstableSnapshot
public import Spec.go_etcd_io.raft.v3.raftLog__hasNextUnstableEnts
public import Spec.go_etcd_io.raft.v3.raftLog__hasNextCommittedEnts

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3
open RawNodeOwnAccess

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
variable [AllG GF]

set_option hygiene false in
/-- Rocq's local `close_view`: close the raft struct unchanged (`Hphys`). -/
local macro "close_view" : tactic => `(tactic| (
  ihave Hphys := Hclose $$ %sl1 %sl2 %ms1 %ms2 %s.outbox %s.logst %s.gh Hf_Term Hf_Vote
    Hf_readStates Hf_raftLog Hf_state Hf_lead Hf_msgs Hmsgs Hmsgs_cap Hf_msgsAA HmsgsAA
    HmsgsAA_cap Houtbox %HmsgsAA_ok %Hout_term %Hgh_out %Hgh_unst Hlog))

set_option hygiene false in
/-- Close the view, refold `ownRawNode` unchanged, return. -/
local macro "finish" : tactic => `(tactic| (
  close_view
  iapply HΦ
  ileft
  isplitr
  · ipureintro; rfl
  iapply ownRawNode_intro γ rn id rs s ps rnv sv steps Hrel Hin Hasync Hdlen Hunp Hsnap Hstok Htrm Hstor
    Hpvoff Hrs_out Hrs_unst Hrs_clb
    $$ Hrn Hphys Hghost Hsoft Hsteps Hsteps_cap Hpend Hpown Hdeliv Hstrecs))

set_option hygiene false in
/-- The one path that returns `false`: no queue is non-empty and no unstable entry is
still to be handed out, so the node is idle. -/
local macro "finish_false" : tactic => `(tactic| (
  ihave %Hl1 := ownSlice_len _ _ _ $$ Hmsgs
  ihave %Hl2 := ownSlice_len _ _ _ $$ HmsgsAA
  have Hnu : nextUnstable s.logst = [] := by
    by_cases h : nextUnstable s.logst = []
    · exact h
    · exact absurd (Hue.trans (decide_eq_true h)) (by decide)
  have Hout0 : s.gh.outlb = 0 := by word
  close_view
  iapply HΦ
  iright
  isplitr
  · ipureintro; rfl
  iapply ownRawNodeIdle_intro γ rn id rs s ps rnv sv steps Hrel Hin Hasync Hdlen Hunp Hsnap
    Hstok Htrm Hstor Hpvoff Hrs_out Hrs_unst Hrs_clb ⟨Hout0, Hnu⟩
    $$ Hrn Hphys Hghost Hsoft Hsteps Hsteps_cap Hpend Hpown Hdeliv Hstrecs))

set_option hygiene false in
/-- The rest of `HasReady` once the hard-state test fell through: Rocq's `all:` tail,
shared by the two ways of falling through. -/
local macro "rest" : tactic => `(tactic| (
  wp_apply wp_raftLog_hasNextUnstableSnapshot $$ [Hlog] as %bsn ⟨Hlog, %Hsn⟩
  · iframe Hlog
  cases bsn
  · wp_auto
    wp_if_destruct
    · finish
    wp_if_destruct
    · finish
    wp_apply wp_raftLog_hasNextUnstableEnts $$ [Hlog] as %bue ⟨Hlog, %Hue⟩
    · iframe Hlog
    cases bue
    · wp_auto
      wp_method_call
      wp_call
      wp_auto
      rw [Hasync]
      wp_apply wp_raftLog_hasNextCommittedEnts $$ [Hlog] as %bce ⟨Hlog, _⟩
      · iframe Hlog
      cases bce
      · wp_auto
        rw [Hrs]
        wp_auto
        finish_false
      · wp_auto
        finish
    · wp_auto
      finish
  · wp_auto
    finish))

theorem RawNode.HasReady.wp_proof
    (wp_SoftState_equal : SoftState.equal.spec (GF := GF) (hG := hG))
    (wp_IsEmptyHardState : IsEmptyHardState.spec (GF := GF) (hG := hG))
    (wp_isHardStateEqual : isHardStateEqual.spec (GF := GF) (hG := hG))
    (wp_raftLog_hasNextUnstableSnapshot :
      raftLog.hasNextUnstableSnapshot.spec (GF := GF) (hG := hG))
    (wp_raftLog_hasNextUnstableEnts : raftLog.hasNextUnstableEnts.spec (GF := GF) (hG := hG))
    (wp_raftLog_hasNextCommittedEnts :
      raftLog.hasNextCommittedEnts.spec (GF := GF) (hG := hG)) :
    RawNode.HasReady.spec (GF := GF) (hG := hG) := by
  intro γ rn id rs
  wp_start as H
  iNamed H
  iNamed Hrn
  icases ownRaftPhys_view γ.reCfg rnv.raft' id s $$ Hphys with
    ⟨%rss, %sl1, %sl2, %ms1, %ms2, Hv⟩
  iNamed Hv
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  wp_apply wp_SoftState_equal $$ [$softSt $Hsoft] as ⟨softSt, _⟩
  wp_if_destruct
  rotate_left
  · finish
  -- `r.hardState()`
  icases ownRaftLog_struct _ _ $$ Hlog with ⟨%lv, Hl, %Hlv, Hlb⟩
  wp_method_call
  wp_call
  wp_auto
  ihave Hlog := Hlb $$ Hl
  wp_apply wp_IsEmptyHardState
  wp_if_destruct
  · rest
  · wp_apply wp_isHardStateEqual
    wp_if_destruct
    · rest
    · finish

end proof

end EtcdGrove
end Perennial
