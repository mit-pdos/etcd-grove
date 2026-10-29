/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvreconf/validConf.lean`. Lean-first (no Rocq
counterpart).

A `nil` configuration becomes a fresh empty `ConfState` (`csPts_of_struct`); `Restore` of it on a
fresh tracker gives the configuration pair at `m` (`confchange.Restore.apiSpec`), assembled into a
tracker at `m` (`ownTrackerM_assemble`); the change is `LeaveJoint`, `EnterJoint` or `Simple` as
`cc` says (its getters), each answering Go's `applyGo` (the `Changer` apiSpecs); the result's size
(`ownCfgPairM_size`) below `2^62` is `applyChange`'s cut (`applyChange_eq_applyGo`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.validConf
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChangeV2__LeaveJoint
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChangeV2__EnterJoint
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChangeV2__GetChanges
public import Proof.go_etcd_io.raft.v3.FrameH

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [StorageModel GF] [AllG GF]

set_option hygiene false in
/-- `validConf`'s end, from the changer's answer `Hr` (at `cfg'`, `prs'`, `err'`), with `Hback`
giving back the configuration. -/
local macro "vc_finish" : tactic => `(tactic| (
    icases Hr with (⟨%m', %Hgo, Hp⟩ | %Hgo)
    · obtain ⟨rfl, Hgo⟩ := Hgo
      icases ownCfgPairM_size _ _ _ $$ [$(frameH `Hp)] with ⟨%M, %dqm, HM, %HMs, -⟩
      try wp_auto
      wp_apply wp_map_len_lt (t := tracker.ProgressMap.ty) prs' M dqm $$ [$(frameH `HM)] as ⟨HM, %HMlt⟩
      try wp_auto
      iapply HΦ
      iframe Hback Hcc
      ipureintro
      unfold ConfOk
      rw [Membership.applyChange_of_applyGo Hgo, ← HMs]
      constructor
      · intro h
        have h' : uint.Z (W64 (GMap.size M)) < uint.Z (W64 4611686018427387904) := by
          simpa using h
        refine ⟨m', ?_⟩
        rw [if_pos (by word)]
      · rintro ⟨m'', h⟩
        have hs : GMap.size M < 2 ^ 62 :=
          Classical.byContradiction fun hc => by rw [if_neg hc] at h; cases h
        simp only [decide_eq_true_eq]
        word
    · obtain ⟨Hne, Hgo⟩ := Hgo
      cases err' with
      | nil => exact absurd rfl Hne
      | ok i =>
        try wp_auto
        iapply HΦ
        iframe Hback Hcc
        ipureintro
        unfold ConfOk
        rw [Membership.applyChange_of_applyGo_none Hgo]
        simp
  ))

set_option hygiene false in
/-- `validConf` from the first `MakeProgressTracker` on, with the configuration owned at a pointer
(`Hown`) and `HbackW` turning it back into the caller's `csOpt`. -/
local macro "vc_rest" : tactic => `(tactic| (
    wp_apply wp_MPT (W64 1) (W64 0) ⟨by decide, by decide⟩ as %tv Htv
    try wp_auto
    wp_apply wp_Restore (confchange.Changer.mk tv (W64 1)) _ _ _ m Hcs Hwf Hres $$ [$(frameH `Hown) $(frameH `Htv)] as %cfg %prs ⟨Hown, Hpair⟩
    ihave Hback := HbackW $$ Hown
    try wp_auto
    wp_apply wp_MPT (W64 1) (W64 0) ⟨by decide, by decide⟩ as %tv2 Htv2
    try wp_auto
    ihave Htrk := ownTrackerM_assemble tv2 cfg prs m $$ [$(frameH `Htv2) $(frameH `Hpair)]
    wp_apply wp_ccLJ ccp dq' cc $$ [$(frameH `HpbI) $(frameH `Hcc)] as Hcc
    wp_if_destruct
    · wp_apply wp_LeaveJoint chg_ptr _ m (.v2 cc) (DFrac.own 1)
        (by simp only [ccV2Of]; rw [Hif.1, Hif.2]) $$ [$(frameH `HccI) $(frameH `chg) $(frameH `Htrk)] as %cfg' %prs' %err' ⟨chg, Htrk, Hr⟩
      try wp_auto
      vc_finish
    · cases Hej' : enterJointOf cc.transition cc.changes.length with
      | none => exact absurd Hej' Hej
      | some p =>
        obtain ⟨al, ok⟩ := p
        wp_apply wp_ccEJ ccp dq' cc Hej $$ [$(frameH `HpbI) $(frameH `Hcc)] as %rv ⟨Hcc, Hrv⟩
        rw [Hej']
        icases Hrv with %Hrv
        subst Hrv
        try wp_auto
        wp_if_destruct
        · try wp_auto
          wp_apply wp_ccGC.1 ccp dq' cc $$ [$(frameH `HpbI) $(frameH `Hcc)] as %chs %ls ⟨Hchs, #Hccs, Hccb⟩
          wp_apply wp_Simple chg_ptr _ m (.v2 cc) cc.transition cc.changes al chs ls
            (DFrac.own 1) dq' rfl Hif Hej' $$ [$(frameH `HccI) $(frameH `chg) $(frameH `Hchs) $(frameH `Hccs) $(frameH `Htrk)]
            as %cfg' %prs' %err' ⟨chg, Hchs, Htrk, Hr⟩
          ihave Hcc := Hccb $$ Hchs
          try wp_auto
          vc_finish
        · try wp_auto
          wp_apply wp_ccGC.1 ccp dq' cc $$ [$(frameH `HpbI) $(frameH `Hcc)] as %chs %ls ⟨Hchs, #Hccs, Hccb⟩
          wp_apply wp_EnterJoint chg_ptr _ m (.v2 cc) cc.transition cc.changes al chs ls
            (DFrac.own 1) dq' rfl Hej' $$ [$(frameH `HccI) $(frameH `chg) $(frameH `Hchs) $(frameH `Hccs) $(frameH `Htrk)]
            as %cfg' %prs' %err' ⟨chg, Hchs, Htrk, Hr⟩
          ihave Hcc := Hccb $$ Hchs
          try wp_auto
          vc_finish
  ))

theorem validConf.wp_proof
    (wp_MPT : tracker.MakeProgressTracker.apiSpec (GF := GF) (hG := hG))
    (wp_Restore : confchange.Restore.apiSpec (GF := GF) (hG := hG))
    (wp_Simple : confchange.Changer.Simple.apiSpec (GF := GF) (hG := hG))
    (wp_EnterJoint : confchange.Changer.EnterJoint.apiSpec (GF := GF) (hG := hG))
    (wp_LeaveJoint : confchange.Changer.LeaveJoint.apiSpec (GF := GF) (hG := hG))
    (wp_ccLJ : raftpb.ConfChangeV2.LeaveJoint.spec (GF := GF) (hG := hG))
    (wp_ccEJ : raftpb.ConfChangeV2.EnterJoint.spec (GF := GF) (hG := hG))
    (wp_ccGC : raftpb.ConfChangeV2.GetChanges.spec (GF := GF) (hG := hG)) :
    validConf.spec (GF := GF) (hG := hG) := by
  intro csp dq c m ccp dq' cc Hcs Hwf Hres Hej
  wp_start as ⟨HcsO, Hcc⟩
  ihave #HpbI : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  ihave #HccI : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange $$ []
  · iPkgInit
  ihave #HtrI : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker $$ []
  · iPkgInit
  iunfold csOpt at HcsO
  icases HcsO with (%Hnil | Hown)
  · obtain ⟨rfl, rfl⟩ := Hnil
    try wp_auto
    ihave Hn1 : (slice.nil ↦* ([] : List w64) : IProp GF) $$ []
    · iapply ownSlice_nil
    ihave Hn2 : (slice.nil ↦* ([] : List w64) : IProp GF) $$ []
    · iapply ownSlice_nil
    ihave Hn3 : (slice.nil ↦* ([] : List w64) : IProp GF) $$ []
    · iapply ownSlice_nil
    ihave Hn4 : (slice.nil ↦* ([] : List w64) : IProp GF) $$ []
    · iapply ownSlice_nil
    ihave #cq : cellRO (null : Loc) (zero_val Bool) $$ []
    · iapply cellRO_null
    imod csPts_of_struct «$r0_ptr» (zero_val raftpb.ConfState)
      (ConfStateM.mk [] [] [] [] false) ⊤ (by rfl) $$ [«$r0» Hn1 Hn2 Hn3 Hn4 cq] with Hown
    · iframe
      iframe cq
    rw [show decide ((zero_val raftpb.ConfState).AutoLeave' ≠ null) = false from
      decide_eq_false (by simp; rfl)]
    ihave HbackW : ownCSM «$r0_ptr» (DFrac.own 1)
        (ConfStateM.mk [] [] [] [] false) -∗
        csOpt null dq (ConfStateM.mk [] [] [] [] false) $$ []
    · iintro -; unfold csOpt; ileft; ipureintro; exact ⟨rfl, rfl⟩
    ihave Hown : ownCSM «$r0_ptr» (DFrac.own 1)
        (ConfStateM.mk [] [] [] [] false) $$ [Hown]
    · iexact Hown
    vc_rest
  · iunfold ownCSM at Hown
    icases csPts_nn _ _ _ _ $$ Hown with ⟨Hown, %Hnn⟩
    try wp_auto
    wp_if_destruct
    · exact absurd rfl Hnn
    ihave HbackW : ownCSM csp dq c -∗ csOpt csp dq c $$ []
    · iintro H; unfold csOpt; iright; iexact H
    vc_rest

end proof

end kvreconf
end EtcdGrove
end Perennial
