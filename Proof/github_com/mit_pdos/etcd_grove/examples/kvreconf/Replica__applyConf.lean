/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvreconf/Replica__applyConf.lean`. Lean-first
(no Rocq counterpart).

`AsV2` gives the change's `ConfChangeV2` (`ccToV2`: a `ConfChange`'s fresh one, a `ConfChangeV2`
itself); the configuration is read under the lock (the applier's half suffices); `validConf`
answers `ConfOk` at the applier's membership (`cfgAt_wf`: well formed, restorable). Rejected: the
store's decision is `skip` (`conf_reject`). Accepted: `node.ApplyConfChange` (`wp_conf_apply`), then
`r.cs` written under the lock with both halves; `EnterJoint` on the `ConfChangeV2` does not panic
(the transition is defined, `ccTransOk`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Replica__applyConf
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.validConf
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Stats__add
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChange__AsV2
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChangeV2__AsV2
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChangeV2__EnterJoint
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.ApplyConfLemmas
public import Proof.go_etcd_io.raft.v3.FrameH
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.PureLemmas

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

theorem enterJoint_some (cc : ConfChangeV2M) (h : enterJointOf cc.transition cc.changes.length ≠ none) :
    ∃ al j, enterJointOf cc.transition cc.changes.length = some (al, j) := by
  cases hx : enterJointOf cc.transition cc.changes.length with
  | none => exact absurd hx h
  | some p => exact ⟨p.1, p.2, rfl⟩

/-- `EnterJoint`'s answer on a defined transition. -/
theorem enterJoint_ret (cc : ConfChangeV2M) (al jt : Bool) (rv : val)
    (h : enterJointOf cc.transition cc.changes.length = some (al, jt)) :
    (match enterJointOf cc.transition cc.changes.length with
      | some (autoLeave, ok) => iprop(⌜rv = PairV #autoLeave #ok⌝)
      | none => iprop(⌜∃ p, rv = PanicV p⌝) : IProp GF) ⊢ ⌜rv = PairV #al #jt⌝ := by
  rw [h]

set_option hygiene false in
/-- `applyConf` after `AsV2` gave the `ConfChangeV2` `v2` (`Hv2`, at `dq2`). -/
local macro "applyconf_rest" oc:term : tactic => `(tactic| (
    try wp_auto
    wp_apply sync.Mutex.wp_Lock _ _ $$ [$(frameH `Hmu)] as ⟨Hlocked, HR⟩
    try wp_auto
    wp_apply sync.Mutex.wp_Unlock _ _ $$ [$(frameH `Hmu) $(frameH `Hlocked) $(frameH `HR)]
    try wp_auto
    ihave %Hwf := cfgAt_wf γr c m ap.length $$ [$(frameH `HcfgA)]
    obtain ⟨Hcsm, Hwf', Hres⟩ := Hwf
    wp_apply wp_validConf csp DFrac.discard c m v2 _ (ccToV2 $oc) Hcsm Hwf' Hres Htr
      $$ [$(frameH `HcsO) $(frameH `HvV)] as %b ⟨-, Hv2, %Hb⟩
    rw [confOk_toV2] at Hb
    cases b
    · -- rejected
      try wp_auto
      have Hno : ¬ ConfOk $oc m := fun h => absurd (Hb.2 h) (by decide)
      imod conf_reject γr vs n l e $oc c m ap.length ⊤ Hk Hd Hno (fun _ _ => CoPset.mem_full)
        $$ Hcl Hl HcfgA Hn with ⟨#Hcfg', Hn'⟩
      ihave #Hctr := isStats_field sts go!"ConfChangesRejected" (by decide) $$ Hstats
      wp_apply wp_add sts _ $$ [$(frameH `Hpkg) $(frameH `Hctr)]
      try wp_auto
      iapply HΦ
      iexists csp, m
      iframe Hn' Hlive
      unfold repOwn
      iexists mK, K, c
      iframe HmK HK HmA HA Hcs Hidx HcsO
      isplitr
      · iexact Hce
      isplitr
      · ipureintro; rw [List.length_append, List.length_singleton]; omega
      isplitr
      · ipureintro; rw [Hlh]; exact Hval
      isplitr
      · ipureintro; rw [Hlh]; exact HA
      iunfold cfgAt at Hcfg'
      icases Hcfg' with ⟨%Hcsm', #Hcfg'⟩
      isplitr
      · ipureintro; exact Hcsm'
      rw [List.length_append, List.length_singleton]
      iexact Hcfg'
    · -- accepted
      try wp_auto
      have Hok : ConfOk $oc m := Hb.1 rfl
      ihave #Hraft : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
      · iPkgInit
      wp_apply wp_conf_apply wp_ACC γr vs id n q l e $oc _ c m ap.length Hk Hd Hok
        $$ [$(frameH `Hraft) $(frameH `HisNode) $(frameH `Hcl) $(frameH `Hl) $(frameH `Hcc0) $(frameH `HcfgA) $(frameH `Hn) $(frameH `Hlive)] as %csp' ⟨%m', %c', #HcsO', #Hcfg', Hn', Hlive⟩
      try wp_auto
      wp_apply sync.Mutex.wp_Lock _ _ $$ [$(frameH `Hmu)] as ⟨Hlocked, HR⟩
      iNamed HR
      iunfold repShared at Hrep
      icases Hrep with ⟨%mA', %A0, %csp0, %c0, %idx', %ap', HmA', HA', Hcs', Hidx', #HcsO0, #Hap', %HA0⟩
      icombine Hcs Hcs' gives %Hcseq
      subst Hcseq
      ihave Hcsf := (typedPointsto_half_split _ csp (1 : Qp)).2 $$ [$(frameH `Hcs) $(frameH `Hcs')]
      try wp_auto
      icases (typedPointsto_half_split _ csp' (1 : Qp)).1 $$ Hcsf with ⟨Hcs, Hcs'⟩
      wp_apply sync.Mutex.wp_Unlock _ _ $$ [$(frameH `Hmu) $(frameH `Hlocked) HmA' HA' Hcs' Hidx'
          HmW HW Hwaiters Hns Hseq HmR HRd Hreads]
      · inext
        unfold lockInv repShared
        iexists ns, mW, W, mR, Rd
        iframe
        isplitl [HmA' HA' Hcs' Hidx']
        · iexists mA', A0, csp', c', idx', ap'
          iframe HmA' HA' Hcs' Hidx' HcsO' Hap'
          ipureintro; exact HA0
        · ipureintro; exact HRdom
      try wp_auto
      ihave #Hctr := isStats_field sts go!"ConfChangesApplied" (by decide) $$ Hstats
      wp_apply wp_add sts _ $$ [$(frameH `Hpkg) $(frameH `Hctr)]
      ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
      · iPkgInit
      obtain ⟨al, jt, Hej⟩ := enterJoint_some (ccToV2 $oc) Htr
      wp_apply wp_EnterJoint v2 _ (ccToV2 $oc) Htr $$ [$(frameH `Hpb) $(frameH `Hv2)] as %rv ⟨Hv2, Hrv⟩
      first
        | icases enterJoint_ret (ccToV2 $oc) al jt rv Hej $$ Hrv with %Hrv
        | icases Hrv with %Hrv
      subst Hrv
      try wp_auto
      ihave #Hctr2 := isStats_field sts go!"JointEntered" (by decide) $$ Hstats
      ihave Hfin : iprop(∃ (csp'' : Loc) (m'' : Membership),
          repOwn γr r (ap ++ [e]) idx csp'' m'' mA A ∗
          appNode γr n l (ap.length + 1) m'' ∗ nodeRunning n γr.cluster kvrRaftN q)
          $$ [HmK HK HmA HA Hcs Hidx Hn' Hlive]
      · iexists csp', m'
        iframe Hn' Hlive
        unfold repOwn
        iexists mK, K, c'
        iframe HmK HK HmA HA Hcs Hidx HcsO'
        isplitr
        · iexact Hce
        isplitr
        · ipureintro; rw [List.length_append, List.length_singleton]; omega
        isplitr
        · ipureintro; rw [Hlh]; exact Hval
        isplitr
        · ipureintro; rw [Hlh]; exact HA
        iunfold cfgAt at Hcfg'
        icases Hcfg' with ⟨%Hcsm', #Hcfg'⟩
        isplitr
        · ipureintro; exact Hcsm'
        rw [List.length_append, List.length_singleton]
        iexact Hcfg'
      try wp_auto
      try wp_if_destruct
      all_goals
        try wp_auto
        first
          | (iapply HΦ; iexact Hfin)
          | (wp_apply wp_add sts _ $$ [$(frameH `Hpkg) $(frameH `Hctr2)]
             try wp_auto
             iapply HΦ
             iexact Hfin)
  ))

theorem Replica.applyConf.wp_proof
    (wp_ACC : node.ApplyConfChange.spec (GF := GF) (hG := hG))
    (wp_validConf : validConf.spec (GF := GF) (hG := hG))
    (wp_add : Stats.add.spec (GF := GF) (hG := hG))
    (wp_ConfChange_AsV2 : raftpb.ConfChange.AsV2.spec (GF := GF) (hG := hG))
    (wp_ConfChangeV2_AsV2 : raftpb.ConfChangeV2.AsV2.spec (GF := GF) (hG := hG))
    (wp_EnterJoint : raftpb.ConfChangeV2.EnterJoint.spec (GF := GF) (hG := hG)) :
    Replica.applyConf.spec (GF := GF) (hG := hG) := by
  intro γr vs id r n st sts q ap idx csp m mA A l e ci o Hpre Hd Htr Hlen'
  wp_start as ⟨#Hrep, Hown, Hn, #Hcc, #Hl, Hlive⟩
  iunfold isReplica at Hrep
  iNamed Hrep
  iunfold repOwn at Hown
  iNamed Hown
  have Hk : l[ap.length]? = some e := by
    obtain ⟨t, rfl⟩ := Hpre
    rw [List.append_assoc, List.getElem?_append_right (Nat.le_refl _)]; simp
  ihave #Hce : isCommittedLogLb γr.cluster (ap ++ [e]) $$ []
  · iapply isCommittedLogLb_mono γr.cluster (ap ++ [e]) l Hpre $$ Hl
  ihave #HcfgA : cfgAt γr c m ap.length $$ []
  · unfold cfgAt; iframe Hcfg; ipureintro; exact Hcsm
  have Hcc' := ccDecode_isConfChange Hd
  -- a conf entry carries no client datum
  have Hlh : logHist (ap ++ [e]) = logHist ap := by
    rw [logHist_snoc]
    have : odOf e = none := by
      unfold odOf; rw [if_neg]; rintro ⟨h, _⟩
      rcases Hcc' with h' | h' <;> rw [h] at h' <;> word
    rw [this]; rfl
  ihave #Hraftpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  cases o with
  | v1 cm =>
    ihave #Hcc0 := Hcc
    ihave #Hcc1 : iprop(∃ p, ⌜ci = interface.mkOk (go.GoType.PointerType raftpb.ConfChange.ty) #p⌝ ∗
        ownConfChange p DFrac.discard cm) $$ []
    · simp only [ownConfChangeI]; iexact Hcc
    icases Hcc1 with ⟨%p, %Hcv, #Hp⟩
    subst Hcv
    try wp_auto
    wp_apply wp_ConfChange_AsV2 p DFrac.discard cm $$ [$Hraftpb $Hp] as %v2 ⟨-, Hv2⟩
    ihave HvV : iprop(ownConfChangeV2 v2 (DFrac.own 1) (ccToV2 (.v1 cm))) $$ [Hv2]
    · rw [show ccToV2 (ConfChangeIM.v1 cm) = cm.asV2 from rfl]; iexact Hv2
    applyconf_rest (ConfChangeIM.v1 cm)
  | v2 cc =>
    ihave #Hcc0 := Hcc
    ihave #Hcc1 : iprop(∃ p, ⌜ci = interface.mkOk (go.GoType.PointerType raftpb.ConfChangeV2.ty) #p⌝ ∗
        ownConfChangeV2 p DFrac.discard cc) $$ []
    · simp only [ownConfChangeI]; iexact Hcc
    icases Hcc1 with ⟨%v2, %Hcv, #Hv2⟩
    subst Hcv
    try wp_auto
    wp_apply wp_ConfChangeV2_AsV2 v2 $$ [$Hraftpb]
    ihave #HvV : iprop(ownConfChangeV2 v2 DFrac.discard (ccToV2 (.v2 cc))) $$ []
    · rw [show ccToV2 (ConfChangeIM.v2 cc) = cc from rfl]; iexact Hv2
    applyconf_rest (ConfChangeIM.v2 cc)

end proof

end kvreconf
end EtcdGrove
end Perennial
