/-
The importable `confchange`/`tracker` specs (`ConfchangeApi.lean`) from the internal ones
(2026-10-29, stage U11): each `*.apiSpec_of` takes the function's internal spec
(`Spec/go_etcd_io/raft/v3/{tracker,confchange}/`) as a hypothesis; `Linked.lean` instantiates
them with `Link.lean`'s results.
-/
module

public import Proof.go_etcd_io.raft.v3.ConfchangeApi
public import Spec.go_etcd_io.raft.v3.tracker.MakeProgressTracker
public import Spec.go_etcd_io.raft.v3.confchange.Restore
public import Spec.go_etcd_io.raft.v3.confchange.Changer__Simple
public import Spec.go_etcd_io.raft.v3.confchange.Changer__EnterJoint
public import Spec.go_etcd_io.raft.v3.confchange.Changer__LeaveJoint
import all Proof.go_etcd_io.raft.v3.ConfchangeApi
import Proof.go_etcd_io.raft.v3.ConfchangeApiImpl
import all Proof.go_etcd_io.raft.v3.InvNode

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section derive
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem tracker.MakeProgressTracker.apiSpec_of
    (H : tracker.MakeProgressTracker.spec (GF := GF) (hG := hG)) :
    tracker.MakeProgressTracker.apiSpec (GF := GF) (hG := hG) := by
  intro mi mb Hmi
  iintro %Φ #Hpkg HΦ
  iapply H mi mb $$ [$Hpkg]
  inext
  iintro %tv %v0 ⟨%Ht, Hv0, -, Hprs⟩
  obtain ⟨Hmi', -, Harr, Hl, Hln, Hal⟩ := Ht
  iapply HΦ
  unfold ownTrackerM
  isplitr
  · ipureintro; rw [Hmi']; exact Hmi
  iexists v0
  iframe Hv0 Hprs
  ipureintro; exact ⟨Harr, Hl, Hln, Hal⟩

theorem confchange.Restore.apiSpec_of (H : confchange.Restore.spec (GF := GF) (hG := hG)) :
    confchange.Restore.apiSpec (GF := GF) (hG := hG) := by
  intro chg cs c dq m Hc Hwf Hr
  iintro %Φ ⟨#Hpkg, Hcs, Ht⟩ HΦ
  unfold ownTrackerM
  icases Ht with ⟨%Hmi, %v0, %Hf, Hv0, Hprs⟩
  obtain ⟨Harr, Hl, Hln, Hal⟩ := Hf
  ipersist Hprs
  rcases Hwf with rfl | Hv
  · -- the empty membership: no op, the tracker's own maps
    obtain ⟨hV, hVO, hL, hLN, hAL⟩ := ApiImpl.confStateIs_empty Hc
    have Hm : restoreM c.VotersOutgoing' c.Voters' c.Learners' c.LearnersNext' c.AutoLeave' =
        some (cfgState ∅ ∅) := by
      rw [hVO, hV, hL, hLN]; rfl
    iapply H chg cs c dq v0 _ Hm Hmi Harr Hl Hln Hal $$ [$Hpkg $Hcs $Hv0 $Hprs]
    inext
    iintro %cfgv %prsm %prs ⟨Hcs, Hv0, #Hprs', Hres⟩
    icases Hres with (⟨%Hops, %Hcfg, %Hprsm, -⟩ | ⟨%Hops, -⟩)
    · subst Hcfg Hprsm
      iapply HΦ
      iframe Hcs
      unfold ownCfgPairM
      iapply ApiImpl.cfgPairBody_empty _ _ v0 Harr Hl Hln Hal $$ Hv0 Hprs'
    · exfalso; exact Hops (restoreSimpleOps_nil _ _ _ _ hVO hV hL hLN)
  · -- a valid membership: `Restore` rebuilds it
    obtain ⟨Hcswf, Hm⟩ := ApiImpl.restore_of_confStateIs c m Hc Hv Hr
    have Hg : CCGood (ApiImpl.stOf m) := Hv.2
    iapply H chg cs c dq v0 _ Hm Hmi Harr Hl Hln Hal $$ [$Hpkg $Hcs $Hv0 $Hprs]
    inext
    iintro %cfgv %prsm %prs ⟨Hcs, -, -, Hres⟩
    icases Hres with (⟨%Hops, -⟩ | ⟨-, Hcfg, Hprsm, %Hdom, Hprogs⟩)
    · exfalso; exact restoreSimpleOps_ne_nil_of_voters _ _ _ _ Hcswf.1 Hops
    · iapply HΦ
      iframe Hcs
      unfold ownCfgPairM
      iapply ApiImpl.cfgPairBody_of_restore m cfgv prsm prs Hg Hdom $$ Hcfg Hprsm Hprogs

theorem confchange.Changer.Simple.apiSpec_of
    (H : confchange.Changer.Simple.spec (GF := GF) (hG := hG)) :
    confchange.Changer.Simple.apiSpec (GF := GF) (hG := hG) := by
  intro p chg m o t l al ccs ls dq dqs Ho Hne Hj
  iintro %Φ ⟨#Hpkg, Hp, Hccs, #Hro, Ht⟩ HΦ
  unfold ownTrackerM ownCfgPairM
  icases Ht with ⟨%Hmi, Ht⟩
  icases ApiImpl.cfgPairBody_tracker _ m $$ Ht with ⟨%pm, %pvs, %dqm, %Hst, Ht, Hback⟩
  obtain ⟨Hg, Hs⟩ := Hst
  iapply H p chg (ApiImpl.cfgOf m) pm pvs ccs ls l dq dqs (DFrac.own 1) dqm (DFrac.own 1) Hmi
    $$ [$Hpkg $Hp $Hccs $Hro $Ht]
  inext
  iintro %cfg %trk %err ⟨Hp, Hccs, Ht, Hres⟩
  iapply HΦ
  iframe Hp Hccs
  isplitl [Ht Hback]
  · isplitr
    · ipureintro; exact Hmi
    · iapply Hback $$ Ht
  · rw [Hs]; unfold Membership.applyGo
    iapply ApiImpl.ownResult_pair chg pvs o m _ cfg trk err Hg
      (ApiImpl.ccApplyM_simple _ Ho Hne Hj) $$ Hres

theorem confchange.Changer.EnterJoint.apiSpec_of
    (H : confchange.Changer.EnterJoint.spec (GF := GF) (hG := hG)) :
    confchange.Changer.EnterJoint.apiSpec (GF := GF) (hG := hG) := by
  intro p chg m o t l al ccs ls dq dqs Ho Hj
  iintro %Φ ⟨#Hpkg, Hp, Hccs, #Hro, Ht⟩ HΦ
  unfold ownTrackerM ownCfgPairM
  icases Ht with ⟨%Hmi, Ht⟩
  icases ApiImpl.cfgPairBody_tracker _ m $$ Ht with ⟨%pm, %pvs, %dqm, %Hst, Ht, Hback⟩
  obtain ⟨Hg, Hs⟩ := Hst
  iapply H p chg (ApiImpl.cfgOf m) pm pvs al ccs ls l dq dqs (DFrac.own 1) dqm (DFrac.own 1) Hmi
    $$ [$Hpkg $Hp $Hccs $Hro $Ht]
  inext
  iintro %cfg %trk %err ⟨Hp, Hccs, Ht, Hres⟩
  iapply HΦ
  iframe Hp Hccs
  isplitl [Ht Hback]
  · isplitr
    · ipureintro; exact Hmi
    · iapply Hback $$ Ht
  · rw [Hs]; unfold Membership.applyGo
    iapply ApiImpl.ownResult_pair chg pvs o m _ cfg trk err Hg
      (ApiImpl.ccApplyM_enterJoint _ Ho Hj) $$ Hres

theorem confchange.Changer.LeaveJoint.apiSpec_of
    (H : confchange.Changer.LeaveJoint.spec (GF := GF) (hG := hG)) :
    confchange.Changer.LeaveJoint.apiSpec (GF := GF) (hG := hG) := by
  intro p chg m o dq Ho
  iintro %Φ ⟨#Hpkg, Hp, Ht⟩ HΦ
  unfold ownTrackerM ownCfgPairM
  icases Ht with ⟨%Hmi, Ht⟩
  icases ApiImpl.cfgPairBody_tracker _ m $$ Ht with ⟨%pm, %pvs, %dqm, %Hst, Ht, Hback⟩
  obtain ⟨Hg, Hs⟩ := Hst
  iapply H p chg (ApiImpl.cfgOf m) pm pvs dq (DFrac.own 1) dqm (DFrac.own 1)
    $$ [$Hpkg $Hp $Ht]
  inext
  iintro %cfg %trk %err ⟨Hp, Ht, Hres⟩
  iapply HΦ
  iframe Hp
  isplitl [Ht Hback]
  · isplitr
    · ipureintro; exact Hmi
    · iapply Hback $$ Ht
  · rw [Hs]; unfold Membership.applyGo
    iapply ApiImpl.ownResult_pair chg pvs o m _ cfg trk err Hg
      (ApiImpl.ccApplyM_leaveJoint _ Ho) $$ Hres

end derive

end EtcdGrove
end Perennial
