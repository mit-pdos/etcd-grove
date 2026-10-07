/-
Port of election_proof/proof_newRaft.v.
-/
import EtcdGrove.Raft.ElectionProof.Spec.newRaft
import EtcdGrove.Raft.ElectionProof.Spec.Config__validate
import EtcdGrove.Raft.ElectionProof.Spec.newLogWithSize
import EtcdGrove.Raft.ElectionProof.Spec.MakeProgressTracker
import EtcdGrove.Raft.ElectionProof.Spec.newReadOnly
import EtcdGrove.Raft.ElectionProof.Spec.traceInitState
import EtcdGrove.Raft.ElectionProof.Spec.raftLog__lastEntryID
import EtcdGrove.Raft.ElectionProof.Spec.confchange_Restore
import EtcdGrove.Raft.ElectionProof.Spec.raft__switchToConfig
import EtcdGrove.Raft.ElectionProof.Spec.assertConfStatesEquivalent
import EtcdGrove.Raft.ElectionProof.Spec.IsEmptyHardState
import EtcdGrove.Raft.ElectionProof.Spec.raft__loadState
import EtcdGrove.Raft.ElectionProof.Spec.raftLog__appliedTo
import EtcdGrove.Raft.ElectionProof.Spec.raft__becomeFollower
import EtcdGrove.Raft.ElectionProof.Spec.ProgressTracker__VoterNodes
import EtcdGrove.Raft.ElectionProof.Spec.fmt_Sprintf
import EtcdGrove.Raft.ElectionProof.Spec.strings_Join

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem newRaft.wp_proof
    (wp_Config_validate : Config.validate.spec (GF := GF) (hG := hG))
    (wp_newLogWithSize : newLogWithSize.spec (GF := GF) (hG := hG))
    (wp_MakeProgressTracker : tracker.MakeProgressTracker.spec (GF := GF) (hG := hG))
    (wp_newReadOnly : newReadOnly.spec (GF := GF) (hG := hG))
    (wp_traceInitState : traceInitState.spec (GF := GF) (hG := hG))
    (wp_raftLog_lastEntryID : raftLog.lastEntryID.spec (GF := GF) (hG := hG))
    (wp_confchange_Restore : confchange.Restore.spec (GF := GF) (hG := hG))
    (wp_raft_switchToConfig : raft.switchToConfig.spec (GF := GF) (hG := hG))
    (wp_assertConfStatesEquivalent : assertConfStatesEquivalent.spec (GF := GF) (hG := hG))
    (wp_IsEmptyHardState : IsEmptyHardState.spec (GF := GF) (hG := hG))
    (wp_raft_loadState : raft.loadState.spec (GF := GF) (hG := hG))
    (wp_raftLog_appliedTo : raftLog.appliedTo.spec (GF := GF) (hG := hG))
    (wp_raft_becomeFollower : raft.becomeFollower.spec (GF := GF) (hG := hG))
    (wp_ProgressTracker_VoterNodes : tracker.ProgressTracker.VoterNodes.spec (GF := GF) (hG := hG))
    (wp_fmt_Sprintf : fmt.Sprintf.spec (GF := GF) (hG := hG))
    (wp_strings_Join : strings.Join.spec (GF := GF) (hG := hG)) :
    newRaft.spec (GF := GF) (hG := hG) := by
  intro c cv lok si prev ents ss hs cs voters dqv
    Hvalid Hlok Hsto HmaxInfl Hcq Hdpf Hidx Hncc Hss Hhs Happ Hvne Hvnd Hv0 Hcs1 Hcs2 Hcs3 Hal
  obtain ⟨HvID, HvID1, HvID2, Hticks, HvSt, HvInfl, HvIB, HvLog, HvRO⟩ := Hvalid
  wp_start as ⟨Hc, #Hlg0, #HisSto, HSto, #HInit⟩
  wp_auto
  wp_apply wp_Config_validate _ _ ⟨HvID, HvID1, HvID2, Hticks, HvSt, HvInfl, HvIB, HvLog, HvRO⟩
    $$ [$Hc] as %cv' ⟨Hc, %Hpres⟩
  obtain ⟨HpID, HpET, HpHT, HpSt, HpAp, HpMI, HpCQ, HpPV, HpDPF, HpLg⟩ := Hpres
  rw [HpSt, Hsto, HpLg, Hlok]
  wp_apply wp_newLogWithSize _ _ _ _ _ _ lok Hidx Hncc Hss rfl $$ [$HisSto $HSto $Hlg0]
    as %l %lv ⟨Hl, %Hlv, Hcore⟩
  obtain ⟨Hlvst, Hlvcm, Hlvap⟩ := Hlv
  iunfold ownRaftLogCore at Hcore
  icases Hcore with ⟨%sprev, %stored, %ss', Hcore⟩
  iNamed Hcore
  obtain ⟨Hsp, Hlstored, Hlstored_eq⟩ := Hstore
  have Hst : ents = stored := Hlstored_eq rfl
  subst sprev
  subst stored
  rw [Hlvst]
  rw [HpSt, Hsto]
  wp_apply HInit $$ [$HStorage] as HSto Hvoters
  ihave HL := ownRaftLog_intro l lv (GoInterface.ok si) none prev ents [] prev.index' prev.index'
    prev ents ss' Hlvst Hlvcm Hlvap Hidx Hnowrap ⟨rfl, Hlstored, Hlstored_eq⟩ Hoffset
    HnoConfChange Happlied Hpapplied Hcommitted Hssnap
    $$ Hl HisSto HSto Husnap Huents Huents_cap Hl_logger Hu_logger
  wp_apply wp_MakeProgressTracker as %tv0 %v0 ⟨%Htv0, Hv0, Hvotes, Hprs0⟩
  obtain ⟨Htv0mi, Htv0mb, Htv0arr, Htv0l, Htv0ln, Htv0al⟩ := Htv0
  wp_apply wp_newReadOnly as %ro Hro
  wp_apply wp_traceInitState
  wp_apply wp_raftLog_lastEntryID $$ [$HL] as %lastID ⟨HL, -⟩
  have Hmi : 0 ≤ sint.Z tv0.MaxInflight' ∧ sint.Z tv0.MaxInflight' < 2 ^ 62 := by
    rw [Htv0mi, HpMI]; omega
  ipersist Hprs0
  wp_apply wp_confchange_Restore ⟨tv0, lastID.index'⟩ _ voters dqv v0 Hvne Hv0 Hcs1 Hcs2 Hcs3
    Hmi Htv0arr Htv0l Htv0ln $$ [$Hvoters $Hv0 $Hprs0]
    as %cfgv %prsm %prs %vref %vm ⟨Hvoters, Hv0, -, %Hcfgv, Hvref, %Hvm, Hprsm, %Hprs, Hprogs⟩
  obtain ⟨Hcfgarr, Hcfgl, Hcfgln, Hcfgal⟩ := Hcfgv
  -- the struct, over the empty configuration: its tracker is the empty
  -- one `MakeProgressTracker` built, and its log is at the state
  -- `newLogWithSize` built. It holds no `Progress` yet, so `prvals` is
  -- empty.
  let ls0 : LogState := ⟨prev, ents, [], prev.index', prev.index', none⟩
  let s0 : NState := ⟨W64 0, W64 0, W64 0, .follower, ∅, [], func.nil, ∅, l, ls0, ∅,
    cv.PreVote'⟩
  ihave Htrk0 := ownTracker_empty tv0 v0 Htv0arr Htv0l Htv0ln Htv0al Hmi $$ Hv0 Hvotes Hprs0
  ihave Hmisc : ownRaftMisc (GF := GF) slice.nil ro slice.nil $$ [Hro]
  · unfold ownRaftMisc
    iexists [], _
    simp only [named]
    iframe Hro
    isplitr
    · iapply ownSlice_nil
    isplitr
    · iapply ownSliceCap_nil
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply ownSlice_nil
    iapply ownSliceCap_nil
  ihave Hnil1 := ownSlice_nil (V := raftpb.Message) (GF := GF) (DFrac.own 1)
  ihave Hnil2 := ownSlice_nil (V := raftpb.Message) (GF := GF) (DFrac.own 1)
  ihave Hcap1 := ownSliceCap_nil (V := raftpb.Message) (GF := GF)
  ihave Hcap2 := ownSliceCap_nil (V := raftpb.Message) (GF := GF)
  ihave Hob := outboxRel_nil (GF := GF)
  ihave Hphys := ownRaftPhys_intro ∅ «$r0_ptr» cv.ID' s0 _ [] [] lok
    HpID rfl rfl rfl rfl rfl HpPV (by rw [HpDPF, Hdpf]) (by rw [HpCQ, Hcq]) rfl rfl HvID
    (by show 0 < sint.Z cv'.ElectionTick'; rw [HpET]; omega) (by rw [HpLg, Hlok]) rfl
    $$ «$r0» Hlg0 Htrk0 HL Hnil1 Hcap1 Hnil2 Hcap2 Hmisc Hob
  -- the configuration `Restore` built, as `switchToConfig` installs it
  ipersist Hprsm
  ihave %Hvlen := ownSlice_len $$ Hvoters
  have Hcsz : (GMap.size (GMap.listToSet voters) : Int) < 2 ^ 63 := by
    rw [GMap.size_list_to_set _ Hvnd]; word
  ihave Hcfg : ownConfig (GF := GF) (GMap.listToSet voters) cfgv prsm prs $$ [Hvref Hprogs]
  · unfold ownConfig
    iexists vref, vm
    simp only [named]
    iframe Hvref Hprsm Hprogs
    ipureintro
    exact ⟨Hcfgarr, Hcfgl, Hcfgln, Hcfgal, Hvm, Hprs, Hcsz⟩
  wp_apply wp_raft_switchToConfig _ _ _ _ s0 cfgv prsm prs (by simp only [s0]; decide) $$ [$Hphys $Hcfg]
    as %cs2 %xs2 %pvs1 ⟨Hphys, Hcs2v, %Hxs2, %Hcs2l⟩
  obtain ⟨Hc2a, Hc2b, Hc2c, Hc2al⟩ := Hcs2l
  have Hperm : voters ≡ₚ xs2 := by
    sorry
  wp_apply wp_assertConfStatesEquivalent _ cs cs2 voters xs2 dqv (DFrac.own 1)
    Hperm Hcs1 Hcs2 Hcs3 Hc2a Hc2b Hc2c (by rw [Hal, Hc2al]) $$ [$Hvoters $Hcs2v]
    as ⟨Hvoters, Hcs2v⟩
  trace_state
  sorry

end proof

end EtcdGrove
end Perennial
