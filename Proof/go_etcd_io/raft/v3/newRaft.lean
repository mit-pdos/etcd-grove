/-
Port of election_proof/proof_newRaft.v.
-/
module

public import Spec.go_etcd_io.raft.v3.newRaft
public import Spec.go_etcd_io.raft.v3.Config__validate
public import Spec.go_etcd_io.raft.v3.newLogWithSize
public import Spec.go_etcd_io.raft.v3.tracker.MakeProgressTracker
public import Spec.go_etcd_io.raft.v3.newReadOnly
public import Spec.go_etcd_io.raft.v3.traceInitState
public import Spec.go_etcd_io.raft.v3.raftLog__lastEntryID
public import Spec.go_etcd_io.raft.v3.confchange.Restore
public import Spec.go_etcd_io.raft.v3.raft__switchToConfig
public import Spec.go_etcd_io.raft.v3.assertConfStatesEquivalent
public import Spec.go_etcd_io.raft.v3.IsEmptyHardState
public import Spec.go_etcd_io.raft.v3.raft__loadState
public import Spec.go_etcd_io.raft.v3.raftLog__appliedTo
public import Spec.go_etcd_io.raft.v3.raft__becomeFollower
public import Spec.go_etcd_io.raft.v3.tracker.ProgressTracker__VoterNodes
public import Spec.fmt.Sprintf
public import Spec.strings.Join

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
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
  intro c cv lok si σ hs cs voters dqv
    Hvalid Hlok Hsto HmaxInfl Hcq Hdpf Hmcs Hidx Hncc Hss Hhs Happ Hvne Hvnd Hv0 Hvlen62 Hcs1 Hcs2 Hcs3 Hal
  obtain ⟨HvID, HvID1, HvID2, Hticks, HvSt, HvInfl, HvIB, HvLog, HvRO⟩ := Hvalid
  wp_start as ⟨Hc, #Hlg0, #HisSto, HSto, #HInit⟩
  wp_auto
  wp_apply wp_Config_validate _ _ ⟨HvID, HvID1, HvID2, Hticks, HvSt, HvInfl, HvIB, HvLog, HvRO⟩
    $$ [$Hc] as %cv' ⟨Hc, %Hpres⟩
  obtain ⟨HpID, HpET, HpHT, HpSt, HpAp, HpMI, HpCQ, HpPV, HpDPF, HpLg, HpMC, HpAW⟩ := Hpres
  rw [HpSt, Hsto, HpLg, Hlok]
  have Hmcs' : 0 < uint.Z cv'.MaxCommittedSizePerReady' := by
    rw [HpMC]
    split
    · rename_i Hz
      rcases Hmcs with Hc | Hc
      · exact absurd Hz Hc
      · have : uint.Z cv.MaxSizePerMsg' ≠ 0 := fun H0 => Hc (by word)
        word
    · rename_i Hz
      have : uint.Z cv.MaxCommittedSizePerReady' ≠ 0 := fun H0 => Hz (by word)
      word
  wp_apply wp_newLogWithSize _ _ _ _ lok Hidx Hncc Hss rfl Hmcs' $$ [$HisSto $HSto $Hlg0]
    as %l %ip ⟨%Hip0, HSto, HLback⟩
  rw [HpSt, Hsto]
  wp_apply HInit $$ [$HSto] as HSto Hvoters
  ihave HL := HLback $$ HSto
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
  let ls0 : LogState := ⟨σ.prev, σ.ents, [], σ.prev.index', σ.prev.index', none, ip, σ.prev.index', [], σ.ents,
    W64 0, cv'.MaxCommittedSizePerReady'⟩
  let s0 : NState := ⟨W64 0, W64 0, W64 0, .follower, ∅, [], func.nil, false, ∅, l, ls0, ∅,
    cv.PreVote'⟩
  ihave Htrk0 := ownTracker_empty tv0 v0 Htv0arr Htv0l Htv0ln Htv0al Hmi $$ Hv0 Hvotes Hprs0
  ihave Hmisc : ownRaftMisc (GF := GF) slice.nil ro slice.nil $$ [Hro]
  · unfold ownRaftMisc
    iexists _
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
    (fun h => absurd h (by simp only [s0]; decide)) (fun _ h => absurd h List.not_mem_nil)
    $$ «$r0» Hlg0 Htrk0 HL Hnil1 Hcap1 Hnil2 Hcap2 Hmisc Hob
  -- the configuration `Restore` built, as `switchToConfig` installs it
  ipersist Hprsm
  ihave %Hvlen := ownSlice_len $$ Hvoters
  have Hcsz : (GMap.size (GMap.listToSet voters) : Int) ≤ 2 ^ 62 := by
    rw [GMap.size_list_to_set _ Hvnd]; exact Hvlen62
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
    refine List.Perm.trans ?_ Hxs2.symm
    refine (List.perm_ext_iff_of_nodup Hvnd (GMap.NoDup_elements _)).2 ?_
    intro k; rw [GMap.elem_of_elements, GMap.elem_of_list_to_set]
  wp_apply wp_assertConfStatesEquivalent _ cs cs2 voters xs2 dqv (DFrac.own 1)
    Hperm Hvlen62 Hcs1 Hcs2 Hcs3 Hc2a Hc2b Hc2c (by rw [Hal, Hc2al]) $$ [$Hvoters $Hcs2v]
    as ⟨Hvoters, Hcs2v⟩
  -- `if !IsEmptyHardState(hs) { r.loadState(hs) }`: both arms end at the
  -- same struct state `s1` and log state `ls1`, so the rest of the proof
  -- is done once, for both.
  let ls1 : LogState := ⟨σ.prev, σ.ents, [], committedAfter σ.prev hs, σ.prev.index', none, ip,
    σ.prev.index', [], σ.ents, W64 0, cv'.MaxCommittedSizePerReady'⟩
  let s1 : NState :=
    { s0 with progress := prs, prvals := pvs1, term := hs.Term', vote := hs.Vote', logst := ls1 }
  wp_join iprop(ownRaftPhys (listToSet voters) «$r0_ptr» cv.ID' s1 ∗ hs_ptr ↦ hs ∗
      r_ptr ↦ «$r0_ptr») at next
    with [Hphys hs r] as ⟨Hphys, hs, r⟩
  · wp_apply wp_IsEmptyHardState
    by_cases Hemp : HsEmpty hs
    · have Hd : decide (hs.Term' = W64 0 ∧ hs.Vote' = W64 0 ∧ hs.Commit' = W64 0) = true :=
        decide_eq_true Hemp
      rw [Hd]
      wp_auto
      isplitr
      · ipureintro; rfl
      iframe hs r
      iapply ownRaftPhys_eq _ _ _ _ _ ?_ $$ Hphys
      obtain ⟨HT, HV, _⟩ := Hemp
      simp only [s1, s0, ls1, ls0, committedAfter, (show HsEmpty hs from ⟨HT, HV, ‹_›⟩), ↓reduceIte,
        HT, HV]
    · have Hd : decide (hs.Term' = W64 0 ∧ hs.Vote' = W64 0 ∧ hs.Commit' = W64 0) = false :=
        decide_eq_false Hemp
      rw [Hd]
      wp_auto
      have Hll : uint.Z (logLast ls0) = uint.Z σ.prev.index' + (σ.ents.length : Int) := by
        simp only [logLast, ls0, List.length_nil]; word
      have Hpre : uint.Z ({ s0 with progress := prs, prvals := pvs1 } : NState).logst.committed
            ≤ uint.Z hs.Commit' ∧
          uint.Z hs.Commit' ≤ uint.Z (logLast ({ s0 with progress := prs, prvals := pvs1 } : NState).logst) := by
        have := Hhs Hemp
        show uint.Z σ.prev.index' ≤ _ ∧ _ ≤ uint.Z (logLast ls0)
        rw [Hll]; exact this
      wp_apply wp_raft_loadState _ _ _
        { s0 with progress := prs, prvals := pvs1 } hs Hpre
        (by show uint.Z (W64 0) ≤ uint.Z hs.Term'; word) $$ [$Hphys] as Hphys
      isplitr
      · ipureintro; rfl
      iframe hs r
      iapply ownRaftPhys_eq _ _ _ _ _ ?_ $$ Hphys
      simp only [s1, s0, ls1, ls0, committedAfter, Hemp, ↓reduceIte]
  -- `if c.Applied > 0 { raftlog.appliedTo(c.Applied, 0) }`, likewise
  let ap : w64 := if cv.Applied' = W64 0 then σ.prev.index' else cv.Applied'
  let ls2 : LogState := ⟨σ.prev, σ.ents, [], committedAfter σ.prev hs, ap, none, ip,
    w64Max σ.prev.index' ap, [], σ.ents, W64 0, cv'.MaxCommittedSizePerReady'⟩
  let s2 : NState := { s1 with logst := ls2 }
  rw [HpAp]
  wp_join iprop(ownRaftPhys (listToSet voters) «$r0_ptr» cv.ID' s2 ∗ c_ptr ↦ c ∗ c ↦ cv' ∗
      raftlog_ptr ↦ l) with [Hphys c Hc raftlog] as ⟨Hphys, c, Hc, raftlog⟩
  · -- `raftlog` is `r.raftLog`: the log, through the accessor
    have Ha0 : cv.Applied' ≠ W64 0 := by intro h; rw [h] at Hif; exact absurd Hif (by decide)
    have Hrng : uint.Z ls1.applied ≤ uint.Z cv'.Applied' ∧ uint.Z cv'.Applied' ≤ uint.Z ls1.committed := by
      rw [HpAp]
      rcases Happ with h | h
      · exact absurd h Ha0
      · exact h
    icases ownRaftPhys_log_at _ «$r0_ptr» cv.ID' s1 $$ Hphys with ⟨HL, Hlogback⟩
    wp_apply wp_raftLog_appliedTo l ls1 cv'.Applied' (W64 0) Hrng $$ [$HL] as HL
    ihave Hphys := Hlogback $$ %_ HL
    isplitr
    · ipureintro; rfl
    iframe c Hc raftlog
    iapply ownRaftPhys_eq _ _ _ _ _ ?_ $$ Hphys
    simp only [s2, ls2, ap, ls1, Ha0, ↓reduceIte, HpAp]
  · have Ha0 : cv.Applied' = W64 0 := by word
    iframe c Hc raftlog
    iapply ownRaftPhys_eq _ _ _ _ _ ?_ $$ Hphys
    simp only [s2, ls2, ap, ls1, s1, Ha0, ↓reduceIte, w64Max, Int.lt_irrefl]
  -- `r.becomeFollower(r.Term, None)`
  wp_apply raft.wp_load_Term $$ Hphys as Hphys
  wp_apply wp_raft_becomeFollower _ _ _ s2 s2.term (W64 0) (Int.le_refl _) $$ [$Hphys]
    as %pvs3 Hphys
  let s3 : NState := { becomeFollower s2 s2.term (W64 0) with prvals := pvs3 }
  -- `r.trk.VoterNodes()`
  icases ownRaftPhys_tracker_same _ _ _ s3 $$ Hphys with ⟨%tv3, Htrkf, Htrk3, Htrkback⟩
  wp_apply wp_ProgressTracker_VoterNodes $$ [$Htrkf $Htrk3] as %nsl %nxs ⟨Htrkf, Htrk3, Hnsl, %Hnxs⟩
  ihave Hphys := Htrkback $$ %tv3 Htrkf Htrk3
  -- the log line's `nodesStrs` loop; what it builds is never read
  ihave IH : iprop(∃ (k x : w64) (sl' : GoSlice) (strs : List GoString),
      "i" ∷ i_ptr ↦ k ∗ "n" ∷ n_ptr ↦ x ∗ "nodesStrs" ∷ nodesStrs_ptr ↦ sl' ∗
      "Hstrs" ∷ sl' ↦* strs ∗
      "Hstrs_cap" ∷ ownSliceCap GoString sl' (DFrac.own 1) ∗
      "Hnsl" ∷ nsl ↦* nxs ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ (nxs.length : Int)⌝) $$ [i n nodesStrs Hnsl]
  · iexists W64 0, _, slice.nil, []
    iframe i n nodesStrs Hnsl
    isplitr
    · iapply ownSlice_nil
    isplitr
    · iapply ownSliceCap_nil
    ipureintro; constructor <;> word
  wp_for IH
  wp_if_destruct
  · ihave %Hnl := ownSlice_len $$ Hnsl
    have Hlt : (sint.Z k).toNat < nxs.length := by word
    obtain ⟨e, He⟩ : ∃ e, nxs[(sint.Z k).toNat]? = some e := ⟨_, List.getElem?_eq_getElem Hlt⟩
    simp only [show 0 ≤ sint.Z k ∧ sint.Z k < sint.Z nsl.len from ⟨Hk.1, Hif⟩, and_self]
    wp_apply wp_load_slice_index nsl (sint.Z k) nxs (DFrac.own 1) e Hk.1 $$ [Hnsl] as Hnsl
    · iframe; ipureintro; exact He
    wp_apply wp_slice_literal
    try (isplitr; (ipureintro; rfl))
    iintro %sla ⟨Hargs, -⟩
    wp_auto
    wp_apply wp_fmt_Sprintf $$ [$Hargs] as %str Hargs
    · ipureintro
      exact _root_.Perennial.fmt.StringArgsWf.cons_other _ _ _ (by simp [go.uint64, go.string])
        _root_.Perennial.fmt.StringArgsWf.nil
    wp_apply wp_slice_literal
    try (isplitr; (ipureintro; rfl))
    iintro %sl2 ⟨Hsl2, -⟩
    wp_auto
    wp_apply wp_slice_append $$ [$Hstrs $Hstrs_cap $Hsl2] as %sl3 ⟨Hstrs, Hstrs_cap, -⟩
    wp_for_post
    iframe
    iexists _, _, _, _
    iframe
    ipureintro; constructor <;> word
  -- the log line: `r.id`, `strings.Join(nodesStrs, ",")`, `r.Term`, then
  -- `r.raftLog.committed` and `r.raftLog.applied` through the log
  wp_apply raft.wp_load_id $$ Hphys as Hphys
  wp_apply wp_strings_Join $$ [$Hstrs] as %joined Hstrs
  wp_apply raft.wp_load_Term $$ Hphys as Hphys
  wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
  icases ownRaftPhys_log_same _ _ _ s3 $$ Hphys with ⟨Hlog3, Hlogback⟩
  icases ownRaftLog_struct _ _ $$ Hlog3 with ⟨%lv3, Hl3, -, Hl3back⟩
  wp_auto
  ihave Hlog3 := Hl3back $$ Hl3
  ihave Hphys := Hlogback $$ Hlog3
  wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
  icases ownRaftPhys_log_same _ _ _ s3 $$ Hphys with ⟨Hlog3, Hlogback⟩
  icases ownRaftLog_struct _ _ $$ Hlog3 with ⟨%lv4, Hl3, -, Hl3back⟩
  wp_auto
  ihave Hlog3 := Hl3back $$ Hl3
  ihave Hphys := Hlogback $$ Hlog3
  wp_raft_log
  iapply HΦ $$ %«$r0_ptr» %s3 %cv'
  iframe Hphys Hc
  isplitr
  · ipureintro; exact HpAW
  -- `becomeFollower(r.Term, None)` keeps the term, so `reset` keeps the
  -- vote: the state is the persisted `HardState`'s
  ipureintro
  refine ⟨⟨rfl, rfl⟩, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  show (if s2.term = s2.term then s2.vote else W64 0) = hs.Vote'
  simp only [↓reduceIte]
  rfl

end proof

end EtcdGrove
end Perennial
