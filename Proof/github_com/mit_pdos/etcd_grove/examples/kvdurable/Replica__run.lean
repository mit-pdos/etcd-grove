/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvdurable/Replica__run.lean`. Lean-first (no
Rocq counterpart; kvreconf's `Replica.run` proof, with the durable part).

The loop keeps `runInv` (`RunInv.lean`). Each `Ready` (`readyGot`) is handled as kvreconf's, with,
in `dmu`, its storage changes on the `MemoryStorage` and the image (`RunImage.lean`): `run`'s claim
finds no batch pending (the phase idle at the driver's durable state), and its half of the image's
hard state ties the image's to the driver's (G12). A cut batch (`sync`: a snapshot, entries, or the
term or vote moved) is recorded (`KdPhase.waiting`) and written (`persist.specRun`, which enters it),
its messages sent before the write only at role leader (`readyLeaderMsgs`); a commit-only batch is
entered at once (`RunDmu.lean`), written or not (`persist.spec`). The frozen bound is raised to the
delivered log (the delivered entries are the batch's durable log's: G14). A write that fails (the
incarnation crashed) ends the loop, `run`'s claim sent with its `nodeRunning` on `runDone`.

raft's facts on a `Ready` not yet in its API (being added to `readyRest`) are isolated below as
private lemmas left `sorry` (`ready_*_G*`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Replica__run
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Replica__applyEntry
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Replica__install
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Replica__answer
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Replica__request
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Replica__persist
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Storage__Append
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Storage__ApplySnapshot
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Storage__SetHardState
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Stats__add
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.fits
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.oneIn
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.decodeState
public import Spec.go_etcd_io.raft.v3.node__Ready
public import Spec.go_etcd_io.raft.v3.node__Advance
public import Spec.go_etcd_io.raft.v3.IsEmptySnap
public import Spec.go_etcd_io.raft.v3.IsEmptyHardState
public import Spec.go_etcd_io.raft.v3.MustSync
public import Spec.go_etcd_io.raft.v3.MemoryStorage__Append
public import Spec.go_etcd_io.raft.v3.MemoryStorage__ApplySnapshot
public import Spec.go_etcd_io.raft.v3.raftpb.Snapshot__GetData
public import Spec.go_etcd_io.raft.v3.raftpb.Snapshot__GetMetadata
public import Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetIndex
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.RunDmu
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.SnapMake
public import Proof.go_etcd_io.raft.v3.Base
public import Proof.go_etcd_io.raft.v3.FrameH

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KdStor GF]

attribute [local instance] kdStorageModel

/-! ## raft's facts on a `Ready`, not yet in its API (being added to `readyRest`) -/

/-- (G4) A `Ready`'s hard state's commit index is at least the driver's previous one. -/
private theorem ready_commit_mono_G4 (γc : Cluster) (N : Namespace) (rd : Ready) (st : NodeDriverState)
    (ce : List LogEntry) (es : List EntryM) (h : HardStateM) (L : Option SnapLoan) (ms : List QMsg)
    (ss : Option (w64 × StateType)) :
    readyRest (GF := GF) γc N rd st ce es h L ms ss ⊢ readyRest γc N rd st ce es h L ms ss ∗
      ⌜uint.nat st.hardState.Commit' ≤ uint.nat (phsNext st.hardState h).Commit'⌝ := by
  sorry

/-- (G7) A `Ready`'s snapshot is past the durable commit index, and the `Ready`'s commit index is at
least its index. -/
private theorem ready_snap_G7 (γc : Cluster) (N : Namespace) (rd : Ready) (st : NodeDriverState)
    (ce : List LogEntry) (es : List EntryM) (h : HardStateM) (l : SnapLoan) (ms : List QMsg)
    (ss : Option (w64 × StateType)) :
    readyRest (GF := GF) γc N rd st ce es h (some l) ms ss ⊢
      readyRest γc N rd st ce es h (some l) ms ss ∗
      ⌜uint.nat st.durable.commit < uint.nat l.snap.Metadata'.Index' ∧
        uint.nat l.snap.Metadata'.Index' ≤ uint.nat (phsNext st.hardState h).Commit'⌝ := by
  sorry

/-- (G8) A `Ready`'s commit index is at most the last index of the durable log after its batch. -/
private theorem ready_commit_le_last_G8 (γc : Cluster) (N : Namespace) (rd : Ready)
    (st : NodeDriverState) (ce : List LogEntry) (es : List EntryM) (h : HardStateM)
    (L : Option SnapLoan) (ms : List QMsg) (ss : Option (w64 × StateType)) :
    readyRest (GF := GF) γc N rd st ce es h L ms ss ⊢ readyRest γc N rd st ce es h L ms ss ∗
      ⌜uint.nat (phsNext st.hardState h).Commit' ≤
        (readyDurable st.durable (phsNext st.hardState h) L es).last⌝ := by
  sorry

/-- (G9) A `Ready`'s entries (without a snapshot) start at most one past the durable log's end. -/
private theorem ready_ents_start_G9 (γc : Cluster) (N : Namespace) (rd : Ready) (st : NodeDriverState)
    (ce : List LogEntry) (es : List EntryM) (h : HardStateM) (ms : List QMsg)
    (ss : Option (w64 × StateType)) :
    readyRest (GF := GF) γc N rd st ce es h none ms ss ⊢ readyRest γc N rd st ce es h none ms ss ∗
      ⌜∀ e0, es.head? = some e0 → uint.nat e0.Index' ≤ st.durable.last + 1⌝ := by
  sorry

/-- (G10) The delivered log after a `Ready` (without a snapshot) is at most its commit index. -/
private theorem ready_delivered_le_commit_G10 (γc : Cluster) (N : Namespace) (rd : Ready)
    (st : NodeDriverState) (ce : List LogEntry) (es : List EntryM) (h : HardStateM) (ms : List QMsg)
    (ss : Option (w64 × StateType)) :
    readyRest (GF := GF) γc N rd st ce es h none ms ss ⊢ readyRest γc N rd st ce es h none ms ss ∗
      ⌜(st.delivered ++ ce).length ≤ uint.nat (phsNext st.hardState h).Commit'⌝ := by
  sorry

/-- (G14) The committed entries a `Ready` (without a snapshot) delivers are in the durable log after
its batch, above its base. -/
private theorem ready_durable_has_delivered_G14 (γc : Cluster) (N : Namespace) (rd : Ready)
    (st : NodeDriverState) (ce : List LogEntry) (es : List EntryM) (h : HardStateM) (ms : List QMsg)
    (ss : Option (w64 × StateType)) :
    readyRest (GF := GF) γc N rd st ce es h none ms ss ⊢ readyRest γc N rd st ce es h none ms ss ∗
      ⌜∀ (j : Nat) (e : LogEntry), ce[j]? = some e →
        uint.nat (readyDurable st.durable (phsNext st.hardState h) none es).base.index' <
          st.delivered.length + 1 + j →
        (readyDurable st.durable (phsNext st.hardState h) none es).ents[st.delivered.length + j -
          uint.nat (readyDurable st.durable (phsNext st.hardState h) none es).base.index']? =
          some (e.toEntryM (W64 (st.delivered.length + 1 + j)))⌝ := by
  sorry

/-- (G17) A `Ready`'s entries (without a snapshot) start past the driver's previous commit index. -/
private theorem ready_ents_above_commit_G17 (γc : Cluster) (N : Namespace) (rd : Ready)
    (st : NodeDriverState) (ce : List LogEntry) (es : List EntryM) (h : HardStateM) (ms : List QMsg)
    (ss : Option (w64 × StateType)) :
    readyRest (GF := GF) γc N rd st ce es h none ms ss ⊢ readyRest γc N rd st ce es h none ms ss ∗
      ⌜∀ e0, es.head? = some e0 → uint.nat st.hardState.Commit' < uint.nat e0.Index'⌝ := by
  sorry

/-- (G20) A `Ready`'s entries decode back from the file (`EntWf`: a type of raft's, `EntryNormal`,
`EntryConfChange` or `EntryConfChangeV2`, and data of a Go slice's length). -/
private theorem ready_ents_wf_G20 (γc : Cluster) (N : Namespace) (rd : Ready) (st : NodeDriverState)
    (ce : List LogEntry) (es : List EntryM) (h : HardStateM) (L : Option SnapLoan) (ms : List QMsg)
    (ss : Option (w64 × StateType)) :
    readyRest (GF := GF) γc N rd st ce es h L ms ss ⊢ readyRest γc N rd st ce es h L ms ss ∗
      ⌜∀ e ∈ es, EntWf e⌝ := by
  sorry

/-- (G21) A non-`nil` `SoftState` pointer (raft's `softStateIs` of a soft state). -/
private theorem softState_ne_null_G21 (p : Loc) (x : w64 × StateType) :
    softStateIs (GF := GF) p (some x) ⊢ ⌜p ≠ null⌝ := by
  sorry

set_option hygiene false in
/-- `run`'s exit: `run`'s half of `nodeRunning` and its claim sent on `runDone`, then `return`. -/
local macro "run_exit" : tactic => `(tactic| (
    try wp_auto
    wp_apply wp_handoff_send ρ.rd ρ.rdc (fun _ => iprop(nodeRunning n γ.r.cluster kdRaftN (1 : Qp).half ∗
        ∃ v : Option GName × RaftState, ghostVar ρ.ph.ph (1 : Qp).half v)) iprop(True)
      iprop(False) () $$ [$(frameH `HrdH) $(frameH `Hprod) Hrun Hclaim] as -
    · isplitl [Hrun Hclaim]
      · iframe Hrun; iexists _; iexact Hclaim
      · itrivial
    try wp_auto
    wp_for_post
    try wp_auto
    iapply HΦ
    itrivial
  ))

theorem Replica.run.wp_proof
    (wp_applyEntry : Replica.applyEntry.spec (GF := GF) (hG := hG))
    (wp_install : Replica.install.spec (GF := GF) (hG := hG))
    (wp_answer : Replica.answer.spec (GF := GF) (hG := hG))
    (wp_request : Replica.request.spec (GF := GF) (hG := hG))
    (wp_persist : Replica.persist.spec (GF := GF) (hG := hG))
    (wp_persistRun : Replica.persist.specRun (GF := GF) (hG := hG))
    (wp_add : Stats.add.spec (GF := GF) (hG := hG))
    (wp_fits : fits.spec (GF := GF) (hG := hG))
    (wp_oneIn : oneIn.spec (GF := GF) (hG := hG))
    (wp_decodeState : decodeState.spec (GF := GF) (hG := hG))
    (wp_SAppend : Storage.Append.spec (GF := GF) (hG := hG))
    (wp_SApplySnapshot : Storage.ApplySnapshot.spec (GF := GF) (hG := hG))
    (wp_SSetHardState : Storage.SetHardState.spec (GF := GF) (hG := hG))
    (wp_Ready : node.Ready.spec (GF := GF) (hG := hG))
    (wp_Advance : node.Advance.spec (GF := GF) (hG := hG))
    (wp_IsEmptySnap : IsEmptySnap.spec (GF := GF) (hG := hG))
    (wp_IsEmptyHardState : IsEmptyHardState.spec (GF := GF) (hG := hG))
    (wp_MustSync : MustSync.spec (GF := GF) (hG := hG))
    (wp_GetData : raftpb.Snapshot.GetData.spec (GF := GF) (hG := hG))
    (wp_GetMetadata : raftpb.Snapshot.GetMetadata.spec (GF := GF) (hG := hG))
    (wp_MdGetIndex : raftpb.SnapshotMetadata.GetIndex.spec (GF := GF) (hG := hG))
    (wp_Append : MemoryStorage.Append.spec (GF := GF) (hG := hG))
    (wp_ApplySnapshot : MemoryStorage.ApplySnapshot.spec (GF := GF) (hG := hG)) :
    Replica.run.spec (GF := GF) (hG := hG) := by
  intro γ vs dir id r n st sts sq ρ f l ap0 hs0 hsp0 S0 m0 snapIndex0 rafted0 Hraf Hsi0
  wp_start as ⟨#Hrr, Hstart, #HhsO0, #Hsend⟩
  ihave #Hrr' := Hrr
  iunfold isReplicaR at Hrr'
  iNamed Hrr'
  ihave #Hrep' := Hrep
  iunfold isReplica at Hrep'
  iNamed Hrep'
  ihave #HrP : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  ihave #HkC := Hcl
  iclear Hcl
  try wp_auto
  ihave Hinv := runInv_init γ id r n st ρ l ap0 hs0 S0 m0 pending_ptr lead_ptr snapIndex_ptr hs_ptr
    rafted_ptr hsp0 snapIndex0 rafted0 Hraf Hsi0 $$ [Hstart pending lead snapIndex hs rafted]
  · iframe Hstart pending lead snapIndex hs rafted HhsO0
  wp_for Hinv
  wp_apply (lc := 3) wp_Ready γ.r.cluster kdRaftN id n $$ [$HrP $HisNode] as %ch #Hch
  try wp_auto
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- a `Ready`
    simp only [chan.blockingClausePre]
    icases isReadyChan_recvAu n ch γ.r.cluster kdRaftN id _ _ rfl $$ Hch HisNode Hdrv
      with ⟨%γc, #Hchan, Hau⟩
    iexists Ready, inferInstance, inferInstance, inferInstance, inferInstance, ch, γc
    isplitr
    · ipureintro; rfl
    isplitr
    · iexact Hchan
    iapply Hau $$ [$Hlc1 $Hlc2]
    inext
    iintro %rdv Hgot
    iunfold readyGot at Hgot
    icases Hgot with ⟨%ce, %es, %h, %L, %ms, %ss, #Hce, #Hcomm, Hrs, Hrest, Hlm, Henter⟩
    ihave ⟨%Hidx, Hrest⟩ := readyRest_indices _ _ _ _ _ _ _ _ _ $$ Hrest
    ihave ⟨Hrest, %G4⟩ := ready_commit_mono_G4 _ _ _ _ _ _ _ _ _ _ $$ Hrest
    ihave ⟨Hrest, %G8⟩ := ready_commit_le_last_G8 _ _ _ _ _ _ _ _ _ _ $$ Hrest
    ihave ⟨Hrest, %G20⟩ := ready_ents_wf_G20 _ _ _ _ _ _ _ _ _ _ $$ Hrest
    simp only at Hidx G4 G8 G20
    try wp_auto
    cases L with
    | none =>
      ihave ⟨Hrest, %G9⟩ := ready_ents_start_G9 _ _ _ _ _ _ _ _ _ $$ Hrest
      ihave ⟨Hrest, %G10⟩ := ready_delivered_le_commit_G10 _ _ _ _ _ _ _ _ _ $$ Hrest
      ihave ⟨Hrest, %G14⟩ := ready_durable_has_delivered_G14 _ _ _ _ _ _ _ _ _ $$ Hrest
      ihave ⟨Hrest, %G17⟩ := ready_ents_above_commit_G17 _ _ _ _ _ _ _ _ _ $$ Hrest
      ihave ⟨%Hin, Hrest⟩ := readyRest_ceInBatch _ _ _ _ _ _ _ _ $$ Hrest
      simp only at G9 G10 G14 G17 Hin
      iunfold readyRest at Hrest
      icases Hrest with ⟨#Hes, Hmsl, Hmsok, #Hhs, #Hss, %Hbnd, Hsnap⟩
      iunfold readySnap at Hsnap
      icases Hsnap with ⟨%Hnull, Happ, #Hcef, -⟩
      wp_apply wp_fits rdv.Entries' es DFrac.discard $$ [$Hpkg $Hes] as %b ⟨-, %Hfit⟩
      cases b
      · run_exit
      have Hfit' := Hfit rfl
      simp only [NodeDriverState.afterReady]
      wp_pures
      -- `lead`, from the `SoftState`
      wp_join iprop(∃ lead' : Bool, lead_ptr ↦ lead' ∗ rd_ptr ↦ rdv ∗
          ⌜lead' = true → roleAfter role ss = StateLeader⌝) at next with [lead rd] as ⟨%lead', lead, rd, %Hlead'⟩
      · cases ss with
        | none =>
          iunfold softStateIs at Hss
          icases Hss with %Hn
          try wp_auto
          wp_if_destruct
          rotate_left
          · exfalso; exact Hif Hn
          wp_join_done
          iexists lead
          iframe
          ipureintro
          intro hl
          simp only [roleAfter, Option.map_none, Option.getD_none]; exact Hsi.1 hl
        | some x =>
          obtain ⟨ld, rs⟩ := x
          ihave %Hnn := softState_ne_null_G21 _ _ $$ Hss
          iunfold softStateIs at Hss
          icases Hss with ⟨#Hld, #Hrs⟩
          try wp_auto
          wp_if_destruct
          · exfalso; exact Hnn Hif
          · try wp_auto
            wp_join_done
            iexists _
            iframe
            ipureintro
            intro hl
            simp only [roleAfter, Option.map_some, Option.getD_some]
            have := (by simpa using hl : rs = (W64 2))
            rw [this]; rfl
      sorry
    | some lo =>
      sorry
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `stopc` closed
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ρ.stopc, ρ.sc
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply ownBroadcastChan_is_chan $$ HstopB
    iapply broadcast_chan_receive _ _ _ _ _ $$ HstopB
    iintro ⟨-, -⟩
    run_exit
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end kvdurable
end EtcdGrove
end Perennial
