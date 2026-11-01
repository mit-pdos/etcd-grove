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

set_option maxHeartbeats 8000000 in
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
      ihave %Hesl := entsPts_len _ _ _ $$ Hes
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
      wp_apply wp_IsEmptySnap rdv.Snapshot' DFrac.discard none $$ [$HrP] as %b2 ⟨%Hb2, -⟩
      · unfold snapOpt; ipureintro; exact Hnull
      subst Hb2
      simp only [Option.elim]
      try wp_auto
      wp_apply wp_IsEmptyHardState rdv.HardState' h $$ [$HrP $Hhs]
      try wp_auto
      -- `sync`: entries, or the term or vote moved
      wp_join (Q := fun v => iprop(⌜∃ b : Bool, v = #b ∧ (b = true ↔ (rdv.Entries'.len ≠ W64 0 ∨
          (¬ (h.Term' = W64 0 ∧ h.Vote' = W64 0 ∧ h.Commit' = W64 0) ∧
            (h.Vote' ≠ hd.Vote' ∨ h.Term' ≠ hd.Term'))))⌝ ∗ rd_ptr ↦ rdv ∗ hs_ptr ↦ hsp ∗
          changed_ptr ↦ !decide (h.Term' = W64 0 ∧ h.Vote' = W64 0 ∧ h.Commit' = W64 0)))
        at (if: _ then _ else _) with [rd hs changed] as ⟨%Hv, rd, hs, changed⟩
      · wp_if_destruct
        · try wp_auto
          have Hlen0 := Hif
          wp_if_destruct
          · try wp_auto
            iframe
            ipureintro
            refine ⟨false, rfl, ?_⟩
            simp only [Bool.false_eq_true, false_iff, not_or, not_and]
            refine ⟨fun h1 => h1 Hlen0, fun h1 => absurd h1 (by simpa using Hif)⟩
          · have Hchg := Hif
            try wp_auto
            wp_apply wp_MustSync rdv.HardState' hsp h hd (W64 0) $$ [$HrP $Hhs $HhsO]
            iframe
            ipureintro
            refine ⟨_, rfl, ?_⟩
            simp only [decide_eq_true_eq]
            constructor
            · intro h1; right; exact ⟨by simpa using Hchg, by simpa using h1⟩
            · intro h1; rcases h1 with h1 | ⟨-, h1⟩
              · exact absurd Hlen0 h1
              · rcases h1 with h1 | h1
                · right; left; exact h1
                · right; right; exact h1
        · try wp_auto
          iframe
          ipureintro
          exact ⟨true, rfl, by simp only [true_iff]; exact Or.inl Hif⟩
      obtain ⟨syncb, rfl, Hsync⟩ := Hv
      try wp_auto
      -- `dmu`: the phase idle at the driver's durable state, the image's hard state the driver's
      irename Hfz => HfzD
      wp_apply (lc := 2) sync.Mutex.wp_Lock _ _ $$ [$Hdmu] as ⟨Hlocked, HI⟩
      iunfold kdDmuInv at HI
      iNamed HI
      icases Hlive with ⟨%S1, %o, %pz, Hwr, %HMok, #Hcert, %Hfb, Hph⟩
      ihave ⟨Hclaim, Hph, %Hidle⟩ := kd_claim_idle γ id n ρ.ph.ph S S1 M pz $$ [Hclaim Hph]
      · iframe Hclaim Hph
      obtain ⟨rfl, HS1, HSM⟩ := Hidle
      subst S1
      ihave %Hcmeq := ghostVar_agree ρ.ph.cm _ _ _ _ $$ Hcm Hcmh
      ihave %Hfzd := monoNatLbOwn_valid ρ.ph.ic 1 fz D.length $$ Hic Hicl
      ihave #Hst' : st.[KStorage, go!"img"] ↦□ ip $$ []
      · iexact Himg
      try wp_auto
      -- the hard state (if any): the image's set to the driver's next one (`phsNext`)
      wp_join iprop(∃ hsp' : Loc, memStorMeta ρ.ms ρ.γs (phsNext hd h) ∗
          ownImage ip (imgSetHardState M (phsNext hd h)) ∗ hs_ptr ↦ hsp' ∗ hsOpt hsp' (phsNext hd h) ∗
          rd_ptr ↦ rdv ∗ r_ptr ↦ r) at next with [Hmeta Himage hs rd r] as
          ⟨%hsp', Hmeta, Himage, hs, #HhsO', rd, r⟩
      · try wp_auto
        wp_if_destruct
        · -- unchanged: `phsNext` keeps the driver's, which the image has
          have Hpe := phsNext_empty hd h (by simpa using Hif)
          rw [Hpe, show imgSetHardState M hd = M by rw [← Hcmeq]; cases M; rfl]
          wp_join_done
          iexists hsp
          rw [← Hcmeq]
          iframe
          rw [Hcmeq]
          iexact HhsO
        · have Hpe := phsNext_ne hd h (by simpa using Hif)
          rw [Hpe]
          try wp_auto
          wp_apply wp_SSetHardState st ρ.ms ρ.γs M.hs ip M rdv.HardState' h
            $$ [$Hpkg $Hrec $Hmeta $Hst' $Himage $Hhs] as ⟨Hmeta, Himage⟩
          try wp_auto
          wp_join_done
          iexists rdv.HardState'
          iframe
          iexact Hhs
      -- the entries, on the `MemoryStorage` (the range raft lends) and the image
      icases append_none_pre st ρ.ms ρ.γs es $$ Hrec Happ with ⟨%k, %old, ⟨%Hk, %Hk0⟩, Hrange⟩
      have h1 : ∀ (j : Nat) (e : EntryM), es[j]? = some e → uint.nat e.Index' = k + j := by
        intro j e hj
        cases hes : es with
        | nil => rw [hes] at hj; cases hj
        | cons e0 rest =>
          rw [Hk e0 (by rw [hes]; rfl)]
          exact Hidx e0 (by rw [hes]; rfl) j e hj
      have h2 : k + es.length ≤ 2 ^ 61 := by
        cases hes : es with
        | nil => rw [Hk0 hes]; simp
        | cons e0 rest =>
          have := Hfit' e0 (by rw [hes]; rfl)
          rw [Hk e0 (by rw [hes]; rfl)]
          rw [hes] at this
          word
      have Hlast := holds_last S M HSM
      have hk9 : es ≠ [] → k ≤ uint.nat (imgSetHardState M (phsNext hd h)).prev + 1 +
          (imgSetHardState M (phsNext hd h)).ents.length := by
        intro hne
        obtain ⟨e0, he0⟩ : ∃ e0, es.head? = some e0 := by
          cases es with
          | nil => exact absurd rfl hne
          | cons x xs => exact ⟨x, rfl⟩
        have := G9 e0 he0
        rw [Hk e0 he0]; simp only [imgSetHardState]; omega
      have hsz : uint.nat (imgSetHardState M (phsNext hd h)).prev + 1 +
          (imgSetHardState M (phsNext hd h)).ents.length + es.length < 2 ^ 63 := by
        obtain ⟨-, Hp61, Hlen, -⟩ := HMok
        simp only [imgSetHardState]
        cases hes : es with
        | nil => simp only [List.length_nil]; word
        | cons e0 rest =>
          have := Hfit' e0 (by rw [hes]; rfl)
          rw [hes] at this
          simp only [List.length_cons] at this ⊢
          word
      ihave #HmsInv' := HmsInv
      iunfold memStorInvP at HmsInv'
      icases HmsInv' with ⟨#Hlock, -, -⟩
      have Htrip : {{ iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
            memStorLock ρ.ms ρ.γs ∗
            (if es = [] then emp else memLog ρ.γs k (DFrac.own 1) old ∗ memEnd ρ.γs (k + old.length))) ∗
            entsPts rdv.Entries' DFrac.discard es }}
          (App (Val (ρ.ms @!! go.GoType.PointerType MemoryStorage.ty @!! go!"Append")) (Val #rdv.Entries'))
          {{ RET #interface.nil; entsPts rdv.Entries' DFrac.discard es ∗
            (if es = [] then emp else memLog ρ.γs k (DFrac.own 1) es ∗ memEnd ρ.γs (k + es.length)) }} := by
        iintro %Φ ⟨⟨#Hr, #Hl, Hb⟩, He⟩ HΦ
        iapply wp_Append ρ.ms ρ.γs k old es rdv.Entries' DFrac.discard h1 h2 $$ [Hb He]
        · iframe Hr Hl Hb He
        iexact HΦ
      wp_apply wp_SAppend st ρ.ms ρ.γs ip (imgSetHardState M (phsNext hd h)) rdv.Entries' DFrac.discard k
          es _ _ h1 hk9 hsz Htrip $$ [$Hpkg $Hrec $Hst' $Himage $Hes Hrange] as ⟨-, Hb, Himage⟩
      · iframe Hrange Hlock
      imod append_none_post st ρ.ms ρ.γs c D ce es k Hsi.2.2.1 Hin Hidx Hk
        $$ Hrec HfzD Hcef Hb with ⟨#HfzD', Hrcpt⟩
      -- the image after the batch: its shape, the batch's durable state
      have Hhead : es ≠ [] → ∃ e0, es.head? = some e0 := by
        intro hne; cases es with
        | nil => exact absurd rfl hne
        | cons x xs => exact ⟨x, rfl⟩
      have Hc0 : uint.nat M.hs.Commit' ≤ uint.nat (phsNext hd h).Commit' := by rw [Hcmeq]; exact G4
      have G17' : es ≠ [] → uint.nat M.hs.Commit' < k := by
        intro hne; obtain ⟨e0, he0⟩ := Hhead hne; rw [Hk e0 he0, Hcmeq]; exact G17 e0 he0
      have G9' : es ≠ [] → k ≤ S.last + 1 := by
        intro hne; obtain ⟨e0, he0⟩ := Hhead hne; rw [Hk e0 he0]; exact G9 e0 he0
      obtain ⟨Hok3, Hh3⟩ := img_ready_ok M S (phsNext hd h) es k HSM HMok Hc0 h1 G20 (fun _ => h2) G8
        G9' G17'
      -- the frozen bound raised to the delivered log
      have HpC : uint.nat M.prev ≤ uint.nat M.hs.Commit' := by have := HMok.2.2.2.2.2.2.1; word
      have HcL : uint.nat M.hs.Commit' ≤ uint.nat M.prev + M.ents.length := HMok.2.2.2.2.2.2.2
      have Hfz0c : max fz (uint.nat M.prev) ≤ uint.nat M.hs.Commit' := by
        rcases Hfzc with h' | h' <;> omega
      have Htk := imgAppend_take (imgSetHardState M (phsNext hd h)) k es
        (max fz (uint.nat M.prev) - uint.nat M.prev)
        (fun hne => by have := G17' hne; simp only [imgSetHardState]; omega)
        (by simp only [imgSetHardState]; omega)
      have HbS : uint.nat S.base.index' ≤ uint.nat M.prev := by
        have := HSM.1; simp only [kdContents] at this; word
      have Hent := img_frozen_facts (imgAppend (imgSetHardState M (phsNext hd h)) k es)
        (readyDurable S (phsNext hd h) none es) (D ++ ce) (uint.nat M.prev) (max fz (uint.nat M.prev))
        (max fz (uint.nat M.prev)) Hh3 (by simp [imgSetHardState]) (Nat.le_refl _) (by omega) (by
          intro i hi1 hi2
          have hj : i - D.length - 1 < ce.length := by simp only [List.length_append] at hi2; omega
          obtain ⟨x, hx⟩ : ∃ x, ce[i - D.length - 1]? = some x := ⟨_, List.getElem?_eq_getElem hj⟩
          refine ⟨x, ?_, ?_⟩
          · rw [List.getElem?_append_right (by omega), show i - 1 - D.length = i - D.length - 1 by omega]
            exact hx
          · have Hg := G14 (i - D.length - 1) x hx (by rw [readyDurable_base_none]; omega)
            rw [readyDurable_base_none] at Hg ⊢
            rw [show ((D.length : Int) + 1 + ((i - D.length - 1 : Nat) : Int)) = (i : Int) by omega,
              show D.length + (i - D.length - 1) - uint.nat S.base.index' =
                i - 1 - uint.nat S.base.index' by omega] at Hg
            exact Hg)
      ihave #Hfzo : memLog ρ.γs (uint.nat M.prev + 1) DFrac.discard
          (M.ents.take (max fz (uint.nat M.prev) - uint.nat M.prev)) $$ []
      · rw [show max fz (uint.nat M.prev) - uint.nat M.prev = fz - uint.nat M.prev by omega]
        iexact Hfz
      ihave #Hfz3 := frozen_extend ρ.γs (uint.nat M.prev) M.ents
        (imgAppend (imgSetHardState M (phsNext hd h)) k es).ents c (max fz (uint.nat M.prev)) (D ++ ce)
        (by omega) (by omega) Htk Hent $$ [Hfzo HfzD']
      · iframe Hfzo HfzD'
      -- `dmu`'s invariant at the new image; the batch recorded, or entered at once
      have HMc3 : uint.nat M.hs.Commit' ≤
          uint.nat (imgAppend (imgSetHardState M (phsNext hd h)) k es).hs.Commit' := by
        rw [imgAppend_hs]; exact Hc0
      have Hfzc3 : max (max fz (uint.nat M.prev)) (D ++ ce).length ≤
            uint.nat (imgAppend (imgSetHardState M (phsNext hd h)) k es).hs.Commit' ∨
          max (max fz (uint.nat M.prev)) (D ++ ce).length ≤
            uint.nat (imgAppend (imgSetHardState M (phsNext hd h)) k es).prev := by
        left; rw [imgAppend_hs]; simp only [imgSetHardState]; omega
      have His3 : uint.nat M.snap.Metadata'.Index' ≤
          uint.nat (imgAppend (imgSetHardState M (phsNext hd h)) k es).snap.Metadata'.Index' := by
        rw [imgAppend_snap]; exact Nat.le_refl _
      ihave Hcmh : ghostVar ρ.ph.cm (1 : Qp).half M.hs $$ [Hcmh]
      · rw [Hcmeq]; iexact Hcmh
      ihave Hrest : kdDmuRest γ id r ρ.ph crashed S M $$ [Hcr Hwr]
      · iunfold kdDmuRest; iframe Hcr; iexists o; iframe Hwr; ipureintro; exact Hfb
      ihave Hmeta : memStorMeta ρ.ms ρ.γs (imgAppend (imgSetHardState M (phsNext hd h)) k es).hs
        $$ [Hmeta]
      · simp only [imgAppend_hs, imgSetHardState]; iexact Hmeta
      ihave #Hcert3 : kdSnapCert γ (imgAppend (imgSetHardState M (phsNext hd h)) k es).snap $$ []
      · simp only [imgAppend_snap, imgSetHardState]; iexact Hcert
      ihave #Hfz3' : memLog ρ.γs (uint.nat (imgAppend (imgSetHardState M (phsNext hd h)) k es).prev + 1)
          DFrac.discard ((imgAppend (imgSetHardState M (phsNext hd h)) k es).ents.take
            (max (max fz (uint.nat M.prev)) (D ++ ce).length -
              uint.nat (imgAppend (imgSetHardState M (phsNext hd h)) k es).prev)) $$ []
      · simp only [imgAppend_prev, imgSetHardState]; iexact Hfz3
      wp_join iprop(∃ γb : GName, r_ptr ↦ r ∗ nodeRunning n γ.r.cluster kdRaftN (1 : Qp).half ∗
          ghostVar ρ.ph.cm (1 : Qp).half (phsNext hd h) ∗
          monoNatLbOwn ρ.ph.ic (max (max fz (uint.nat M.prev)) (D ++ ce).length) ∗
          (if syncb then iprop(ghostVar ρ.ph.ph (1 : Qp).half (some γb, readyDurable S (phsNext hd h) none es) ∗
              savedPropOwn γb DFrac.discard (kdBatchRes γ id n
                { storage := kdStorIface st, delivered := D ++ ce, hardState := phsNext hd h,
                  handling := some (es, none), key := ρ.key, durable := readyDurable S (phsNext hd h) none es,
                  role := roleAfter role ss } ms))
           else iprop(ghostVar ρ.ph.ph (1 : Qp).half ((none : Option GName), readyDurable S (phsNext hd h) none es) ∗
              kdBatchRes γ id n
                { storage := kdStorIface st, delivered := D ++ ce, hardState := phsNext hd h,
                  handling := some (es, none), key := ρ.key, durable := readyDurable S (phsNext hd h) none es,
                  role := roleAfter role ss } ms)))
        at next with [r Hlc1 Hrest Himage Hmeta Hic His Hcm Hph Hclaim Hcmh Henter Hrun Hlocked]
        as ⟨%γb, r, Hrun, Hcmh, #Hicl', Hphase⟩
      · try wp_auto
        cases syncb
        · -- a commit-only batch: entered at once (its durable state's commit only moves)
          have Hlen0 : rdv.Entries'.len = W64 0 := by
            refine Classical.byContradiction fun hne => ?_
            exact absurd (Hsync.2 (Or.inl hne)) (by simp)
          have Hes0 : es = [] := by
            apply List.eq_nil_of_length_eq_zero
            rw [Hesl.1, Hlen0]; rfl
          have Htv : (phsNext hd h).Term' = S.term ∧ (phsNext hd h).Vote' = S.vote := by
            by_cases hE : h.Term' = W64 0 ∧ h.Vote' = W64 0 ∧ h.Commit' = W64 0
            · rw [phsNext_empty hd h hE]; exact ⟨Htie.1.symm, Htie.2.symm⟩
            · rw [phsNext_ne hd h hE]
              have hn : ¬ (h.Vote' ≠ hd.Vote' ∨ h.Term' ≠ hd.Term') := fun hv =>
                absurd (Hsync.2 (Or.inr ⟨hE, hv⟩)) (by simp)
              simp only [ne_eq, not_or, Decidable.not_not] at hn
              exact ⟨hn.2.trans Htie.1.symm, hn.1.trans Htie.2.symm⟩
          subst Hes0
          imod dmu_close_enter γ dir id r n st ρ.ms ρ.γs ρ.ph crashed ip M
            (imgAppend (imgSetHardState M (phsNext hd h)) k []) fz
            (max (max fz (uint.nat M.prev)) (D ++ ce).length) S
            { storage := kdStorIface st, delivered := D, hardState := hd, handling := none, key := ρ.key,
              durable := S, role := role }
            { storage := kdStorIface st, delivered := D ++ ce, hardState := phsNext hd h,
              handling := some ([], none), key := ρ.key, durable := readyDurable S (phsNext hd h) none [],
              role := roleAfter role ss } ms Hok3 Hh3 rfl HMc3 (by omega) Hfzc3 His3
            (fun σ Hσ Hc => holds_commit_only S σ (phsNext hd h) Hσ Htv.1 Htv.2
              (by rw [imgAppend_hs] at Hc; simpa [imgSetHardState] using Hc))
            $$ [Hlc1 Hrest Himg Himage Hmeta Hic Hfz3' His Hcm Hcert3 Hph Hclaim Hcmh Henter Hrun]
            with ⟨HI, Hclaim, Hres, Hrun, Hcmh, #Hicl'⟩
          · iframe Hlc1 HfInv Hrest Himg Himage Hmeta Hic Hfz3' His Hcm Hcert3 Hph Hclaim Hcmh Henter Hrun
          wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hdmu $Hlocked HI]
          · inext; iexact HI
          wp_join_done
          iexists γ.files
          simp only [imgAppend_hs, imgSetHardState, Bool.false_eq_true, ↓reduceIte]
          iframe
          iexact Hicl'
        · -- a cut batch: recorded, `persist` enters it
          imod dmu_close_cut γ id r n st ρ.ms ρ.γs ρ.ph crashed ip M
            (imgAppend (imgSetHardState M (phsNext hd h)) k es) fz
            (max (max fz (uint.nat M.prev)) (D ++ ce).length) S
            { storage := kdStorIface st, delivered := D, hardState := hd, handling := none, key := ρ.key,
              durable := S, role := role }
            { storage := kdStorIface st, delivered := D ++ ce, hardState := phsNext hd h,
              handling := some (es, none), key := ρ.key, durable := readyDurable S (phsNext hd h) none es,
              role := roleAfter role ss } ms Hok3 Hh3 rfl HMc3 (by omega) Hfzc3
            His3 $$ [Hrest Himg Himage Hmeta Hic Hfz3' His Hcm Hcert3 Hph Hclaim Hcmh Henter]
            with ⟨%γb, HI, Hclaim, #Hsv, Hcmh, #Hicl'⟩
          · iframe Hrest Himg Himage Hmeta Hic Hfz3' His Hcm Hcert3 Hph Hclaim Hcmh Henter
          wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hdmu $Hlocked HI]
          · inext; iexact HI
          wp_join_done
          iexists γb
          simp only [imgAppend_hs, imgSetHardState, ↓reduceIte]
          iframe
          iframe Hicl' Hsv
      clear Htrip Hhead G17' G9' Htk Hent HMc3 Hfzc3 His3
      -- `write`: the batch's, or a commit-only one one time in two
      wp_join iprop(∃ wb : Bool, write_ptr ↦ wb ∗ ⌜syncb = true → wb = true⌝ ∗
          changed_ptr ↦ !decide (h.Term' = W64 0 ∧ h.Vote' = W64 0 ∧ h.Commit' = W64 0) ∗ r_ptr ↦ r) at next
        with [write changed r] as ⟨%wb, write, %Hwb, changed, r⟩
      · cases syncb
        · try wp_auto
          wp_if_destruct
          rotate_left
          · wp_apply wp_oneIn (W64 2) (by decide) $$ [$Hpkg] as %b -
            wp_if_destruct
            rotate_left
            · try wp_auto
              wp_join_done
              iexists true; iframe; ipureintro; intro h'; cases h'
            · ihave #Hcu := isStats_field sts go!"CommitUnwritten" (by decide) $$ Hstats
              try wp_auto
              wp_apply wp_add sts _ $$ [$Hpkg $Hcu]
              try wp_auto
              wp_join_done
              iexists false; iframe; ipureintro; intro h'; cases h'
          · wp_join_done
            iexists false; iframe; ipureintro; intro h'; cases h'
        · try wp_auto
          wp_join_done
          iexists true; iframe; ipureintro; intro _; rfl
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
