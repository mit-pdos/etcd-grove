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

The committed entries are applied in order (`applyEntry`, with a snapshot request at random), the
entries the replicated state covers skipped: after a restart below the snapshot `ap` is ahead of the
delivered log, and the node's configuration stays at `len ap` until the delivered log reaches it (G22:
`applyEntry` takes the view only for an entry it does not cover; `runInv`'s view). Then `answer`,
`Advance` (its stopped answer refuted by `run`'s `nodeRunning`) and a request with raft's applied
index as the compaction bound at random. A snapshot `Ready`: its data decodes (`kd_snap_recv`), both
storages take it under `dmu` (the image does not refuse it: G7), its batch is cut (always written),
the replicated state takes it (`install`), and `Advance` gives the node's configuration at it: the
invariant at the snapshot's log, compacted and frozen at its index.

raft's facts on a `Ready` are its `readyRest` laws (G4, G7-G10, G14, G17, G20, G21; G7's in the hard
state's commit index, the image's: `img_snap_fresh_hs`). (G23: `MemoryStorage.ApplySnapshot`'s
`memSnapLb γs 0` is `isReplicaR`'s `#HsnLb`.)
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
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetIndex
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

/-! ## raft's facts on a `Ready`

raft's `readyRest` laws (`InvNode.lean`: `readyRest_commit_mono` (G4), `_snap` (G7), `_commit_le_last`
(G8), `_ents_start` (G9), `_delivered_le_commit` (G10), `_durable_has_delivered` (G14),
`_ents_above_commit` (G17), `readyRest_ents_type` (G20's type half), `softStateIs_ne_null` (G21)). -/

/-- An entry slice's entries have data of a Go slice's length. -/
private theorem entsRO_data_len (s : GoSlice) (es : List EntryM) :
    entsRO (GF := GF) s es ⊢ ⌜∀ e ∈ es, (e.Data'.length : Int) < 2 ^ 63⌝ := by
  have key : ∀ (l : Loc) (e : EntryM), entRO (GF := GF) l e ⊢ ⌜(e.Data'.length : Int) < 2 ^ 63⌝ := by
    intro l e
    unfold entRO entPts
    iintro H
    iNamed H
    ihave %h := ownSlice_len $$ Hd
    ipureintro; word
  unfold entsRO entsPts
  iintro H
  icases H with ⟨%ls, -, Hb⟩
  ihave %Hp := (BigSepL2.bigSepL2_mono_of_forall (fun {_ x1 x2} => key x1 x2)).trans
    BigSepL2.bigSepL2_pure_intro $$ Hb
  ihave %Hl := entsBig_length $$ Hb
  ipureintro
  intro e he
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem he
  exact Hp k ls[k] es[k] (List.getElem?_eq_getElem (by omega)) (List.getElem?_eq_getElem hk)

/-- (G20) A `Ready`'s entries decode back from the file (`EntWf`: a type of raft's, `EntryNormal`,
`EntryConfChange` or `EntryConfChangeV2` (raft's `readyRest_ents_type`), and data of a Go slice's
length (`entsRO`)). -/
private theorem ready_ents_wf_G20 (γc : Cluster) (N : Namespace) (id : w64) (rd : Ready) (st : NodeDriverState)
    (ce : List LogEntry) (es : List EntryM) (h : HardStateM) (L : Option SnapLoan) (ms : List QMsg)
    (ss : Option (w64 × StateType)) :
    readyRest (GF := GF) γc N id rd st ce es h L ms ss ⊢ readyRest γc N id rd st ce es h L ms ss ∗
      ⌜∀ e ∈ es, EntWf e⌝ := by
  iintro H
  icases readyRest_ents_type γc N id rd st ce es h L ms ss $$ H with ⟨H, %Hty⟩
  ihave #Hes : entsRO rd.Entries' es $$ [H]
  · iunfold readyRest at H
    icases H with ⟨#Hes, -⟩
    iexact Hes
  ihave %Hd := entsRO_data_len _ _ $$ Hes
  iframe H
  ipureintro
  intro e he
  exact ⟨Hty e he, Hd e he⟩

/-- The applier's view at `i` from the node's configuration at `i` (nothing to skip). -/
private theorem appNode_at (γr : KdNames) (n : Loc) (L : List LogEntry) (i : Nat) (m : Membership) :
    nodeConfig (GF := GF) n γr.r.cluster kdRaftN ⟨i, m⟩ ∗ deliveredLogLb n γr.r.cluster kdRaftN L ⊢
      appNode γr n L i m := by
  iintro ⟨Hc, #Hd⟩
  unfold appNode
  iexists ⟨i, m⟩
  iframe Hc Hd
  isplitl []
  · iapply skippedIn_noConf
    intro j e h1 h2; simp only at h1 h2; omega
  · ipureintro; exact ⟨rfl, Nat.le_refl _⟩

/-- The persistent facts of the replicated state: committed, its configuration, its bound. -/
private theorem repOwn_facts (γ : KdNames) (r : Loc) (ap : List LogEntry) (idx : w64) (csp : Loc)
    (m : Membership) (mA : Loc) (A : GMap (List w8) (List w8)) :
    repOwn (GF := GF) γ r ap idx csp m mA A ⊢ repOwn γ r ap idx csp m mA A ∗
      (isCommittedLogLb γ.r.cluster ap ∗ confAt γ.r.cluster ap.length m ∗
        ⌜(ap.length : Int) < 2 ^ 61⌝) := by
  iintro Hown
  iunfold repOwn at Hown
  iNamed Hown
  iframe Hap Hcfg
  isplitl
  · unfold repOwn
    iexists mK, K, c
    iframe
    iframe Hap HcsO Hcfg
    ipureintro; exact ⟨Hlen, Hval, HA, Hcsm, Hsz⟩
  · ipureintro; exact Hlen

/-- A snapshot raft hands out reads back from the file (`SnapWf`: its conf state's and data's
lengths are a Go slice's). -/
private theorem ownSnapS_wf (p : Loc) (dq : DFrac) (sv : SnapshotM) :
    ownSnapS (GF := GF) p dq sv ⊢ ⌜SnapWf sv⌝ := by
  iintro H
  iNamed H
  iNamed Hm
  ihave %Hd' := ownSlice_len $$ Hd
  iunfold csSet at Hc
  icases Hc with (Hc | Hc)
  all_goals
    iNamed Hc
    ihave %H1 := ownSlice_len $$ Hv
    ihave %H2 := ownSlice_len $$ Hl
    ihave %H3 := ownSlice_len $$ Ho
    ihave %H4 := ownSlice_len $$ Hn
    ipureintro
    unfold SnapWf ConfWf
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> word

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
    (wp_EGetIndex : raftpb.Entry.GetIndex.spec (GF := GF) (hG := hG))
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
  ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
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
    ihave ⟨%Hidx, Hrest⟩ := readyRest_indices _ _ _ _ _ _ _ _ _ _ $$ Hrest
    ihave ⟨Hrest, %G4⟩ := readyRest_commit_mono _ _ _ _ _ _ _ _ _ _ _ $$ Hrest
    ihave ⟨Hrest, %G8⟩ := readyRest_commit_le_last _ _ _ _ _ _ _ _ _ _ _ $$ Hrest
    ihave ⟨Hrest, %G20⟩ := ready_ents_wf_G20 _ _ _ _ _ _ _ _ _ _ _ $$ Hrest
    simp only at Hidx G4 G8 G20
    try wp_auto
    cases L with
    | none =>
      ihave ⟨Hrest, %G9⟩ := readyRest_ents_start _ _ _ _ _ _ _ _ _ _ $$ Hrest
      ihave ⟨Hrest, %G10⟩ := readyRest_delivered_le_commit _ _ _ _ _ _ _ _ _ _ $$ Hrest
      ihave ⟨Hrest, %G14⟩ := readyRest_durable_has_delivered _ _ _ _ _ _ _ _ _ _ $$ Hrest
      ihave ⟨Hrest, %G17⟩ := readyRest_ents_above_commit _ _ _ _ _ _ _ _ _ _ $$ Hrest
      ihave ⟨%Hin, Hrest⟩ := readyRest_ceInBatch _ _ _ _ _ _ _ _ _ $$ Hrest
      simp only at G9 G10 G14 G17 Hin
      iunfold readyRest at Hrest
      icases Hrest with ⟨#Hes, Hmsl, Hmsok, #Hhs, #Hss, %Hbnd, Hsnap, -⟩
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
          ihave %Hnn := softStateIs_ne_null _ _ $$ Hss
          iunfold softStateIs at Hss
          icases Hss with ⟨-, #Hld, #Hrs⟩
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
      have HcL : uint.nat M.hs.Commit' ≤ uint.nat M.prev + M.ents.length := HMok.2.2.2.2.2.2.2.1
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
      -- `first`: at role leader, a cut batch's messages sent before the write one time in two
      wp_join (Q := fun v => iprop(⌜∃ fb : Bool, v = #fb ∧ (fb = true → syncb = true ∧ lead' = true)⌝ ∗
          lead_ptr ↦ lead' ∗ sync_ptr ↦ syncb)) at (if: _ then _ else _) with [lead sync]
        as ⟨%Hfv, lead, sync⟩
      · cases lead' <;> cases syncb
        all_goals try wp_auto
        all_goals first
          | (iframe; ipureintro; exact ⟨false, rfl, fun h' => by cases h'⟩)
          | (wp_apply wp_oneIn (W64 2) (by decide) $$ [$Hpkg] as %b -
             iframe; ipureintro; exact ⟨b, rfl, fun _ => ⟨rfl, rfl⟩⟩)
      obtain ⟨fb, rfl, Hfb⟩ := Hfv
      try wp_auto
      -- sent first: at role leader (`readyLeaderMsgs`)
      wp_join iprop((⌜fb = true⌝ ∨ (rdv.Messages' ↦* List.map QMsg.loc ms ∗
            [∗list] q ∈ ms, iprop(msgOwn q.loc (readyDq q.st) q.st ∗ msgCredits γ.r.cluster kdRaftN q.st))) ∗
          r_ptr ↦ r ∗ rd_ptr ↦ rdv ∗ send_ptr ↦ f) at next with [Hmsl Hmsok Hlm r rd send]
        as ⟨Hmq, r, rd, send⟩
      · cases fb
        · try wp_auto
          wp_join_done
          iframe
          iright
          iframe
        · obtain ⟨-, Hl⟩ := Hfb rfl
          have Hrole := Hlead' Hl
          iunfold readyLeaderMsgs at Hlm
          ihave #Hmsgs := Hlm $$ %Hrole
          ihave #Hlsf := isStats_field sts go!"LeaderSentFirst" (by decide) $$ Hstats
          try wp_auto
          wp_apply wp_add sts _ $$ [$Hpkg $Hlsf]
          try wp_auto
          wp_bind (App (Val #f) _)
          iunfold sendSpec at Hsend
          iapply Hsend $$ [Hmsl Hmsok]
          · iframe Hpkg Hmsl
            iapply kd_readyMsgs_sent $$ [$Hmsok $Hmsgs]
          iintro !> -
          try wp_auto
          wp_join_done
          iframe
          ileft; ipureintro; rfl
      -- the write: `persist` enters a cut batch; a failed write (crashed) ends the loop
      wp_join (Q := fun v => iprop((⌜v = executeVal⌝ ∗ nodeRunning n γ.r.cluster kdRaftN (1 : Qp).half ∗
            ghostVar ρ.ph.ph (1 : Qp).half ((none : Option GName), readyDurable S (phsNext hd h) none es) ∗
            kdBatchRes γ id n (
                { storage := kdStorIface st, delivered := D ++ ce, hardState := phsNext hd h, handling := some (es, none), key := ρ.key, durable := readyDurable S (phsNext hd h) none es, role := roleAfter role ss } : NodeDriverState) ms ∗
            r_ptr ↦ r ∗ handoffProducer ρ.rd false) ∨ ⌜v = returnVal #()⌝))
        at next with [Hrun Hphase r Hprod]
      · cases wb
        · have hs : syncb = false := by
            cases syncb
            · rfl
            · exact absurd (Hwb rfl) (by simp)
          subst hs
          simp only [Bool.false_eq_true, ↓reduceIte]
          icases Hphase with ⟨Hclaim, Hres⟩
          try wp_auto
          ileft; iframe; ipureintro; rfl
        · cases syncb
          · simp only [Bool.false_eq_true, ↓reduceIte]
            icases Hphase with ⟨Hclaim, Hres⟩
            try wp_auto
            wp_apply wp_persist γ vs dir id r n st sts sq ρ.ms ρ.γs ρ.ph (1 : Qp).half $$ [$Hrep $Hrun]
              as %ok Hrun
            cases ok
            · try wp_auto
              wp_apply wp_handoff_send ρ.rd ρ.rdc (fun _ => iprop(nodeRunning n γ.r.cluster kdRaftN (1 : Qp).half ∗
                  ∃ v : Option GName × RaftState, ghostVar ρ.ph.ph (1 : Qp).half v)) iprop(True)
                iprop(False) () $$ [$HrdH $Hprod Hrun Hclaim] as -
              · isplitl [Hrun Hclaim]
                · iframe Hrun; iexists _; iexact Hclaim
                · itrivial
              try wp_auto
              iright; ipureintro; rfl
            · try wp_auto
              ileft; iframe; ipureintro; rfl
          · simp only [↓reduceIte]
            icases Hphase with ⟨Hclaim, #Hsv⟩
            try wp_auto
            wp_apply wp_persistRun γ vs dir id r n st sts sq ρ.ms ρ.γs ρ.ph (1 : Qp).half (
                { storage := kdStorIface st, delivered := D ++ ce, hardState := phsNext hd h, handling := some (es, none), key := ρ.key, durable := readyDurable S (phsNext hd h) none es, role := roleAfter role ss } : NodeDriverState) ms γb
              $$ [$Hrep $Hrun $Hclaim $Hsv] as %ok ⟨Hrun, Hpost⟩
            cases ok
            · simp only [Bool.false_eq_true, ↓reduceIte]
              irename Hpost => Hclaim
              try wp_auto
              wp_apply wp_handoff_send ρ.rd ρ.rdc (fun _ => iprop(nodeRunning n γ.r.cluster kdRaftN (1 : Qp).half ∗
                  ∃ v : Option GName × RaftState, ghostVar ρ.ph.ph (1 : Qp).half v)) iprop(True)
                iprop(False) () $$ [$HrdH $Hprod Hrun Hclaim] as -
              · isplitl [Hrun Hclaim]
                · iframe Hrun; iexists _; iexact Hclaim
                · itrivial
              try wp_auto
              iright; ipureintro; rfl
            · simp only [↓reduceIte]
              icases Hpost with ⟨Hclaim, Hres⟩
              try wp_auto
              ileft; iframe; ipureintro; rfl
      iintro Hq
      icases Hq with (⟨%Hv, Hrun, Hclaim, Hres, r, Hprod⟩ | %Hv)
      rotate_left
      · subst Hv
        try wp_auto
        wp_for_post
        try wp_auto
        iapply HΦ
        itrivial
      subst Hv
      iunfold kdBatchRes at Hres
      icases Hres with ⟨Hdrv, #Hmsgs⟩
      try wp_auto
      -- sent after the write
      wp_join iprop(r_ptr ↦ r ∗ rd_ptr ↦ rdv ∗ send_ptr ↦ f) at next with [Hmq r rd send]
        as ⟨r, rd, send⟩
      · cases fb
        · icases Hmq with (%h' | ⟨Hmsl, Hmsok⟩)
          · cases h'
          try wp_auto
          wp_bind (App (Val #f) _)
          iunfold sendSpec at Hsend
          iapply Hsend $$ [Hmsl Hmsok]
          · iframe Hpkg Hmsl
            iapply kd_readyMsgs_sent $$ [$Hmsok $Hmsgs]
          iintro !> -
          try wp_auto
          wp_join_done
        · try wp_auto
          wp_join_done
      -- the read states, noted
      icases Hrs with ⟨%rsts, #Hsts, #Hstsok⟩
      ihave Hvs := kd_readStatesPts_rsOk γ.r.cluster rdv.ReadStates' rsts $$ [Hsts Hstsok]
      · iframe Hsts Hstsok
      icases Hvs with ⟨%vls, #Hvls, #Hvlsok⟩
      try wp_auto
      wp_apply wp_slice_append $$ [$Hpv $Hpcap $Hvls] as %pv' ⟨Hpv, Hpcap, -⟩
      ihave #Hps' : iprop([∗list] v ∈ ps ++ vls, rsOk γ.r.cluster v) $$ []
      · iapply (BigSepL.bigSepL_append (Φ := fun _ v => rsOk (GF := GF) γ.r.cluster v)).2
        iframe Hps Hvlsok
      iclear Hps
      -- applying the committed entries, in order (those the replicated state covers skipped)
      iunfold committedEntriesAt at Hce
      icases entsPts_elim _ _ _ $$ Hce with ⟨%cls, #Hcel, #Hceb⟩
      ihave %Hcelen := ownSlice_len $$ Hcel
      ihave %Hcebl := entsBig_length $$ Hceb
      rw [kvreconf.kvr_toEntries_length] at Hcebl
      ihave ⟨Hdrv, #Hdl⟩ := nodeDriver_deliveredLogLb _ _ _ _ $$ Hdrv
      icases nodeDriver_nodeCommitLb _ _ _ _ $$ Hdrv with ⟨Hdrv, #HclD⟩
      ihave %Hlen61 := kd_frozenTo_len _ _ _ $$ HfzD'
      ihave #HfzM := HfzD'
      iunfold kvreconf.frozenTo at HfzM
      try wp_auto
      -- the view at `D ++ ce`: the node's configuration stays at `len ap` while `ap` is ahead
      ihave ⟨%HDap, Hview⟩ : iprop(⌜D.length ≤ ap.length⌝ ∗
          ((⌜D.length + sint.nat (W64 0) = ap.length⌝ ∗ appNode γ n (D ++ ce) ap.length m) ∨
          (⌜D.length + sint.nat (W64 0) < ap.length⌝ ∗
            nodeConfig n γ.r.cluster kdRaftN ⟨ap.length, m⟩))) $$ [Hview]
      · icases Hview with (⟨%Heq, Hv⟩ | ⟨%Hlt, Hc, -⟩)
        · isplitr
          · ipureintro; omega
          ileft
          isplitr
          · ipureintro; simp only [show sint.nat (W64 0) = 0 from rfl]; omega
          rw [← Heq]
          iapply appNode_extend γ n D (D ++ ce) D.length m (List.prefix_append _ _) (Nat.le_refl _)
            $$ [$Hv $Hdl]
        · isplitr
          · ipureintro; omega
          iright
          iframe Hc
          ipureintro; simp only [show sint.nat (W64 0) = 0 from rfl]; omega
      ihave IH : iprop(∃ (k : w64) (ev : Loc) (si rf : w64) (ap' : List LogEntry) (csp' : Loc)
          (m' : Membership) (A' : GMap (List w8) (List w8)),
          "i" ∷ i_ptr ↦ k ∗ "e" ∷ e_ptr ↦ ev ∗ "r" ∷ r_ptr ↦ r ∗ "snapIndex" ∷ snapIndex_ptr ↦ si ∗
          "rafted" ∷ rafted_ptr ↦ rf ∗
          "Hown" ∷ repOwn γ r ap' (W64 ap'.length) csp' m' mA A' ∗
          "Hview" ∷ ((⌜D.length + sint.nat k = ap'.length⌝ ∗ appNode γ n (D ++ ce) ap'.length m') ∨
            (⌜D.length + sint.nat k < ap'.length⌝ ∗ nodeConfig n γ.r.cluster kdRaftN ⟨ap'.length, m'⟩)) ∗
          "Hrun" ∷ nodeRunning n γ.r.cluster kdRaftN (1 : Qp).half ∗
          "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ (ce.length : Int) ∧ c ≤ uint.nat si ∧
            uint.nat rf = D.length + sint.nat k ∧ D.length + sint.nat k ≤ ap'.length ∧
            (ap'.length ≤ uint.nat si ∨ ap'.length ≤ D.length + sint.nat k)⌝)
        $$ [i e r snapIndex rafted Hown Hview Hrun]
      · iexists W64 0, _, snapIndex, rafted, ap, csp, m, A
        iframe
        ipureintro
        simp only [show sint.nat (W64 0) = 0 from rfl, Nat.add_zero]
        exact ⟨by word, by word, Hsi.2.1, Hsi.2.2.2.1, HDap, Hsi.2.2.2.2⟩
      wp_for IH
      wp_if_destruct
      · have Hlt : sint.nat k < ce.length := by rw [← Hcebl, Hcelen.1]; have := Hk.1; word
        obtain ⟨en, Hen⟩ : ∃ en, ce[sint.nat k]? = some en := ⟨_, List.getElem?_eq_getElem Hlt⟩
        have HD'len : D.length + sint.nat k < (D ++ ce).length := by
          simp only [List.length_append]; omega
        have H61 : (D ++ ce).length < 2 ^ 61 := Hlen61 (by have := Hsi.2.2.1; omega)
        have Hget : (LogEntry.toEntries ce D.length)[sint.nat k]? =
            some (en.toEntryM (W64 (((D.length + sint.nat k : Nat) : Int) + 1))) := by
          rw [kvreconf.kvr_toEntries_get _ _ _ _ Hen]; push_cast; rfl
        ihave ⟨%ln, %Hln, #Hent⟩ := entsBig_lookup cls _ (sint.nat k) _ Hget $$ Hceb
        simp only [show 0 ≤ sint.Z k ∧ sint.Z k < sint.Z rdv.CommittedEntries'.len from ⟨Hk.1, Hif⟩,
          _root_.and_self, ↓reduceIte]
        wp_apply wp_load_slice_index rdv.CommittedEntries' (sint.Z k) _ DFrac.discard ln Hk.1 $$ [Hcel] as -
        · iframe Hcel; ipureintro; rw [show (sint.Z k).toNat = sint.nat k by word]; exact Hln
        have Htk : ce.take (sint.nat k + 1) = ce.take (sint.nat k) ++ [en] := by
          rw [List.take_add_one, Hen]; rfl
        have Hpre : (D ++ ce).take (D.length + sint.nat k) ++ [en] <+: D ++ ce := by
          rw [List.take_length_add_append, List.append_assoc, ← Htk]
          exact (List.prefix_append_right_inj _).mpr (List.take_prefix _ _)
        ihave ⟨Hown, #Hap', #Hcfg', %Hapl⟩ := repOwn_facts γ r ap' _ csp' m' mA A' $$ Hown
        ihave %Hag := isCommittedLogLb_agree γ.r.cluster ap' (D ++ ce) $$ [$Hap' $Hcomm]
        have Hcov : D.length + sint.nat k < ap'.length ∨ ap' <+: D ++ ce := by
          by_cases hc : D.length + sint.nat k < ap'.length
          · exact .inl hc
          · right; rcases Hag with h' | h'
            · exact h'
            · have := h'.length_le; omega
        ihave ⟨Hvpre, Hvcfg⟩ : iprop((if D.length + sint.nat k < ap'.length then emp
              else appNode γ n (D ++ ce) ap'.length m') ∗
            (if D.length + sint.nat k < ap'.length then nodeConfig n γ.r.cluster kdRaftN ⟨ap'.length, m'⟩
              else emp)) $$ [Hview]
        · by_cases hc : D.length + sint.nat k < ap'.length
          · simp only [hc, ↓reduceIte]
            icases Hview with (⟨%Heq, -⟩ | ⟨-, Hc⟩)
            · exfalso; omega
            · iframe Hc
          · simp only [hc, ↓reduceIte]
            icases Hview with (⟨-, Hv⟩ | ⟨%Hlt', -⟩)
            · iframe Hv
            · exfalso; omega
        wp_apply wp_applyEntry γ vs dir id r n st sts sq ρ.ms ρ.γs ρ.ph (1 : Qp).half ap' _ csp' m' mA A'
            (D ++ ce) (D.length + sint.nat k) en ln Hpre Hcov (by push_cast; omega) (by word)
            Hk.2.2.2.2.1
          $$ [$Hrep $Hown $Hvpre $Hent $Hcomm $Hrun] as ⟨%ap2, %csp2, %m2, %A2, %Hap2, Hown, Hvpost, Hrun⟩
        have Hap2f : D.length + sint.nat k + 1 ≤ ap2.length ∧
            (ap2.length ≤ uint.nat si ∨ ap2.length ≤ D.length + sint.nat k + 1) := by
          by_cases hc : D.length + sint.nat k < ap'.length
          · simp only [hc, ↓reduceIte] at Hap2; subst ap2; have := Hk.2.2.2.2.2; omega
          · simp only [hc, ↓reduceIte] at Hap2; subst ap2; simp only [List.length_append, List.length_singleton]
            have := Hk.2.2.2.2.1; omega
        ihave ⟨Hown, #Hap2', #Hcfg2, %Hap2l⟩ := repOwn_facts γ r ap2 _ csp2 m2 mA A2 $$ Hown
        ihave Hview2 : iprop((⌜D.length + (sint.nat k + 1) = ap2.length⌝ ∗
              appNode γ n (D ++ ce) ap2.length m2) ∨
            (⌜D.length + (sint.nat k + 1) < ap2.length⌝ ∗
              nodeConfig n γ.r.cluster kdRaftN ⟨ap2.length, m2⟩)) $$ [Hvpost Hvcfg]
        · by_cases hc : D.length + sint.nat k < ap'.length
          · simp only [hc, ↓reduceIte] at Hap2; subst ap2
            simp only [hc, ↓reduceIte]
            ihave %Hm := confAt_agree γ.r.cluster _ m' m2 $$ [$Hcfg' $Hcfg2]
            subst Hm
            rcases Nat.lt_or_ge (D.length + sint.nat k + 1) ap'.length with h' | h'
            · iright; iframe Hvcfg; ipureintro; omega
            · ileft
              isplitr
              · ipureintro; omega
              iapply appNode_at γ n (D ++ ce) ap'.length m' $$ [$Hvcfg $Hdl]
          · simp only [hc, ↓reduceIte] at Hap2; subst ap2
            simp only [hc, ↓reduceIte]
            ileft
            isplitr
            · ipureintro; simp only [List.length_append, List.length_singleton]; omega
            iexact Hvpost
        ihave %Hag2 := isCommittedLogLb_agree γ.r.cluster ap2 (D ++ ce) $$ [$Hap2' $Hcomm]
        have Hpre2 : uint.nat si < ap2.length → ap2 <+: D ++ ce := by
          intro hs
          rcases Hag2 with h' | h'
          · exact h'
          · have := h'.length_le
            have hl : (D ++ ce).length = ap2.length := by have := Hap2f.2; omega
            rw [← h'.eq_of_length hl]
            exact List.prefix_refl _
        have Hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
        try wp_auto
        wp_apply wp_EGetIndex.1 ln DFrac.discard _ $$ [$Hpb $Hent] as -
        try simp only [LogEntry.toEntryM]
        try wp_auto
        wp_apply wp_oneIn (W64 8) (by decide) $$ [$Hpkg] as %b -
        wp_if_destruct
        · wp_for_post
          iframe
          iexists k + W64 1, ln, si, W64 (((D.length + sint.nat k : Nat) : Int) + 1), ap2, csp2, m2, A2
          rw [Hk1]
          iframe
          ipureintro
          refine ⟨by word, by word, Hk.2.2.1, by word, by omega, by omega⟩
        · ihave Hicp : iprop(⌜ap2.length ≤ uint.nat si⌝ ∨ monoNatLbOwn ρ.ph.ic ap2.length) $$ []
          · rcases Nat.lt_or_ge (uint.nat si) ap2.length with h' | h'
            · iright
              iapply monoNatLbOwn_le ap2.length (by have := (Hpre2 h').length_le; omega) $$ Hicl'
            · ileft; ipureintro; exact h'
          wp_apply wp_request γ vs dir id r n st sts sq ρ ap2 csp2 m2 mA A2 (D ++ ce) c si (W64 0) true
              Hpre2 Hk.2.2.1 (by simp)
            $$ [$Hrr $Hown $Hcp $HfzM $Hdl $HclD Hicp] as %ret ⟨Hown, %Hsv1⟩
          · iframe Hicp; ileft; ipureintro; rfl
          wp_for_post
          iframe
          iexists k + W64 1, ln, ret, W64 (((D.length + sint.nat k : Nat) : Int) + 1), ap2, csp2, m2, A2
          rw [Hk1]
          iframe
          ipureintro
          refine ⟨by word, by word, ?_, by word, by omega, ?_⟩
          · rcases Hsv1 with h' | ⟨h', h''⟩
            · rw [h']; exact Hk.2.2.1
            · rw [h']; have := Hk.2.2.1; word
          · rcases Hsv1 with h' | ⟨h', h''⟩
            · rw [h']; omega
            · left; rw [h']; word
      · have Hfull : sint.nat k = ce.length := by
          rw [← Hcebl, Hcelen.1]; have := Hk.2.1; have := Hk.1; word
        obtain ⟨-, -, Hc1, Hrf, HDk, Hdisj⟩ := Hk
        rw [Hfull] at Hrf HDk Hdisj
        have HDce : (D ++ ce).length = D.length + ce.length := List.length_append
        ihave ⟨Hown, #Hap', #Hcfg', %Hapl⟩ := repOwn_facts γ r ap' _ csp' m' mA A' $$ Hown
        ihave %Hag := isCommittedLogLb_agree γ.r.cluster ap' (D ++ ce) $$ [$Hap' $Hcomm]
        wp_apply wp_answer γ vs dir id r n st sts sq ρ.ms ρ.γs ρ.ph ap' _ csp' m' mA A' pv' (ps ++ vls)
            (DFrac.own 1) (by word) $$ [$Hrep $Hown $Hpv $Hps'] as %rest ⟨Hown, %ps', Hrest, Hcap2, #Hps2⟩
        -- `r.node.Advance()`: the view opened (nothing skipped while `ap` is ahead)
        ihave #HkC' := HkC
        iunfold kdCluster at HkC'
        icases HkC' with ⟨#Hic, -⟩
        ihave ⟨%v, Hcfg, #Hsk, Hback⟩ : iprop(∃ v : ConfigView, nodeConfig n γ.r.cluster kdRaftN v ∗
            skippedIn γ.r.cluster (D ++ ce) v.applied (D ++ ce).length ∗
            (nodeConfig n γ.r.cluster kdRaftN v -∗
              ((⌜(D ++ ce).length = ap'.length⌝ ∗ appNode γ n (D ++ ce) (D ++ ce).length m') ∨
               (⌜(D ++ ce).length < ap'.length⌝ ∗ nodeConfig n γ.r.cluster kdRaftN ⟨ap'.length, m'⟩ ∗
                 deliveredLogLb n γ.r.cluster kdRaftN (D ++ ce))))) $$ [Hview]
        · rw [Hfull]
          icases Hview with (⟨%Heq, Hv⟩ | ⟨%Hlt, Hc⟩)
          · rw [show (D ++ ce).length = ap'.length by omega]
            icases appNode_open γ n (D ++ ce) ap'.length m' $$ Hv with ⟨%v, Hcfg, #Hsk, Hback⟩
            iexists v
            iframe Hcfg Hsk
            iintro Hc
            ileft
            isplitr
            · ipureintro; rfl
            iapply Hback $$ Hc
          · iexists ⟨ap'.length, m'⟩
            iframe Hc
            isplitr
            · iapply skippedIn_noConf
              intro j e h1 h2; simp only at h1; omega
            iintro Hc
            iright
            iframe Hc Hdl
            ipureintro; omega
        wp_apply wp_Advance n γ.r.cluster kdRaftN id _ es none v rfl (fun _ h => by cases h)
          $$ [$HrP $Hic $HisNode $Hdrv $Hrcpt $Hcfg $Hsk] as Hadv
        icases Hadv with (⟨Hdrv, #Hal', Hcfg⟩ | ⟨#Hstop, -⟩)
        rotate_left
        · iexfalso
          iapply nodeRunning_stopped n γ.r.cluster kdRaftN _ $$ [$Hrun $Hstop]
        ihave Hview := Hback $$ Hcfg
        -- `snapIndex = r.request(snapIndex, oneIn(4), bound)`, `bound` raft's applied index or `0`
        try wp_auto
        wp_apply wp_oneIn (W64 4) (by decide) $$ [$Hpkg] as %b1 -
        wp_join iprop(∃ bnd : w64, bound_ptr ↦ bnd ∗ rafted_ptr ↦ rf ∗ ⌜bnd = W64 0 ∨ bnd = rf⌝)
          at next with [bound rafted] as ⟨%bnd, bound, rafted, %Hbnd'⟩
        · wp_if_destruct
          · try wp_auto
            wp_join_done
            iexists _; iframe; ipureintro; first | (left; rfl) | (right; rfl)
          · wp_join_done
            iexists _; iframe; ipureintro; first | (left; rfl) | (right; rfl)
        try wp_auto
        wp_apply wp_oneIn (W64 4) (by decide) $$ [$Hpkg] as %b2 -
        have Hpre2 : uint.nat si < ap'.length → ap' <+: D ++ ce := by
          intro hs
          rcases Hag with h' | h'
          · exact h'
          · have := h'.length_le
            have hl : (D ++ ce).length = ap'.length := by omega
            rw [← h'.eq_of_length hl]
            exact List.prefix_refl _
        ihave Hicp : iprop(⌜ap'.length ≤ uint.nat si⌝ ∨ monoNatLbOwn ρ.ph.ic ap'.length) $$ []
        · rcases Nat.lt_or_ge (uint.nat si) ap'.length with h' | h'
          · iright
            iapply monoNatLbOwn_le ap'.length (by have := (Hpre2 h').length_le; omega) $$ Hicl'
          · ileft; ipureintro; exact h'
        ihave Hbndp : iprop(⌜bnd = W64 0⌝ ∨ nodeAppliedLb γ.r.cluster ρ.key (uint.nat bnd)) $$ []
        · rcases Hbnd' with h' | h'
          · ileft; ipureintro; exact h'
          · iright; rw [h', Hrf, ← HDce]; iexact Hal'
        have Hble : uint.nat bnd ≤ (D ++ ce).length := by
          rcases Hbnd' with h' | h'
          · rw [h']; simp
          · rw [h', Hrf]; omega
        wp_apply wp_request γ vs dir id r n st sts sq ρ ap' csp' m' mA A' (D ++ ce) c si bnd b2
            Hpre2 Hc1 Hble
          $$ [$Hrr $Hown $Hcp $HfzM $Hdl $HclD Hicp Hbndp] as %ret ⟨Hown, %Hsv1⟩
        · iframe Hicp Hbndp
        -- the loop's invariant, at `D ++ ce`
        ihave #Hicl2 : monoNatLbOwn ρ.ph.ic (D ++ ce).length $$ []
        · iapply monoNatLbOwn_le (D ++ ce).length (by omega) $$ Hicl'
        wp_for_post
        iframe
        unfold runInv
        iexists D ++ ce, phsNext hd h, readyDurable S (phsNext hd h) none es, roleAfter role ss, ap', csp',
          mA, m', A', ret, rf, c, rest, ps', lead', hsp'
        iframe
        iframe Hcp HfzD' HhsO' Hps2 Hicl2
        ipureintro
        obtain ⟨Ht, Hv, -⟩ := readyDurable_tv S (phsNext hd h) none es
        refine ⟨⟨Ht, Hv⟩, Hlead', ?_, by omega, by omega, ?_⟩
        · rcases Hsv1 with h' | ⟨h', h''⟩
          · rw [h']; exact Hc1
          · rw [h']; word
        · rcases Hsv1 with h' | ⟨h', h''⟩
          · rw [h']; omega
          · left; rw [h']; word
    | some lo =>
      ihave ⟨Hrest, %G7⟩ := readyRest_snap _ _ _ _ _ _ _ _ _ _ _ $$ Hrest
      simp only at G7
      iunfold readyRest at Hrest
      icases Hrest with ⟨#Hes, Hmsl, Hmsok, #Hhs, #Hss, %Hbnd, Hsnap, -⟩
      iunfold readySnap at Hsnap
      icases Hsnap with ⟨%Hl, Hss4, #HcL, #Hcert, ⟨%k, %old, %Hk, Hlog, Hend⟩, #Hgiven, #HclS, -, -⟩
      obtain ⟨Hdlv, Hptr, Hce0, Hpre, Hlt, Hdlen, Hpos, H61, -, Hli⟩ := Hl
      subst Hce0
      ihave ⟨Hss4, %Hsw⟩ := persistent_entails_left (ownSnapS_wf _ _ _) $$ Hss4
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
          ihave %Hnn := softStateIs_ne_null _ _ $$ Hss
          iunfold softStateIs at Hss
          icases Hss with ⟨-, #Hld, #Hrs⟩
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
      have Hne : lo.snap.Metadata'.Index' ≠ W64 0 := by intro h; rw [h] at Hpos; simp at Hpos
      have Hslen : (strip lo.dlv).length = uint.nat lo.snap.Metadata'.Index' := by
        unfold strip; rw [List.length_map]; exact Hdlen
      -- the snapshot: a quarter for the reads, a quarter for `ApplySnapshot`
      icases ownSnapS_split lo.ptr (DFrac.own (Qp.half (Qp.half 1))) (DFrac.own (Qp.half (Qp.half 1)))
        lo.snap $$ [Hss4] with ⟨Hs1, Hs2⟩
      · rw [← dfrac_own_half_half]; iexact Hss4
      ihave Hs1 := ownSnapS_M _ _ _ $$ Hs1
      try wp_auto
      rw [← Hptr]
      wp_apply wp_IsEmptySnap lo.ptr _ (some lo.snap) $$ [$HrP Hs1] as %b2 ⟨%Hb2, Hs1⟩
      · unfold snapOpt; iexact Hs1
      unfold snapOpt at Hb2
      subst Hb2
      ihave Hs1 : ownSnapM lo.ptr (DFrac.own (Qp.half (Qp.half 1))) lo.snap $$ [Hs1]
      · unfold snapOpt; iexact Hs1
      simp only [Option.elim, decide_eq_false Hne]
      -- the snapshot's facts: valid, its data the state of the delivered log
      imod kd_snap_recv γ vs lo.snap (strip lo.dlv) Hpos H61 Hslen $$ HkC HcL Hcert
        with ⟨#Hsv, %mL, #HcaL, %HmL⟩
      obtain ⟨HcsL, HszL, HdatL⟩ := HmL
      have HdatL' := HdatL
      obtain ⟨kvs, ops, Hdat, Hwk, Hwo, Hkv, Hans⟩ := HdatL
      -- `decodeState(rd.Snapshot.GetData())`
      try wp_auto
      rw [← Hptr]
      wp_apply wp_GetData.1 lo.ptr _ lo.snap $$ [$Hpb $Hs1] as %ds ⟨Hds, Hs1back⟩
      rw [Hdat, ← encState_eq]
      wp_apply wp_decodeState ds _ kvs ops Hwk Hwo $$ [$Hpkg $Hds] as %mK %mA2 ⟨Hds, %K', %A', HK', HA', %HKA⟩
      ihave Hs1 := Hs1back $$ Hds
      try wp_auto
      wp_apply wp_IsEmptyHardState rdv.HardState' h $$ [$HrP $Hhs]
      try wp_auto
      simp only [Bool.not_false]
      have Hc0' : uint.nat hd.Commit' ≤ uint.nat (phsNext hd h).Commit' := G4
      -- `dmu`: the phase idle at the driver's durable state, the image's hard state the driver's
      irename Hfz => HfzD
      wp_apply (lc := 2) sync.Mutex.wp_Lock _ _ $$ [$Hdmu] as ⟨Hlocked, HI⟩
      iunfold kdDmuInv at HI
      iNamed HI
      icases Hlive with ⟨%S1, %o, %pz, Hwr, %HMok, #Hcert0, %Hfb, Hph⟩
      ihave ⟨Hclaim, Hph, %Hidle⟩ := kd_claim_idle γ id n ρ.ph.ph S S1 M pz $$ [Hclaim Hph]
      · iframe Hclaim Hph
      obtain ⟨rfl, HS1, HSM⟩ := Hidle
      subst S1
      ihave %Hcmeq := ghostVar_agree ρ.ph.cm _ _ _ _ $$ Hcm Hcmh
      ihave #Hst' : st.[KStorage, go!"img"] ↦□ ip $$ []
      · iexact Himg
      -- `ApplySnapshot`, on the `MemoryStorage` (attached) and the image (not refused: G7)
      ihave #Hinit := isInitialized_access $$ HrP
      iunfold isInitialized at Hinit
      iNamed Hinit
      iunfold errorsNewVar at ErrSnapOODNew
      icases ErrSnapOODNew with ⟨%eood, #Heood, -⟩
      ihave Hlog := kdStorLog_to st ρ.ms ρ.γs _ _ _ $$ Hrec Hlog
      ihave Hend := kdStorEnd_to st ρ.ms ρ.γs _ $$ Hrec Hend
      have Htrip : {{ iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
            memStorAt ρ.ms ρ.γs (kdJ γ.r.cluster ρ.key) none
              iprop((kdJ γ.r.cluster ρ.key).B (uint.nat lo.snap.Metadata'.Index') ∗
                (kdJ γ.r.cluster ρ.key).SV lo.snap ∗
                (kdJ γ.r.cluster ρ.key).DL (uint.nat lo.snap.Metadata'.Index')) ∗
            memLog ρ.γs k (DFrac.own 1) old ∗ memEnd ρ.γs (k + old.length) ∗
            snapArg lo.ptr (DFrac.own (Qp.half (Qp.half 1))) lo.snap ∗ memSnapLb ρ.γs 0 ∗
            globalAddr ErrSnapOutOfDate ↦□
              (interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #eood)) }}
          (App (Val (ρ.ms @!! go.GoType.PointerType MemoryStorage.ty @!! go!"ApplySnapshot")) (Val #lo.ptr))
          {{ RET #interface.nil; ownSnapM lo.ptr (DFrac.own (Qp.half (Qp.half 1))) lo.snap ∗
            (memCompacted ρ.γs (uint.nat lo.snap.Metadata'.Index') ∗
              memLog ρ.γs (uint.nat lo.snap.Metadata'.Index') DFrac.discard [memDummy lo.snap] ∗
              memEnd ρ.γs (uint.nat lo.snap.Metadata'.Index' + 1)) }} := by
        iintro %Φ HP HΦ
        iapply wp_ApplySnapshot ρ.ms ρ.γs (kdJ γ.r.cluster ρ.key) none k old lo.ptr _ lo.snap _ Hk
          (by word) $$ HP
        inext
        iintro ⟨Hs, Hc, Hd, He, -, -⟩
        iapply HΦ
        iframe
      try wp_auto
      rw [← Hptr]
      wp_apply wp_SApplySnapshot st ρ.ms ρ.γs ip M lo.ptr _ lo.snap _ _ _ Htrip
        $$ [$Hpkg $Hrec $Hst' $Himage $Heood Hlog Hend Hs2] as %err ⟨Hs2, ⟨#HcpS, #Hdum, HendS⟩, Hres⟩
      · iframe Hlog Hend HsnLb
        isplitl []
        · iapply memStorAt_none_intro $$ HmsInv
          simp only [kdJ]
          iframe Hgiven Hsv HclS
        unfold snapArg
        iright; iexact Hs2
      simp only [img_snap_fresh M S lo.snap HSM (by rw [Hcmeq]; exact G7.1), ↓reduceIte]
      icases Hres with ⟨-, Himage⟩
      -- the hard state (if any): the image's set to the driver's next one (`phsNext`)
      wp_join iprop(∃ hsp' : Loc, memStorMeta ρ.ms ρ.γs (phsNext hd h) ∗
          ownImage ip (imgSetHardState (imgApplySnapshot M lo.snap) (phsNext hd h)) ∗ hs_ptr ↦ hsp' ∗
          hsOpt hsp' (phsNext hd h) ∗ rd_ptr ↦ rdv ∗ r_ptr ↦ r) at next with [Hmeta Himage hs rd r] as
          ⟨%hsp', Hmeta, Himage, hs, #HhsO', rd, r⟩
      · try wp_auto
        wp_if_destruct
        · have Hpe := phsNext_empty hd h (by simpa using Hif)
          rw [Hpe, show imgSetHardState (imgApplySnapshot M lo.snap) hd = imgApplySnapshot M lo.snap by
            rw [← Hcmeq]; rfl]
          wp_join_done
          iexists hsp
          rw [← Hcmeq]
          iframe
          rw [Hcmeq]
          iexact HhsO
        · have Hpe := phsNext_ne hd h (by simpa using Hif)
          rw [Hpe]
          try wp_auto
          wp_apply wp_SSetHardState st ρ.ms ρ.γs M.hs ip (imgApplySnapshot M lo.snap) rdv.HardState' h
            $$ [$Hpkg $Hrec $Hmeta $Hst' $Himage $Hhs] as ⟨Hmeta, Himage⟩
          try wp_auto
          wp_join_done
          iexists rdv.HardState'
          iframe
          iexact Hhs
      -- the entries after the snapshot, on the `MemoryStorage` and the image
      ihave ⟨Hrange, Hkeep⟩ := snapAppend_pre ρ.γs (uint.nat lo.snap.Metadata'.Index' + 1) es $$ HendS
      have h1 : ∀ (j : Nat) (e : EntryM), es[j]? = some e →
          uint.nat e.Index' = (uint.nat lo.snap.Metadata'.Index' + 1) + j := by
        intro j e hj
        have := Hli j e hj
        simp only [snapId] at this
        word
      have h2 : uint.nat lo.snap.Metadata'.Index' + 1 + es.length ≤ 2 ^ 61 := by
        cases hes : es with
        | nil => simp only [List.length_nil, Nat.add_zero]; word
        | cons e0 rest =>
          have Hf := Hfit' e0 (by rw [hes]; rfl)
          have He0 := h1 0 e0 (by rw [hes]; rfl)
          rw [hes] at Hf
          simp only [List.length_cons] at Hf ⊢
          word
      ihave #HmsInv' := HmsInv
      iunfold memStorInvP at HmsInv'
      icases HmsInv' with ⟨#Hlock, -, -⟩
      have Htrip2 : {{ iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
            memStorLock ρ.ms ρ.γs ∗
            (if es = [] then emp else memLog ρ.γs (uint.nat lo.snap.Metadata'.Index' + 1) (DFrac.own 1)
              ([] : List EntryM) ∗
              memEnd ρ.γs (uint.nat lo.snap.Metadata'.Index' + 1 + ([] : List EntryM).length))) ∗
            entsPts rdv.Entries' DFrac.discard es }}
          (App (Val (ρ.ms @!! go.GoType.PointerType MemoryStorage.ty @!! go!"Append")) (Val #rdv.Entries'))
          {{ RET #interface.nil; entsPts rdv.Entries' DFrac.discard es ∗
            (if es = [] then emp else memLog ρ.γs (uint.nat lo.snap.Metadata'.Index' + 1) (DFrac.own 1) es ∗
              memEnd ρ.γs (uint.nat lo.snap.Metadata'.Index' + 1 + es.length)) }} := by
        iintro %Φ ⟨⟨#Hr, #Hl, Hb⟩, He⟩ HΦ
        iapply wp_Append ρ.ms ρ.γs (uint.nat lo.snap.Metadata'.Index' + 1) [] es rdv.Entries' DFrac.discard
          h1 h2 $$ [Hb He]
        · iframe Hr Hl Hb He
        iexact HΦ
      wp_apply wp_SAppend st ρ.ms ρ.γs ip (imgSetHardState (imgApplySnapshot M lo.snap) (phsNext hd h))
          rdv.Entries' DFrac.discard (uint.nat lo.snap.Metadata'.Index' + 1) es _ _ h1
          (fun _ => by simp [imgSetHardState, imgApplySnapshot])
          (by simp only [imgSetHardState, imgApplySnapshot, List.length_nil, Nat.add_zero]; omega) Htrip2
        $$ [$Hpkg $Hrec $Hst' $Himage $Hes Hrange] as ⟨-, Hb, Himage⟩
      · iframe Hrange Hlock
      ihave ⟨Hb, HendB⟩ := snapAppend_post ρ.γs _ es $$ [Hb Hkeep]
      · iframe Hb Hkeep
      -- the image after the batch: its shape, the batch's durable state
      obtain ⟨Hok3, Hh3⟩ := img_ready_snap_ok M S (phsNext hd h) lo.snap lo es rfl Hsw Hpos H61 h1 G20 h2
        G7.2 G8
      have HMS : uint.nat M.hs.Commit' ≤ uint.nat S.commit := by
        have H7 := HSM.2.2.2.2.2.2.2.1
        simp only [kdContents, StorContents.commit] at H7
        exact H7
      have HpC : uint.nat M.prev ≤ uint.nat M.hs.Commit' := by have := HMok.2.2.2.2.2.2.1; word
      have HMc3 : uint.nat M.hs.Commit' ≤ uint.nat (imgAppend (imgSetHardState (imgApplySnapshot M lo.snap)
          (phsNext hd h)) (uint.nat lo.snap.Metadata'.Index' + 1) es).hs.Commit' := by
        rw [imgAppend_hs]; simp only [imgSetHardState]; rw [Hcmeq]; exact G4
      have Hfzi : fz ≤ uint.nat lo.snap.Metadata'.Index' := by
        have h7 : uint.nat M.hs.Commit' < uint.nat lo.snap.Metadata'.Index' := by
          rw [Hcmeq]; exact G7.1
        rcases Hfzc with h' | h' <;> omega
      have Hfzc3 : uint.nat lo.snap.Metadata'.Index' ≤ uint.nat (imgAppend (imgSetHardState
            (imgApplySnapshot M lo.snap) (phsNext hd h)) (uint.nat lo.snap.Metadata'.Index' + 1) es).hs.Commit' ∨
          uint.nat lo.snap.Metadata'.Index' ≤ uint.nat (imgAppend (imgSetHardState
            (imgApplySnapshot M lo.snap) (phsNext hd h)) (uint.nat lo.snap.Metadata'.Index' + 1) es).prev := by
        left; rw [imgAppend_hs]; exact G7.2
      have His3 : uint.nat M.snap.Metadata'.Index' ≤ uint.nat (imgAppend (imgSetHardState
          (imgApplySnapshot M lo.snap) (phsNext hd h)) (uint.nat lo.snap.Metadata'.Index' + 1)
            es).snap.Metadata'.Index' := by
        rw [imgAppend_snap]; simp only [imgSetHardState, imgApplySnapshot]
        by_cases h0 : M.snap.Metadata'.Index' = W64 0
        · rw [h0]; simp
        · have := holds_snap_commit S M HSM h0
          have h7 : uint.nat M.hs.Commit' < uint.nat lo.snap.Metadata'.Index' := by
            rw [Hcmeq]; exact G7.1
          omega
      ihave #Hfz3' : memLog ρ.γs (uint.nat (imgAppend (imgSetHardState (imgApplySnapshot M lo.snap)
            (phsNext hd h)) (uint.nat lo.snap.Metadata'.Index' + 1) es).prev + 1) DFrac.discard
          ((imgAppend (imgSetHardState (imgApplySnapshot M lo.snap) (phsNext hd h))
            (uint.nat lo.snap.Metadata'.Index' + 1) es).ents.take (uint.nat lo.snap.Metadata'.Index' -
            uint.nat (imgAppend (imgSetHardState (imgApplySnapshot M lo.snap) (phsNext hd h))
              (uint.nat lo.snap.Metadata'.Index' + 1) es).prev)) $$ []
      · simp only [imgAppend_prev, imgSetHardState, imgApplySnapshot, Nat.sub_self, List.take_zero]
        iapply memLog_nil
      ihave #Hcert3 : kdSnapCert γ (imgAppend (imgSetHardState (imgApplySnapshot M lo.snap) (phsNext hd h))
          (uint.nat lo.snap.Metadata'.Index' + 1) es).snap $$ []
      · simp only [imgAppend_snap, imgSetHardState, imgApplySnapshot]
        unfold kdSnapCert
        iright
        iframe Hsv
        iexists strip lo.dlv, mL
        iframe HcL HcaL
        ipureintro; exact ⟨Hslen, HdatL', HcsL, HszL⟩
      ihave Hcmh : ghostVar ρ.ph.cm (1 : Qp).half M.hs $$ [Hcmh]
      · rw [Hcmeq]; iexact Hcmh
      ihave Hrest : kdDmuRest γ id r ρ.ph crashed S M $$ [Hcr Hwr]
      · iunfold kdDmuRest; iframe Hcr; iexists o; iframe Hwr; ipureintro; exact Hfb
      ihave Hmeta : memStorMeta ρ.ms ρ.γs (imgAppend (imgSetHardState (imgApplySnapshot M lo.snap)
          (phsNext hd h)) (uint.nat lo.snap.Metadata'.Index' + 1) es).hs $$ [Hmeta]
      · simp only [imgAppend_hs, imgSetHardState]; iexact Hmeta
      -- a snapshot's batch is always cut: recorded, `persist` enters it
      imod dmu_close_cut γ id r n st ρ.ms ρ.γs ρ.ph crashed ip M
        (imgAppend (imgSetHardState (imgApplySnapshot M lo.snap) (phsNext hd h))
          (uint.nat lo.snap.Metadata'.Index' + 1) es) fz (uint.nat lo.snap.Metadata'.Index') S
        { storage := kdStorIface st, delivered := D, hardState := hd, handling := none, key := ρ.key,
          durable := S, role := role }
        { storage := kdStorIface st, delivered := strip lo.dlv, hardState := phsNext hd h,
          handling := some (es, some lo), key := ρ.key, durable := readyDurable S (phsNext hd h) (some lo) es,
          role := roleAfter role ss } ms Hok3 Hh3 rfl HMc3 Hfzi Hfzc3 His3
        $$ [Hrest Himg Himage Hmeta Hic Hfz3' His Hcm Hcert3 Hph Hclaim Hcmh Henter]
        with ⟨%γb, HI, Hclaim, #Hsvb, Hcmh, #Hicl'⟩
      · iframe Hrest Himg Himage Hmeta Hic Hfz3' His Hcm Hcert3 Hph Hclaim Hcmh Henter
      wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hdmu $Hlocked HI]
      · inext; iexact HI
      ihave Hcmh : ghostVar ρ.ph.cm (1 : Qp).half (phsNext hd h) $$ [Hcmh]
      · simp only [imgAppend_hs, imgSetHardState]; iexact Hcmh
      -- `r.install(rd.Snapshot.GetMetadata(), kv, ops)`
      have Hkv' : ∀ k, (K' !! k).getD [] = kvreconf.kvFold (kvreconf.logHist (strip lo.dlv)) k := by
        intro k; rw [HKA.1 k]; exact Hkv k
      have Hans' : kvreconf.AppliedOk A' (kvreconf.logHist (strip lo.dlv)) := by
        unfold kvreconf.AppliedOk
        have : (fun d => A' !! d) = (fun o => List.lookup o ops) := funext HKA.2
        rw [this]; exact Hans
      try wp_auto
      rw [← Hptr]
      wp_apply wp_GetMetadata.1 lo.ptr _ lo.snap $$ [$Hpb $Hs1] as %pm ⟨Hpm, Hs1back⟩
      wp_apply wp_install γ vs dir id r n st sts sq ρ.ms ρ.γs ρ.ph ap _ csp m mA A pm _ lo.snap.Metadata'
          mK mA2 K' A' (strip lo.dlv) mL Hslen (by rw [Hslen]; word) Hkv' Hans' HcsL HszL
        $$ [$Hrep $Hown $Hpm $HK' $HA' $HcL $HcaL] as ⟨Hpm, %csp2, Hown⟩
      ihave Hs1 := Hs1back $$ Hpm
      -- `snapIndex = rd.Snapshot.GetMetadata().GetIndex()`, `rafted = snapIndex`
      try wp_auto
      rw [← Hptr]
      wp_apply wp_GetMetadata.1 lo.ptr _ lo.snap $$ [$Hpb $Hs1] as %pm2 ⟨Hpm2, Hs1back⟩
      wp_apply wp_MdGetIndex pm2 _ _ $$ [$Hpb $Hpm2] as Hpm2
      ihave Hs1 := Hs1back $$ Hpm2
      try wp_auto
      -- `first`: at role leader, the messages sent before the write one time in two
      wp_join (Q := fun v => iprop(⌜∃ fb : Bool, v = #fb ∧ (fb = true → lead' = true)⌝ ∗
          lead_ptr ↦ lead' ∗ sync_ptr ↦ true)) at (if: _ then _ else _) with [lead sync]
        as ⟨%Hfv, lead, sync⟩
      · cases lead'
        all_goals try wp_auto
        all_goals first
          | (iframe; ipureintro; exact ⟨false, rfl, fun h' => by cases h'⟩)
          | (wp_apply wp_oneIn (W64 2) (by decide) $$ [$Hpkg] as %b -
             iframe; ipureintro; exact ⟨b, rfl, fun _ => rfl⟩)
      obtain ⟨fb, rfl, Hfb⟩ := Hfv
      try wp_auto
      -- sent first: at role leader (`readyLeaderMsgs`)
      wp_join iprop((⌜fb = true⌝ ∨ (rdv.Messages' ↦* List.map QMsg.loc ms ∗
            [∗list] q ∈ ms, iprop(msgOwn q.loc (readyDq q.st) q.st ∗ msgCredits γ.r.cluster kdRaftN q.st))) ∗
          r_ptr ↦ r ∗ rd_ptr ↦ rdv ∗ send_ptr ↦ f) at next with [Hmsl Hmsok Hlm r rd send]
        as ⟨Hmq, r, rd, send⟩
      · cases fb
        · try wp_auto
          wp_join_done
          iframe
          iright
          iframe
        · have Hl := Hfb rfl
          have Hrole := Hlead' Hl
          iunfold readyLeaderMsgs at Hlm
          ihave #Hmsgs := Hlm $$ %Hrole
          ihave #Hlsf := isStats_field sts go!"LeaderSentFirst" (by decide) $$ Hstats
          try wp_auto
          wp_apply wp_add sts _ $$ [$Hpkg $Hlsf]
          try wp_auto
          wp_bind (App (Val #f) _)
          iunfold sendSpec at Hsend
          iapply Hsend $$ [Hmsl Hmsok]
          · iframe Hpkg Hmsl
            iapply kd_readyMsgs_sent $$ [$Hmsok $Hmsgs]
          iintro !> -
          try wp_auto
          wp_join_done
          iframe
          ileft; ipureintro; rfl
      -- the write: `persist` enters the batch; a failed write (crashed) ends the loop
      wp_join (Q := fun v => iprop((⌜v = executeVal⌝ ∗ nodeRunning n γ.r.cluster kdRaftN (1 : Qp).half ∗
            ghostVar ρ.ph.ph (1 : Qp).half ((none : Option GName), readyDurable S (phsNext hd h) (some lo) es) ∗
            kdBatchRes γ id n (
                { storage := kdStorIface st, delivered := strip lo.dlv, hardState := phsNext hd h,
                  handling := some (es, some lo), key := ρ.key,
                  durable := readyDurable S (phsNext hd h) (some lo) es,
                  role := roleAfter role ss } : NodeDriverState) ms ∗
            r_ptr ↦ r ∗ handoffProducer ρ.rd false) ∨ ⌜v = returnVal #()⌝))
        at next with [Hrun Hclaim r Hprod]
      · try wp_auto
        wp_apply wp_persistRun γ vs dir id r n st sts sq ρ.ms ρ.γs ρ.ph (1 : Qp).half (
            { storage := kdStorIface st, delivered := strip lo.dlv, hardState := phsNext hd h,
              handling := some (es, some lo), key := ρ.key,
              durable := readyDurable S (phsNext hd h) (some lo) es,
              role := roleAfter role ss } : NodeDriverState) ms γb
          $$ [$Hrep $Hrun $Hclaim $Hsvb] as %ok ⟨Hrun, Hpost⟩
        cases ok
        · simp only [Bool.false_eq_true, ↓reduceIte]
          irename Hpost => Hclaim
          try wp_auto
          wp_apply wp_handoff_send ρ.rd ρ.rdc (fun _ => iprop(nodeRunning n γ.r.cluster kdRaftN (1 : Qp).half ∗
              ∃ v : Option GName × RaftState, ghostVar ρ.ph.ph (1 : Qp).half v)) iprop(True)
            iprop(False) () $$ [$HrdH $Hprod Hrun Hclaim] as -
          · isplitl [Hrun Hclaim]
            · iframe Hrun; iexists _; iexact Hclaim
            · itrivial
          try wp_auto
          iright; ipureintro; rfl
        · simp only [↓reduceIte]
          icases Hpost with ⟨Hclaim, Hres⟩
          try wp_auto
          ileft; iframe; ipureintro; rfl
      iintro Hq
      icases Hq with (⟨%Hv, Hrun, Hclaim, Hres, r, Hprod⟩ | %Hv)
      rotate_left
      · subst Hv
        try wp_auto
        wp_for_post
        try wp_auto
        iapply HΦ
        itrivial
      subst Hv
      iunfold kdBatchRes at Hres
      icases Hres with ⟨Hdrv, #Hmsgs⟩
      try wp_auto
      -- sent after the write
      wp_join iprop(r_ptr ↦ r ∗ rd_ptr ↦ rdv ∗ send_ptr ↦ f) at next with [Hmq r rd send]
        as ⟨r, rd, send⟩
      · cases fb
        · icases Hmq with (%h' | ⟨Hmsl, Hmsok⟩)
          · cases h'
          try wp_auto
          wp_bind (App (Val #f) _)
          iunfold sendSpec at Hsend
          iapply Hsend $$ [Hmsl Hmsok]
          · iframe Hpkg Hmsl
            iapply kd_readyMsgs_sent $$ [$Hmsok $Hmsgs]
          iintro !> -
          try wp_auto
          wp_join_done
        · try wp_auto
          wp_join_done
      -- the read states, noted
      icases Hrs with ⟨%rsts, #Hsts, #Hstsok⟩
      ihave Hvs := kd_readStatesPts_rsOk γ.r.cluster rdv.ReadStates' rsts $$ [Hsts Hstsok]
      · iframe Hsts Hstsok
      icases Hvs with ⟨%vls, #Hvls, #Hvlsok⟩
      try wp_auto
      wp_apply wp_slice_append $$ [$Hpv $Hpcap $Hvls] as %pv' ⟨Hpv, Hpcap, -⟩
      ihave #Hps' : iprop([∗list] v ∈ ps ++ vls, rsOk γ.r.cluster v) $$ []
      · iapply (BigSepL.bigSepL_append (Φ := fun _ v => rsOk (GF := GF) γ.r.cluster v)).2
        iframe Hps Hvlsok
      iclear Hps
      -- no committed entries
      iunfold committedEntriesAt at Hce
      icases entsPts_elim _ _ _ $$ Hce with ⟨%cls, #Hcel, #Hceb⟩
      ihave %Hcelen := ownSlice_len $$ Hcel
      ihave %Hcebl := entsBig_length $$ Hceb
      rw [kvreconf.kvr_toEntries_length] at Hcebl
      try wp_auto
      ihave IH : iprop(∃ ev : Loc, "i" ∷ i_ptr ↦ W64 0 ∗ "e" ∷ e_ptr ↦ ev) $$ [i e]
      · iexists _; iframe
      wp_for IH
      wp_if_destruct
      · exfalso
        simp only [List.length_nil] at Hcebl
        have := Hcelen.1; word
      have Hidxeq : lo.snap.Metadata'.Index' = W64 ((strip lo.dlv).length : Int) := by rw [Hslen]; word
      ihave Hown : repOwn γ r (strip lo.dlv) (W64 (strip lo.dlv).length) csp2 mL mA2 A' $$ [Hown]
      · rw [← Hidxeq]; iexact Hown
      wp_apply wp_answer γ vs dir id r n st sts sq ρ.ms ρ.γs ρ.ph (strip lo.dlv) _ csp2 mL mA2 A' pv'
          (ps ++ vls) (DFrac.own 1) (by rw [Hslen]; word) $$ [$Hrep $Hown $Hpv $Hps']
        as %rest ⟨Hown, %ps', Hrest, Hcap2, #Hps2⟩
      -- `r.node.Advance()`: the node's configuration at the snapshot's
      ihave #HkC' := HkC
      iunfold kdCluster at HkC'
      icases HkC' with ⟨#Hic, -⟩
      ihave ⟨%v, Hcfg⟩ : iprop(∃ v : ConfigView, nodeConfig n γ.r.cluster kdRaftN v) $$ [Hview]
      · icases Hview with (⟨-, Hv⟩ | ⟨-, Hc, -⟩)
        · iunfold appNode at Hv
          icases Hv with ⟨%v, Hc, -, -, -⟩
          iexists v; iexact Hc
        · iexists _; iexact Hc
      ihave Hs := ownSnapM_combine lo.ptr _ _ lo.snap $$ [Hs1 Hs2]
      · iframe Hs1 Hs2
      ihave Hs : ownSnapM lo.ptr (DFrac.own (Qp.half 1)) lo.snap $$ [Hs]
      · rw [dfrac_own_half_half (Qp.half 1)]; iexact Hs
      ihave Hrcpt := kd_snapReceipt st ρ.ms ρ.γs lo es $$ Hrec Hs HcpS Hdum Hb HendB
      wp_apply wp_Advance n γ.r.cluster kdRaftN id _ es (some lo) v rfl
          (fun l' h => by cases h; exact Hdlen)
        $$ [$HrP $Hic $HisNode $Hdrv Hrcpt $Hcfg] as Hadv
      · simp only [advReceipt]
        iframe Hrcpt Hcert
      icases Hadv with (⟨Hdrv, #Hal', %m2, Hcfg, #Hca2, %Hcs2⟩ | ⟨#Hstop, -⟩)
      rotate_left
      · iexfalso
        iapply nodeRunning_stopped n γ.r.cluster kdRaftN _ $$ [$Hrun $Hstop]
      ihave #HcaL' : confAt γ.r.cluster (uint.nat lo.snap.Metadata'.Index') mL $$ []
      · rw [← Hslen]; iexact HcaL
      ihave %Hm := confAt_agree γ.r.cluster _ m2 mL $$ [$Hca2 $HcaL']
      subst Hm
      ihave ⟨Hdrv, #Hdl⟩ := nodeDriver_deliveredLogLb _ _ _ _ $$ Hdrv
      icases nodeDriver_nodeCommitLb _ _ _ _ $$ Hdrv with ⟨Hdrv, #HclD⟩
      ihave Hview := appNode_snap γ n (strip lo.dlv) _ m2 Hslen $$ [$Hcfg $Hdl]
      ihave #Hfz2 := kd_frozenTo_snap (GF := GF) ρ.γs (strip lo.dlv) _ Hslen
      ihave #HfzM := Hfz2
      iunfold kvreconf.frozenTo at HfzM
      -- `snapIndex = r.request(snapIndex, oneIn(4), bound)`, `bound` raft's applied index or `0`
      try wp_auto
      wp_apply wp_oneIn (W64 4) (by decide) $$ [$Hpkg] as %b1 -
      wp_join iprop(∃ bnd : w64, bound_ptr ↦ bnd ∗ rafted_ptr ↦ lo.snap.Metadata'.Index' ∗
          ⌜bnd = W64 0 ∨ bnd = lo.snap.Metadata'.Index'⌝)
        at next with [bound rafted] as ⟨%bnd, bound, rafted, %Hbnd'⟩
      · wp_if_destruct
        · try wp_auto
          wp_join_done
          iexists _; iframe; ipureintro; first | (left; rfl) | (right; rfl)
        · wp_join_done
          iexists _; iframe; ipureintro; first | (left; rfl) | (right; rfl)
      try wp_auto
      wp_apply wp_oneIn (W64 4) (by decide) $$ [$Hpkg] as %b2 -
      have Hble : uint.nat bnd ≤ (strip lo.dlv).length := by
        rcases Hbnd' with h' | h'
        · rw [h']; simp
        · rw [h', Hslen]; exact Nat.le_refl _
      ihave Hicp : iprop(⌜(strip lo.dlv).length ≤ uint.nat lo.snap.Metadata'.Index'⌝ ∨
          monoNatLbOwn ρ.ph.ic (strip lo.dlv).length) $$ []
      · ileft; ipureintro; omega
      ihave Hbndp : iprop(⌜bnd = W64 0⌝ ∨ nodeAppliedLb γ.r.cluster ρ.key (uint.nat bnd)) $$ []
      · rcases Hbnd' with h' | h'
        · ileft; ipureintro; exact h'
        · iright; rw [h', ← Hslen]; iexact Hal'
      wp_apply wp_request γ vs dir id r n st sts sq ρ (strip lo.dlv) csp2 m2 mA2 A' (strip lo.dlv)
          (uint.nat lo.snap.Metadata'.Index') lo.snap.Metadata'.Index' bnd b2 (fun _ => List.prefix_refl _)
          (Nat.le_refl _) Hble
        $$ [$Hrr $Hown $HcpS $HfzM $Hdl $HclD Hicp Hbndp] as %ret ⟨Hown, %Hsv1⟩
      · iframe Hicp Hbndp
      have Hc2 : uint.nat lo.snap.Metadata'.Index' ≤ uint.nat ret := by
        rcases Hsv1 with h' | ⟨h', h''⟩
        · rw [h']; exact Nat.le_refl _
        · rw [h']; have : uint.nat (W64 ((strip lo.dlv).length : Int)) = (strip lo.dlv).length := by
            rw [Hslen]; word
          omega
      -- the loop's invariant, at the snapshot's log
      ihave #Hicl2 : monoNatLbOwn ρ.ph.ic (strip lo.dlv).length $$ []
      · rw [Hslen]; iexact Hicl'
      ihave Hview2 : iprop((⌜(strip lo.dlv).length = (strip lo.dlv).length⌝ ∗
          appNode γ n (strip lo.dlv) (strip lo.dlv).length m2) ∨
          (⌜(strip lo.dlv).length < (strip lo.dlv).length⌝ ∗
            nodeConfig n γ.r.cluster kdRaftN ⟨(strip lo.dlv).length, m2⟩ ∗
            deliveredLogLb n γ.r.cluster kdRaftN (strip lo.dlv))) $$ [Hview]
      · ileft; iframe Hview; ipureintro; rfl
      wp_for_post
      iframe
      unfold runInv
      iexists strip lo.dlv, phsNext hd h, readyDurable S (phsNext hd h) (some lo) es, roleAfter role ss,
        strip lo.dlv, csp2, mA2, m2, A', ret, lo.snap.Metadata'.Index', uint.nat lo.snap.Metadata'.Index',
        rest, ps', lead', hsp'
      iframe
      iframe HcpS Hfz2 HhsO' Hps2 Hicl2
      ipureintro
      obtain ⟨Ht, Hv, -⟩ := readyDurable_tv S (phsNext hd h) (some lo) es
      exact ⟨⟨Ht, Hv⟩, Hlead', Hc2, by omega, by omega, Or.inr (Nat.le_refl _)⟩
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
