/-
Port of election_proof/proof_stepFollower.v.
-/
module

public import Spec.go_etcd_io.raft.v3.stepFollower
public import Spec.go_etcd_io.raft.v3.raft__handleAppendEntries
public import Spec.go_etcd_io.raft.v3.raft__handleHeartbeat
public import Spec.go_etcd_io.raft.v3.raft__handleSnapshot
public import Spec.go_etcd_io.raft.v3.raft__send
public import Spec.go_etcd_io.raft.v3.raft__hup

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

set_option linter.unusedSimpArgs false in
/-- By type. The type switch's first test is against `MsgProp`
(`W32 2`); rewriting `m.Type` to its literal lets `wp_auto` decide
the rest by computation.

- `MsgVoteResp`, `MsgBeat`, `MsgAppResp`, `MsgHeartbeatResp`: no arm
  matches; `return nil`.
- `MsgProp`, leaderless: `r.lead == None` holds, the `Infof` reads
  `r.id`, `r.Term` and the logger, and the `return` loads
  `ErrProposalDropped` -- a package global, whose points-to
  `isInitialized_access` hands out.
- `MsgProp`, with a leader: `disableProposalForwarding` is `false`
  (`raft.wp_load_disableProposalForwardingC`), `m.To = r.lead` is a
  store into the local copy of `m`, and `send` takes clause (e).
- `MsgApp`/`MsgHeartbeat`/`MsgSnap`: two stores (`electionElapsed`,
  untracked, and `lead`), then `handleAppendEntries`/`handleHeartbeat`/
  `handleSnapshot` at `{ s with lead := m.From' }`.
- `MsgReadIndex` (2026-10-12): leaderless, `Infof` and `nil`; otherwise
  `m.To = r.lead` and `send`, by its last clause (the requester kept if set).
- `MsgReadIndexResp` (2026-10-12): not one entry, `Errorf` and `nil`; otherwise
  `r.readStates` grows by `ReadState{m.Index, m.Entries[0].Data}`, through
  `ownRaftPhysC_misc`. -/
theorem stepFollower.wp_proof
    (wp_raft_handleAppendEntries : raft.handleAppendEntries.spec (GF := GF) (hG := hG))
    (wp_raft_handleHeartbeat : raft.handleHeartbeat.spec (GF := GF) (hG := hG))
    (wp_raft_handleSnapshot : raft.handleSnapshot.spec (GF := GF) (hG := hG))
    (wp_raft_send : raft.send.spec (GF := GF) (hG := hG))
    (wp_raft_hup : raft.hup.spec (GF := GF) (hG := hG)) :
    stepFollower.spec (GF := GF) (hG := hG) := by
  intro c scfg r id s m ents sv voters cl Hty Hri Hprop Happ Hhb Hrest
  wp_start as H
  iNamed H
  ihave #Hinit := isInitialized_access $$ Hpkg
  unfold isInitialized
  icases Hinit with ⟨%e1, %e2, %e3, %e4, %errPropDropped, %gr, %_, %_, %_, %_, #Hinit⟩
  iNamed Hinit
  wp_auto
  rcases Hty with Hty | Hty | Hty | Hty | Hty | Hty | Hty | Hty | Hty | Hty | Hty | Hty | Hty |
    Hty
  · -- `MsgVoteResp`: no arm
    rw [Hty]
    simp only [MsgVoteResp]
    wp_auto
    iapply HΦ $$ %GoInterface.nil %s %false %c
    iframe Hphys
    simp only [Bool.false_eq_true, ↓reduceIte]
    ipureintro
    simp [FollowerStepResultC, MsgSnap, Hty, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat,
      MsgAppResp, MsgHeartbeatResp, MsgSnap, MsgPreVoteResp]
  · -- `MsgProp`
    obtain ⟨Hfrom0, Hterm0, Hlid⟩ := Hprop Hty
    rw [Hty]
    simp only [MsgProp]
    wp_auto
    wp_apply raft.wp_load_leadC $$ Hphys as Hphys
    by_cases Hlead : s.lead = W64 0
    · -- leaderless: dropped
      rw [decide_eq_true Hlead]
      wp_auto
      wp_apply raft.wp_load_idC $$ Hphys as Hphys
      wp_apply raft.wp_load_TermC $$ Hphys as Hphys
      wp_raft_logC
      iapply HΦ $$ %errPropDropped %s %true %c
      iframe Hphys
      simp only [↓reduceIte]
      isplitr
      · ipureintro
        simp [FollowerStepResultC, MsgSnap, Hty, Hlead, MsgVoteResp, MsgProp]
      iexact ErrPropDropped
    · -- forwarded to the leader
      rw [decide_eq_false Hlead]
      wp_auto
      wp_apply raft.wp_load_disableProposalForwardingC $$ Hphys as Hphys
      wp_apply raft.wp_load_leadC $$ Hphys as Hphys
      ihave Hes := Hents $$ %(Or.inr trivial)
      icases Hes with ⟨#Hes, -⟩
      ihave #Hcl := Hctx $$ %(by simp [Hty, MsgHeartbeat, MsgProp])
      wp_apply wp_raft_send _ _ _ _ { m with To' := s.lead } ents cl [propForward id s.lead m ents cl]
          (Or.imp_right Or.inl Hfrom0) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Hty, Hterm0, fun h => Hlid h, rfl⟩)))))
        $$ [$Hphys $Hes $Hcl]
      · iapply send_no_snap
        simp [Hty, MsgProp, MsgSnap]
      iintro Hphys
      wp_auto
      iapply HΦ $$ %GoInterface.nil %_ %false %c
      iframe
      simp only [Bool.false_eq_true, ↓reduceIte]
      ipureintro
      simp [FollowerStepResultC, MsgSnap, Hty, MsgVoteResp, MsgProp]
      exact Hlead
  · -- `MsgApp`: adopt the sender as leader, then `handleAppendEntries`
    obtain ⟨Hwf, Hnw, Hconf, Hfid⟩ := Happ Hty
    rw [Hty]
    simp only [MsgApp]
    wp_auto
    wp_apply raft.wp_store_electionElapsedC $$ Hphys as Hphys
    wp_apply raft.wp_store_leadC $$ Hphys as Hphys
    ihave Hes := Hents $$ %(Or.inl trivial)
    icases Hes with ⟨#Hes, Hcap⟩
    wp_apply wp_raft_handleAppendEntries _ _ _ { s with lead := m.From' } _ _ Hwf Hnw Hconf Hfid
      $$ [$Hphys $Hes $Hcap]
      as %s' ⟨Hphys, %Hres⟩
    iapply HΦ $$ %GoInterface.nil %s' %false %c
    iframe
    simp only [Bool.false_eq_true, ↓reduceIte]
    ipureintro
    refine ⟨?_, trivial⟩
    simp [FollowerStepResultC, MsgSnap, Hty, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat,
      MsgAppResp, MsgHeartbeatResp, MsgSnap, MsgPreVoteResp]
    exact Hres
  · -- `MsgHeartbeat`: adopt the sender as leader, then `handleHeartbeat`
    obtain ⟨Hcommit, Hfrom⟩ := Hhb Hty
    rw [Hty]
    simp only [MsgHeartbeat]
    wp_auto
    wp_apply raft.wp_store_electionElapsedC $$ Hphys as Hphys
    wp_apply raft.wp_store_leadC $$ Hphys as Hphys
    ihave #Hcl := Hctx $$ %(by simp [Hty, MsgHeartbeat, MsgProp])
    wp_apply wp_raft_handleHeartbeat _ _ _ { s with lead := m.From' } _ cl Hcommit Hfrom
      $$ [$Hphys $Hcl] as Hphys
    iapply HΦ $$ %GoInterface.nil %_ %false %c
    iframe
    simp only [Bool.false_eq_true, ↓reduceIte]
    ipureintro
    refine ⟨?_, trivial⟩
    simp [FollowerStepResultC, MsgSnap, Hty, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat,
      MsgAppResp, MsgHeartbeatResp, MsgSnap, MsgPreVoteResp]
  · -- `MsgBeat`, `MsgAppResp`, `MsgHeartbeatResp`: no arm
    rcases Hty with Hty' | Hty' | Hty' <;> rw [Hty'] <;>
      simp only [MsgBeat, MsgAppResp, MsgHeartbeatResp] <;> wp_auto
    all_goals
      iapply HΦ $$ %GoInterface.nil %s %false %c
      iframe Hphys
      simp only [Bool.false_eq_true, ↓reduceIte]
      ipureintro
      simp [FollowerStepResultC, MsgSnap, Hty', MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat,
        MsgAppResp, MsgHeartbeatResp, MsgSnap, MsgPreVoteResp]
  · -- `MsgSnap`: adopt the sender as leader, then `handleSnapshot`
    ihave Hs := Hsnap $$ %Hty
    icases Hs with ⟨%learners, %Hsc, #Hsv, #Hvs, #Hls⟩
    obtain ⟨Hscope, Hrole, Hvotes, Hcfg, Hfid⟩ := Hsc
    rw [Hty]
    simp only [MsgSnap]
    wp_auto
    wp_apply raft.wp_store_electionElapsedC $$ Hphys as Hphys
    wp_apply raft.wp_store_leadC $$ Hphys as Hphys
    -- (2026-10-14) at any configuration: `handleSnapshot` on the struct at `c`
    wp_apply wp_raft_handleSnapshot c scfg _ _ { s with lead := m.From' } _ sv voters learners Hrole
      Hvotes Hcfg Hscope Hfid $$ [$Hphys $Hsv $Hvs $Hls]
      as %s' %c' ⟨Hphys, %Hres, %Hc'⟩
    iapply HΦ $$ %GoInterface.nil %s' %false %c'
    iframe
    simp only [Bool.false_eq_true, ↓reduceIte]
    ipureintro
    refine ⟨?_, trivial⟩
    simp [FollowerStepResultC, MsgSnap, Hty, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat,
      MsgAppResp, MsgHeartbeatResp, MsgSnap, MsgPreVoteResp]
    exact ⟨Hc', Hres⟩
  · -- `MsgPreVoteResp` (2026-10-04): no arm
    rw [Hty]
    simp only [MsgPreVoteResp]
    wp_auto
    iapply HΦ $$ %GoInterface.nil %s %false %c
    iframe Hphys
    simp only [Bool.false_eq_true, ↓reduceIte]
    ipureintro
    simp [FollowerStepResultC, MsgSnap, Hty, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat,
      MsgAppResp, MsgHeartbeatResp, MsgSnap, MsgPreVoteResp]

  · -- `MsgReadIndex` (2026-10-12): forwarded to the leader, if any
    obtain ⟨Hterm0, Hlid⟩ := Hri Hty
    ihave #Hes := Hrents $$ %(Or.inl Hty)
    ihave #Hcl := Hctx $$ %(Or.inr (Or.inr Hty))
    rw [Hty]
    simp only [MsgReadIndex]
    wp_auto
    wp_apply raft.wp_load_leadC $$ Hphys as Hphys
    by_cases Hlead : s.lead = W64 0
    · -- leaderless: logged and dropped
      rw [decide_eq_true Hlead]
      wp_auto
      wp_apply raft.wp_load_idC $$ Hphys as Hphys
      wp_apply raft.wp_load_TermC $$ Hphys as Hphys
      wp_raft_logC
      iapply HΦ $$ %GoInterface.nil %s %false %c
      iframe Hphys
      simp only [Bool.false_eq_true, ↓reduceIte]
      ipureintro
      refine ⟨?_, trivial⟩
      simp [FollowerStepResultC, MsgSnap, Hty, Hlead, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat,
        MsgAppResp, MsgHeartbeatResp, MsgSnap, MsgPreVoteResp, MsgReadIndex]
    · -- forwarded to the leader
      rw [decide_eq_false Hlead]
      wp_auto
      wp_apply raft.wp_load_leadC $$ Hphys as Hphys
      wp_apply wp_raft_send _ _ _ _ { m with To' := s.lead } ents cl
          [readForward id s.lead m ents cl]
          (Or.inr (Or.inr (Or.inl Hty)))
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨Hty, Hterm0, fun h => Hlid h, rfl⟩)))))
        $$ [$Hphys $Hes $Hcl]
      · iapply send_no_snap
        simp [Hty, MsgReadIndex, MsgSnap]
      iintro Hphys
      wp_auto
      iapply HΦ $$ %GoInterface.nil %_ %false %c
      iframe
      simp only [Bool.false_eq_true, ↓reduceIte]
      ipureintro
      refine ⟨?_, trivial⟩
      simp [FollowerStepResultC, MsgSnap, Hty, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat,
        MsgAppResp, MsgHeartbeatResp, MsgSnap, MsgPreVoteResp, MsgReadIndex]
      exact fun h => absurd h Hlead
  · -- `MsgReadIndexResp` (2026-10-12): one entry becomes a `ReadState`
    ihave #Hes := Hrents $$ %(Or.inr Hty)
    ihave %Hlen := ownSlice_len _ _ _ $$ Hes
    rw [Hty]
    simp only [MsgReadIndexResp]
    wp_auto
    wp_if_destruct
    · -- one entry: `r.readStates = append(r.readStates, ReadState{m.Index, m.Entries[0].Data})`
      obtain ⟨e, rfl⟩ : ∃ e, ents = [e] :=
        List.length_eq_one_iff.1 (by rw [Hlen.1, Hif]; rfl)
      icases ownSlice_elem_acc (sint.Z (W64 0)) e m.Entries' DFrac.discard [e] (by word) (by simp)
        $$ Hes with ⟨#He, -⟩
      iStructNamed He
      icases ownRaftPhysC_misc _ _ _ $$ Hphys with ⟨%rs, %ro, %pr, Hrs, Hro, Hpr, Hmisc, Hback⟩
      iunfold ownRaftMisc at Hmisc
      iNamed Hmisc
      wp_auto
      simp only [show (0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z m.Entries'.len) = True from
        eq_true ⟨by word, by rw [Hif]; word⟩, ↓reduceIte]
      wp_auto
      wp_apply wp_slice_literal (V := ReadState) [ReadState.mk m.Index' e.Data']
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl, -⟩
      wp_auto
      wp_apply wp_slice_append_persistent (V := ReadState) _ _ _ _ _
        $$ [$HreadStates $HreadStates_cap $Hsl]
        as %rs' ⟨Hrs', Hcap', -⟩
      ihave Hmisc : ownRaftMisc (GF := GF) rs' ro pr
          { s.rd with states := s.rd.states ++ [ReadState.mk m.Index' e.Data'] }
          $$ [Hrs' Hcap' Hro_obj Hpri Hpri_cap]
      · unfold ownRaftMisc
        simp only [named]
        iframe Hrs' Hcap' Hro_obj Hpri Hpri_cap Hpri_ents
      ihave Hphys := Hback $$ %rs' %ro %pr %_ Hrs Hro Hpr Hmisc
      iapply HΦ $$ %GoInterface.nil %_ %false %c
      iframe Hphys
      simp only [Bool.false_eq_true, ↓reduceIte]
      ipureintro
      refine ⟨?_, trivial⟩
      simp [FollowerStepResultC, MsgSnap, Hty, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat,
        MsgAppResp, MsgHeartbeatResp, MsgSnap, MsgPreVoteResp, MsgReadIndex, MsgReadIndexResp,
        addReadState]
    · -- not one entry: logged and ignored
      wp_apply raft.wp_load_idC $$ Hphys as Hphys
      wp_raft_logC
      iapply HΦ $$ %GoInterface.nil %s %false %c
      iframe Hphys
      simp only [Bool.false_eq_true, ↓reduceIte]
      ipureintro
      refine ⟨?_, trivial⟩
      have Hne : ¬ ents.length = 1 := fun h => Hif (by
        have := Hlen.1; rw [h] at this; word)
      match ents, Hne with
      | [], _ =>
        simp [FollowerStepResultC, MsgSnap, Hty, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat,
          MsgAppResp, MsgHeartbeatResp, MsgSnap, MsgPreVoteResp, MsgReadIndex, MsgReadIndexResp]
      | _ :: _ :: _, _ =>
        simp [FollowerStepResultC, MsgSnap, Hty, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat,
          MsgAppResp, MsgHeartbeatResp, MsgSnap, MsgPreVoteResp, MsgReadIndex, MsgReadIndexResp]
      | [_], h => exact absurd rfl h
  · -- `MsgForgetLeader` (2026-10-13): the read-only option is `Safe` (not `LeaseBased`),
    -- then a leader, if any, is forgotten
    rw [Hty]
    simp only [MsgForgetLeader]
    wp_auto
    icases ownRaftPhysC_readOnly c r id _ $$ Hphys with ⟨%ro, Hrof, Hro, Hback⟩
    icases ownReadOnly_option ro _ $$ Hro with ⟨%o, %Hosafe, Hopt, Hroback⟩
    wp_auto
    ihave Hro := Hroback $$ Hopt
    ihave Hphys := Hback $$ %ro %_ Hrof Hro
    ihave Hphys := ownRaftPhysC_eq c r id _ s rfl $$ Hphys
    subst Hosafe
    wp_auto
    wp_apply raft.wp_load_leadC $$ Hphys as Hphys
    by_cases Hlead : s.lead = W64 0
    · rw [decide_eq_true Hlead]
      wp_auto
      iapply HΦ $$ %GoInterface.nil %s %false %c
      have Hs : s = { s with lead := W64 0 } := by cases s; simp_all
      iframe Hphys
      simp only [Bool.false_eq_true, ↓reduceIte]
      ipureintro
      refine ⟨?_, trivial⟩
      simp [FollowerStepResultC, MsgSnap, Hty, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat,
        MsgAppResp, MsgHeartbeatResp, MsgSnap, MsgPreVoteResp, MsgReadIndex, MsgReadIndexResp,
        MsgForgetLeader, MsgTransferLeader, MsgUnreachable, MsgSnapStatus, MsgTimeoutNow]
      exact Hs
    · rw [decide_eq_false Hlead]
      wp_auto
      wp_apply raft.wp_load_idC $$ Hphys as Hphys
      wp_apply raft.wp_load_leadC $$ Hphys as Hphys
      wp_apply raft.wp_load_TermC $$ Hphys as Hphys
      wp_raft_logC
      wp_apply raft.wp_store_leadC $$ Hphys as Hphys
      iapply HΦ $$ %GoInterface.nil %_ %false %c
      iframe Hphys
      simp only [Bool.false_eq_true, ↓reduceIte]
      ipureintro
      refine ⟨?_, trivial⟩
      simp [FollowerStepResultC, MsgSnap, Hty, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat,
        MsgAppResp, MsgHeartbeatResp, MsgSnap, MsgPreVoteResp, MsgReadIndex, MsgReadIndexResp,
        MsgForgetLeader, MsgTransferLeader, MsgUnreachable, MsgSnapStatus, MsgTimeoutNow]
  · -- `MsgTransferLeader` (2026-10-13): forwarded to the leader, if any; it is outside
    -- the model (`mtypeOf` is `none`), so nothing is queued abstractly
    obtain ⟨Htl, -⟩ := Hrest (Or.inl Hty)
    obtain ⟨Hterm0, Hents0, Hctx0⟩ := Htl Hty
    rw [Hty]
    simp only [MsgTransferLeader]
    wp_auto
    wp_apply raft.wp_load_leadC $$ Hphys as Hphys
    by_cases Hlead : s.lead = W64 0
    · rw [decide_eq_true Hlead]
      wp_auto
      wp_apply raft.wp_load_idC $$ Hphys as Hphys
      wp_apply raft.wp_load_TermC $$ Hphys as Hphys
      wp_raft_logC
      iapply HΦ $$ %GoInterface.nil %s %false %c
      iframe Hphys
      simp only [Bool.false_eq_true, ↓reduceIte]
      ipureintro
      refine ⟨?_, trivial⟩
      simp [FollowerStepResultC, MsgSnap, Hty, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat,
        MsgAppResp, MsgHeartbeatResp, MsgSnap, MsgPreVoteResp, MsgReadIndex, MsgReadIndexResp,
        MsgForgetLeader, MsgTransferLeader, MsgUnreachable, MsgSnapStatus, MsgTimeoutNow]
    · rw [decide_eq_false Hlead]
      wp_auto
      wp_apply raft.wp_load_leadC $$ Hphys as Hphys
      obtain ⟨Hterm0', Hlid⟩ := Hterm0.resolve_left Hlead
      wp_apply wp_raft_send _ _ _ _ { m with To' := s.lead } [] [] []
          (Or.inr (Or.inr (Or.inr Hty)))
          (Or.inr (Or.inr (Or.inl (Or.inr ⟨by rw [Hty]; rfl, Hterm0', fun h => Hlid h, rfl⟩))))
        $$ [$Hphys]
      · isplitr
        · rw [Hents0]; iapply ownSlice_nil
        isplitr
        · rw [Hctx0]; iapply ownSlice_nil
        iapply send_no_snap
        simp [Hty, MsgTransferLeader, MsgSnap]
      iintro Hphys
      ihave Hphys := ownRaftPhysC_unsend c r id s $$ Hphys
      wp_auto
      iapply HΦ $$ %GoInterface.nil %s %false %c
      iframe Hphys
      simp only [Bool.false_eq_true, ↓reduceIte]
      ipureintro
      refine ⟨?_, trivial⟩
      simp [FollowerStepResultC, MsgSnap, Hty, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat,
        MsgAppResp, MsgHeartbeatResp, MsgSnap, MsgPreVoteResp, MsgReadIndex, MsgReadIndexResp,
        MsgForgetLeader, MsgTransferLeader, MsgUnreachable, MsgSnapStatus, MsgTimeoutNow]
  · -- `MsgTimeoutNow` (2026-10-13): `hup(campaignTransfer)`, an ordinary campaign
    obtain ⟨-, Htn⟩ := Hrest (Or.inr Hty)
    obtain ⟨Hnw, Hwf⟩ := Htn Hty
    rw [Hty]
    simp only [MsgTimeoutNow]
    wp_auto
    wp_apply raft.wp_load_idC $$ Hphys as Hphys
    wp_apply raft.wp_load_TermC $$ Hphys as Hphys
    wp_raft_logC
    wp_apply wp_raft_hup c r id s _ Hnw
        (fun h => by simp [campaignTransfer, campaignPreElection] at h) Hwf
      $$ [$Hphys] as %s' ⟨Hphys, %Hok⟩
    iapply HΦ $$ %GoInterface.nil %s' %false %c
    iframe Hphys
    simp only [Bool.false_eq_true, ↓reduceIte]
    ipureintro
    refine ⟨?_, trivial⟩
    simp only [FollowerStepResultC, Hty, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat,
        MsgAppResp, MsgHeartbeatResp, MsgSnap, MsgPreVoteResp, MsgReadIndex, MsgReadIndexResp,
        MsgForgetLeader, MsgTransferLeader, MsgUnreachable, MsgSnapStatus, MsgTimeoutNow, W32]
    simp
    exact Hok
  · -- `MsgUnreachable` (2026-10-13): no arm
    rw [Hty]
    simp only [MsgUnreachable]
    wp_auto
    iapply HΦ $$ %GoInterface.nil %s %false %c
    iframe Hphys
    simp only [Bool.false_eq_true, ↓reduceIte]
    ipureintro
    refine ⟨?_, trivial⟩
    simp [FollowerStepResultC, MsgSnap, Hty, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat,
        MsgAppResp, MsgHeartbeatResp, MsgSnap, MsgPreVoteResp, MsgReadIndex, MsgReadIndexResp,
        MsgForgetLeader, MsgTransferLeader, MsgUnreachable, MsgSnapStatus, MsgTimeoutNow]
  · -- `MsgSnapStatus` (2026-10-13): no arm
    rw [Hty]
    simp only [MsgSnapStatus]
    wp_auto
    iapply HΦ $$ %GoInterface.nil %s %false %c
    iframe Hphys
    simp only [Bool.false_eq_true, ↓reduceIte]
    ipureintro
    refine ⟨?_, trivial⟩
    simp [FollowerStepResultC, MsgSnap, Hty, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat,
        MsgAppResp, MsgHeartbeatResp, MsgSnap, MsgPreVoteResp, MsgReadIndex, MsgReadIndexResp,
        MsgForgetLeader, MsgTransferLeader, MsgUnreachable, MsgSnapStatus, MsgTimeoutNow]

end proof

end EtcdGrove
end Perennial
