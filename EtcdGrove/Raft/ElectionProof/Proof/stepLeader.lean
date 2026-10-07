/-
Port of `election_proof/proof_stepLeader.v`.
-/
import EtcdGrove.Raft.ElectionProof.Spec.stepLeader
import EtcdGrove.Raft.ElectionProof.Spec.raft__bcastHeartbeat
import EtcdGrove.Raft.ElectionProof.Spec.raft__sendAppend
import EtcdGrove.Raft.ElectionProof.Spec.raft__maybeSendAppend
import EtcdGrove.Raft.ElectionProof.Spec.raft__bcastAppend
import EtcdGrove.Raft.ElectionProof.Spec.raft__appendEntry
import EtcdGrove.Raft.ElectionProof.Spec.raft__maybeCommit
import EtcdGrove.Raft.ElectionProof.Spec.releasePendingReadIndexMessages
import EtcdGrove.Raft.ElectionProof.Spec.Progress__MaybeUpdate
import EtcdGrove.Raft.ElectionProof.Spec.Progress__MaybeDecrTo
import EtcdGrove.Raft.ElectionProof.Spec.Progress__BecomeProbe
import EtcdGrove.Raft.ElectionProof.Spec.Progress__BecomeReplicate
import EtcdGrove.Raft.ElectionProof.Spec.Progress__CanBumpCommit
import EtcdGrove.Raft.ElectionProof.Spec.Inflights__FreeLE
import EtcdGrove.Raft.ElectionProof.Spec.raftLog__findConflictByTerm
import EtcdGrove.Raft.ElectionProof.Spec.raftLog__lastIndex
import EtcdGrove.Raft.ElectionProof.Spec.raftLog__firstIndex

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

variable (cfg : GSet w64)

set_option pp.maxSteps 10000000

/-- A list written back at the element it holds. -/
private theorem list_set_self {A : Type} (l : List A) (i : Int) (x : A)
    (H : l[i.toNat]? = some x) : l.set i.toNat x = l := by
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.1 H
  rw [← hget]; exact List.set_getElem_self hlt

/-- One peer's `Progress`, borrowed out of a struct whose `Progress` values are `pvs`
and given back at new values, keeping the state of the shape `{ s with prvals := _ }`
(so that a run of writes does not pile up record updates). -/
private theorem ownRaftPhys_pr_at (r : Loc) (id : w64) (s : NState) (pvs : GMap w64 Progress)
    (to : w64) (pr : Loc) (p : Progress) :
    ⊢ ownRaftPhys (GF := GF) cfg r id { s with prvals := pvs } -∗
      ⌜s.progress !! to = some pr⌝ -∗
      ⌜pvs !! to = some p⌝ -∗
      ownProgress pr p ∗
      (∀ p', ownProgress pr p' -∗
         ownRaftPhys cfg r id { s with prvals := <[to := p']> pvs }) := by
  iintro Hphys %Hlk %Hv
  icases ownRaftPhys_pr_upd cfg r id { s with prvals := pvs } to pr p $$ Hphys %Hlk %Hv
    with ⟨Hp, Hback⟩
  iframe Hp
  iintro %p' Hp
  iapply Hback $$ %p' Hp

private theorem ownRaftPhys_ins_id (r : Loc) (id : w64) (s : NState) (pvs : GMap w64 Progress)
    (k : w64) (a : Progress) (Hk : pvs !! k = some a) :
    ⊢ ownRaftPhys (GF := GF) cfg r id { s with prvals := <[k := a]> pvs } -∗
      ownRaftPhys cfg r id { s with prvals := pvs } := by
  rw [GMap.insert_id pvs k a Hk]
  iintro H; iexact H

private theorem ownRaftPhys_prvals_self (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhys (GF := GF) cfg r id s -∗ ownRaftPhys cfg r id { s with prvals := s.prvals } := by
  iintro H; iexact H

private theorem sendMsgs_nil_prvals (s : NState) (pvs : GMap w64 Progress) :
    { sendMsgs s [] with prvals := pvs } = { s with prvals := pvs } := by
  simp [sendMsgs]

/-- **`MsgVoteResp`, `MsgApp`, `MsgHeartbeat`, `MsgPreVoteResp`**: both switches fall
through, whether or not the sender has a `Progress`. -/
private theorem wp_stepLeader_noop (r : Loc) (id : w64) (s : NState) (m : raftpb.Message)
    (Hty : m.Type' = MsgVoteResp ∨ m.Type' = MsgApp ∨
      m.Type' = MsgHeartbeat ∨ m.Type' = MsgPreVoteResp) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhys cfg r id s }}
      (App (App (Val #(functions stepLeader [])) (Val #r)) (Val #m))
    {{ (err : GoInterface) (s' : NState), RET #err;
        ownRaftPhys cfg r id s' ∗ ⌜err = interface.nil⌝ ∗
        ⌜LeaderNonpropResult cfg id s m s'⌝ }} := by
  wp_start as Hphys
  wp_auto
  have Hres : LeaderNonpropResult cfg id s m s := Or.inl ⟨Hty, rfl⟩
  rcases Hty with Hl | Hl | Hl | Hl
  all_goals
    first
    | simp only [Hl, MsgVoteResp] | simp only [Hl, MsgApp] | simp only [Hl, MsgHeartbeat]
    | simp only [Hl, MsgPreVoteResp]
    wp_auto
    icases ownRaftPhys_tracker_same cfg r id s $$ Hphys with ⟨%tv, Htrkf, Htrk, Hback⟩
    icases ownTracker_progress_map cfg tv _ $$ Htrk with ⟨#Hprs, -, Htrk⟩
    wp_auto
    ihave Hphys := Hback $$ Htrkf Htrk
    wp_apply wp_map_lookup1 go.uint64 (go.GoType.PointerType tracker.Progress.ty) _ s.progress
      m.From' _ $$ Hprs with -
    wp_if_destruct
    · -- no `Progress` for the sender: `Debugf`, return
      wp_apply raft.wp_load_id $$ Hphys as Hphys
      wp_raft_log
      iapply HΦ
      iframe Hphys
      ipureintro
      exact ⟨rfl, Hres⟩
    · first
      | simp only [Hl, MsgVoteResp] | simp only [Hl, MsgApp] | simp only [Hl, MsgHeartbeat]
      | simp only [Hl, MsgPreVoteResp]
      wp_auto
      iapply HΦ
      iframe Hphys
      ipureintro
      exact ⟨rfl, Hres⟩

/-- **`MsgBeat`**: `bcastHeartbeat`, return. -/
private theorem wp_stepLeader_beat
    (wp_raft_bcastHeartbeat : raft.bcastHeartbeat.spec (GF := GF) (hG := hG))
    (r : Loc) (id : w64) (s : NState) (m : raftpb.Message)
    (Hty : m.Type' = MsgBeat) (Hlead : s.role = .leader) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhys cfg r id s }}
      (App (App (Val #(functions stepLeader [])) (Val #r)) (Val #m))
    {{ (err : GoInterface) (s' : NState), RET #err;
        ownRaftPhys cfg r id s' ∗ ⌜err = interface.nil⌝ ∗
        ⌜LeaderNonpropResult cfg id s m s'⌝ }} := by
  wp_start as Hphys
  wp_auto
  simp only [Hty, MsgBeat]
  wp_auto
  wp_apply wp_raft_bcastHeartbeat cfg r id s Hlead $$ [$Hphys] as %ms %pvs ⟨Hphys, %Hms, %Hmm⟩
  iapply HΦ
  iframe Hphys
  ipureintro
  exact ⟨rfl, Or.inr (Or.inl ⟨Hty, ms, pvs, rfl, Hms, Hmm⟩)⟩

/-- **`MsgHeartbeatResp`** -/
private theorem wp_stepLeader_hbresp
    (wp_raft_sendAppend : raft.sendAppend.spec (GF := GF) (hG := hG))
    (wp_raftLog_lastIndex : raftLog.lastIndex.spec (GF := GF) (hG := hG))
    (r : Loc) (id : w64) (s : NState) (m : raftpb.Message)
    (Hty : m.Type' = MsgHeartbeatResp) (Hlead : s.role = .leader) (Hself : m.From' ≠ id) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhys cfg r id s ∗
        m.Context' ↦*□ ([] : List w8) }}
      (App (App (Val #(functions stepLeader [])) (Val #r)) (Val #m))
    {{ (err : GoInterface) (s' : NState), RET #err;
        ownRaftPhys cfg r id s' ∗ ⌜err = interface.nil⌝ ∗
        ⌜LeaderNonpropResult cfg id s m s'⌝ }} := by
  wp_start as ⟨Hphys, #Hctx⟩
  wp_auto
  simp only [Hty, MsgHeartbeatResp]
  wp_auto
  icases ownRaftPhys_tracker_same cfg r id s $$ Hphys with ⟨%tv, Htrkf, Htrk, Hback⟩
  icases ownTracker_progress_map cfg tv _ $$ Htrk with ⟨#Hprs, %Hdom, Htrk⟩
  icases ownTracker_prvals_dom cfg tv _ $$ Htrk with ⟨%Hpdom, Htrk⟩
  dsimp only at Hdom Hpdom
  wp_auto
  ihave Hphys := Hback $$ Htrkf Htrk
  wp_apply wp_map_lookup1 go.uint64 (go.GoType.PointerType tracker.Progress.ty) _ s.progress
    m.From' _ $$ Hprs with -
  cases Hlk : s.progress !! m.From' with
  | none =>
    -- no `Progress` for the sender
    simp only [Option.getD_none]
    wp_auto
    wp_apply raft.wp_load_id $$ Hphys as Hphys
    wp_raft_log
    iapply HΦ $$ %interface.nil %s
    iframe Hphys
    ipureintro
    refine ⟨rfl, Or.inr (Or.inr (Or.inl ⟨Hty, [], s.prvals, ?_, fun _ h => absurd h List.not_mem_nil, rfl⟩))⟩
    simp [sendMsgs]
  | some pr =>
  simp only [Option.getD_some]
  have Hfcfg : m.From' ∈ cfg := by rw [← Hdom, GMap.elem_of_dom]; exact ⟨pr, Hlk⟩
  obtain ⟨p, Hpvs⟩ : ∃ p, s.prvals !! m.From' = some p := by
    rw [← GMap.elem_of_dom, Hpdom, GMap.elem_of_dom]; exact ⟨pr, Hlk⟩
  ihave Hphys := ownRaftPhys_prvals_self cfg r id s $$ Hphys
  icases ownRaftPhys_pr_at cfg r id s s.prvals m.From' pr p $$ Hphys %Hlk %Hpvs with ⟨Hpa, Hpback⟩
  iNamed Hpa
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hpv
  wp_if_destruct
  · exact absurd rfl Hnn
  simp only [Hty, MsgHeartbeatResp]
  wp_auto
  trace_state
  sorry

/-- **`MsgAppResp`** -/
private theorem wp_stepLeader_appresp
    (wp_raft_sendAppend : raft.sendAppend.spec (GF := GF) (hG := hG))
    (wp_raft_maybeSendAppend : raft.maybeSendAppend.spec (GF := GF) (hG := hG))
    (wp_raft_bcastAppend : raft.bcastAppend.spec (GF := GF) (hG := hG))
    (wp_raft_maybeCommit : raft.maybeCommit.spec (GF := GF) (hG := hG))
    (wp_releasePendingReadIndexMessages :
      releasePendingReadIndexMessages.spec (GF := GF) (hG := hG))
    (wp_Progress_MaybeUpdate : tracker.Progress.MaybeUpdate.spec (GF := GF) (hG := hG))
    (wp_Progress_MaybeDecrTo : tracker.Progress.MaybeDecrTo.spec (GF := GF) (hG := hG))
    (wp_Progress_BecomeProbe : tracker.Progress.BecomeProbe.spec (GF := GF) (hG := hG))
    (wp_Progress_BecomeReplicate :
      tracker.Progress.BecomeReplicate.spec (GF := GF) (hG := hG))
    (wp_Progress_CanBumpCommit : tracker.Progress.CanBumpCommit.spec (GF := GF) (hG := hG))
    (wp_Inflights_FreeLE : tracker.Inflights.FreeLE.spec (GF := GF) (hG := hG))
    (wp_raftLog_findConflictByTerm : raftLog.findConflictByTerm.spec (GF := GF) (hG := hG))
    (wp_raftLog_lastIndex : raftLog.lastIndex.spec (GF := GF) (hG := hG))
    (wp_raftLog_firstIndex : raftLog.firstIndex.spec (GF := GF) (hG := hG))
    (r : Loc) (id : w64) (s : NState) (m : raftpb.Message)
    (Hty : m.Type' = MsgAppResp) (Hlead : s.role = .leader) (Hid : id ∈ cfg)
    (Hfrom0 : m.From' ≠ W64 0) (Hself : m.Reject' = true → m.From' ≠ id) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhys cfg r id s }}
      (App (App (Val #(functions stepLeader [])) (Val #r)) (Val #m))
    {{ (err : GoInterface) (s' : NState), RET #err;
        ownRaftPhys cfg r id s' ∗ ⌜err = interface.nil⌝ ∗
        ⌜LeaderNonpropResult cfg id s m s'⌝ }} := by
  sorry

/-- **`MsgProp`**

`len(m.Entries) == 0` is false (`ents ≠ []`); `r.trk.Progress[r.id]` is a hit
(`id ∈ cfg`, and a `Progress` pointer is never nil); `r.leadTransferee` is `0`; the
conf-change loop reads each entry's `Type` -- `EntryNormal`, so neither `Unmarshal` arm
runs and `cc` stays nil -- and writes nothing. Then `appendEntry` stamps the batch and,
if it accepts it, `bcastAppend`. -/
private theorem wp_stepLeader_prop
    (wp_raft_bcastAppend : raft.bcastAppend.spec (GF := GF) (hG := hG))
    (wp_raft_appendEntry : raft.appendEntry.spec (GF := GF) (hG := hG))
    (r : Loc) (id : w64) (s : NState) (m : raftpb.Message) (ents : List raftpb.Entry)
    (Hty : m.Type' = MsgProp) (Hid : id ∈ cfg) (Hne : ents ≠ [])
    (Hnorm : ∀ e ∈ ents, e.Type' = EntryNormal) (Hsmall : (ents.length : Int) < 2^61) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhys cfg r id s ∗
        m.Entries' ↦* ents }}
      (App (App (Val #(functions stepLeader [])) (Val #r)) (Val #m))
    {{ (err : GoInterface) (s' : NState) (dropped : Bool), RET #err;
        ownRaftPhys cfg r id s' ∗
        ⌜LeaderProposeResult id s ents dropped s'⌝ ∗
        (if dropped then globalAddr ErrProposalDropped ↦□ err
         else ⌜err = interface.nil⌝) ∗
        m.Entries' ↦* ents.mapIdx (stamp s.term (logLast s.logst)) }} := by
  wp_start as ⟨Hphys, Hes⟩
  ihave #Hinit := isInitialized_access $$ Hpkg
  unfold isInitialized
  icases Hinit with ⟨%e1, %e2, %e3, %e4, %errPropDropped, %gr, #Hinit⟩
  iNamed Hinit
  wp_auto
  simp only [Hty, MsgProp]
  wp_auto
  ihave %Hl := ownSlice_len _ _ _ $$ Hes
  wp_if_destruct
  · exfalso
    apply Hne
    apply List.eq_nil_of_length_eq_zero
    rw [Hl.1, Hif]; rfl
  wp_apply raft.wp_load_id $$ Hphys as Hphys
  icases ownRaftPhys_tracker_same cfg r id s $$ Hphys with ⟨%tv, Htrkf, Htrk, Hback⟩
  icases ownTracker_progress_map cfg tv _ $$ Htrk with ⟨#Hprs, %Hdom, Htrk⟩
  icases ownTracker_prvals_dom cfg tv _ $$ Htrk with ⟨%Hpdom, Htrk⟩
  dsimp only at Hdom Hpdom
  wp_auto
  ihave Hphys := Hback $$ Htrkf Htrk
  wp_apply wp_map_lookup1 go.uint64 (go.GoType.PointerType tracker.Progress.ty) _ s.progress
    id _ $$ Hprs with -
  obtain ⟨pr, Hlk⟩ : ∃ pr, s.progress !! id = some pr := by
    rw [← GMap.elem_of_dom, Hdom]; exact Hid
  obtain ⟨p, Hpvs⟩ : ∃ p, s.prvals !! id = some p := by
    rw [← GMap.elem_of_dom, Hpdom, GMap.elem_of_dom]; exact ⟨pr, Hlk⟩
  icases ownRaftPhys_pr cfg r id s id pr p $$ Hphys %Hlk %Hpvs with ⟨Hpa, Hpback⟩
  iNamed Hpa
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hpv
  ihave Hphys := Hpback $$ [Hpv Hinfl]
  · iapply ownProgress_intro $$ Hpv Hinfl %Habs
  rw [Hlk]
  simp only [Option.getD_some]
  wp_if_destruct
  · exact absurd rfl Hnn
  wp_apply raft.wp_load_leadTransferee $$ Hphys as Hphys
  rename_i gi_ptr
  irename : (gi_ptr ↦ zero_val w64 : IProp GF) => Hgi
  ihave IH : iprop(∃ (n k : w64),
      "Hj" ∷ i_ptr ↦ n ∗
      "Hgi" ∷ gi_ptr ↦ k ∗
      "Hes" ∷ m.Entries' ↦* ents ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (ents.length : Int)⌝) $$ [i Hgi Hes]
  · iexists W64 0, zero_val w64
    iframe
    ipureintro
    word
  wp_for IH
  wp_if_destruct
  · list_elem ents (sint.nat n) as e
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by word))]
    wp_apply wp_load_slice_index _ (sint.Z n) ents (DFrac.own 1) e Hn.1 $$ [Hes] with Hes
    · iframe
      ipureintro
      exact He_lookup
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by word))]
    icases ownSlice_elem_acc (sint.Z n) e _ (DFrac.own 1) ents Hn.1 He_lookup $$ Hes
      with ⟨He, Hesback⟩
    have Hety : e.Type' = EntryNormal := Hnorm e (List.mem_of_getElem? He_lookup)
    wp_auto
    simp only [Hety, EntryNormal]
    wp_auto
    simp only [Hety, EntryNormal]
    wp_auto
    ihave Hes := Hesback $$ %e He
    rw [list_set_self ents (sint.Z n) e He_lookup]
    wp_for_post
    iframe
    iexists n + W64 1, n
    iframe
    ipureintro
    word
  · wp_apply wp_raft_appendEntry cfg r id s _ ents Hnorm Hsmall $$ [$Hphys $Hes]
      as %acc ⟨-, Hes, Hphys⟩
    cases acc <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · -- dropped
      wp_auto
      iapply HΦ $$ %errPropDropped %s %true
      iframe Hphys Hes
      isplitr
      · ipureintro
        simp [LeaderProposeResult]
      simp only [↓reduceIte]
      iexact ErrPropDropped
    · wp_auto
      wp_apply wp_raft_bcastAppend $$ [$Hphys] as %ms %pvs ⟨Hphys, %Hms, %Hmm⟩
      iapply HΦ $$ %interface.nil %_ %false
      iframe Hphys Hes
      isplitr
      · ipureintro
        simp only [LeaderProposeResult, Bool.false_eq_true, ↓reduceIte]
        exact ⟨ms, pvs, rfl, Hms, Hmm⟩
      · simp only [Bool.false_eq_true, ↓reduceIte]
        ipureintro; trivial

/-- By the message type, one lemma each. The non-`MsgProp` lemmas are stated at
`LeaderNonpropResult` with `err = nil`; `HΦ'` turns that into the postcondition with
`dropped = false`. -/
theorem stepLeader.wp_proof
    (wp_raft_bcastHeartbeat : raft.bcastHeartbeat.spec (GF := GF) (hG := hG))
    (wp_raft_sendAppend : raft.sendAppend.spec (GF := GF) (hG := hG))
    (wp_raft_maybeSendAppend : raft.maybeSendAppend.spec (GF := GF) (hG := hG))
    (wp_raft_bcastAppend : raft.bcastAppend.spec (GF := GF) (hG := hG))
    (wp_raft_appendEntry : raft.appendEntry.spec (GF := GF) (hG := hG))
    (wp_raft_maybeCommit : raft.maybeCommit.spec (GF := GF) (hG := hG))
    (wp_releasePendingReadIndexMessages :
      releasePendingReadIndexMessages.spec (GF := GF) (hG := hG))
    (wp_Progress_MaybeUpdate : tracker.Progress.MaybeUpdate.spec (GF := GF) (hG := hG))
    (wp_Progress_MaybeDecrTo : tracker.Progress.MaybeDecrTo.spec (GF := GF) (hG := hG))
    (wp_Progress_BecomeProbe : tracker.Progress.BecomeProbe.spec (GF := GF) (hG := hG))
    (wp_Progress_BecomeReplicate :
      tracker.Progress.BecomeReplicate.spec (GF := GF) (hG := hG))
    (wp_Progress_CanBumpCommit : tracker.Progress.CanBumpCommit.spec (GF := GF) (hG := hG))
    (wp_Inflights_FreeLE : tracker.Inflights.FreeLE.spec (GF := GF) (hG := hG))
    (wp_raftLog_findConflictByTerm : raftLog.findConflictByTerm.spec (GF := GF) (hG := hG))
    (wp_raftLog_lastIndex : raftLog.lastIndex.spec (GF := GF) (hG := hG))
    (wp_raftLog_firstIndex : raftLog.firstIndex.spec (GF := GF) (hG := hG)) :
    stepLeader.spec (GF := GF) (hG := hG) := by
  intro cfg r id s m ents Hty Hlead Hid Hfrom0 Hself Hprop
  iintro %Φ ⟨#Hinit, Hphys, Hctx, Hents⟩ HΦ
  by_cases Hp : m.Type' = MsgProp
  · obtain ⟨Hne, Hnorm, Hsmall⟩ := Hprop Hp
    ihave Hes := Hents $$ %Hp
    iapply wp_stepLeader_prop cfg wp_raft_bcastAppend wp_raft_appendEntry r id s m ents Hp Hid
      Hne Hnorm Hsmall $$ [Hphys Hes]
    · iframe
      iexact Hinit
    inext
    iintro %err %s' %dropped ⟨Hphys, %Hres, Herr, Hes⟩
    iapply HΦ
    iframe Hphys Herr
    isplitr
    · ipureintro
      simp only [LeaderStepResult, Hp, ↓reduceIte]
      exact Hres
    · iintro -
      iexact Hes
  ihave HΦ' : iprop(▷ ∀ (err : GoInterface) (s' : NState),
      ownRaftPhys cfg r id s' ∗ ⌜err = interface.nil⌝ ∗
      ⌜LeaderNonpropResult cfg id s m s'⌝ -∗ Φ #err) $$ [HΦ]
  · inext
    iintro %err %s' ⟨Hphys, %Herr, %Hres⟩
    iapply HΦ $$ %err %s' %false
    iframe Hphys
    isplitr
    · ipureintro
      simp only [LeaderStepResult, Hp, ↓reduceIte]
      exact ⟨trivial, Hres⟩
    isplitr
    · simp only [Bool.false_eq_true, ↓reduceIte]
      ipureintro; exact Herr
    · iintro %Hc
      exact absurd Hc Hp
  rcases Hty with Hty | Hty | Hty | Hty | Hty | Hty | Hty | Hty
  · iapply wp_stepLeader_noop cfg r id s m (Or.inl Hty) $$ [Hphys] HΦ'
    iframe
    iexact Hinit
  · iapply wp_stepLeader_beat cfg wp_raft_bcastHeartbeat r id s m Hty Hlead $$ [Hphys] HΦ'
    iframe
    iexact Hinit
  · ihave #Hc := Hctx $$ %Hty
    iapply wp_stepLeader_hbresp cfg wp_raft_sendAppend wp_raftLog_lastIndex r id s m Hty Hlead
      (Hself (Or.inl Hty)) $$ [Hphys] HΦ'
    iframe
    iframe Hinit Hc
  · iapply wp_stepLeader_appresp cfg wp_raft_sendAppend wp_raft_maybeSendAppend
      wp_raft_bcastAppend wp_raft_maybeCommit wp_releasePendingReadIndexMessages
      wp_Progress_MaybeUpdate wp_Progress_MaybeDecrTo wp_Progress_BecomeProbe
      wp_Progress_BecomeReplicate wp_Progress_CanBumpCommit wp_Inflights_FreeLE
      wp_raftLog_findConflictByTerm wp_raftLog_lastIndex wp_raftLog_firstIndex
      r id s m Hty Hlead Hid (Hfrom0 Hty) (fun Hr => Hself (Or.inr ⟨Hty, Hr⟩)) $$ [Hphys] HΦ'
    iframe
    iexact Hinit
  · exact absurd Hty Hp
  · iapply wp_stepLeader_noop cfg r id s m (Or.inr (Or.inl Hty)) $$ [Hphys] HΦ'
    iframe
    iexact Hinit
  · iapply wp_stepLeader_noop cfg r id s m (Or.inr (Or.inr (Or.inl Hty))) $$ [Hphys] HΦ'
    iframe
    iexact Hinit
  · iapply wp_stepLeader_noop cfg r id s m (Or.inr (Or.inr (Or.inr Hty))) $$ [Hphys] HΦ'
    iframe
    iexact Hinit

end proof

end EtcdGrove
end Perennial
