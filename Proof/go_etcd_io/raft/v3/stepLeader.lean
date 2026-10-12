/-
Port of `election_proof/proof_stepLeader.v`.

Lean notes: the Rocq `wp_wand`/`wp_if_join` joins are `wp_join … at next` (or
`at (If _ (Val #true) _)` for the `||` of `MaybeUpdate`); Rocq's `set … ; clearbody` of the
`Progress` maps is `generalize`. The type switches are decided by rewriting `m.Type'` to
its literal (`simp only [Hty, MsgX]`) rather than by `bool_decide_eq_false_2`. The Rocq
helper lemmas `commit_same`, `commit_same_nil`, `send_msgs_app2`, `become_probe_match`,
`maybe_update_match` and `repl_sends_eq` are not needed separately (the equalities are
closed inline by `simp [sendMsgs]`, `rfl`, `replSends_prvals`/`replSends_send_prvals`);
`list_set_self` (an element written back at itself) is new.
-/
module

public import Spec.go_etcd_io.raft.v3.stepLeader
public import Spec.go_etcd_io.raft.v3.raft__bcastHeartbeat
public import Spec.go_etcd_io.raft.v3.raft__sendAppend
public import Spec.go_etcd_io.raft.v3.raft__maybeSendAppend
public import Spec.go_etcd_io.raft.v3.raft__bcastAppend
public import Spec.go_etcd_io.raft.v3.raft__appendEntry
public import Spec.go_etcd_io.raft.v3.raft__maybeCommit
public import Spec.go_etcd_io.raft.v3.releasePendingReadIndexMessages
public import Spec.go_etcd_io.raft.v3.tracker.Progress__MaybeUpdate
public import Spec.go_etcd_io.raft.v3.tracker.Progress__MaybeDecrTo
public import Spec.go_etcd_io.raft.v3.tracker.Progress__BecomeProbe
public import Spec.go_etcd_io.raft.v3.tracker.Progress__BecomeReplicate
public import Spec.go_etcd_io.raft.v3.tracker.Progress__CanBumpCommit
public import Spec.go_etcd_io.raft.v3.tracker.Inflights__FreeLE
public import Spec.go_etcd_io.raft.v3.raftLog__findConflictByTerm
public import Spec.go_etcd_io.raft.v3.raftLog__lastIndex
public import Spec.go_etcd_io.raft.v3.raftLog__firstIndex

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

variable (cfg : GSet w64)

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

/-- `Match` under `MaybeDecrTo`. -/
private theorem decrTo_match (p : Progress) (a b : w64) :
    (progressMaybeDecrTo p a b).2.matched = p.matched := by
  unfold progressMaybeDecrTo
  repeat' split
  all_goals rfl

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
    (Hty : m.Type' = MsgHeartbeatResp) (_Hlead : s.role = .leader) (Hself : m.From' ≠ id) :
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
  -- `pr.RecentActive = true; pr.MsgAppFlowPaused = false` (`RecentActive` is in no record)
  have Habs' := (progressAbs_Some _ _ _).1 Habs
  ihave Hphys := Hpback $$ %{ p with paused := false } [Hpv Hinfl]
  · iapply ownProgress_intro pr _ { p with paused := false } $$ Hpv Hinfl
    ipureintro
    obtain ⟨H1, H2, H3, H4, H5, H6, -, -⟩ := Habs'
    exact (progressAbs_Some _ _ _).2 ⟨H1, H2, H3, H4, H5, H6, rfl, rfl⟩
  have Hmm1 : prvalsMatch (<[m.From' := { p with paused := false }]> s.prvals)
      = prvalsMatch s.prvals := prvalsMatch_insert_same _ _ p _ Hpvs rfl
  generalize Hp1 : ({ p with paused := false } : Progress) = p1 at *
  generalize Hpvs1 : (<[m.From' := p1]> s.prvals : GMap w64 Progress) = pvs1 at *
  have Hpvs1' : pvs1 !! m.From' = some p1 := by rw [← Hpvs1]; exact GMap.lookup_insert_eq _ _ _
  -- `if pr.Match < r.raftLog.lastIndex() || pr.State == StateProbe { r.sendAppend(m.From) }`,
  -- joined
  wp_join iprop(∃ (ms : List Msg) (pvs : GMap w64 Progress),
      "Hphys" ∷ ownRaftPhys cfg r id { sendMsgs s ms with prvals := pvs } ∗
      "%Hms" ∷ ⌜ReplSends id s ms⌝ ∗
      "%Hmm" ∷ ⌜prvalsMatch pvs = prvalsMatch s.prvals⌝ ∗
      "m" ∷ m_ptr ↦ m ∗ "r" ∷ r_ptr ↦ r ∗ "pr" ∷ pr_ptr ↦ pr) at next
    with [Hphys m r pr] as HR
  · wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
    icases ownRaftPhys_log_same cfg r id _ $$ Hphys with ⟨Hlog, Hlogback⟩
    wp_apply wp_raftLog_lastIndex $$ [$Hlog] as %li ⟨Hlog, %Hli⟩
    ihave Hphys := Hlogback $$ Hlog
    wp_if_destruct
    · -- behind
      wp_apply wp_raft_sendAppend cfg r id _ m.From' Hself Hfcfg $$ [$Hphys]
        as %ms %pvs ⟨Hphys, %Hms, %Hmm⟩
      wp_join_done
      iexists ms, pvs
      iframe
      ipureintro
      exact ⟨(replSends_prvals id s pvs1 ms).1 Hms, Hmm.trans Hmm1⟩
    icases ownRaftPhys_pr cfg r id _ m.From' pr p1 $$ Hphys %Hlk %Hpvs1' with ⟨Hpa, Hpback⟩
    iNamed Hpa
    wp_auto
    ihave Hphys := Hpback $$ [Hpv Hinfl]
    · iapply ownProgress_intro $$ Hpv Hinfl %Habs
    wp_if_destruct
    · -- probing
      wp_apply wp_raft_sendAppend cfg r id _ m.From' Hself Hfcfg $$ [$Hphys]
        as %ms %pvs ⟨Hphys, %Hms, %Hmm⟩
      wp_join_done
      iexists ms, pvs
      iframe
      ipureintro
      exact ⟨(replSends_prvals id s pvs1 ms).1 Hms, Hmm.trans Hmm1⟩
    ·
      wp_join_done
      iexists [], pvs1
      rw [sendMsgs_nil_prvals]
      iframe
      ipureintro
      exact ⟨fun _ h => absurd h List.not_mem_nil, Hmm1⟩
  iNamed HR
  -- `if r.readOnly.option != ReadOnlySafe || len(m.Context) == 0 { return nil }`
  icases ownRaftPhys_readOnly cfg r id _ $$ Hphys with ⟨%ro, %rr, %Hpend, Hrof, Hro, Hback⟩
  icases ownReadOnly_option ro rr $$ Hro with ⟨%o, Hopt, Hroback⟩
  wp_auto
  ihave Hro := Hroback $$ Hopt
  ihave Hphys := Hback $$ %ro %rr %Hpend Hrof Hro
  ihave %Hcl := ownSlice_len _ _ _ $$ Hctx
  have Hcz : m.Context'.len = W64 0 := by simp only [List.length_nil] at Hcl; word
  ihave HΦ : iprop(Φ #interface.nil) $$ [HΦ Hphys]
  · iapply HΦ $$ %interface.nil %{ sendMsgs s ms with prvals := pvs }
    iframe Hphys
    ipureintro
    exact ⟨rfl, Or.inr (Or.inr (Or.inl ⟨Hty, ms, pvs, rfl, Hms, Hmm⟩))⟩
  by_cases Ho : o = W64 0
  · simp only [Ho, decide_true, Bool.not_true]
    wp_auto
    rw [Hcz]
    wp_auto
    iexact HΦ
  · simp only [Ho, decide_false, Bool.not_false]
    wp_auto
    iexact HΦ

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
    (_wp_raftLog_lastIndex : raftLog.lastIndex.spec (GF := GF) (hG := hG))
    (wp_raftLog_firstIndex : raftLog.firstIndex.spec (GF := GF) (hG := hG))
    (r : Loc) (id : w64) (s : NState) (m : raftpb.Message)
    (Hty : m.Type' = MsgAppResp) (Hlead : s.role = .leader) (Hid : id ∈ cfg)
    (Hfrom0 : m.From' ≠ W64 0) (Hself : m.Reject' = true → m.From' ≠ id) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhys cfg r id s }}
      (App (App (Val #(functions stepLeader [])) (Val #r)) (Val #m))
    {{ (err : GoInterface) (s' : NState), RET #err;
        ownRaftPhys cfg r id s' ∗ ⌜err = interface.nil⌝ ∗
        ⌜LeaderNonpropResult cfg id s m s'⌝ }} := by
  wp_start as Hphys
  wp_auto
  simp only [Hty, MsgAppResp]
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
    refine ⟨rfl, Or.inr (Or.inr (Or.inr ⟨Hty, Or.inl ⟨?_, rfl⟩⟩))⟩
    rw [GMap.elem_of_dom]; rintro ⟨v, hv⟩; rw [Hlk] at hv; cases hv
  | some pr =>
  simp only [Option.getD_some]
  have Hfcfg : m.From' ∈ cfg := by rw [← Hdom, GMap.elem_of_dom]; exact ⟨pr, Hlk⟩
  have Hfdom : m.From' ∈ domSet s.progress := by rw [GMap.elem_of_dom]; exact ⟨pr, Hlk⟩
  obtain ⟨p, Hpvs⟩ : ∃ p, s.prvals !! m.From' = some p := by
    rw [← GMap.elem_of_dom, Hpdom, GMap.elem_of_dom]; exact ⟨pr, Hlk⟩
  ihave Hphys := ownRaftPhys_prvals_self cfg r id s $$ Hphys
  icases ownRaftPhys_pr_at cfg r id s s.prvals m.From' pr p $$ Hphys %Hlk %Hpvs with ⟨Hpa, Hpback⟩
  iNamed Hpa
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hpv
  wp_if_destruct
  · exact absurd rfl Hnn
  simp only [Hty, MsgAppResp]
  wp_auto
  -- `pr.RecentActive = true`: the record is unchanged (`RecentActive` is in none)
  have Habs' := (progressAbs_Some _ _ _).1 Habs
  ihave Hphys := Hpback $$ %p [Hpv Hinfl]
  · iapply ownProgress_intro pr _ p $$ Hpv Hinfl
    ipureintro
    obtain ⟨H1, H2, H3, H4, H5, H6, H8, -⟩ := Habs'
    exact (progressAbs_Some _ _ _).2 ⟨H1, H2, H3, H4, H5, H6, H8, rfl⟩
  have Hmm1 : prvalsMatch (<[m.From' := p]> s.prvals)
      = prvalsMatch s.prvals := prvalsMatch_insert_same _ _ p _ Hpvs rfl
  generalize Hpvs1 : (<[m.From' := p]> s.prvals : GMap w64 Progress) = pvs1 at *
  have Hpvs1' : pvs1 !! m.From' = some p := by rw [← Hpvs1]; exact GMap.lookup_insert_eq _ _ _
  cases Hrej : m.Reject'
  · -- accepted
    wp_auto
    -- `pr.MaybeUpdate(m.Index) || (pr.Match == m.Index && pr.State == StateProbe)`: its
    -- value does not matter to the postcondition, only that `pr` is left at
    -- `MaybeUpdate`'s value
    icases ownRaftPhys_pr_at cfg r id s pvs1 m.From' pr p $$ Hphys %Hlk %Hpvs1' with ⟨Hpa, Hpback⟩
    wp_join (Q := fun v => iprop(∃ c : Bool, ⌜v = #c⌝ ∗
        ownProgress pr (progressMaybeUpdate p m.Index') ∗
        "m" ∷ m_ptr ↦ m ∗ "pr" ∷ pr_ptr ↦ pr)) at (If _ (Val #true) _) with [Hpa m pr]
    · wp_apply wp_Progress_MaybeUpdate $$ [$Hpa] as Hpa
      iNamed Hpa
      wp_if_destruct
      · iexists true
        iframe
        isplitr
        · ipureintro; rfl
        iapply ownProgress_intro $$ Hpv Hinfl %Habs
      wp_if_destruct
      · iexists _
        iframe
        isplitr
        · ipureintro; rfl
        iapply ownProgress_intro $$ Hpv Hinfl %Habs
      · iexists false
        iframe
        isplitr
        · ipureintro; rfl
        iapply ownProgress_intro $$ Hpv Hinfl %Habs
    iintro ⟨%c, %Hv, Hpa, m, pr⟩
    subst Hv
    ihave Hphys := Hpback $$ %(progressMaybeUpdate p m.Index') Hpa
    have Hx : prvalsMatch s.prvals !! m.From' = some p.matched := by
      simp only [prvalsMatch, GMap.fmap_eq, GMap.lookup_fmap, Hpvs]; rfl
    have Hmm2 : prvalsMatch (<[m.From' := progressMaybeUpdate p m.Index']> pvs1) =
        <[m.From' := if uint.Z p.matched < uint.Z m.Index' then m.Index' else p.matched]>
          (prvalsMatch s.prvals) := by
      have Hpm : (progressMaybeUpdate p m.Index').matched =
          if uint.Z p.matched < uint.Z m.Index' then m.Index' else p.matched := by
        unfold progressMaybeUpdate
        split <;> rfl
      rw [← Hmm1, ← Hpm]
      simp only [prvalsMatch, GMap.fmap_eq]
      exact GMap.fmap_insert _ _ _ _
    generalize Hp2 : progressMaybeUpdate p m.Index' = p2 at *
    generalize Hpvs2 : (<[m.From' := p2]> pvs1 : GMap w64 Progress) = pvs2 at *
    have Hpvs2' : pvs2 !! m.From' = some p2 := by rw [← Hpvs2]; exact GMap.lookup_insert_eq _ _ _
    cases c
    · -- nothing to do
      wp_auto
      iapply HΦ $$ %interface.nil %{ s with prvals := pvs2 }
      iframe Hphys
      ipureintro
      refine ⟨rfl, Or.inr (Or.inr (Or.inr ⟨Hty, Or.inr (Or.inr ⟨Hfdom, Hrej,
        p.matched, pvs2, s.logst.committed, [], Hx, Hmm2, Or.inl rfl,
        fun _ h => absurd h List.not_mem_nil, ?_⟩)⟩))⟩
      cases s; simp [sendMsgs]
    wp_auto
    -- the `switch` on `pr.State`, joined: `Match` does not move
    iNamed m
    iNamed pr
    wp_join iprop(∃ (p3 : Progress),
        "Hphys" ∷ ownRaftPhys cfg r id { s with prvals := <[m.From' := p3]> pvs2 } ∗
        "%Hm3" ∷ ⌜p3.matched = p2.matched⌝ ∗
        "m" ∷ m_ptr ↦ m ∗ "r" ∷ r_ptr ↦ r ∗ "pr" ∷ pr_ptr ↦ pr) at next
      with [Hphys m r pr] as HJ
    · icases ownRaftPhys_pr_at cfg r id s pvs2 m.From' pr p2 $$ Hphys %Hlk %Hpvs2'
        with ⟨Hpa, Hpback⟩
      iNamed Hpa
      have Habs2 := (progressAbs_Some _ _ _).1 Habs
      have Hst := Habs2.2.1
      have Hm := Habs2.2.2.1
      wp_auto
      rw [Hst]
      cases Hst2 : p2.state <;> simp only [prstateW64]
      · -- `StateProbe`: `BecomeReplicate`
        wp_auto
        ihave Hpa := ownProgress_intro pr _ p2 $$ Hpv Hinfl %Habs
        wp_apply wp_Progress_BecomeReplicate $$ [$Hpa] as Hpa
        ihave Hphys := Hpback $$ %(progressBecomeReplicate p2) Hpa
        wp_join_done
        iexists progressBecomeReplicate p2
        iframe
        ipureintro; rfl
      · -- `StateReplicate`: `pr.Inflights.FreeLE(m.Index)`
        wp_auto
        simp only [Hst, Hst2, prstateW64]
        wp_auto
        simp only [Hst, Hst2, prstateW64]
        wp_auto
        wp_apply wp_Inflights_FreeLE $$ [$Hinfl] as %i' ⟨Hinfl, -⟩
        have Habs3 : progressAbs pv i' = some { p2 with infl := i' } := by
          obtain ⟨A1, A2, A3, A4, A5, A6, A8, -⟩ := Habs2
          exact (progressAbs_Some _ _ _).2 ⟨A1, A2, A3, A4, A5, A6, A8, rfl⟩
        ihave Hpa := ownProgress_intro pr pv { p2 with infl := i' } $$ Hpv Hinfl %Habs3
        ihave Hphys := Hpback $$ %{ p2 with infl := i' } Hpa
        wp_join_done
        iexists { p2 with infl := i' }
        iframe
        ipureintro; rfl
      · -- `StateSnapshot`: `pr.Match + 1 >= r.raftLog.firstIndex()`
        wp_auto
        simp only [Hst, Hst2, prstateW64]
        wp_auto
        rw [Hm]
        ihave Hpa := ownProgress_intro pr _ p2 $$ Hpv Hinfl %Habs
        ihave Hphys := Hpback $$ %p2 Hpa
        ihave Hphys := ownRaftPhys_ins_id cfg r id s pvs2 m.From' p2 Hpvs2' $$ Hphys
        wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
        icases ownRaftPhys_log_same cfg r id _ $$ Hphys with ⟨Hlog, Hlogback⟩
        wp_apply wp_raftLog_firstIndex $$ [$Hlog] as %fi ⟨Hlog, -⟩
        ihave Hphys := Hlogback $$ Hlog
        wp_if_destruct
        · -- back from needing a snapshot: `BecomeProbe`, `BecomeReplicate`
          wp_apply raft.wp_load_id $$ Hphys as Hphys
          wp_raft_log
          icases ownRaftPhys_pr_at cfg r id s pvs2 m.From' pr p2 $$ Hphys %Hlk %Hpvs2'
            with ⟨Hpa, Hpback⟩
          wp_apply wp_Progress_BecomeProbe $$ [$Hpa] as Hpa
          wp_apply wp_Progress_BecomeReplicate $$ [$Hpa] as Hpa
          ihave Hphys := Hpback $$ %(progressBecomeReplicate (progressBecomeProbe p2)) Hpa
          wp_join_done
          iexists progressBecomeReplicate (progressBecomeProbe p2)
          iframe
          ipureintro; rfl
        · -- `pr.State == StateReplicate`: no, `StateSnapshot`
          icases ownRaftPhys_pr_at cfg r id s pvs2 m.From' pr p2 $$ Hphys %Hlk %Hpvs2'
            with ⟨Hpa, Hpback⟩
          iNamed Hpa
          have Hst' := ((progressAbs_Some _ _ _).1 Habs).2.1
          wp_auto
          simp only [Hst', Hst2, prstateW64]
          wp_auto
          ihave Hpa := ownProgress_intro pr _ p2 $$ Hpv Hinfl %Habs
          ihave Hphys := Hpback $$ %p2 Hpa
          wp_join_done
          iexists p2
          iframe
          ipureintro; rfl
    iNamed HJ
    have Hmm3 : prvalsMatch (<[m.From' := p3]> pvs2) = prvalsMatch pvs2 :=
      prvalsMatch_insert_same _ _ p2 _ Hpvs2' Hm3
    generalize Hpvs3 : (<[m.From' := p3]> pvs2 : GMap w64 Progress) = pvs3 at *
    have Hpvs3' : pvs3 !! m.From' = some p3 := by rw [← Hpvs3]; exact GMap.lookup_insert_eq _ _ _
    wp_auto
    -- `if r.maybeCommit() { release...; r.bcastAppend() } else if r.id != m.From &&
    --   pr.CanBumpCommit(r.raftLog.committed) { r.sendAppend(m.From) }`, joined
    wp_join iprop(∃ (c : w64) (ms : List Msg) (pvs4 : GMap w64 Progress),
        "Hphys" ∷ ownRaftPhys cfg r id
          { sendMsgs { s with logst := { s.logst with committed := c } } ms with prvals := pvs4 } ∗
        "%Hc" ∷ ⌜c = s.logst.committed ∨ CommitOk cfg (toPState { s with prvals := pvs3 }) c⌝ ∗
        "%Hms" ∷ ⌜ReplSends id { s with logst := { s.logst with committed := c } } ms⌝ ∗
        "%Hmm4" ∷ ⌜prvalsMatch pvs4 = prvalsMatch pvs3⌝ ∗
        "m" ∷ m_ptr ↦ m ∗ "r" ∷ r_ptr ↦ r ∗ "pr" ∷ pr_ptr ↦ pr) at next
      with [Hphys m r pr] as HJ
    · wp_apply wp_raft_maybeCommit cfg r id { s with prvals := pvs3 } Hlead Hid $$ [$Hphys]
        as %b %N ⟨Hphys, %HN⟩
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · -- not committed: `r.id != m.From && pr.CanBumpCommit(r.raftLog.committed)`
        wp_auto
        wp_apply raft.wp_load_id $$ Hphys as Hphys
        by_cases Hsame : id = m.From'
        · -- the leader's own acknowledgement
          simp only [eq_true Hsame, decide_true, Bool.not_true]
          wp_auto
          wp_join_done
          iexists s.logst.committed, [], pvs3
          ihave Hphys := ownRaftPhys_eq cfg r id _
            { sendMsgs { s with logst := { s.logst with committed := s.logst.committed } } [] with
                prvals := pvs3 } (by simp [sendMsgs]) $$ Hphys
          iframe
          ipureintro
          exact ⟨Or.inl rfl, fun _ h => absurd h List.not_mem_nil, rfl⟩
        · simp only [Hsame, decide_false, Bool.not_false]
          wp_auto
          wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
          icases ownRaftPhys_log_same cfg r id _ $$ Hphys with ⟨Hlog, Hlogback⟩
          icases ownRaftLog_struct _ _ $$ Hlog with ⟨%lv, Hl, -, Hlb⟩
          wp_auto
          ihave Hlog := Hlb $$ Hl
          ihave Hphys := Hlogback $$ Hlog
          icases ownRaftPhys_pr_at cfg r id s pvs3 m.From' pr p3 $$ Hphys %Hlk %Hpvs3'
            with ⟨Hpa, Hpback⟩
          wp_apply wp_Progress_CanBumpCommit $$ [$Hpa] as Hpa
          ihave Hphys := Hpback $$ %p3 Hpa
          ihave Hphys := ownRaftPhys_ins_id cfg r id s pvs3 m.From' p3 Hpvs3' $$ Hphys
          cases Hcb : progressCanBumpCommit p3 lv.committed'
          · wp_auto
            wp_join_done
            iexists s.logst.committed, [], pvs3
            ihave Hphys := ownRaftPhys_eq cfg r id _
              { sendMsgs { s with logst := { s.logst with committed := s.logst.committed } } [] with
                  prvals := pvs3 } (by simp [sendMsgs]) $$ Hphys
            iframe
            ipureintro
            exact ⟨Or.inl rfl, fun _ h => absurd h List.not_mem_nil, rfl⟩
          · wp_auto
            wp_apply wp_raft_sendAppend cfg r id _ m.From' (Ne.symm Hsame) Hfcfg $$ [$Hphys]
              as %ms %pvs4 ⟨Hphys, %Hms, %Hmm4⟩
            wp_join_done
            iexists s.logst.committed, ms, pvs4
            ihave Hphys := ownRaftPhys_eq cfg r id _
              { sendMsgs { s with logst := { s.logst with committed := s.logst.committed } } ms with
                  prvals := pvs4 } (by simp [sendMsgs]) $$ Hphys
            iframe
            ipureintro
            refine ⟨Or.inl rfl, ?_, Hmm4⟩
            have := (replSends_prvals id s pvs3 ms).1 Hms
            simpa using this
      · -- committed: `releasePendingReadIndexMessages` is a no-op, then `bcastAppend`
        wp_auto
        wp_apply wp_releasePendingReadIndexMessages $$ [$Hphys] as Hphys
        wp_apply wp_raft_bcastAppend $$ [$Hphys] as %ms %pvs4 ⟨Hphys, %Hms, %Hmm4⟩
        wp_join_done
        iexists N, ms, pvs4
        ihave Hphys := ownRaftPhys_eq cfg r id _
          { sendMsgs { s with logst := { s.logst with committed := N } } ms with prvals := pvs4 }
          (by simp [sendMsgs]) $$ Hphys
        iframe
        ipureintro
        exact ⟨Or.inr (HN rfl),
          (replSends_prvals id { s with logst := { s.logst with committed := N } } pvs3 ms).1 Hms,
          Hmm4⟩
    iNamed HJ
    generalize Hsc : ({ s with logst := { s.logst with committed := c } } : NState) = sc at *
    wp_auto
    wp_apply raft.wp_load_id $$ Hphys as Hphys
    -- `if r.id != m.From { for r.maybeSendAppend(m.From, false) {} }`, joined
    wp_join iprop(∃ (ms' : List Msg) (pvs5 : GMap w64 Progress),
        "Hphys" ∷ ownRaftPhys cfg r id { sendMsgs sc (ms ++ ms') with prvals := pvs5 } ∗
        "%Hms'" ∷ ⌜ReplSends id sc ms'⌝ ∗
        "%Hmm5" ∷ ⌜prvalsMatch pvs5 = prvalsMatch pvs4⌝ ∗
        "m" ∷ m_ptr ↦ m ∗ "r" ∷ r_ptr ↦ r) at next
      with [Hphys m r] as HJ
    · by_cases Hsame : id = m.From'
      · simp only [eq_true Hsame, decide_true, Bool.not_true]
        wp_auto
        wp_join_done
        iexists [], pvs4
        rw [List.append_nil]
        iframe
        ipureintro
        exact ⟨fun _ h => absurd h List.not_mem_nil, rfl⟩
      simp only [Hsame, decide_false, Bool.not_false]
      wp_auto
      ihave IH : iprop(∃ (ms' : List Msg) (pvs5 : GMap w64 Progress),
          "Hphys" ∷ ownRaftPhys cfg r id { sendMsgs sc (ms ++ ms') with prvals := pvs5 } ∗
          "%Hms'" ∷ ⌜ReplSends id sc ms'⌝ ∗
          "%Hmm5" ∷ ⌜prvalsMatch pvs5 = prvalsMatch pvs4⌝ ∗
          "m" ∷ m_ptr ↦ m ∗ "r" ∷ r_ptr ↦ r) $$ [Hphys m r]
      · iexists [], pvs4
        rw [List.append_nil]
        iframe
        ipureintro
        exact ⟨fun _ h => absurd h List.not_mem_nil, rfl⟩
      wp_for IH
      wp_apply wp_raft_maybeSendAppend cfg r id _ m.From' false (Ne.symm Hsame) Hfcfg $$ [$Hphys]
        as %b %ms'' %pvs'' ⟨Hphys, %Hms'', %Hmm''⟩
      have Hms3 : ReplSends id sc (ms' ++ ms'') :=
        replSends_app _ _ _ _ Hms' ((replSends_send_prvals _ _ _ _ _).1 Hms'')
      ihave Hphys := ownRaftPhys_eq cfg r id _
        { sendMsgs sc (ms ++ (ms' ++ ms'')) with prvals := pvs'' }
        (by simp [sendMsgs, List.append_assoc]) $$ Hphys
      cases b
      · cleanup_bool_decide
        isplitr
        · itrivial
        iexists ms' ++ ms'', pvs''
        iframe
        ipureintro
        exact ⟨Hms3, Hmm''.trans Hmm5⟩
      · cleanup_bool_decide
        wp_auto
        wp_for_post
        iframe
        iexists ms' ++ ms'', pvs''
        iframe
        ipureintro
        exact ⟨Hms3, Hmm''.trans Hmm5⟩
    iNamed HJ
    wp_auto
    -- `m.From == r.leadTransferee && ...`: `leadTransferee = 0 ≠ m.From`, so
    -- `sendTimeoutNow` is not reached
    wp_apply raft.wp_load_leadTransferee $$ Hphys as Hphys
    simp only [Hfrom0, decide_false]
    wp_auto
    iapply HΦ $$ %interface.nil %{ sendMsgs sc (ms ++ ms') with prvals := pvs5 }
    iframe Hphys
    ipureintro
    have Hts : toPState { s with prvals := pvs5 } = toPState { s with prvals := pvs3 } := by
      simp only [toPState, Hmm5, Hmm4]
    refine ⟨rfl, Or.inr (Or.inr (Or.inr ⟨Hty, Or.inr (Or.inr ⟨Hfdom, Hrej,
      p.matched, pvs5, c, ms ++ ms', Hx, ?_, ?_, ?_, ?_⟩)⟩))⟩
    · rw [Hmm5, Hmm4, Hmm3, Hmm2]
    · rw [Hts]; exact Hc
    · rw [Hsc]; exact replSends_app _ _ _ _ Hms Hms'
    · rw [← Hsc]
  · -- rejected
    have Hself := Hself Hrej
    wp_auto
    wp_apply raft.wp_load_id $$ Hphys as Hphys
    wp_raft_log
    -- `nextProbeIdx`, from `findConflictByTerm` when `m.LogTerm > 0`
    wp_join iprop(∃ (np : w64),
        "nextProbeIdx" ∷ nextProbeIdx_ptr ↦ np ∗
        "Hphys" ∷ ownRaftPhys cfg r id { s with prvals := pvs1 } ∗
        "m" ∷ m_ptr ↦ m ∗ "r" ∷ r_ptr ↦ r) with [nextProbeIdx Hphys m r] as HR
    · wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
      icases ownRaftPhys_log_same cfg r id _ $$ Hphys with ⟨Hlog, Hlogback⟩
      wp_apply wp_raftLog_findConflictByTerm $$ [$Hlog] as %i' %t' ⟨Hlog, -⟩
      ihave Hphys := Hlogback $$ Hlog
      wp_join_done
    iNamed HR
    wp_auto
    -- `pr.MaybeDecrTo(m.Index, nextProbeIdx)`
    icases ownRaftPhys_pr_at cfg r id s pvs1 m.From' pr p $$ Hphys %Hlk %Hpvs1' with ⟨Hpa, Hpback⟩
    wp_apply wp_Progress_MaybeDecrTo $$ [$Hpa] as Hpa
    ihave Hphys := Hpback $$ %(progressMaybeDecrTo p m.Index' np).2 Hpa
    have Hmm2 : prvalsMatch (<[m.From' := (progressMaybeDecrTo p m.Index' np).2]> pvs1)
        = prvalsMatch s.prvals := by
      rw [← Hmm1]; exact prvalsMatch_insert_same _ _ p _ Hpvs1' (decrTo_match _ _ _)
    generalize Hp2 : (progressMaybeDecrTo p m.Index' np) = dp at *
    obtain ⟨b, p2⟩ := dp
    generalize Hpvs2 : (<[m.From' := p2]> pvs1 : GMap w64 Progress) = pvs2 at *
    have Hpvs2' : pvs2 !! m.From' = some p2 := by rw [← Hpvs2]; exact GMap.lookup_insert_eq _ _ _
    cases b
    · -- nothing to resend
      wp_auto
      iapply HΦ $$ %interface.nil %{ s with prvals := pvs2 }
      iframe Hphys
      ipureintro
      refine ⟨rfl, Or.inr (Or.inr (Or.inr ⟨Hty, Or.inr (Or.inl ⟨Hfdom, Hrej, [], pvs2, ?_,
        fun _ h => absurd h List.not_mem_nil, Hmm2⟩)⟩))⟩
      rw [sendMsgs_nil_prvals]
    wp_auto
    wp_apply raft.wp_load_id $$ Hphys as Hphys
    wp_raft_log
    -- `if pr.State == StateReplicate { pr.BecomeProbe() }`
    icases ownRaftPhys_pr_at cfg r id s pvs2 m.From' pr p2 $$ Hphys %Hlk %Hpvs2' with ⟨Hpa, Hpback⟩
    iNamed Hpa
    have Hst2 := ((progressAbs_Some _ _ _).1 Habs).2.1
    wp_auto
    rw [Hst2]
    ihave Hpa := ownProgress_intro pr _ p2 $$ Hpv Hinfl %Habs
    by_cases Hrep : p2.state = .replicate
    · rw [Hrep]
      wp_auto
      wp_apply wp_Progress_BecomeProbe $$ [$Hpa] as Hpa
      ihave Hphys := Hpback $$ %(progressBecomeProbe p2) Hpa
      have HM3 : (progressBecomeProbe p2).matched = p2.matched := rfl
      generalize Hpvs3 : (<[m.From' := progressBecomeProbe p2]> pvs2 : GMap w64 Progress) = pvs3
      wp_apply wp_raft_sendAppend cfg r id _ m.From' Hself Hfcfg $$ [$Hphys]
        as %ms %pvs ⟨Hphys, %Hms, %Hmm⟩
      ihave Hphys := ownRaftPhys_eq cfg r id _ { sendMsgs s ms with prvals := pvs }
        (by simp [sendMsgs]) $$ Hphys
      iapply HΦ $$ %interface.nil %{ sendMsgs s ms with prvals := pvs }
      iframe Hphys
      ipureintro
      refine ⟨rfl, Or.inr (Or.inr (Or.inr ⟨Hty, Or.inr (Or.inl ⟨Hfdom, Hrej, ms, pvs, rfl,
        (replSends_prvals id s _ ms).1 Hms, ?_⟩)⟩))⟩
      rw [Hmm, ← Hmm2, ← Hpvs3]
      exact prvalsMatch_insert_same _ _ p2 _ Hpvs2' HM3
    · have Hne : prstateW64 p2.state ≠ W64 1 := by
        cases h : p2.state <;> simp_all [prstateW64]
      simp only [show (prstateW64 p2.state = W64 1) = False from eq_false Hne, decide_false]
      wp_auto
      ihave Hphys := Hpback $$ %p2 Hpa
      have HM3 : p2.matched = p2.matched := rfl
      generalize Hpvs3 : (<[m.From' := p2]> pvs2 : GMap w64 Progress) = pvs3
      wp_apply wp_raft_sendAppend cfg r id _ m.From' Hself Hfcfg $$ [$Hphys]
        as %ms %pvs ⟨Hphys, %Hms, %Hmm⟩
      ihave Hphys := ownRaftPhys_eq cfg r id _ { sendMsgs s ms with prvals := pvs }
        (by simp [sendMsgs]) $$ Hphys
      iapply HΦ $$ %interface.nil %{ sendMsgs s ms with prvals := pvs }
      iframe Hphys
      ipureintro
      refine ⟨rfl, Or.inr (Or.inr (Or.inr ⟨Hty, Or.inr (Or.inl ⟨Hfdom, Hrej, ms, pvs, rfl,
        (replSends_prvals id s _ ms).1 Hms, ?_⟩)⟩))⟩
      rw [Hmm, ← Hmm2, ← Hpvs3]
      exact prvalsMatch_insert_same _ _ p2 _ Hpvs2' HM3

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
    (Hnorm : ∀ e ∈ ents, e.Type' = EntryNormal) (Hsmall : (ents.length : Int) < 2^61)
    (Hnz : s.term ≠ W64 0) :
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
  icases Hinit with ⟨%e1, %e2, %e3, %e4, %errPropDropped, %gr, %_, %_, %_, %_, #Hinit⟩
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
  · wp_apply wp_raft_appendEntry cfg r id s _ ents Hnorm Hsmall Hnz $$ [$Hphys $Hes]
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
  · obtain ⟨Hne, Hnorm, Hsmall, Hnz⟩ := Hprop Hp
    ihave Hes := Hents $$ %Hp
    iapply wp_stepLeader_prop cfg wp_raft_bcastAppend wp_raft_appendEntry r id s m ents Hp Hid
      Hne Hnorm Hsmall Hnz $$ [Hphys Hes]
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
