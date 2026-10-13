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

Read-index (2026-10-13, Lean-first): `MsgReadIndex` (`wp_stepLeader_readindex`), the read
path of `MsgHeartbeatResp` (`recvAck`, `maybeAdvance` on the tracker's voter map, through
`ownRaftPhys_readOnly_trk`, and the range over the confirmed requests, each answered by
`responseToReadIndexReq` and a `send`), and the release of the pending requests after a
commit (`MsgAppResp`). A queued request's fields are loaded from its persistent points-to
through the generated field accessors (`wp_auto` does not split `p ↦□ rv`).
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
public import Spec.go_etcd_io.raft.v3.raft__committedEntryInCurrentTerm
public import Spec.go_etcd_io.raft.v3.sendMsgReadIndexResponse
public import Spec.go_etcd_io.raft.v3.raft__responseToReadIndexReq
public import Spec.go_etcd_io.raft.v3.raft__send
public import Spec.go_etcd_io.raft.v3.readOnly__recvAck
public import Spec.go_etcd_io.raft.v3.readOnly__maybeAdvance
public import Spec.go_etcd_io.raft.v3.tracker.ProgressTracker__IsSingleton

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

/-- The voter map out of a tracker, back at any map with the same key set. -/
private theorem ownTracker_voters (tv : tracker.ProgressTracker) (t : Trk) :
    ⊢ ownTracker (GF := GF) cfg tv t -∗
      ∃ (vr : Loc) (voters : GMap w64 Unit),
        ⌜tv.Config'.Voters'.arr = [vr, map.nil]⌝ ∗ ⌜domSet voters = cfg⌝ ∗
        ⌜(GMap.size cfg : Int) ≤ 2 ^ 62⌝ ∗ vr ↦$ voters ∗
        (∀ voters' : GMap w64 Unit, ⌜domSet voters' = cfg⌝ -∗ vr ↦$ voters' -∗
           ownTracker cfg tv t) := by
  iintro Hown
  iunfold ownTracker at Hown
  icases Hown with ⟨%voters_ref, %voters, %learners, %learnersNext, Hown⟩
  iNamed Hown
  iexists voters_ref, voters
  isplitr
  · ipureintro; exact Hvoters_arr
  isplitr
  · ipureintro; exact Hvoters_dom
  isplitr
  · ipureintro; exact Hcfg_size
  iframe Hvoters
  iintro %voters' %Hd Hv
  iapply ownTracker_intro cfg tv t.votes t.prs t.peers voters_ref voters' learners learnersNext
    Hprs_dom Hvoters_arr Hautoleave Hd Hno_learners Hcfg_size HmaxInfl
    $$ Hvotes Hprs Hprogs Hv Hlearners HlearnersNext

/-! The read path's pure facts. -/

private theorem recvAck_pending (r : ReadOnly) (src : w64) (ctx : List w8) :
    (readonlyRecvAck r src ctx).pending = r.pending ∧
    (readonlyRecvAck r src ctx).confirmed = r.confirmed := by
  unfold readonlyRecvAck; split <;> exact ⟨rfl, rfl⟩

private theorem advance_mem (r : ReadOnly) (N : w64) (q : ReadReq)
    (H : q ∈ (readonlyAdvance r N).2) : q ∈ r.pending := by
  unfold readonlyAdvance at H
  split at H
  · simp at H
  · exact List.mem_of_mem_take H

/-- After the sender's acknowledgement, every voter's is still a position sent. -/
private theorem recvAck_bound (r : ReadOnly) (src : w64) (ctx : List w8)
    (Hb : ∀ v ∈ cfg, uint.Z ((r.acks !! v).getD (W64 0))
            ≤ uint.Z r.confirmed + (r.pending.length : Int))
    (Hc : ctx ≠ [] → uint.Z (leToU64 (ctx.take 8))
            ≤ uint.Z r.confirmed + (r.pending.length : Int)) :
    ∀ v ∈ cfg, uint.Z (((readonlyRecvAck r src ctx).acks !! v).getD (W64 0))
      ≤ uint.Z (readonlyRecvAck r src ctx).confirmed +
        ((readonlyRecvAck r src ctx).pending.length : Int) := by
  intro v Hv
  unfold readonlyRecvAck
  split
  · exact Hb v Hv
  · rename_i hne
    simp only
    by_cases hv : src = v
    · subst hv
      rw [GMap.lookup_insert_eq]
      simp only [Option.getD_some]
      rw [w64Max_spec]
      have := Hb src Hv
      have := Hc hne
      omega
    · rw [GMap.lookup_insert_ne _ _ hv]
      exact Hb v Hv

private theorem readRespondAll_snoc (id : w64) (s : NState) (qs : List ReadReq) (n : Nat)
    (q : ReadReq) (H : qs[n]? = some q) :
    readRespondAll id s (qs.take (n + 1)) = readRespond id (readRespondAll id s (qs.take n)) q := by
  unfold readRespondAll
  rw [List.take_add_one, H]
  simp [List.foldl_append]

/-- **`MsgVoteResp`, `MsgApp`, `MsgHeartbeat`, `MsgPreVoteResp`**: both switches fall
through, whether or not the sender has a `Progress`. -/
private theorem wp_stepLeader_noop (r : Loc) (id : w64) (s : NState) (m : raftpb.Message)
    (ents : List raftpb.Entry) (ctx : List w8)
    (Hty : m.Type' = MsgVoteResp ∨ m.Type' = MsgApp ∨
      m.Type' = MsgHeartbeat ∨ m.Type' = MsgPreVoteResp) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhys cfg r id s }}
      (App (App (Val #(functions stepLeader [])) (Val #r)) (Val #m))
    {{ (err : GoInterface) (s' : NState), RET #err;
        ownRaftPhys cfg r id s' ∗ ⌜err = interface.nil⌝ ∗
        ⌜LeaderNonpropResult cfg id s m ents ctx s'⌝ }} := by
  wp_start as Hphys
  wp_auto
  have Hres : LeaderNonpropResult cfg id s m ents ctx s := Or.inl ⟨Hty, rfl⟩
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
    (r : Loc) (id : w64) (s : NState) (m : raftpb.Message) (ents : List raftpb.Entry)
    (ctx : List w8) (Hty : m.Type' = MsgBeat) (Hlead : s.role = .leader) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhys cfg r id s }}
      (App (App (Val #(functions stepLeader [])) (Val #r)) (Val #m))
    {{ (err : GoInterface) (s' : NState), RET #err;
        ownRaftPhys cfg r id s' ∗ ⌜err = interface.nil⌝ ∗
        ⌜LeaderNonpropResult cfg id s m ents ctx s'⌝ }} := by
  wp_start as Hphys
  wp_auto
  simp only [Hty, MsgBeat]
  wp_auto
  wp_apply wp_raft_bcastHeartbeat cfg r id s Hlead $$ [$Hphys] as %ms %pvs ⟨Hphys, %Hms, %Hmm⟩
  iapply HΦ
  iframe Hphys
  ipureintro
  exact ⟨rfl, Or.inr (Or.inl ⟨Hty, ms, pvs, rfl, fun m' h => (Hms m' h).1, Hmm⟩)⟩

/-- **`MsgHeartbeatResp`** -/
private theorem wp_stepLeader_hbresp
    (wp_raft_sendAppend : raft.sendAppend.spec (GF := GF) (hG := hG))
    (wp_raftLog_lastIndex : raftLog.lastIndex.spec (GF := GF) (hG := hG))
    (wp_readOnly_recvAck : readOnly.recvAck.spec (GF := GF) (hG := hG))
    (wp_readOnly_maybeAdvance : readOnly.maybeAdvance.spec (GF := GF) (hG := hG))
    (wp_raft_responseToReadIndexReq : raft.responseToReadIndexReq.spec (GF := GF) (hG := hG))
    (wp_raft_send : raft.send.spec (GF := GF) (hG := hG))
    (r : Loc) (id : w64) (s : NState) (m : raftpb.Message) (ents : List raftpb.Entry)
    (ctx : List w8)
    (Hty : m.Type' = MsgHeartbeatResp) (Hself : m.From' ≠ id)
    (Hid : id ∈ cfg) (Hrd : RdOk cfg s.rd)
    (Hclen : ctx = [] ∨ 8 ≤ ctx.length)
    (Hcb : ctx ≠ [] → uint.Z (leToU64 (ctx.take 8))
            ≤ uint.Z s.rd.ro.confirmed + (s.rd.ro.pending.length : Int)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhys cfg r id s ∗
        m.Context' ↦*□ ctx }}
      (App (App (Val #(functions stepLeader [])) (Val #r)) (Val #m))
    {{ (err : GoInterface) (s' : NState), RET #err;
        ownRaftPhys cfg r id s' ∗ ⌜err = interface.nil⌝ ∗
        ⌜LeaderNonpropResult cfg id s m ents ctx s'⌝ }} := by
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
    have Hnd : m.From' ∉ domSet s.progress := by
      rw [GMap.elem_of_dom]; rintro ⟨v, hv⟩; rw [Hlk] at hv; cases hv
    refine ⟨rfl, Or.inr (Or.inr (Or.inl ⟨Hty, [], s.prvals,
      fun _ h => absurd h List.not_mem_nil, rfl, Or.inl ⟨Or.inr Hnd, ?_⟩⟩))⟩
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
  generalize Hs1 : ({ sendMsgs s ms with prvals := pvs } : NState) = s1 at *
  have Hs1rd : s1.rd = s.rd := by rw [← Hs1]; simp [sendMsgs]
  -- `if r.readOnly.option != ReadOnlySafe || len(m.Context) == 0 { return nil }`
  icases ownRaftPhys_readOnly cfg r id _ $$ Hphys with ⟨%ro, Hrof, Hro, Hback⟩
  icases ownReadOnly_option ro _ $$ Hro with ⟨%o, %Hosafe, Hopt, Hroback⟩
  wp_auto
  ihave Hro := Hroback $$ Hopt
  ihave Hphys := Hback $$ %ro %_ Hrof Hro
  ihave Hphys := ownRaftPhys_eq cfg r id _ s1 rfl $$ Hphys
  ihave %Hcl := ownSlice_len _ _ _ $$ Hctx
  subst Hosafe
  simp only [_root_.decide_true, Bool.not_true]
  wp_auto
  wp_if_destruct
  · -- no context
    have Hc0 : ctx = [] := by
      apply List.eq_nil_of_length_eq_zero; rw [Hcl.1, Hif]; rfl
    iapply HΦ $$ %interface.nil %s1
    iframe Hphys
    ipureintro
    exact ⟨rfl, Or.inr (Or.inr (Or.inl ⟨Hty, ms, pvs, Hms, Hmm, Or.inl ⟨Or.inl Hc0, Hs1.symm⟩⟩))⟩
  have Hc0 : ctx ≠ [] := by
    rintro rfl; apply Hif; simp only [List.length_nil] at Hcl; word
  -- `r.readOnly.recvAck(m.From, m.Context)`
  icases ownRaftPhys_readOnly cfg r id s1 $$ Hphys with ⟨%ro, Hrof, Hro, Hback⟩
  wp_auto
  wp_apply wp_readOnly_recvAck ro s1.rd.ro m.From' m.Context' ctx DFrac.discard $$ [$Hro $Hctx]
    as ⟨Hro, -⟩
  · ipureintro; exact Hclen
  generalize Hra : readonlyRecvAck s1.rd.ro m.From' ctx = ra at *
  ihave Hphys := Hback $$ %ro %ra Hrof Hro
  -- `rss := r.readOnly.maybeAdvance(r.trk.Voters)`
  icases ownRaftPhys_readOnly_trk cfg r id _ $$ Hphys with
    ⟨%tv, %ro2, Htrkf, Htrk, Hrof, Hro, Hback⟩
  icases ownTracker_voters cfg tv _ $$ Htrk with ⟨%vr, %voters, %Harr, %Hvd, %Hcsz, Hv, Htrkback⟩
  have Hbound := recvAck_bound cfg s1.rd.ro m.From' ctx (by rw [Hs1rd]; exact Hrd.1)
    (by rw [Hs1rd]; exact Hcb)
  rw [Hra] at Hbound
  wp_auto
  wp_apply wp_readOnly_maybeAdvance ro2 ra tv.Config'.Voters' vr voters $$ [$Hro $Hv]
    as %sl %N ⟨%HN, Hro, ⟨%ids', %Hids', Hv⟩, ⟨%ptrs, #Hsl, #Hreqs⟩⟩
  · isplitr
    · ipureintro; exact Harr
    isplitr
    · ipureintro; rw [Hvd]; exact Hcsz
    isplitr
    · ipureintro; rw [Hvd]; intro h; rw [h] at Hid; exact absurd Hid (GMap.not_elem_of_empty _)
    · ipureintro; rw [Hvd]; exact Hbound
  ihave Htrk := Htrkback $$ %ids' %(Hids'.trans Hvd) Hv
  ihave Hphys := Hback $$ %tv %ro2 %(readonlyAdvance ra N).1 Htrkf Htrk Hrof Hro
  rw [Hvd] at HN
  generalize Hqs : (readonlyAdvance ra N).2 = qs at *
  generalize Hs3 : ({ s1 with rd := { s1.rd with ro := (readonlyAdvance ra N).1 } } : NState)
    = s3 at *
  ihave Hphys := ownRaftPhys_eq cfg r id _ s3 (by rw [← Hs3]) $$ Hphys
  ihave %Hlen := BigSepL2.bigSepL2_length $$ Hreqs
  ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
  -- every confirmed request has entries
  have Hqents : ∀ q ∈ qs, q.ents ≠ [] := by
    intro q Hq
    rw [← Hqs] at Hq
    have Hq' := advance_mem _ _ _ Hq
    rw [← Hra, (recvAck_pending _ _ _).1, Hs1rd] at Hq'
    exact Hrd.2.1 q Hq'
  -- `for _, rs := range rss { ... }`: each confirmed request answered, in order
  ihave IH : iprop(∃ (n : w64) (rv : Loc),
      "i" ∷ i_ptr ↦ n ∗ "rs" ∷ rs_ptr ↦ rv ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (qs.length : Int)⌝ ∗
      "Hphys" ∷ ownRaftPhys cfg r id (readRespondAll id s3 (qs.take (sint.Z n).toNat)))
    $$ [i rs Hphys]
  · iexists W64 0, zero_val Loc
    rw [show (sint.Z (W64 0)).toNat = 0 from rfl, List.take_zero]
    iframe
    ipureintro
    word
  wp_for IH
  wp_if_destruct
  · -- one more confirmed request
    have Hlt : (sint.Z n).toNat < qs.length := by word
    obtain ⟨q, Hq⟩ : ∃ q, qs[(sint.Z n).toNat]? = some q :=
      ⟨_, List.getElem?_eq_getElem Hlt⟩
    obtain ⟨p, Hp⟩ : ∃ p, ptrs[(sint.Z n).toNat]? = some p :=
      ⟨_, List.getElem?_eq_getElem (by rw [Hlen]; exact Hlt)⟩
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len by word))]
    wp_apply wp_load_slice_index sl (sint.Z n) ptrs DFrac.discard p Hn.1 $$ [Hsl] as -
    · iframe Hsl; ipureintro; exact Hp
    ihave #Hrq := BigSepL2.bigSepL2_lookup (Φ := fun _ p q => ownReadreq (GF := GF) p q) Hp Hq
      $$ Hreqs
    iunfold ownReadreq at Hrq
    icases Hrq with ⟨%rv, #Hrq⟩
    iNamed Hrq
    have Hrvi := Hrv_idx
    obtain ⟨e, es, Hqe⟩ : ∃ e es, q.ents = e :: es := by
      have := Hqents q (List.mem_of_getElem? Hq)
      cases h : q.ents with
      | nil => exact absurd h this
      | cons e es => exact ⟨e, es, rfl⟩
    ihave #Hrvents' : rv.req'.Entries' ↦*□ (e :: es) $$ [Hrv_ents]
    · rw [← Hqe]; iexact Hrv_ents
    have Hgrow := readRespondAll_snoc id s3 qs _ q Hq
    generalize Hcur : readRespondAll id s3 (qs.take (sint.Z n).toNat) = cur at *
    icases (go_etcd_io.raft.v3.readIndexRequest.readIndexRequest_access_load_req p rv
      DFrac.discard).access_strict $$ Hrv with ⟨#Hreq, -⟩
    icases (go_etcd_io.raft.v3.readIndexRequest.readIndexRequest_access_load_index p rv
      DFrac.discard).access_strict $$ Hrv with ⟨#Hidx, -⟩
    wp_apply wp_load_pers _ rv.req' $$ Hreq
    wp_apply wp_raft_responseToReadIndexReq cfg r id cur rv.req' rv.index' e es
      $$ [$Hphys $Hrvents'] as %resp Hpost
    by_cases Hloc : rv.req'.From' = W64 0 ∨ rv.req'.From' = id
    · -- a local request: a `ReadState`
      rw [ite_eq_left_of_eq_true _ _ (eq_true Hloc)]
      icases Hpost with ⟨Hphys, %Hto⟩
      rw [Hto, decide_eq_true rfl]
      wp_auto
      have Hstep : readRespond id cur q = addReadState cur rv.index' e.Data' := by
        have Hl : q.src = W64 0 ∨ q.src = id := by rw [← Hrvi.2]; exact Hloc
        rw [readRespond, ite_eq_left_of_eq_true _ _ (eq_true Hl)]
        simp only [Hqe, Hrvi.1]
      ihave Hphys : ownRaftPhys cfg r id
          (readRespondAll id s3 (qs.take (sint.Z (n + W64 1)).toNat)) $$ [Hphys]
      · rw [show (sint.Z (n + W64 1)).toNat = (sint.Z n).toNat + 1 by word, Hgrow, Hstep]
        iexact Hphys
      wp_for_post
      iframe
      iexists n + W64 1, p
      iframe
      ipureintro
      word
    · -- a forwarded one: the response
      rw [ite_eq_right_of_eq_false _ _ (eq_false Hloc)]
      icases Hpost with ⟨Hphys, %Hresp⟩
      subst Hresp
      wp_auto
      rw [decide_eq_false (fun h => Hloc (Or.inl h))]
      wp_auto
      wp_apply wp_raft_send cfg r id cur (readIndexRespMsg rv.req' rv.index') (e :: es) []
          [absMsgFrom .readIndexResp (readIndexRespMsg rv.req' rv.index') id cur.term (e :: es) []]
          (Or.inl rfl)
          (Or.inr (Or.inl ⟨.readIndexResp, Or.inr (Or.inr (Or.inl rfl)), rfl, rfl,
            fun h => Hloc (Or.inr h), rfl⟩))
        $$ [$Hphys]
      · simp only [named]
        rw [show (readIndexRespMsg rv.req' rv.index').Entries' = rv.req'.Entries' from rfl,
          show (readIndexRespMsg rv.req' rv.index').Context' = slice.nil from rfl]
        isplitr
        · iexact Hrvents'
        isplitr
        · iapply ownSlice_nil
        iapply send_no_snap (readIndexRespMsg rv.req' rv.index')
        simp [readIndexRespMsg, MsgSnap]
      iintro Hphys
      have Hstep : readRespond id cur q =
          sendMsgs cur [absMsgFrom .readIndexResp (readIndexRespMsg rv.req' rv.index') id cur.term
            (e :: es) []] := by
        have Hl : ¬ (q.src = W64 0 ∨ q.src = id) := by rw [← Hrvi.2]; exact Hloc
        rw [readRespond, ite_eq_right_of_eq_false _ _ (eq_false Hl), Hqe, ← Hrvi.1, ← Hrvi.2]
        rfl
      ihave Hphys : ownRaftPhys cfg r id
          (readRespondAll id s3 (qs.take (sint.Z (n + W64 1)).toNat)) $$ [Hphys]
      · rw [show (sint.Z (n + W64 1)).toNat = (sint.Z n).toNat + 1 by word, Hgrow, Hstep]
        iexact Hphys
      wp_auto
      wp_for_post
      iframe
      iexists n + W64 1, p
      iframe
      ipureintro
      word
  · -- all answered
    have Hfull : (sint.Z n).toNat = qs.length := by word
    rw [Hfull, List.take_length]
    subst Hra Hqs Hs3 Hs1
    iapply HΦ
    iframe Hphys
    ipureintro
    exact ⟨rfl, Or.inr (Or.inr (Or.inl ⟨Hty, ms, pvs, Hms, Hmm, Or.inr ⟨Hc0, N, HN, rfl⟩⟩))⟩

/-- **`MsgReadIndex`** (not at a single voter): pending until an entry of the term is
committed, then `sendMsgReadIndexResponse`. -/
private theorem wp_stepLeader_readindex
    (wp_IsSingleton : tracker.ProgressTracker.IsSingleton.spec (GF := GF) (hG := hG))
    (wp_raft_committedEntryInCurrentTerm :
      raft.committedEntryInCurrentTerm.spec (GF := GF) (hG := hG))
    (wp_sendMsgReadIndexResponse : sendMsgReadIndexResponse.spec (GF := GF) (hG := hG))
    (r : Loc) (id : w64) (s : NState) (m : raftpb.Message) (ents : List raftpb.Entry)
    (ctx : List w8)
    (Hty : m.Type' = MsgReadIndex) (Hlead : s.role = .leader) (Hnz : s.term ≠ W64 0)
    (Hsz : 1 < GMap.size cfg) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhys cfg r id s ∗
        m.Entries' ↦*□ ents }}
      (App (App (Val #(functions stepLeader [])) (Val #r)) (Val #m))
    {{ (err : GoInterface) (s' : NState), RET #err;
        ownRaftPhys cfg r id s' ∗ ⌜err = interface.nil⌝ ∗
        ⌜LeaderNonpropResult cfg id s m ents ctx s'⌝ }} := by
  wp_start as ⟨Hphys, #Hes⟩
  wp_auto
  simp only [Hty, MsgReadIndex]
  wp_auto
  -- `r.trk.IsSingleton()`: no, more than one voter
  icases ownRaftPhys_tracker_same cfg r id s $$ Hphys with ⟨%tv, Htrkf, Htrk, Hback⟩
  icases ownTracker_voters cfg tv _ $$ Htrk with ⟨%vr, %voters, %Harr, %Hvd, %Hcsz, Hv, Htrkback⟩
  ihave Hv := ownIdsetQ_map vr (DFrac.own 1) voters $$ Hv
  ihave Hnil := ownIdsetQ_nil (GF := GF) (DFrac.own 1)
  wp_apply wp_IsSingleton _ (DFrac.own 1) tv vr map.nil (DFrac.own 1) (DFrac.own 1) voters ∅ Harr
    $$ [$Htrkf $Hv $Hnil] as ⟨Htrkf, Hv, -⟩
  have Hvsz : GMap.size voters = GMap.size cfg := by rw [← Hvd, GMap.size_dom]
  have Hns : ¬ (GMap.size voters = 1 ∧ GMap.size (∅ : GMap w64 Unit) = 0) := by
    rintro ⟨h, -⟩; omega
  simp only [Hns, decide_false]
  wp_auto
  icases ownIdsetQ_elim _ _ _ $$ Hv with (⟨%Hn, %He⟩ | Hv)
  · subst He
    rw [GMap.map_size_empty] at Hvsz
    omega
  ihave Htrk := Htrkback $$ %voters %Hvd Hv
  ihave Hphys := Hback $$ %tv Htrkf Htrk
  -- `r.committedEntryInCurrentTerm()`
  wp_apply wp_raft_committedEntryInCurrentTerm cfg r id s Hnz $$ [$Hphys] as %b ⟨Hphys, %Hb⟩
  cases b
  · -- postponed: `r.pendingReadIndexMessages = append(r.pendingReadIndexMessages, m)`
    have Hb' : plogTermAt s.logst.prev (s.logst.sents ++ s.logst.uents) s.logst.committed
        ≠ some s.term := fun h => absurd (Hb.2 h) (by simp)
    wp_auto
    icases ownRaftPhys_misc cfg r id s $$ Hphys with
      ⟨%rs, %ro, %pr, Hfrs, Hfro, Hfpr, Hmisc, Hmback⟩
    iunfold ownRaftMisc at Hmisc
    iNamed Hmisc
    wp_auto
    wp_apply wp_slice_literal
    try (isplitr; (ipureintro; rfl))
    iintro %sl1 ⟨Hsl1, -⟩
    wp_auto
    wp_apply wp_slice_append $$ [$Hpri $Hpri_cap $Hsl1] as %pr' ⟨Hpri, Hpri_cap, -⟩
    ihave Hphys := Hmback $$ %rs %ro %pr' %{ s.rd with pend := s.rd.pend ++ [(m, ents)] }
      Hfrs Hfro Hfpr [HreadStates HreadStates_cap Hro_obj Hpri Hpri_cap]
    · unfold ownRaftMisc
      simp only [named, List.map_append, List.map_cons, List.map_nil]
      iframe HreadStates HreadStates_cap Hro_obj Hpri Hpri_cap
      iapply (BigSepL.bigSepL_snoc (PROP := IProp GF)).2
      iframe Hpri_ents Hes
    iapply HΦ
    iframe Hphys
    ipureintro
    exact ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inl ⟨Hty, Or.inl ⟨Hb', rfl⟩⟩)))⟩
  · -- `sendMsgReadIndexResponse(r, m)`
    have Hb' := Hb.1 rfl
    wp_auto
    wp_apply wp_sendMsgReadIndexResponse cfg r id s m ents Hlead $$ [$Hphys $Hes]
      as %ms %pvs ⟨Hphys, %Hms, %Hmm⟩
    iapply HΦ
    iframe Hphys
    ipureintro
    exact ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inl ⟨Hty, Or.inr ⟨Hb', ms, pvs, rfl, Hms, Hmm⟩⟩)))⟩

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
    (Hfrom0 : m.From' ≠ W64 0) (Hself : m.Reject' = true → m.From' ≠ id) (Hnz : s.term ≠ W64 0)
    (ents : List raftpb.Entry) (ctx : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhys cfg r id s }}
      (App (App (Val #(functions stepLeader [])) (Val #r)) (Val #m))
    {{ (err : GoInterface) (s' : NState), RET #err;
        ownRaftPhys cfg r id s' ∗ ⌜err = interface.nil⌝ ∗
        ⌜LeaderNonpropResult cfg id s m ents ctx s'⌝ }} := by
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
    refine ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr ⟨Hty, Or.inl ⟨?_, rfl⟩⟩)))⟩
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
      refine ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr ⟨Hty, Or.inr (Or.inr ⟨Hfdom, Hrej,
        p.matched, pvs2, s.logst.committed, [], [], Hx, Hmm2, Or.inl rfl,
        fun _ h => absurd h List.not_mem_nil, ?_⟩)⟩)))⟩
      simp only [↓reduceIte, true_and]
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
    -- `if r.maybeCommit() { releasePendingReadIndexMessages(r); r.bcastAppend() } else if
    --   r.id != m.From && pr.CanBumpCommit(r.raftLog.committed) { r.sendAppend(m.From) }`,
    -- joined: `s2` is the state the release leaves (the committed one, if nothing is
    -- committed), `hb` its heartbeats
    wp_join iprop(∃ (c : w64) (s2 : NState) (hb ms : List Msg) (pvs4 : GMap w64 Progress),
        "Hphys" ∷ ownRaftPhys cfg r id { sendMsgs (sendMsgs s2 hb) ms with prvals := pvs4 } ∗
        "%Hc" ∷ ⌜c = s.logst.committed ∨ CommitOk cfg (toPState { s with prvals := pvs3 }) c⌝ ∗
        "%Hs2" ∷ ⌜if c = s.logst.committed then
                    hb = [] ∧ s2 = { s with logst := { s.logst with committed := c } }
                  else
                    ReleaseHbs id { s with logst := { s.logst with committed := c },
                                           prvals := pvs3 } hb ∧
                    s2 = releasedState id { s with logst := { s.logst with committed := c } }⌝ ∗
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
          simp only [eq_true Hsame, _root_.decide_true]
          wp_auto
          wp_join_done
          iexists s.logst.committed, { s with logst := { s.logst with committed := s.logst.committed } },
            [], [], pvs3
          ihave Hphys := ownRaftPhys_eq cfg r id _
            { sendMsgs (sendMsgs { s with logst := { s.logst with committed := s.logst.committed } }
                [] ) [] with prvals := pvs3 } (by simp [sendMsgs]) $$ Hphys
          iframe
          ipureintro
          exact ⟨Or.inl rfl, by simp, fun _ h => absurd h List.not_mem_nil, rfl⟩
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
            iexists s.logst.committed,
              { s with logst := { s.logst with committed := s.logst.committed } }, [], [], pvs3
            ihave Hphys := ownRaftPhys_eq cfg r id _
              { sendMsgs (sendMsgs { s with logst := { s.logst with committed := s.logst.committed } }
                  []) [] with prvals := pvs3 } (by simp [sendMsgs]) $$ Hphys
            iframe
            ipureintro
            exact ⟨Or.inl rfl, by simp, fun _ h => absurd h List.not_mem_nil, rfl⟩
          · wp_auto
            wp_apply wp_raft_sendAppend cfg r id _ m.From' (Ne.symm Hsame) Hfcfg $$ [$Hphys]
              as %ms %pvs4 ⟨Hphys, %Hms, %Hmm4⟩
            wp_join_done
            iexists s.logst.committed,
              { s with logst := { s.logst with committed := s.logst.committed } }, [], ms, pvs4
            ihave Hphys := ownRaftPhys_eq cfg r id _
              { sendMsgs (sendMsgs { s with logst := { s.logst with committed := s.logst.committed } }
                  []) ms with prvals := pvs4 } (by simp [sendMsgs]) $$ Hphys
            iframe
            ipureintro
            refine ⟨Or.inl rfl, by simp, ?_, Hmm4⟩
            have := (replSends_prvals id s pvs3 ms).1 Hms
            simpa using this
      · -- committed (an entry of the leader's term): the pending read-index requests are
        -- released, then `bcastAppend`
        have HcN := HN rfl
        have HNne : N ≠ s.logst.committed := by
          intro h; have := HcN.1; rw [h] at this; simp [toPState] at this
        wp_auto
        wp_apply wp_releasePendingReadIndexMessages cfg r id
            { s with prvals := pvs3, logst := { s.logst with committed := N } } Hlead Hnz
            (fun _ => HcN.2.2.1) $$ [$Hphys]
          as %hb %pvsR ⟨Hphys, %Hhb, %HmmR⟩
        wp_apply wp_raft_bcastAppend $$ [$Hphys] as %ms %pvs4 ⟨Hphys, %Hms, %Hmm4⟩
        wp_join_done
        iexists N, releasedState id { s with logst := { s.logst with committed := N } }, hb, ms,
          pvs4
        ihave Hphys := ownRaftPhys_eq cfg r id _
          { sendMsgs (sendMsgs (releasedState id { s with logst := { s.logst with committed := N } })
              hb) ms with prvals := pvs4 }
          (by simp [sendMsgs, releasedState]) $$ Hphys
        iframe
        ipureintro
        refine ⟨Or.inr HcN, ?_, fun m' hm => replOk_proper _ _ _ _ rfl rfl rfl rfl (Hms m' hm),
          Hmm4.trans HmmR⟩
        simp only [HNne, ↓reduceIte, and_true]
        exact Hhb
    iNamed HJ
    generalize Hsc : ({ s with logst := { s.logst with committed := c } } : NState) = sc at *
    have Hs2l : s2.term = sc.term ∧ s2.logst = sc.logst := by
      split at Hs2 <;> (obtain ⟨-, rfl⟩ := Hs2; exact ⟨rfl, rfl⟩)
    wp_auto
    wp_apply raft.wp_load_id $$ Hphys as Hphys
    -- `if r.id != m.From { for r.maybeSendAppend(m.From, false) {} }`, joined
    wp_join iprop(∃ (ms' : List Msg) (pvs5 : GMap w64 Progress),
        "Hphys" ∷ ownRaftPhys cfg r id { sendMsgs (sendMsgs s2 hb) (ms ++ ms') with prvals := pvs5 } ∗
        "%Hms'" ∷ ⌜ReplSends id sc ms'⌝ ∗
        "%Hmm5" ∷ ⌜prvalsMatch pvs5 = prvalsMatch pvs4⌝ ∗
        "m" ∷ m_ptr ↦ m ∗ "r" ∷ r_ptr ↦ r) at next
      with [Hphys m r] as HJ
    · by_cases Hsame : id = m.From'
      · simp only [eq_true Hsame, _root_.decide_true]
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
          "Hphys" ∷ ownRaftPhys cfg r id
            { sendMsgs (sendMsgs s2 hb) (ms ++ ms') with prvals := pvs5 } ∗
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
        replSends_app _ _ _ _ Hms' (by
          intro m' hm
          refine replOk_proper _ _ _ _ ?_ ?_ ?_ ?_ (Hms'' m' hm)
          · exact Hs2l.1.symm
          · exact congrArg LogState.prev Hs2l.2.symm
          · exact congrArg (fun l => l.sents ++ l.uents) Hs2l.2.symm
          · exact congrArg LogState.committed Hs2l.2.symm)
      ihave Hphys := ownRaftPhys_eq cfg r id _
        { sendMsgs (sendMsgs s2 hb) (ms ++ (ms' ++ ms'')) with prvals := pvs'' }
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
    iapply HΦ $$ %interface.nil %{ sendMsgs (sendMsgs s2 hb) (ms ++ ms') with prvals := pvs5 }
    iframe Hphys
    ipureintro
    have Hts : toPState { s with prvals := pvs5 } = toPState { s with prvals := pvs3 } := by
      simp only [toPState, Hmm5, Hmm4]
    subst Hsc
    refine ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr ⟨Hty, Or.inr (Or.inr ⟨Hfdom, Hrej,
      p.matched, pvs5, c, hb, ms ++ ms', Hx, ?_, ?_, ?_, ?_⟩)⟩)))⟩
    · rw [Hmm5, Hmm4, Hmm3, Hmm2]
    · rw [Hts]; exact Hc
    · exact replSends_app _ _ _ _ Hms Hms'
    · by_cases Hceq : c = s.logst.committed
      · simp only [Hceq, ↓reduceIte] at Hs2 ⊢
        obtain ⟨rfl, rfl⟩ := Hs2
        exact ⟨rfl, by simp [sendMsgs]⟩
      · simp only [Hceq, ↓reduceIte] at Hs2 ⊢
        obtain ⟨Hhb, rfl⟩ := Hs2
        refine ⟨fun m' hm => ⟨?_, (Hhb m' hm).2⟩, rfl⟩
        have Hts' : toPState { s with logst := { s.logst with committed := c }, prvals := pvs5 } =
            toPState { s with logst := { s.logst with committed := c }, prvals := pvs3 } := by
          simp only [toPState, Hmm5, Hmm4]
        rw [Hts']; exact (Hhb m' hm).1
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
      refine ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr ⟨Hty, Or.inr (Or.inl ⟨Hfdom, Hrej, [], pvs2, ?_,
        fun _ h => absurd h List.not_mem_nil, Hmm2⟩)⟩)))⟩
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
      refine ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr ⟨Hty, Or.inr (Or.inl ⟨Hfdom, Hrej, ms, pvs, rfl,
        (replSends_prvals id s _ ms).1 Hms, ?_⟩)⟩)))⟩
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
      refine ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr ⟨Hty, Or.inr (Or.inl ⟨Hfdom, Hrej, ms, pvs, rfl,
        (replSends_prvals id s _ ms).1 Hms, ?_⟩)⟩)))⟩
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
    (wp_raftLog_firstIndex : raftLog.firstIndex.spec (GF := GF) (hG := hG))
    (wp_ProgressTracker_IsSingleton :
      tracker.ProgressTracker.IsSingleton.spec (GF := GF) (hG := hG))
    (wp_raft_committedEntryInCurrentTerm :
      raft.committedEntryInCurrentTerm.spec (GF := GF) (hG := hG))
    (wp_sendMsgReadIndexResponse : sendMsgReadIndexResponse.spec (GF := GF) (hG := hG))
    (wp_readOnly_recvAck : readOnly.recvAck.spec (GF := GF) (hG := hG))
    (wp_readOnly_maybeAdvance : readOnly.maybeAdvance.spec (GF := GF) (hG := hG))
    (wp_raft_responseToReadIndexReq : raft.responseToReadIndexReq.spec (GF := GF) (hG := hG))
    (wp_raft_send : raft.send.spec (GF := GF) (hG := hG)) :
    stepLeader.spec (GF := GF) (hG := hG) := by
  intro cfg r id s m ents ctx Hty Hlead Hid Hfrom0 Hself Hprop Hrd Hnz Hri Hhr
  iintro %Φ ⟨#Hinit, Hphys, Hctx, Hents, Hrents⟩ HΦ
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
      ⌜LeaderNonpropResult cfg id s m ents ctx s'⌝ -∗ Φ #err) $$ [HΦ]
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
  rcases Hty with Hty | Hty | Hty | Hty | Hty | Hty | Hty | Hty | Hty
  · iapply wp_stepLeader_noop cfg r id s m ents ctx (Or.inl Hty) $$ [Hphys] HΦ'
    iframe
    iexact Hinit
  · iapply wp_stepLeader_beat cfg wp_raft_bcastHeartbeat r id s m ents ctx Hty Hlead $$ [Hphys] HΦ'
    iframe
    iexact Hinit
  · ihave #Hc := Hctx $$ %Hty
    obtain ⟨Hclen, Hcb⟩ := Hhr Hty
    iapply wp_stepLeader_hbresp cfg wp_raft_sendAppend wp_raftLog_lastIndex wp_readOnly_recvAck
      wp_readOnly_maybeAdvance wp_raft_responseToReadIndexReq wp_raft_send r id s m ents ctx Hty
      (Hself (Or.inl Hty)) Hid Hrd Hclen Hcb $$ [Hphys] HΦ'
    iframe
    iframe Hinit Hc
  · iapply wp_stepLeader_appresp cfg wp_raft_sendAppend wp_raft_maybeSendAppend
      wp_raft_bcastAppend wp_raft_maybeCommit wp_releasePendingReadIndexMessages
      wp_Progress_MaybeUpdate wp_Progress_MaybeDecrTo wp_Progress_BecomeProbe
      wp_Progress_BecomeReplicate wp_Progress_CanBumpCommit wp_Inflights_FreeLE
      wp_raftLog_findConflictByTerm wp_raftLog_lastIndex wp_raftLog_firstIndex
      r id s m Hty Hlead Hid (Hfrom0 Hty) (fun Hr => Hself (Or.inr ⟨Hty, Hr⟩)) Hnz ents ctx
      $$ [Hphys] HΦ'
    iframe
    iexact Hinit
  · exact absurd Hty Hp
  · iapply wp_stepLeader_noop cfg r id s m ents ctx (Or.inr (Or.inl Hty)) $$ [Hphys] HΦ'
    iframe
    iexact Hinit
  · iapply wp_stepLeader_noop cfg r id s m ents ctx (Or.inr (Or.inr (Or.inl Hty))) $$ [Hphys] HΦ'
    iframe
    iexact Hinit
  · iapply wp_stepLeader_noop cfg r id s m ents ctx (Or.inr (Or.inr (Or.inr Hty))) $$ [Hphys] HΦ'
    iframe
    iexact Hinit
  · obtain ⟨Hsz, -⟩ := Hri Hty
    ihave #Hes := Hrents $$ %Hty
    iapply wp_stepLeader_readindex cfg wp_ProgressTracker_IsSingleton
      wp_raft_committedEntryInCurrentTerm wp_sendMsgReadIndexResponse r id s m ents ctx Hty Hlead
      Hnz Hsz $$ [Hphys] HΦ'
    iframe
    iframe Hinit Hes

end proof

end EtcdGrove
end Perennial
