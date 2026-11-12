/- Port of election_proof/proof_traceSendMessage.v.

(Q8 stage 1, slice 4, 2026-11-09) Both modes: untraced, the nil check; traced, the message's type
(lent out of the caller's resource), for a `MsgApp` the sender's `Progress` read into the properties
(the map made read-only), and `traceEvent` with the send hook's event. -/
module

public import Spec.go_etcd_io.raft.v3.traceSendMessage
public import Spec.go_etcd_io.raft.v3.traceEvent
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetType
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetFrom

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

set_option hygiene false in
/-- A traced type's event (`ty`, `evt`), the properties' map `mp` read-only as `e0`'s: `traceEvent`
with the caller's resource and the send hook's gate. -/
local macro "tsm_fire " ty:term:max evt:term:max e0:term:max hrep:term : tactic => `(tactic| (
  subst HoE
  rw [sendGate_of (ty := $ty) (evt := $evt) (by rw [Hty]; rfl) rfl]
  dsimp only [TraceFireOpt]
  try simp only [rsmSendAppendEntriesRequest, rsmSendAppendEntriesResponse, rsmSendRequestVoteRequest,
    rsmSendRequestVoteResponse]
  try wp_auto
  wp_apply wp_traceEvent $evt r ml mp (GoInterface.ok l) (some γd) _ Q R $$ [Htl Hfire HP Hback]
  · iframe Htl Hfire
    iapply (trOwn_some γd _).2
    iexists c, id, s, P, (some a), $e0
    iframe HP Hback
    isplitr
    · iapply raftReadLend_of_lend; iexact HRL
    isplitr
    · iexact HML
    isplitr
    · iapply ($hrep) $$ Hmp
    ipureintro
    refine ⟨by decide, fun e h hm hc h1 _ _ => sendEvOf_of_hdr a.ms $ty [] (by rw [Hty]; rfl)
      (by decide) h hm hc h1⟩
  iintro ⟨HR, HQ⟩
  try wp_auto
  iapply HΦ
  iframe HR HQ))

theorem traceSendMessage.wp_proof
    (wp_traceEvent : traceEvent.spec (GF := GF) (hG := hG))
    (wp_GetType : raftpb.Message.GetType.spec (GF := GF) (hG := hG))
    (wp_GetFrom : raftpb.Message.GetFrom.spec (GF := GF) (hG := hG)) :
    traceSendMessage.spec (GF := GF) (hG := hG) := by
  intro r ml tl tr oE Q R
  wp_start as ⟨#Htl, %Hok, Hown, Hfire⟩
  cases tl with
  | nil =>
    wp_auto
    iapply HΦ
    isplitl [Hown]
    · iapply trOwn_wand
      iframe Hown
      iintro ⟨%c, %id, %s, %P, %a, HP, -, -, -, Hb⟩
      iapply Hb $$ HP
    iapply traceFireOpt_nil $$ Hfire
  | ok l =>
    cases tr with
    | none => exact absurd (Hok rfl) (by unfold TraceLoggerOk; exact nofun)
    | some γd =>
      icases (trOwn_some γd _).1 $$ Hown with ⟨%c, %id, %s, %P, %a, HP, #HRL, #HML, %Hp, Hback⟩
      obtain ⟨Hns, HoE⟩ := Hp
      wp_auto
      wp_apply wp_map_make1 (K := GoString) (V := GoInterface) go.string go.any as %mp Hmp
      try wp_auto
      ihave #HML' := HML
      iunfold MsgLend at HML'
      icases HML' $$ HP with ⟨Hm, HPb⟩
      iunfold msgArg at Hm HPb
      wp_apply wp_GetType.1 $$ [$Hm] as Hm
      ihave HP := HPb $$ Hm
      generalize Hty : a.ms.msg.Type' = t at Hns ⊢
      by_cases h3 : t = W32 3
      · subst h3
        wp_auto
        simp only [rsmSendAppendEntriesRequest]
        try wp_auto
        -- `m.GetFrom()`, out of the message
        ihave #HML2 := HML
        iunfold MsgLend at HML2
        icases HML2 $$ HP with ⟨Hm, HPb⟩
        iunfold msgArg at Hm HPb
        wp_apply wp_GetFrom.1 $$ [$Hm] as Hm
        ihave HP := HPb $$ Hm
        -- `r.trk.Progress`, out of raft's state
        ihave #HRL' := HRL
        iunfold RaftLend at HRL'
        icases HRL' $$ HP with ⟨Hphys, HPb⟩
        icases ownRaftPhysC_tracker_same c r id s $$ Hphys with ⟨%tv, Htrkf, Htrk, Htback⟩
        icases ownTrackerC_progress_map c tv _ $$ Htrk with ⟨#Hprs, %Hdom, Htrk⟩
        icases (Access.access
            (A := r.[raft, go!"trk"].[tracker.ProgressTracker, go!"Progress"] ↦ tv.Progress')
            (A' := r.[raft, go!"trk"].[tracker.ProgressTracker, go!"Progress"] ↦ tv.Progress')
            (P := r.[raft, go!"trk"] ↦ tv)) $$ Htrkf with ⟨Hpf, Htrkback⟩
        wp_auto
        ihave Htrkf := Htrkback $$ Hpf
        ihave Hphys := Htback $$ %tv Htrkf Htrk
        ihave HP := HPb $$ Hphys
        wp_apply wp_map_lookup2 go.uint64 (go.GoType.PointerType tracker.Progress.ty) _ s.progress
          a.ms.msg.From' _ $$ Hprs with -
        cases hpr : s.progress !! a.ms.msg.From' with
        | none =>
          try simp only [Option.isSome_none, Bool.false_eq_true, _root_.decide_false]
          wp_auto
          imod ownMap_persist mp _ _ $$ Hmp with #Hmp
          tsm_fire MsgType.app (W64 9) noProps (tracingPropsRep_empty mp)
        | some pr =>
          try simp only [Option.isSome_some, _root_.decide_true, Option.getD_some]
          wp_auto
          -- the sender's `Progress`, out of raft's state
          ihave #HRL3 := HRL
          iunfold RaftLend at HRL3
          icases HRL3 $$ HP with ⟨Hphys, HPb⟩
          icases ownRaftPhysC_tracker_same c r id s $$ Hphys with ⟨%tv2, Htrkf, Htrk, Htback⟩
          icases ownTrackerC_lookup_same c tv2 _ a.ms.msg.From' pr hpr $$ Htrk with ⟨%pp, %Hv, Hp, Hpb⟩
          iunfold ownProgress at Hp
          iNamed Hp
          wp_auto
          wp_apply wp_mapInsert $$ [$Hmp] as Hmp
          wp_apply wp_mapInsert $$ [$Hmp] as Hmp
          ihave Hp := ownProgress_intro pr pv pp $$ Hpv Hinfl %Habs
          ihave Htrk := Hpb $$ Hp
          ihave Hphys := Htback $$ %tv2 Htrkf Htrk
          ihave HP := HPb $$ Hphys
          imod ownMap_persist mp _ _ $$ Hmp with #Hmp
          tsm_fire MsgType.app (W64 9) { noProps with propMatch := some pv.Match', propNext := some pv.Next' }
            (tracingPropsRep_mn mp pv.Match' pv.Next')
      rw [decide_eq_false h3]
      wp_auto
      by_cases h7 : t = W32 7
      · subst h7; exact absurd rfl Hns
      by_cases h8 : t = W32 8
      · subst h8
        wp_auto
        imod ownMap_persist mp _ _ $$ Hmp with #Hmp
        tsm_fire MsgType.heartbeat (W64 9) noProps (tracingPropsRep_empty mp)
      by_cases h9 : t = W32 9
      · subst h9
        wp_auto
        imod ownMap_persist mp _ _ $$ Hmp with #Hmp
        tsm_fire MsgType.heartbeatResp (W64 11) noProps (tracingPropsRep_empty mp)
      by_cases h4 : t = W32 4
      · subst h4
        wp_auto
        imod ownMap_persist mp _ _ $$ Hmp with #Hmp
        tsm_fire MsgType.appResp (W64 11) noProps (tracingPropsRep_empty mp)
      by_cases h5 : t = W32 5
      · subst h5
        wp_auto
        imod ownMap_persist mp _ _ $$ Hmp with #Hmp
        tsm_fire MsgType.vote (W64 13) noProps (tracingPropsRep_empty mp)
      by_cases h6 : t = W32 6
      · subst h6
        wp_auto
        imod ownMap_persist mp _ _ $$ Hmp with #Hmp
        tsm_fire MsgType.voteResp (W64 15) noProps (tracingPropsRep_empty mp)
      -- a type the hook does not trace: nothing logged
      simp only [decide_eq_false h7]
      try wp_auto
      simp only [decide_eq_false h8]
      try wp_auto
      simp only [decide_eq_false h9]
      try wp_auto
      simp only [decide_eq_false h4]
      try wp_auto
      simp only [decide_eq_false h5]
      try wp_auto
      simp only [decide_eq_false h6]
      try wp_auto
      subst HoE
      rw [sendGate_none_of (fun ty hty => (untraced_type ⟨h3, h4, h5, h6, h7, h8, h9⟩ ty (Hty ▸ hty)).1)]
      dsimp only [TraceFireOpt]
      iapply HΦ
      iframe Hfire
      iapply (trOwn_some γd _).2
      iapply Hback $$ HP

end proof

end EtcdGrove
end Perennial
