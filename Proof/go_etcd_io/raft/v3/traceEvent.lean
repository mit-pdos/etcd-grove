/-
Lean-first (no Rocq counterpart): the proof of `traceEvent` (`Spec/go_etcd_io/raft/v3/traceEvent.lean`).
Untraced, the nil check; traced (Q8 stage 1, slice 2), the event's builder: every field read
from raft's state (lent by the caller), then the message (slice 4: lent by the caller out of the same
resource, `makeTracingMessage` of it), the event's cell and slices made read-only, the logger's
`TraceEvent` handed the caller's update.
-/
module

public import Spec.go_etcd_io.raft.v3.traceEvent
public import Spec.go_etcd_io.raft.v3.stateMachineEventType__String
public import Spec.go_etcd_io.raft.v3.StateType__String
public import Spec.go_etcd_io.raft.v3.formatConf
public import Spec.go_etcd_io.raft.v3.makeTracingState
public import Spec.go_etcd_io.raft.v3.makeTracingMessage
public import Spec.go_etcd_io.raft.v3.raftLog__lastIndex
public import Spec.go_etcd_io.raft.v3.quorum.MajorityConfig__Slice
public import Spec.strconv.FormatUint

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

/-- `makeTracingMessage` of the message argument, either case. -/
theorem wp_makeTracingMessage_arg (h : makeTracingMessage.spec (GF := GF) (hG := hG)) (m : Loc)
    (om : Option MsgArg) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ msgArg m om }}
      (App (Val #(functions makeTracingMessage [])) (Val #m))
    {{ (p : Loc), RET #p; msgArg m om ∗ tracingMsgRep p (msgArgTrace om) }} := by
  cases om with
  | none =>
    iintro %Φ ⟨#Hpkg, Hm⟩ HΦ
    simp only [msgArg]
    icases Hm with %Hm
    subst Hm
    iapply h.1 $$ [$Hpkg]
    inext
    iintro -
    iapply HΦ $$ %null
    simp only [msgArgTrace, tracingMsgRep]
    isplitr <;> ipureintro <;> trivial
  | some a =>
    simp only [msgArg]
    iintro %Φ ⟨#Hpkg, Hm⟩ HΦ
    iapply h.2 m a.dq a.dqe a.cap a.ms $$ [$Hpkg $Hm]
    inext
    iintro %p ⟨Hm, Hrep⟩
    iapply HΦ $$ %p
    simp only [msgArgTrace]
    iframe Hm Hrep

theorem traceEvent.wp_proof
    (wp_evtString : stateMachineEventType.String.spec (GF := GF) (hG := hG))
    (wp_FormatUint : strconv.FormatUint.spec (GF := GF) (hG := hG))
    (wp_makeTracingState : makeTracingState.spec (GF := GF) (hG := hG))
    (wp_lastIndex : raftLog.lastIndex.spec (GF := GF) (hG := hG))
    (wp_Slice : quorum.MajorityConfig.Slice.spec (GF := GF) (hG := hG))
    (wp_formatConf : formatConf.spec (GF := GF) (hG := hG))
    (wp_StateString : StateType.String.spec (GF := GF) (hG := hG))
    (wp_makeTracingMessage : makeTracingMessage.spec (GF := GF) (hG := hG)) :
    traceEvent.spec (GF := GF) (hG := hG) := by
  intro evt r m prop tl tr E Q R
  wp_start as ⟨#Htl, Hown, Hfire⟩
  cases tr with
  | none =>
    icases (traceFire_none tl E Q).1 $$ Hfire with ⟨%Hok, HQ⟩
    unfold TraceLoggerOk at Hok; subst Hok
    wp_auto
    iapply HΦ
    iframe
    iapply trOwn_none_intro
  | some γd =>
    icases (trOwn_some γd _).1 $$ Hown with ⟨%c, %id, %s, %P, %om, %e0, HP, #HRL, #HML, #Hprops, %Hp, Hback⟩
    obtain ⟨Hevt, HE⟩ := Hp
    iunfold RaftLend at HRL
    icases HRL $$ HP with ⟨Hphys, HPb⟩
    dsimp only [TraceFire]
    icases Hfire with ⟨%tn, #Hdir, #Hlog, %Hnn, Hau⟩
    iunfold isTraceLogger at Hlog
    icases Hlog with (%Hn | ⟨%l, %Hl, #Hm⟩)
    · exact absurd Hn Hnn
    subst Hl
    wp_auto
    rw [method_unfold (t := go.GoType.PointerType stateMachineEventType.ty)]
    wp_call
    wp_auto
    haveI : go.NotInterface go.int := ⟨by unfold go.int; trivial⟩
    wp_apply wp_evtString evt Hevt as %nm %Hnm
    wp_apply raft.wp_load_idC $$ Hphys as Hphys
    wp_apply wp_FormatUint
    · ipureintro; word
    iintro %nid %Hnid
    wp_auto
    wp_apply wp_makeTracingState $$ [$Hphys] as %ts ⟨Hphys, %Hts⟩
    wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
    icases ownRaftPhysC_log_at (c := c) (V := c.voters) r id s $$ Hphys with ⟨Hlog, %Hgh, Hlogback⟩
    wp_apply wp_lastIndex $$ [$Hlog] as %li ⟨Hlog, %Hli⟩
    ihave Hphys := Hlogback $$ %s.logst Hlog
    ihave Hphys := Hphys $$ []
    · ipureintro; exact Hgh
    ihave Hphys : ownRaftPhysCV c c.voters r id s $$ [Hphys]
    · iapply Hphys; ipureintro; intro _; exact Int.le_refl _
    -- `r.trk.Voters[0].Slice()`, `[1]`: the tracker out of raft's state, as `ConfState`'s proof
    icases ownRaftPhysC_tracker c (V := c.voters) r id s $$ Hphys with ⟨%tv, Htrkf, Htrk, Htback⟩
    iunfold ownTrackerC at Htrk
    iNamed Htrk
    simp only at Hinv Hdom Hflags Hsize
    icases ownCfgCC_elim _ _ _ $$ Hcfg with ⟨%vin, %vout, %Harr, Hin, Hout, Hl, Hln, %Hal⟩
    have Hsz : ∀ s' : GSet w64, s' ⊆ c.ids → (GMap.size s' : Int) ≤ 2 ^ 62 := by
      intro s' hs
      have := size_le_of_sub_dom s' s.progress (by rw [Hdom]; exact hs)
      omega
    icases (Access.access
        (A := r.[raft, go!"trk"].[tracker.ProgressTracker, go!"Config"].[tracker.Config, go!"Voters"] ↦
          tv.Config'.Voters')
        (A' := r.[raft, go!"trk"].[tracker.ProgressTracker, go!"Config"].[tracker.Config, go!"Voters"] ↦
          tv.Config'.Voters')
        (P := r.[raft, go!"trk"] ↦ tv)) $$ Htrkf with ⟨Hvf, Htrkback⟩
    icases array_acc _ (sint.Z (W64 0)) _ _ _ vin (by decide) (by rw [Harr]; rfl)
      $$ Hvf with ⟨Hc0, Hcback⟩
    rw [method_unfold (t := go.GoType.PointerType quorum.MajorityConfig.ty)]
    wp_call
    wp_auto
    ihave %Hvin_nn := ownMap_not_nil $$ Hin
    wp_apply wp_Slice _ c.incoming $$ [Hin] as %sl0 %xs0 ⟨Hin, Hsl0, -, %Hxs0⟩
    · isplitl
      · unfold ownIdsetOpt; iright; iexact Hin
      · ipureintro; exact Hsz _ (incoming_sub_ids c)
    wp_apply wp_formatConf $$ [$Hsl0] as %a ⟨-, Ha⟩
    ihave Hvf := Hcback $$ Hc0
    icases array_acc _ (sint.Z (W64 1)) _ _ _ vout (by decide) (by rw [Harr]; rfl)
      $$ Hvf with ⟨Hc1, Hcback⟩
    rw [method_unfold (t := go.GoType.PointerType quorum.MajorityConfig.ty)]
    wp_call
    wp_auto
    icases ownIdsetC_split _ _ _ $$ Hout with ⟨Hoq, %Hoc⟩
    wp_apply wp_Slice vout c.outgoing $$ [Hoq] as %sl1 %xs1 ⟨Hoo, Hsl1, -, %Hxs1⟩
    · isplitl
      · unfold ownIdsetOpt; iapply ownIdsetQ_elim _ _ _ $$ Hoq
      · ipureintro; exact Hsz _ (outgoing_sub_ids c)
    wp_apply wp_formatConf $$ [$Hsl1] as %b ⟨-, Hb⟩
    ihave Hvf := Hcback $$ Hc1
    have HarrEq : array.mk 2 ((tv.Config'.Voters'.arr.set (sint.Z (W64 0)).toNat vin).set
        (sint.Z (W64 1)).toNat vout) = tv.Config'.Voters' := by
      generalize tv.Config'.Voters' = a at Harr ⊢
      cases a
      simp only at Harr
      subst Harr
      rfl
    rw [HarrEq]
    ihave Htrkf := Htrkback $$ Hvf
    ihave Hin : ownIdsetQ (GF := GF) vin (DFrac.own 1) c.incoming $$ [Hin]
    · unfold ownIdsetQ; iunfold ownIdsetOpt at Hin; iexact Hin
    ihave Hin := ownIdsetQ_not_nil _ _ _ Hvin_nn $$ Hin
    ihave Hoq : ownIdsetQ (GF := GF) vout (DFrac.own 1) c.outgoing $$ [Hoo]
    · unfold ownIdsetQ; iunfold ownIdsetOpt at Hoo; iexact Hoo
    ihave Hout := ownIdsetC_join _ _ _ Hoc $$ Hoq
    ihave Hcfg := ownCfgCC_intro tv.Config' (DFrac.own 1) c vin vout Harr Hal $$ Hin Hout Hl Hln
    ihave Htrk := ownTrackerC_intro c tv s.votes s.progress s.prvals Hinv Hdom Hflags Hsize HmaxInfl
      $$ Hvotes Hprs Hprogs Hcfg
    ihave Hphys := Htback $$ %tv %s.votes Htrkf Htrk
    ipersist Ha
    ipersist Hb
    ihave Hphys : ownRaftPhysCV c c.voters r id s $$ [Hphys]
    · iexact Hphys
    -- `r.state.String()`
    rw [method_unfold (t := go.GoType.PointerType StateType.ty)]
    wp_call
    wp_apply raft.wp_load_stateC $$ Hphys as Hphys
    try wp_auto
    haveI : go.NotInterface go.uint64 := ⟨by unfold go.uint64; trivial⟩
    wp_apply wp_StateString s.role
    -- the message, out of the caller's resource
    ihave HP := HPb $$ Hphys
    iunfold MsgLend at HML
    icases HML $$ HP with ⟨Hmsg, HPb⟩
    wp_apply (wp_makeTracingMessage_arg wp_makeTracingMessage m om) $$ [$Hmsg] as %pm ⟨Hmsg, #Hmrep⟩
    ihave HP := HPb $$ Hmsg
    try wp_auto
    ipersist «$a0»
    rw [domSet_gset] at Hxs0 Hxs1
    have HEv : EvHdrOf evt id s c
        ⟨nm, nid, ts.Term', ts.Vote', ts.Commit', roleStr s.role, li, (xs0.map decStr, xs1.map decStr),
          msgArgTrace om, none, e0.propCC, e0.propMatch, e0.propNext⟩ := by
      refine ⟨Hnm, Hnid, Hts.1, Hts.2.1, Hts.2.2, rfl, ?_, ⟨xs0, xs1, Hxs0, Hxs1, rfl⟩⟩
      rw [plastIndex_toPState]
      unfold logLast
      word
    ihave #Hrep : tracingEventRep «$a0_ptr»
        (⟨nm, nid, ts.Term', ts.Vote', ts.Commit', roleStr s.role, li, (xs0.map decStr, xs1.map decStr),
          msgArgTrace om, none, e0.propCC, e0.propMatch, e0.propNext⟩ : TraceEv) $$ []
    · iunfold tracingEventRep
      iexists _, a, b
      iframe «$a0» Ha Hb
      isplitr
      · ipureintro; trivial
      isplitr
      · iexact Hmrep
      isplitr
      · simp only [tracingCCRep]; itrivial
      simp only
      iapply tracingPropsRep_of prop _ e0 ?_ ?_ ?_ $$ Hprops
      all_goals rfl
    ihave Hupd := Hau $$ %_ []
    · ipureintro; exact HE _ HEv rfl rfl rfl rfl rfl
    wp_bind (App (Val #(methods l.ty go!"TraceEvent" l.v)) (Val #«$a0_ptr»))
    iapply wp_wand $$ (Hm $$ %«$a0_ptr» %_ %Q Hrep Hupd)
    iintro %v ⟨%Hv, HQ⟩
    subst Hv
    wp_auto
    iapply HΦ
    iframe HQ
    iapply (trOwn_some γd R).2
    iapply Hback $$ HP

end proof

end EtcdGrove
end Perennial
