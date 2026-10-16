/- Lean-first (no Rocq counterpart; 2026-10-12, read-index).

Since 2026-10-14 (the pinned raft with the single-voter fix): `r.trk.Voters[0][r.id]` is a
lookup in the incoming voter set (`wp_idset_lookup2`), `IsSingleton` the sizes of the two
halves (`IsSingleton.spec_trackerC`); both true is `CfgSingle c id` (`cfgSingle_iff`), and
then `responseToReadIndexReq` at the commit index and, for a forwarded request, the `send` of
its response: `readRespond` of the request (the state's `arriveReq`).

Otherwise the option is `ReadOnlySafe` (`ownReadOnly_option`), so the lease-based branch is dead.
`addRequest` at the commit index; `heartbeatCtx` of the non-empty queue is the position,
which `recvAck` records for the leader itself (`readonlyArrive`, through `hbCtx_add`); the
heartbeats then carry the context of the queue with the request (`hbCtx_recvAck`).
-/
module

public import Raft37.Spec.go_etcd_io.raft.v3.raftpb.Message__GetTo
public import Raft37.Spec.go_etcd_io.raft.v3.sendMsgReadIndexResponse
public import Raft37.Spec.go_etcd_io.raft.v3.readOnly__addRequest
public import Raft37.Spec.go_etcd_io.raft.v3.readOnly__recvAck
public import Raft37.Spec.go_etcd_io.raft.v3.readOnly__heartbeatCtx
public import Raft37.Spec.go_etcd_io.raft.v3.raft__send
public import Raft37.Spec.go_etcd_io.raft.v3.tracker.ProgressTracker__IsSingleton

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section helpers
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The incoming voter set of the tracker, borrowed. -/
theorem ownTrackerC_incoming (c : CfgM) (tv : tracker.ProgressTracker) (t : Trk) :
    ⊢ ownTrackerC (GF := GF) c tv t -∗
      ∃ (vin vout : Loc), ⌜tv.Config'.Voters'.arr = [vin, vout]⌝ ∗
        ownIdsetQ vin (DFrac.own 1) c.incoming ∗
        (ownIdsetQ vin (DFrac.own 1) c.incoming -∗ ownTrackerC c tv t) := by
  obtain ⟨votes, prs, pvs⟩ := t
  iintro Hown
  iunfold ownTrackerC at Hown
  iNamed Hown
  icases ownCfgCC_voters _ _ $$ Hcfg with ⟨%vin, %vout, %Harr, Hv0, Hv1, Hcback⟩
  iexists vin, vout
  isplitr
  · ipureintro; exact Harr
  iframe Hv0
  iintro Hv0
  ihave Hcfg := Hcback $$ Hv0 Hv1
  iapply ownTrackerC_intro c tv votes prs pvs Hinv Hdom Hflags Hsize HmaxInfl
    $$ Hvotes Hprs Hprogs Hcfg

/-- `array_acc`, putting back the same element. -/
theorem array_acc_same {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (p : Loc)
    (i : Int) (dq : DFrac) (n : Int) (a : GoArray V n) (v : V)
    (hpos : 0 ≤ i) (hlookup : a.arr[i.toNat]? = some v) :
    typedPointsto (GF := GF) p a dq ⊢
      iprop(typedPointsto (arrayIndexRef V i p) v dq ∗
        (typedPointsto (arrayIndexRef V i p) v dq -∗ typedPointsto p a dq)) := by
  have hset : a.arr.set i.toNat v = a.arr := by
    obtain ⟨h, rfl⟩ := List.getElem?_eq_some_iff.1 hlookup
    exact List.set_getElem_self h
  iintro Ha
  icases array_acc (GF := GF) p i dq n a v hpos hlookup $$ Ha with ⟨Hv, Ha⟩
  iframe Hv
  iintro Hv
  ihave Ha := Ha $$ %v Hv
  rw [hset]
  iexact Ha

end helpers

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem sendMsgReadIndexResponse.wp_proof
    (wp_IsSingleton : tracker.ProgressTracker.IsSingleton.spec (GF := GF) (hG := hG))
    (wp_raft_responseToReadIndexReq : raft.responseToReadIndexReq.spec (GF := GF) (hG := hG))
    (wp_raft_send : raft.send.spec (GF := GF) (hG := hG))
    (wp_readOnly_addRequest : readOnly.addRequest.spec (GF := GF) (hG := hG))
    (wp_readOnly_recvAck : readOnly.recvAck.spec (GF := GF) (hG := hG))
    (wp_readOnly_heartbeatCtx : readOnly.heartbeatCtx.spec (GF := GF) (hG := hG))
    (wp_raft_bcastHeartbeat : raft.bcastHeartbeat.spec (GF := GF) (hG := hG))
    (wp_Message_GetTo : raftpb.Message.GetTo.spec (GF := GF) (hG := hG)) :
    sendMsgReadIndexResponse.spec (GF := GF) (hG := hG) := by
  intro c r id s ml m ents sn ctx rs Hlead Hne
  wp_start as ⟨Hphys, #Hm⟩
  wp_auto
  -- `_, isVoter := r.trk.Voters[0][r.id]`
  wp_apply raft.wp_load_idC $$ Hphys as Hphys
  icases ownRaftPhysC_tracker_same c r id s $$ Hphys with ⟨%tv, Htrkf, Htrk, Hback⟩
  icases ownTrackerC_incoming c tv _ $$ Htrk with ⟨%vin, %vout, %Harr, Hv0, Htrkback⟩
  icases (go_etcd_io.raft.v3.tracker.ProgressTracker.ProgressTracker_access_load_Config
    _ tv (DFrac.own 1)).access_strict $$ Htrkf with ⟨Hcf, Hcfback⟩
  icases (go_etcd_io.raft.v3.tracker.Config.Config_access_load_Voters
    _ tv.Config' (DFrac.own 1)).access_strict $$ Hcf with ⟨Hvf, Hvfback⟩
  icases array_acc_same (GF := GF) _ (sint.Z (W64 0)) _ _ _ vin (by decide)
      (by simp [Harr]) $$ Hvf with ⟨Hv0f, Hv0back⟩
  wp_auto
  ihave Hvf := Hv0back $$ Hv0f
  ihave Hcf := Hvfback $$ Hvf
  ihave Htrkf := Hcfback $$ Hcf
  wp_apply wp_idset_lookup2 $$ Hv0 as Hv0
  ihave Htrk := Htrkback $$ Hv0
  by_cases Hin : (c.incoming !! id).isSome = true
  · rw [decide_eq_true Hin]
    wp_auto
    -- `r.trk.IsSingleton()`
    wp_apply (tracker.ProgressTracker.IsSingleton.spec_trackerC wp_IsSingleton c _ (DFrac.own 1)
      tv _) $$ [$Htrkf $Htrk] as ⟨Htrkf, Htrk⟩
    ihave Hphys := Hback $$ %tv Htrkf Htrk
    by_cases Hsz : GMap.size c.incoming = 1 ∧ GMap.size c.outgoing = 0
    · -- the leader is the single voter: answered at once at the commit index
      have Hsg : CfgSingle c id := (cfgSingle_iff c id).2 ⟨Hin, Hsz.1, Hsz.2⟩
      rw [decide_eq_true Hsz]
      wp_auto
      wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
      icases ownRaftPhysC_log_same c r id s $$ Hphys with ⟨Hlog, Hlogback⟩
      icases ownRaftLog_struct _ _ $$ Hlog with ⟨%lv, Hl, %Hlv, Hlb⟩
      wp_auto
      ihave Hlog := Hlb $$ Hl
      obtain ⟨Hcm, -⟩ := Hlv
      rw [Hcm]
      ihave Hphys := Hlogback $$ Hlog
      obtain ⟨e, es, rfl⟩ : ∃ e es, ents = e :: es := by
        cases ents with
        | nil => exact absurd rfl Hne
        | cons e es => exact ⟨e, es, rfl⟩
      wp_apply wp_raft_responseToReadIndexReq c r id s ml m s.logst.committed e es sn ctx rs
        $$ [$Hphys $Hm] as %resp Hpost
      by_cases Hloc : m.From' = W64 0 ∨ m.From' = id
      · -- a local request: a `ReadState`
        rw [ite_eq_left_of_eq_true _ _ (eq_true Hloc)]
        icases Hpost with ⟨Hphys, Hresp⟩
        wp_apply wp_Message_GetTo.1 resp (DFrac.own 1) DFrac.discard false _ $$ [$Hresp] as Hresp
        iapply HΦ
        iframe Hphys
        ipureintro
        left
        refine ⟨Hsg, ?_⟩
        have Hl : (arriveReq s m (e :: es)).src = W64 0 ∨ (arriveReq s m (e :: es)).src = id := Hloc
        rw [readRespond, ite_eq_left_of_eq_true _ _ (eq_true Hl)]
        rfl
      · -- a forwarded one: the response
        rw [ite_eq_right_of_eq_false _ _ (eq_false Hloc)]
        icases Hpost with ⟨Hphys, Hresp⟩
        wp_apply wp_Message_GetTo.1 resp (DFrac.own 1) DFrac.discard false _ $$ [$Hresp] as Hresp
        rw [decide_eq_false (fun h => Hloc (Or.inl h))]
        wp_auto
        wp_apply wp_raft_send c r id s resp (readIndexRespMsg m s.logst.committed) (e :: es) none
            [] []
            [absMsgFrom .readIndexResp (readIndexRespMsg m s.logst.committed) id s.term
              (e :: es) []]
            (Or.inl rfl)
            (Or.inr (Or.inl ⟨.readIndexResp, Or.inr (Or.inr (Or.inl rfl)), rfl, rfl,
              fun h => Hloc (Or.inr h), rfl⟩))
            (fun h => by simp [readIndexRespMsg, MsgSnap] at h)
          $$ [$Hphys $Hresp]
        iintro Hphys
        wp_auto
        iapply HΦ
        iframe Hphys
        ipureintro
        left
        refine ⟨Hsg, ?_⟩
        have Hl : ¬ ((arriveReq s m (e :: es)).src = W64 0 ∨ (arriveReq s m (e :: es)).src = id) :=
          Hloc
        rw [readRespond, ite_eq_right_of_eq_false _ _ (eq_false Hl)]
        rfl
    · have Hns : ¬ CfgSingle c id := fun h => Hsz ((cfgSingle_iff c id).1 h).2
      rw [decide_eq_false Hsz]
      wp_auto
      -- `switch r.readOnly.option`: `ReadOnlySafe`
      icases ownRaftPhysC_readOnly c r id s $$ Hphys with ⟨%ro, Hrof, Hro, Hback⟩
      icases ownReadOnly_option ro _ $$ Hro with ⟨%o, %Hosafe, Hopt, Hroback⟩
      wp_auto
      ihave Hro := Hroback $$ Hopt
      ihave Hphys := Hback $$ %ro %_ Hrof Hro
      ihave Hphys := ownRaftPhysC_eq c r id _ s rfl $$ Hphys
      subst Hosafe
      wp_auto
      -- `addRequest(r.raftLog.committed, m)`
      wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
      icases ownRaftPhysC_log_same c r id s $$ Hphys with ⟨Hlog, Hlogback⟩
      icases ownRaftLog_struct _ _ $$ Hlog with ⟨%lv, Hl, %Hlv, Hlb⟩
      wp_auto
      ihave Hlog := Hlb $$ Hl
      obtain ⟨Hcm, -⟩ := Hlv
      rw [Hcm]
      ihave Hphys := Hlogback $$ Hlog
      icases ownRaftPhysC_readOnly c r id s $$ Hphys with ⟨%ro, Hrof, Hro, Hback⟩
      wp_auto
      wp_apply wp_readOnly_addRequest $$ [$Hro $Hm] as Hro
      ihave Hphys := Hback $$ %ro %_ Hrof Hro
      -- `recvAck(r.id, heartbeatCtx())`: the queue is not empty
      wp_apply raft.wp_load_idC $$ Hphys as Hphys
      icases ownRaftPhysC_readOnly $$ Hphys with ⟨%ro, Hrof, Hro, Hback⟩
      wp_auto
      wp_apply wp_readOnly_heartbeatCtx $$ [$Hro] as %sl ⟨Hro, Hsl⟩
      icases Hsl with (⟨%Hpend, -⟩ | ⟨-, Hsl, -⟩)
      · simp at Hpend
      wp_apply wp_readOnly_recvAck $$ [$Hro $Hsl] as ⟨Hro, -⟩
      · ipureintro; right; simp [u64Le_length]
      ihave Hphys := Hback $$ %ro %_ Hrof Hro
      ihave Hphys := ownRaftPhysC_eq c r id _ (arriveState id s m ents)
        (by simp only [arriveState, readonlyArrive, arriveReq, hbCtx_add]) $$ Hphys
      -- `bcastHeartbeat()`
      wp_apply wp_raft_bcastHeartbeat _ _ _ (arriveState id s m ents) Hlead $$ [$Hphys]
        as %ms %pvs ⟨Hphys, %Hms, %Hmm⟩
      iapply HΦ
      iframe Hphys
      ipureintro
      right
      refine ⟨Hns, ms, pvs, rfl, fun m' Hm' => ⟨(Hms m' Hm').1, ?_⟩, Hmm⟩
      rw [(Hms m' Hm').2]
      simp only [arriveState, readonlyArrive, hbCtx_recvAck]
  · have Hns : ¬ CfgSingle c id := fun h => Hin ((cfgSingle_iff c id).1 h).1
    rw [decide_eq_false Hin]
    wp_auto
    ihave Hphys := Hback $$ %tv Htrkf Htrk
    -- `switch r.readOnly.option`: `ReadOnlySafe`
    icases ownRaftPhysC_readOnly c r id s $$ Hphys with ⟨%ro, Hrof, Hro, Hback⟩
    icases ownReadOnly_option ro _ $$ Hro with ⟨%o, %Hosafe, Hopt, Hroback⟩
    wp_auto
    ihave Hro := Hroback $$ Hopt
    ihave Hphys := Hback $$ %ro %_ Hrof Hro
    ihave Hphys := ownRaftPhysC_eq c r id _ s rfl $$ Hphys
    subst Hosafe
    wp_auto
    -- `addRequest(r.raftLog.committed, m)`
    wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
    icases ownRaftPhysC_log_same c r id s $$ Hphys with ⟨Hlog, Hlogback⟩
    icases ownRaftLog_struct _ _ $$ Hlog with ⟨%lv, Hl, %Hlv, Hlb⟩
    wp_auto
    ihave Hlog := Hlb $$ Hl
    obtain ⟨Hcm, -⟩ := Hlv
    rw [Hcm]
    ihave Hphys := Hlogback $$ Hlog
    icases ownRaftPhysC_readOnly c r id s $$ Hphys with ⟨%ro, Hrof, Hro, Hback⟩
    wp_auto
    wp_apply wp_readOnly_addRequest $$ [$Hro $Hm] as Hro
    ihave Hphys := Hback $$ %ro %_ Hrof Hro
    -- `recvAck(r.id, heartbeatCtx())`: the queue is not empty
    wp_apply raft.wp_load_idC $$ Hphys as Hphys
    icases ownRaftPhysC_readOnly $$ Hphys with ⟨%ro, Hrof, Hro, Hback⟩
    wp_auto
    wp_apply wp_readOnly_heartbeatCtx $$ [$Hro] as %sl ⟨Hro, Hsl⟩
    icases Hsl with (⟨%Hpend, -⟩ | ⟨-, Hsl, -⟩)
    · simp at Hpend
    wp_apply wp_readOnly_recvAck $$ [$Hro $Hsl] as ⟨Hro, -⟩
    · ipureintro; right; simp [u64Le_length]
    ihave Hphys := Hback $$ %ro %_ Hrof Hro
    ihave Hphys := ownRaftPhysC_eq c r id _ (arriveState id s m ents)
      (by simp only [arriveState, readonlyArrive, arriveReq, hbCtx_add]) $$ Hphys
    -- `bcastHeartbeat()`
    wp_apply wp_raft_bcastHeartbeat _ _ _ (arriveState id s m ents) Hlead $$ [$Hphys]
      as %ms %pvs ⟨Hphys, %Hms, %Hmm⟩
    iapply HΦ
    iframe Hphys
    ipureintro
    right
    refine ⟨Hns, ms, pvs, rfl, fun m' Hm' => ⟨(Hms m' Hm').1, ?_⟩, Hmm⟩
    rw [(Hms m' Hm').2]
    simp only [arriveState, readonlyArrive, hbCtx_recvAck]

