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
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetType
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetFrom
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetEntries
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetIndex
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetData
public import Proof.go_etcd_io.raft.v3.TracedUntraced
public import Proof.go_etcd_io.raft.v3.TracedUntracedStep

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
  `ownRaftPhysC_misc`.

raft v3.7 (2026-10-15, stage R4): the type is read by `m.GetType()` and the other fields by
their getters (`GetFrom`, `GetEntries`, `GetIndex`, `Entry.GetData`, each a callee). A forwarded
message (`MsgProp`, `MsgReadIndex`, `MsgTransferLeader`) gets `m.To = new(r.lead)`: a fresh cell
frozen (`cellRO_alloc`) and stored (`msgPtsC_store_To`), then the message is frozen as raft's
(`msgIn_to_msgOwn`) and given to `send`; `MsgApp`/`MsgSnap` hand the received message to
`handleAppendEntries`/`handleSnapshot` (entries read-only: not a `MsgProp`). A `MsgReadIndexResp`'s
`ReadState` holds the entry's data slice (`readStatesPts`, D6). -/
theorem stepFollower.wp_proof
    (wp_raft_handleAppendEntries : raft.handleAppendEntries.spec (GF := GF) (hG := hG))
    (wp_raft_handleHeartbeat : raft.handleHeartbeat.spec (GF := GF) (hG := hG))
    (wp_raft_handleSnapshot : raft.handleSnapshot.spec (GF := GF) (hG := hG))
    (wp_raft_send : raft.send.spec (GF := GF) (hG := hG))
    (wp_raft_hup : raft.hup.spec (GF := GF) (hG := hG))
    (wp_GetType : raftpb.Message.GetType.spec (GF := GF) (hG := hG))
    (wp_GetFrom : raftpb.Message.GetFrom.spec (GF := GF) (hG := hG))
    (wp_GetEntries : raftpb.Message.GetEntries.spec (GF := GF) (hG := hG))
    (wp_GetIndex : raftpb.Message.GetIndex.spec (GF := GF) (hG := hG))
    (wp_GetData : raftpb.Entry.GetData.spec (GF := GF) (hG := hG)) :
    stepFollower.spec (GF := GF) (hG := hG) := by
  -- (Q8 stage 1, slice 8) the gated specs, each arm consuming its gates; a `MsgSnap` untraced
  intro c scfg r id s ml m ents sn rs sv cl G G' Hty Hri Hstz Hprop Happ Hhb Hrest Hsnap Hnors Hpinv Hidx Hxtr
  wp_start as H
  iNamed H
  ihave #Hinit := isInitialized_access $$ Hpkg
  unfold isInitialized
  icases Hinit with ⟨%e1, %e2, %e3, %e4, %errPropDropped, %gr, %_, %_, %_, %_, #Hinit⟩
  iNamed Hinit
  wp_auto
  wp_apply wp_GetType.1 ml _ _ _ _ $$ [$Hm] as Hm
  rcases Hty with Hty | Hty | Hty | Hty | Hty | Hty | Hty | Hty | Hty | Hty | Hty | Hty | Hty |
    Hty
  · -- `MsgVoteResp`: no arm
    simp only [Hty, MsgVoteResp]
    wp_auto
    iapply HΦ $$ %GoInterface.nil %s %false %c
    iframe Hphys
    simp only [Bool.false_eq_true, ↓reduceIte]
    isplitr [HG]
    · ipureintro
      simp [FollowerStepResultC, MsgSnap, Hty, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat,
        MsgAppResp, MsgHeartbeatResp, MsgCheckQuorum, MsgSnap, MsgPreVoteResp]
    isplitr [HG]
    · ipureintro; first | rfl | trivial
    iright; isplitr
    · ipureintro; simp [MsgApp, MsgHeartbeat, MsgTimeoutNow]
    iidx HG
  · -- `MsgProp`
    obtain ⟨Hfrom0, Hterm0, Hlid⟩ := Hprop Hty
    simp only [Hty, MsgProp]
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
      isplitr [HG]
      · ipureintro
        simp [FollowerStepResultC, MsgSnap, Hty, Hlead, MsgVoteResp, MsgProp]
      isplitr [HG]
      · iexact ErrPropDropped
      iright; isplitr
      · ipureintro; simp [MsgApp, MsgHeartbeat, MsgTimeoutNow]
      iidx HG
    · -- forwarded to the leader: `m.To = new(r.lead)`, the message frozen and sent
      rw [decide_eq_false Hlead]
      wp_auto
      wp_apply raft.wp_load_disableProposalForwardingC $$ Hphys as Hphys
      wp_apply raft.wp_load_leadC $$ Hphys as Hphys
      imod cellRO_alloc $$ «$r0» with #cTo
      icases msgPtsC_store_To _ _ _ _ $$ Hm with ⟨%pTo, HTo, Hback⟩
      wp_auto
      ihave Hm := Hback $$ %_ %s.lead HTo cTo
      imod msgIn_to_msgOwn $$ Hm with Hm
      ihave Hgs : HookGateOpt s.gh.tr r (sendOutGate id s c ({ m with To' := s.lead } : MessageM).Type'
          [propForward id s.lead m ents cl]) (G (s.outbox ++ [propForward id s.lead m ents cl])) $$ [Hgfwd HG]
      · have hn : sendOutGate id s c ({ m with To' := s.lead } : MessageM).Type'
            [propForward id s.lead m ents cl] = none := by
          show sendOutGate id s c m.Type' _ = none
          rw [Hty]; rfl
        rw [hn]
        iapply Hgfwd $$ %(by first | exact Or.inl trivial | exact Or.inl Hty) %([propForward id s.lead m ents cl])
          %(by intro x hx; simp only [List.mem_singleton] at hx; subst hx; rfl) HG
      wp_apply wp_raft_send c r id s ml { m with To' := s.lead } ents sn cl rs
          [propForward id s.lead m ents cl] (G (s.outbox ++ [propForward id s.lead m ents cl]))
          (Or.imp_right Or.inl Hfrom0)
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Hty, Hterm0, fun h => Hlid h, rfl⟩)))))
          (fun h => by simp [Hty, MsgProp, MsgSnap] at h)
          (fun h => by simp [Hty, MsgProp, MsgApp] at h)
        (Hnors (.inl Hty))
        (fun _ => mtypeOf_send_eq Hty) $$ [$Hphys $Hm $Hgs]
        as ⟨Hphys, HG⟩
      · iapply tsSrc_ne; exact (fun h => by simp [Hty, MsgProp, MsgSnap] at h)
      iapply HΦ $$ %GoInterface.nil %_ %false %c
      iframe Hphys
      simp only [Bool.false_eq_true, ↓reduceIte]
      isplitr [HG]
      · ipureintro
        simp [FollowerStepResultC, MsgSnap, Hty, MsgVoteResp, MsgProp]
        exact Hlead
      isplitr [HG]
      · ipureintro; first | rfl | trivial
      iright; isplitr
      · ipureintro; simp [MsgApp, MsgHeartbeat, MsgTimeoutNow]
      iidx HG
  · -- `MsgApp`: adopt the sender as leader, then `handleAppendEntries`
    obtain ⟨Hwf, Hnw, Hconf, Hfid, Hnl⟩ := Happ Hty
    rw [show (if m.Type' = MsgProp then DFrac.own 1 else DFrac.discard) = DFrac.discard by
      simp [Hty, MsgApp, MsgProp]]
    ihave Hga := Hgapp $$ %Hty
    simp only [Hty, MsgApp]
    wp_auto
    wp_apply raft.wp_store_electionElapsedC $$ Hphys as Hphys
    wp_apply wp_GetFrom.1 ml _ _ _ _ $$ [$Hm] as Hm
    wp_apply raft.wp_store_leadC $$ Hphys as Hphys
    ihave Hga2 : ∀ (s1 : NState) (mm : Msg),
        ⌜HandleAppResult id ({ s with lead := m.From' } : NState) m ents (sendMsgs s1 [mm])⌝ -∗
        G s.outbox -∗ HookGateOpt ({ s with lead := m.From' } : NState).gh.tr r
          (sendOutGate id s1 c MsgAppResp [mm]) (G' (sendMsgs s1 [mm]).outbox) $$ [Hga]
    · iintro %s1 %mm %Hr HG
      ispecialize Hga $$ %s1 %mm %Hr HG
      iapply hookGateOpt_congr _ _ r _ _ _ (by rfl) (by rfl) $$ Hga
    wp_apply wp_raft_handleAppendEntries c r id { s with lead := m.From' } ml m ents sn cl rs
        (G s.outbox) G'
        Hwf Hnw Hconf Hfid Hty Hnl (by simp only; first | exact Hstz (Or.inl Hty) | exact Hstz (Or.inr (Or.inl Hty)) | exact Hstz (Or.inr (Or.inr Hty)))
        $$ [$Hphys $Hm $HG $Hga2] as %s' ⟨Hphys, %Hres, HG⟩
    iapply HΦ $$ %GoInterface.nil %s' %false %c
    iframe Hphys
    simp only [Bool.false_eq_true, ↓reduceIte]
    isplitr [HG]
    · ipureintro
      simp [FollowerStepResultC, MsgSnap, Hty, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat,
        MsgAppResp, MsgHeartbeatResp, MsgCheckQuorum, MsgSnap, MsgPreVoteResp]
      exact Hres
    isplitr [HG]
    · ipureintro; first | rfl | trivial
    ileft; isplitr
    · ipureintro; simp
    iidx HG
  · -- `MsgHeartbeat`: adopt the sender as leader, then `handleHeartbeat`
    obtain ⟨Hcommit, Hfrom⟩ := Hhb Hty
    ihave Hgh := Hghb $$ %Hty
    simp only [Hty, MsgHeartbeat]
    wp_auto
    wp_apply raft.wp_store_electionElapsedC $$ Hphys as Hphys
    wp_apply wp_GetFrom.1 ml _ _ _ _ $$ [$Hm] as Hm
    wp_apply raft.wp_store_leadC $$ Hphys as Hphys
    ihave Hgh2 : G s.outbox -∗ HookGateOpt ({ s with lead := m.From' } : NState).gh.tr r
        (sendOutGate id { ({ s with lead := m.From' } : NState) with
            logst := { ({ s with lead := m.From' } : NState).logst with
              committed := plogCommitTo ({ s with lead := m.From' } : NState).logst.committed m.Commit' } }
          c MsgHeartbeatResp
          [{ Msg.plain .heartbeatResp id m.From' ({ s with lead := m.From' } : NState).term false with ctx := cl }])
        (G' (s.outbox ++ [{ Msg.plain .heartbeatResp id m.From' s.term false with ctx := cl }])) $$ [Hgh]
    · iintro HG
      ispecialize Hgh $$ HG
      iapply hookGateOpt_congr _ _ r _ _ _ (by rfl) (by rfl) $$ Hgh
    wp_apply wp_raft_handleHeartbeat c r id { s with lead := m.From' } ml _ _ _ m ents sn cl rs (G s.outbox)
        (G' (s.outbox ++ [{ Msg.plain .heartbeatResp id m.From' s.term false with ctx := cl }]))
        Hcommit Hfrom (by simp only; first | exact Hstz (Or.inl Hty) | exact Hstz (Or.inr (Or.inl Hty)) | exact Hstz (Or.inr (Or.inr Hty)))
        $$ [$Hphys $Hm $HG $Hgh2] as ⟨Hphys, -, HG⟩
    iapply HΦ $$ %GoInterface.nil %_ %false %c
    iframe Hphys
    simp only [Bool.false_eq_true, ↓reduceIte]
    isplitr [HG]
    · ipureintro
      simp [FollowerStepResultC, MsgSnap, Hty, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat,
        MsgAppResp, MsgHeartbeatResp, MsgCheckQuorum, MsgSnap, MsgPreVoteResp]
    isplitr [HG]
    · ipureintro; first | rfl | trivial
    ileft; isplitr
    · ipureintro; simp
    iidx HG
  · -- `MsgBeat`, `MsgAppResp`, `MsgHeartbeatResp`: no arm
    rcases Hty with Hty' | Hty' | Hty' | Hty' <;>
      simp only [Hty', MsgBeat, MsgAppResp, MsgHeartbeatResp, MsgCheckQuorum] <;> wp_auto
    all_goals
      iapply HΦ $$ %GoInterface.nil %s %false %c
      iframe Hphys
      simp only [Bool.false_eq_true, ↓reduceIte]
      isplitr [HG]
      · ipureintro
        simp [FollowerStepResultC, MsgSnap, Hty', MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat,
          MsgAppResp, MsgHeartbeatResp, MsgCheckQuorum, MsgSnap, MsgPreVoteResp]
      isplitr [HG]
      · ipureintro; first | rfl | trivial
      iright; isplitr
      · ipureintro; simp [MsgApp, MsgHeartbeat, MsgTimeoutNow]
      iidx HG
  · -- `MsgSnap`: adopt the sender as leader, then `handleSnapshot` (untraced only)
    obtain ⟨Hsn, Hscfg, Hscope, Hrole, Hvotes, Hfid, Hns, Htr⟩ := Hsnap Hty
    rw [show (if m.Type' = MsgProp then DFrac.own 1 else DFrac.discard) = DFrac.discard by
      simp [Hty, MsgSnap, MsgProp]]
    simp only [Hty, MsgSnap]
    wp_auto
    wp_apply raft.wp_store_electionElapsedC $$ Hphys as Hphys
    wp_apply wp_GetFrom.1 ml _ _ _ _ $$ [$Hm] as Hm
    wp_apply raft.wp_store_leadC $$ Hphys as Hphys
    ihave #Hcs : ksnCert (GF := GF) s.gh.sn (snapTrip sv sv.Metadata'.ConfState'.lists) $$ []
    · iunfold rcvSrc at Hcert
      icases Hcert with (%Hn | ⟨%sv', %Hsv', #Hc⟩)
      · exact (Hn rfl).elim
      · rw [Hsn] at Hsv'; obtain rfl := Option.some.inj Hsv'; iexact Hc
    wp_apply wp_raft_handleSnapshot c r id { s with lead := m.From' } ml m ents sn cl rs sv scfg
        Hrole Hvotes Hsn Hscfg Hscope Hfid Hns (by simp only; first | exact Hstz (Or.inl Hty) | exact Hstz (Or.inr (Or.inl Hty)) | exact Hstz (Or.inr (Or.inr Hty))) (by tr_none) $$ [$Hphys $Hm $Hcs]
      as %s' ⟨Hphys, %Hres⟩
    -- (2026-11-10, slice 14) untraced: the caller's resource ignores the outbox
    ihave HG : G s'.outbox $$ [HG]
    · rw [Hidx Htr s'.outbox s.outbox]; iexact HG
    iapply HΦ $$ %GoInterface.nil %s' %false %c
    iframe Hphys
    simp only [Bool.false_eq_true, ↓reduceIte]
    isplitr [HG]
    · ipureintro
      simp [FollowerStepResultC, MsgSnap, Hty, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat,
        MsgAppResp, MsgHeartbeatResp, MsgCheckQuorum, MsgSnap, MsgPreVoteResp]
      exact Hres
    isplitr [HG]
    · ipureintro; first | rfl | trivial
    iright; isplitr
    · ipureintro; simp [MsgApp, MsgHeartbeat, MsgTimeoutNow]
    iidx HG
  · -- `MsgPreVoteResp` (2026-10-04): no arm
    simp only [Hty, MsgPreVoteResp]
    wp_auto
    iapply HΦ $$ %GoInterface.nil %s %false %c
    iframe Hphys
    simp only [Bool.false_eq_true, ↓reduceIte]
    isplitr [HG]
    · ipureintro
      simp [FollowerStepResultC, MsgSnap, Hty, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat,
        MsgAppResp, MsgHeartbeatResp, MsgCheckQuorum, MsgSnap, MsgPreVoteResp]
    isplitr [HG]
    · ipureintro; first | rfl | trivial
    iright; isplitr
    · ipureintro; simp [MsgApp, MsgHeartbeat, MsgTimeoutNow]
    iidx HG
  · -- `MsgReadIndex` (2026-10-12): forwarded to the leader, if any
    obtain ⟨Hterm0, Hlid⟩ := Hri Hty
    simp only [Hty, MsgReadIndex]
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
      isplitr [HG]
      · ipureintro
        simp [FollowerStepResultC, MsgSnap, Hty, Hlead, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat,
          MsgBeat, MsgAppResp, MsgHeartbeatResp, MsgCheckQuorum, MsgSnap, MsgPreVoteResp, MsgReadIndex]
      isplitr [HG]
      · ipureintro; first | rfl | trivial
      iright; isplitr
      · ipureintro; simp [MsgApp, MsgHeartbeat, MsgTimeoutNow]
      iidx HG
    · -- forwarded to the leader
      rw [decide_eq_false Hlead]
      wp_auto
      wp_apply raft.wp_load_leadC $$ Hphys as Hphys
      imod cellRO_alloc $$ «$r0» with #cTo
      icases msgPtsC_store_To _ _ _ _ $$ Hm with ⟨%pTo, HTo, Hback⟩
      wp_auto
      ihave Hm := Hback $$ %_ %s.lead HTo cTo
      imod msgIn_to_msgOwn $$ Hm with Hm
      ihave Hgs : HookGateOpt s.gh.tr r (sendOutGate id s c ({ m with To' := s.lead } : MessageM).Type'
          [readForward id s.lead m ents cl]) (G (s.outbox ++ [readForward id s.lead m ents cl])) $$ [Hgfwd HG]
      · have hn : sendOutGate id s c ({ m with To' := s.lead } : MessageM).Type'
            [readForward id s.lead m ents cl] = none := by
          show sendOutGate id s c m.Type' _ = none
          rw [Hty]; rfl
        rw [hn]
        iapply Hgfwd $$ %(by first | exact Or.inr (Or.inl trivial) | exact Or.inr (Or.inl Hty))
          %([readForward id s.lead m ents cl])
          %(by intro x hx; simp only [List.mem_singleton] at hx; subst hx; rfl) HG
      wp_apply wp_raft_send c r id s ml { m with To' := s.lead } ents sn cl rs
          [readForward id s.lead m ents cl] (G (s.outbox ++ [readForward id s.lead m ents cl]))
          (Or.inr (Or.inr (Or.inl Hty)))
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨Hty, Hterm0, fun h => Hlid h, rfl⟩)))))
          (fun h => by simp [Hty, MsgReadIndex, MsgSnap] at h)
          (fun h => by simp [Hty, MsgReadIndex, MsgApp] at h)
        (Hnors (.inr (.inl Hty)))
        (fun _ => mtypeOf_send_eq Hty) $$ [$Hphys $Hm $Hgs]
        as ⟨Hphys, HG⟩
      · iapply tsSrc_ne; exact (fun h => by simp [Hty, MsgReadIndex, MsgSnap] at h)
      iapply HΦ $$ %GoInterface.nil %_ %false %c
      iframe Hphys
      simp only [Bool.false_eq_true, ↓reduceIte]
      isplitr [HG]
      · ipureintro
        simp [FollowerStepResultC, MsgSnap, Hty, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat,
          MsgAppResp, MsgHeartbeatResp, MsgCheckQuorum, MsgSnap, MsgPreVoteResp, MsgReadIndex]
        exact fun h => absurd h Hlead
      isplitr [HG]
      · ipureintro; first | rfl | trivial
      iright; isplitr
      · ipureintro; simp [MsgApp, MsgHeartbeat, MsgTimeoutNow]
      iidx HG
  · -- `MsgReadIndexResp` (2026-10-12): one entry becomes a `ReadState`
    simp only [Hty, MsgReadIndexResp]
    wp_auto
    wp_apply wp_GetEntries.1 ml _ _ _ _ $$ [$Hm] as %es %els ⟨Hes, #Hents, Hcap, Hback⟩
    ihave %Hlen := ownSlice_len _ _ _ $$ Hes
    ihave %Hlen2 := BigSepL2.bigSepL2_length $$ Hents
    ihave Hm := Hback $$ %(needsCap m) %els %ents Hes Hents Hcap
    wp_if_destruct
    · -- one entry: `r.readStates = append(r.readStates, ReadState{m.GetIndex(),
      -- m.GetEntries()[0].GetData()})`
      obtain ⟨e, rfl⟩ : ∃ e, ents = [e] :=
        List.length_eq_one_iff.1 (by rw [← Hlen2, Hlen.1, Hif]; rfl)
      icases ownRaftPhysC_misc _ _ _ $$ Hphys with ⟨%rsl, %ro, %pr, Hrs, Hro, Hpr, Hmisc, Hback⟩
      iunfold ownRaftMisc at Hmisc
      iNamed Hmisc
      wp_auto
      wp_apply wp_GetIndex.1 ml _ _ _ _ $$ [$Hm] as Hm
      wp_apply wp_GetEntries.1 ml _ _ _ _ $$ [$Hm] as %es' %els' ⟨Hes', #Hents', -, -⟩
      ihave %Hlen' := BigSepL2.bigSepL2_length $$ Hents'
      obtain ⟨l0, rfl⟩ : ∃ l0, els' = [l0] := List.length_eq_one_iff.1 Hlen'
      ihave %Hlen'' := ownSlice_len _ _ _ $$ Hes'
      ihave #He := BigSepL2.bigSepL2_singleton.1 $$ Hents'
      simp only [show (0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z es'.len) = True from
        eq_true ⟨by word, by have := Hlen''.1; simp at this; word⟩, ↓reduceIte]
      wp_apply wp_load_slice_index es' (sint.Z (W64 0)) [l0] DFrac.discard l0 (by word)
        $$ [Hes'] with -
      · iframe Hes'; ipureintro; rfl
      wp_apply wp_GetData.1 l0 DFrac.discard e $$ [$He] as %ds ⟨#Hds, -⟩
      wp_apply wp_slice_literal (V := ReadState) [ReadState.mk m.Index' ds]
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl, -⟩
      wp_auto
      iunfold readStatesPts at HreadStates
      icases HreadStates with ⟨%vs, #Hvs, #Hvsl⟩
      wp_apply wp_slice_append_persistent (V := ReadState) rsl vs _ [ReadState.mk m.Index' ds]
          (DFrac.own 1) $$ [$Hvs $HreadStates_cap $Hsl]
        as %rs' ⟨#Hrs', Hcap', -⟩
      ihave Hmisc : ownRaftMisc (GF := GF) rs' ro pr
          { s.rd with states := s.rd.states ++ [ReadStateM.mk m.Index' e.Data'] }
          $$ [Hcap' Hro_obj Hpri Hpri_cap]
      · unfold ownRaftMisc
        simp only [named]
        iframe Hcap' Hro_obj Hpri Hpri_cap
        iunfold readStatesPts
        iexists vs ++ [ReadState.mk m.Index' ds]
        iframe Hrs'
        iapply BigSepL2.bigSepL2_snoc.2
        iframe Hvsl
        isplitl
        · ipureintro; rfl
        iexact Hds
      ihave Hphys := Hback $$ %rs' %ro %pr %_ Hrs Hro Hpr Hmisc
      iapply HΦ $$ %GoInterface.nil %_ %false %c
      iframe Hphys
      simp only [Bool.false_eq_true, ↓reduceIte]
      isplitr [HG]
      · ipureintro
        simp [FollowerStepResultC, MsgSnap, Hty, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat,
          MsgAppResp, MsgHeartbeatResp, MsgCheckQuorum, MsgSnap, MsgPreVoteResp, MsgReadIndex, MsgReadIndexResp,
          addReadState]
      isplitr [HG]
      · ipureintro; first | rfl | trivial
      iright; isplitr
      · ipureintro; simp [MsgApp, MsgHeartbeat, MsgTimeoutNow]
      iidx HG
    · -- not one entry: logged and ignored
      wp_apply raft.wp_load_idC $$ Hphys as Hphys
      wp_apply wp_GetFrom.1 ml _ _ _ _ $$ [$Hm] as Hm
      wp_apply wp_GetEntries.1 ml _ _ _ _ $$ [$Hm] as %es' %els' ⟨Hes', -, -, -⟩
      wp_raft_logC
      iapply HΦ $$ %GoInterface.nil %s %false %c
      iframe Hphys
      simp only [Bool.false_eq_true, ↓reduceIte]
      isplitr [HG]
      · ipureintro
        have Hne : ¬ ents.length = 1 := fun h => Hif (by
          rw [← Hlen2] at h; have := Hlen.1; rw [h] at this; word)
        match ents, Hne with
        | [], _ =>
          simp [FollowerStepResultC, MsgSnap, Hty, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat,
            MsgAppResp, MsgHeartbeatResp, MsgCheckQuorum, MsgSnap, MsgPreVoteResp, MsgReadIndex, MsgReadIndexResp]
        | _ :: _ :: _, _ =>
          simp [FollowerStepResultC, MsgSnap, Hty, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat,
            MsgAppResp, MsgHeartbeatResp, MsgCheckQuorum, MsgSnap, MsgPreVoteResp, MsgReadIndex, MsgReadIndexResp]
        | [_], h => exact absurd rfl h
      isplitr [HG]
      · ipureintro; first | rfl | trivial
      iright; isplitr
      · ipureintro; simp [MsgApp, MsgHeartbeat, MsgTimeoutNow]
      iidx HG
  · -- `MsgForgetLeader` (2026-10-13): the read-only option is `Safe` (not `LeaseBased`),
    -- then a leader, if any, is forgotten
    simp only [Hty, MsgForgetLeader]
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
      isplitr [HG]
      · ipureintro
        simp [FollowerStepResultC, MsgSnap, Hty, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat,
          MsgAppResp, MsgHeartbeatResp, MsgCheckQuorum, MsgSnap, MsgPreVoteResp, MsgReadIndex, MsgReadIndexResp,
          MsgForgetLeader, MsgTransferLeader, MsgUnreachable, MsgSnapStatus, MsgTimeoutNow]
        exact Hs
      isplitr [HG]
      · ipureintro; first | rfl | trivial
      iright; isplitr
      · ipureintro; simp [MsgApp, MsgHeartbeat, MsgTimeoutNow]
      iidx HG
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
      isplitr [HG]
      · ipureintro
        simp [FollowerStepResultC, MsgSnap, Hty, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat,
          MsgAppResp, MsgHeartbeatResp, MsgCheckQuorum, MsgSnap, MsgPreVoteResp, MsgReadIndex, MsgReadIndexResp,
          MsgForgetLeader, MsgTransferLeader, MsgUnreachable, MsgSnapStatus, MsgTimeoutNow]
      isplitr [HG]
      · ipureintro; first | rfl | trivial
      iright; isplitr
      · ipureintro; simp [MsgApp, MsgHeartbeat, MsgTimeoutNow]
      iidx HG
  · -- `MsgTransferLeader` (2026-10-13): forwarded to the leader, if any; it is outside
    -- the model (`mtypeOf` is `none`), so nothing is queued abstractly
    obtain ⟨Htl, -⟩ := Hrest (Or.inl Hty)
    obtain ⟨Hterm0, Hents0, Hctx0, Hxo⟩ := Htl Hty
    subst Hents0 Hctx0
    simp only [Hty, MsgTransferLeader]
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
      isplitr [HG]
      · ipureintro
        simp [FollowerStepResultC, MsgSnap, Hty, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat,
          MsgAppResp, MsgHeartbeatResp, MsgCheckQuorum, MsgSnap, MsgPreVoteResp, MsgReadIndex, MsgReadIndexResp,
          MsgForgetLeader, MsgTransferLeader, MsgUnreachable, MsgSnapStatus, MsgTimeoutNow]
      isplitr [HG]
      · ipureintro; first | rfl | trivial
      iright; isplitr
      · ipureintro; simp [MsgApp, MsgHeartbeat, MsgTimeoutNow]
      iidx HG
    · rw [decide_eq_false Hlead]
      wp_auto
      wp_apply raft.wp_load_leadC $$ Hphys as Hphys
      obtain ⟨Hterm0', Hlid⟩ := Hterm0.resolve_left Hlead
      imod cellRO_alloc $$ «$r0» with #cTo
      icases msgPtsC_store_To _ _ _ _ $$ Hm with ⟨%pTo, HTo, Hback⟩
      wp_auto
      ihave Hm := Hback $$ %_ %s.lead HTo cTo
      imod msgIn_to_msgOwn $$ Hm with Hm
      ihave Hgs : HookGateOpt s.gh.tr r (sendOutGate id s c ({ m with To' := s.lead } : MessageM).Type'
          []) (G (s.outbox ++ [])) $$ [Hgfwd HG]
      · have hn : sendOutGate id s c ({ m with To' := s.lead } : MessageM).Type' [] = none := by
          show sendOutGate id s c m.Type' _ = none
          rw [Hty]; rfl
        rw [hn]
        iapply Hgfwd $$ %(by first | exact Or.inr (Or.inr trivial) | exact Or.inr (Or.inr Hty)) %([] : List Msg)
          %(by intro x hx; cases hx) HG
      wp_apply wp_raft_send c r id s ml { m with To' := s.lead } [] sn [] rs [] (G (s.outbox ++ []))
          (Or.inr (Or.inr (Or.inr Hty)))
          (Or.inr (Or.inr (Or.inl (Or.inr ⟨Or.inr Hty, fun h => absurd (Hty.symm.trans h) (by simp [MsgTransferLeader, MsgTimeoutNow]),
            rfl, rfl, Hterm0', fun h => Hlid h, rfl, fun _ => Hxo Hlead⟩))))
          (fun h => by simp [Hty, MsgTransferLeader, MsgSnap] at h)
          (fun h => by simp [Hty, MsgTransferLeader, MsgApp] at h)
        (Hnors (.inr (.inr Hty)))
        (fun h => absurd (Hxtr Hty) h) $$ [$Hphys $Hm $Hgs]
        as ⟨Hphys, HG⟩
      · iapply tsSrc_ne; exact (fun h => by simp [Hty, MsgTransferLeader, MsgSnap] at h)
      ihave Hphys := ownRaftPhysC_unsend c r id s $$ Hphys
      iapply HΦ $$ %GoInterface.nil %s %false %c
      iframe Hphys
      simp only [Bool.false_eq_true, ↓reduceIte]
      isplitr [HG]
      · ipureintro
        simp [FollowerStepResultC, MsgSnap, Hty, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat,
          MsgAppResp, MsgHeartbeatResp, MsgCheckQuorum, MsgSnap, MsgPreVoteResp, MsgReadIndex, MsgReadIndexResp,
          MsgForgetLeader, MsgTransferLeader, MsgUnreachable, MsgSnapStatus, MsgTimeoutNow]
      isplitr [HG]
      · ipureintro; first | rfl | trivial
      iright; isplitr
      · ipureintro; simp [MsgApp, MsgHeartbeat, MsgTimeoutNow]
      iidx HG
  · -- `MsgTimeoutNow` (2026-10-13): `hup(campaignTransfer)`, an ordinary campaign
    obtain ⟨-, Htn⟩ := Hrest (Or.inr Hty)
    obtain ⟨Hnw, Hwf, Hfla⟩ := Htn Hty
    ihave Hgc := Hgcamp $$ %Hty
    ihave #Hgv := Hgvote $$ %Hty
    have Hde : decide (campaignTransfer = campaignPreElection) = false := by
      simp (config := {decide := true}) [campaignTransfer, campaignPreElection]
    have Htc : transferCtx campaignTransfer = campaignTransfer := by
      simp [transferCtx]
    ihave Hgbc : ⌜HupCampaigns c id s⌝ -∗ G s.outbox -∗
        (if campaignTransfer = campaignPreElection then iprop(|={⊤}=> G' s.outbox)
        else HookGate s.gh.tr r (NodeEvOf (W64 1) id (becomeCandidate id s) c) (G' s.outbox)) $$ [Hgc]
    · simp only [eq_false (show ¬ _ from by simpa using Hde), ite_false]
      iintro %_
      iexact Hgc
    ihave #Hgsend : □ (∀ (pvs : GMap w64 Progress) (y : w64) (o : List Msg), ⌜y ∈ c.voters⌝ -∗ G' o -∗
        HookGateOpt s.gh.tr r
          (sendOutGate id { campRoleState id s (decide (campaignTransfer = campaignPreElection))
              with prvals := pvs } c
            (if y = id then vrespW32 (decide (campaignTransfer = campaignPreElection))
             else vreqW32 (decide (campaignTransfer = campaignPreElection)))
            [campMsg (decide (campaignTransfer = campaignPreElection)) id (s.term + W64 1)
              (plogLast s.logst.prev (s.logst.sents ++ s.logst.uents)) (transferCtx campaignTransfer) y])
          (G' (o ++ [campMsg (decide (campaignTransfer = campaignPreElection)) id (s.term + W64 1)
              (plogLast s.logst.prev (s.logst.sents ++ s.logst.uents)) (transferCtx campaignTransfer) y]))) $$ []
    · rw [Hde, Htc]
      imodintro
      iintro %pvs %y %o %Hy HG
      ispecialize Hgv $$ %pvs %y %o %Hy HG
      iapply hookGateOpt_congr _ _ r _ _ _ (by rfl) (by rfl) $$ Hgv
    simp only [Hty, MsgTimeoutNow]
    wp_auto
    wp_apply raft.wp_load_idC $$ Hphys as Hphys
    wp_apply raft.wp_load_TermC $$ Hphys as Hphys
    wp_apply wp_GetFrom.1 ml _ _ _ _ $$ [$Hm] as Hm
    wp_raft_logC
    try rw [show go_etcd_io.raft.v3.campaignTransfer = #campaignTransfer from rfl]
    wp_apply wp_raft_hup c r id s campaignTransfer (G s.outbox) G' Hnw
        (fun h => by simp [campaignTransfer, campaignPreElection] at h) Hwf Hfla Hpinv
      $$ [$Hphys $HG $Hgbc $Hgsend] as %s' ⟨Hphys, HG, %Hok, %Hpc⟩
    iapply HΦ $$ %GoInterface.nil %s' %false %c
    iframe Hphys
    simp only [Bool.false_eq_true, ↓reduceIte]
    isplitr [HG]
    · ipureintro
      simp only [FollowerStepResultC, Hty, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat,
          MsgAppResp, MsgHeartbeatResp, MsgCheckQuorum, MsgSnap, MsgPreVoteResp, MsgReadIndex, MsgReadIndexResp,
          MsgForgetLeader, MsgTransferLeader, MsgUnreachable, MsgSnapStatus, MsgTimeoutNow, W32]
      simp
      exact ⟨Hok, fun h => (Hpc h).resolve_right
        (by simp [campaignTransfer, campaignPreElection])⟩
    isplitr [HG]
    · ipureintro; first | rfl | trivial
    icases HG with (⟨%Hs, HG⟩ | HG)
    · subst Hs
      iright; isplitr
      · ipureintro; simp [MsgApp, MsgHeartbeat, MsgTimeoutNow]
      iidx HG
    · ileft; isplitr
      · ipureintro; simp
      iidx HG
  · -- `MsgUnreachable` (2026-10-13): no arm
    simp only [Hty, MsgUnreachable]
    wp_auto
    iapply HΦ $$ %GoInterface.nil %s %false %c
    iframe Hphys
    simp only [Bool.false_eq_true, ↓reduceIte]
    isplitr [HG]
    · ipureintro
      simp [FollowerStepResultC, MsgSnap, Hty, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat,
          MsgAppResp, MsgHeartbeatResp, MsgCheckQuorum, MsgSnap, MsgPreVoteResp, MsgReadIndex, MsgReadIndexResp,
          MsgForgetLeader, MsgTransferLeader, MsgUnreachable, MsgSnapStatus, MsgTimeoutNow]
    isplitr [HG]
    · ipureintro; first | rfl | trivial
    iright; isplitr
    · ipureintro; simp [MsgApp, MsgHeartbeat, MsgTimeoutNow]
    iidx HG
  · -- `MsgSnapStatus` (2026-10-13): no arm
    simp only [Hty, MsgSnapStatus]
    wp_auto
    iapply HΦ $$ %GoInterface.nil %s %false %c
    iframe Hphys
    simp only [Bool.false_eq_true, ↓reduceIte]
    isplitr [HG]
    · ipureintro
      simp [FollowerStepResultC, MsgSnap, Hty, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat,
          MsgAppResp, MsgHeartbeatResp, MsgCheckQuorum, MsgSnap, MsgPreVoteResp, MsgReadIndex, MsgReadIndexResp,
          MsgForgetLeader, MsgTransferLeader, MsgUnreachable, MsgSnapStatus, MsgTimeoutNow]
    isplitr [HG]
    · ipureintro; first | rfl | trivial
    iright; isplitr
    · ipureintro; simp [MsgApp, MsgHeartbeat, MsgTimeoutNow]
    iidx HG

end proof

end EtcdGrove
end Perennial
