/-
The code's steps as steps of the dynamic model (2026-10-14, reconfiguration stage B7), Lean-first.

`raft.Step`'s branch lemmas produce `StepC c` witnesses (stage B7a), which the static ghost state
follows (`ownRaftGhost_stepC`). The dynamic ghost state follows `StepR` (`ownRaftGhostR_stepR`),
which is stronger: the campaign guard, the exact proposal loop, `AppCommitEq`, and the fields
`applied`, `pci`, `snap` and the ghost configuration index, configuration and full prefix. This
file is the bridge.

* `RGh`: the ghost part of `RState` (configuration index, configuration, full prefix); `rOf s g`:
  the `RState` of the physical state `s` with it. `pci` is the code's `pendingConfIndex` at a
  leader and `0` otherwise: Go clears it in `reset`, which every `becomeX` but
  `becomePreCandidate` calls, so it is meaningful only at a leader, and `StepR` reads it only
  there (`propBatch`); taking `0` elsewhere makes the model's `lose`/`abandon` (which keep it) and
  the code's `becomeFollower` (which clears it) agree without a code invariant.
* `StepCF c id`: the rules of `StepC c id` that touch none of `StepR`'s extra fields (all but
  `campaign`, `win`, `propose`, `snapRestore`), `sendApps` with `AppCommitEq`. A `StepCF`
  derivation is a `StepC` one (`StepCF.toC`) and a `StepR` one at any `RState` over it whose
  non-leader `pci` is `0` (`StepCF.toR`; the `pci` is kept at a leader, cleared at a step-down).
* `RFrame s s'`: a step of the code that keeps `applied`, the pending snapshot and, at a leader
  that stays one, `pendingConfIndex` -- with which `rOf` maps a `StepCF` step of `toPState` to a
  `StepR` step (`rOf_frame`).
* `StepCD c id m s recv s'`: what a branch of `raft.Step` delivers: the `StepC` witness (static
  mode) and, for every ghost part over `c` and the dynamic mode's premises (`DynHyp`: not a
  `MsgSnap` -- whose branch delivers `StepCDS` instead, below --, no pre-candidate --
  pre-vote is off at the `RawNode` API, and the campaign after a won pre-vote checks nothing in
  Go --, and for `MsgStorageApplyResp` no pending snapshot and A1: no conf entry between the
  configuration index and the new `applied`), the `StepR` witness. `StepCD.frame` builds it from
  a `StepCF` witness and `RFrame`.
* `StepCDS c c' cn id sid s recv s'` (2026-10-14, stage B8): what the `MsgSnap` branch delivers:
  the `StepC` witness and, for every ghost part over `c`, prefix `fp'` ending at the snapshot's
  entry id `sid` and configuration state over `cn` (the configuration the snapshot's
  `ConfState` denotes) that the model admits after `fp'`, a `StepR` witness to a ghost part over
  `c'` (`StepR.snapRestore` for a restore, `stepR_snap_restore`; a frame step otherwise).
-/
module

public import Raft37.Proof.go_etcd_io.raft.v3.StepLemmasC
public import Raft37.Proof.go_etcd_io.raft.v3.Protocol.StepR
public import Raft37.Proof.go_etcd_io.raft.v3.SpecResults

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open GMap go_etcd_io.raft.v3

section frame
variable [FfiSyntax]

variable (c : CfgM) (id : w64)

/-- `StepC c id` without the rules that move `StepR`'s extra fields (see the file header). -/
inductive StepCF : PState → List Msg → PState → Prop where
  | refl (s : PState) : StepCF s [] s
  | trans (s₀ : PState) (r₁ : List Msg) (s₁ : PState) (r₂ : List Msg) (s₂ : PState) :
      StepCF s₀ r₁ s₁ → StepCF s₁ r₂ s₂ → StepCF s₀ (r₁ ++ r₂) s₂
  | higherTerm (m : Msg) (s : PState) :
      uint.Z s.term < uint.Z m.term →
      m.dst = id →
      (fromLeader m.ty = true → m.src ≠ id) →
      StepCF s [m] (pbecomeFollower s m.term (if fromLeader m.ty then m.src else W64 0))
  | grantVote (m : Msg) (s : PState) :
      m.ty = .vote →
      m.dst = id →
      m.src ≠ W64 0 →
      m.term = s.term →
      PCanVote s m.src →
      plogUpToDate s.base s.log (entryID.mk m.logterm m.index) = true →
      StepCF s [m]
        (psendMsgs { s with vote := m.src } [Msg.plain .voteResp id m.src s.term false])
  | rejectVote (m : Msg) (s : PState) :
      m.ty = .vote →
      m.dst = id →
      StepCF s [m] (psendMsgs s [Msg.plain .voteResp id m.src s.term true])
  | recordVote (m : Msg) (s : PState) :
      m.ty = .voteResp →
      m.dst = id →
      m.term = s.term →
      s.role = .candidate →
      StepCF s [m] { s with votes := recordVote s.votes m.src (!m.reject) }
  | lose (s : PState) :
      s.role = .candidate →
      JLost c s.votes →
      StepCF s [] (pbecomeFollower s s.term (W64 0))
  | drain (s : PState) (o' : List Msg) :
      o'.Subperm s.outbox →
      StepCF s [] { s with outbox := o' }
  | appAccept (m : Msg) (s : PState) (lastnewi : w64) (es' : List EntryM) :
      m.ty = .app →
      m.dst = id →
      m.src ≠ id →
      m.term = s.term →
      s.role ≠ .leader →
      uint.Z s.commit ≤ uint.Z m.index →
      plogMaybeAppend s.base s.log (entryID.mk m.logterm m.index) m.entries
        = some (lastnewi, es') →
      (plogFindConflict s.base s.log m.entries = W64 0 ∨
        uint.Z s.commit < uint.Z (plogFindConflict s.base s.log m.entries)) →
      StepCF s [m]
        (psendMsgs
          { padoptLeader s m.src with
              log := es',
              commit := plogCommitTo s.commit
                          (if uint.Z m.commit < uint.Z lastnewi then m.commit else lastnewi) }
          [Msg.mk .appResp id m.src s.term false lastnewi (W64 0) (W64 0) (W64 0) []])
  | appStale (m : Msg) (s : PState) :
      m.ty = .app →
      m.dst = id →
      m.src ≠ id →
      m.term = s.term →
      s.role ≠ .leader →
      uint.Z m.index < uint.Z s.commit →
      StepCF s [m]
        (psendMsgs (padoptLeader s m.src)
          [Msg.mk .appResp id m.src s.term false s.commit (W64 0) (W64 0) (W64 0) []])
  | appReject (m : Msg) (s : PState) (hint hintterm : w64) :
      m.ty = .app →
      m.dst = id →
      m.src ≠ id →
      m.term = s.term →
      s.role ≠ .leader →
      uint.Z s.commit ≤ uint.Z m.index →
      ¬ PlogMatches s.base s.log (entryID.mk m.logterm m.index) →
      StepCF s [m]
        (psendMsgs (padoptLeader s m.src)
          [Msg.mk .appResp id m.src s.term true m.index hintterm (W64 0) hint []])
  | heartbeat (m : Msg) (s : PState) :
      m.ty = .heartbeat →
      m.dst = id →
      m.src ≠ id →
      m.term = s.term →
      s.role ≠ .leader →
      uint.Z m.commit ≤ plogLastIndexZ s.base s.log →
      StepCF s [m]
        (psendMsgs
          { padoptLeader s m.src with commit := plogCommitTo s.commit m.commit }
          [{ Msg.plain .heartbeatResp id m.src s.term false with ctx := m.ctx }])
  | beat (s : PState) (ms : List Msg) :
      s.role = .leader →
      (∀ m ∈ ms, HeartbeatOk id s m) →
      (∀ m ∈ ms, HbCtxOk s.rd.ro m.ctx) →
      StepCF s [] (psendMsgs s ms)
  | appResp (m : Msg) (s : PState) (x : w64) :
      m.ty = .appResp →
      m.dst = id →
      m.term = s.term →
      s.role = .leader →
      m.reject = false →
      s.matched !! m.src = some x →
      StepCF s [m]
        { s with matched :=
            <[m.src := if uint.Z x < uint.Z m.index then m.index else x]> s.matched }
  | commit (s : PState) (n : w64) :
      s.role = .leader →
      uint.Z s.commit < uint.Z n →
      uint.Z n ≤ plogLastIndexZ s.base s.log →
      plogTermAt s.base s.log n = some s.term →
      JQuorum c (ackedBy s n) →
      StepCF s [] { s with commit := n }
  | sendApps (s : PState) (ms : List Msg) :
      s.role = .leader →
      (∀ m ∈ ms, ReplOk id s m) →
      (∀ m ∈ ms, AppCommitEq s m) →
      StepCF s [] (psendMsgs s ms)
  | propForward (m : Msg) (s : PState) :
      m.ty = .propose →
      s.role = .follower →
      s.lead ≠ W64 0 →
      StepCF s [m]
        (psendMsgs s
          [Msg.mkV .propose id s.lead (W64 0) m.reject m.index m.logterm m.commit
             m.rejecthint m.entries [] m.ctx])
  | snapFastfwd (m : Msg) (s : PState) :
      m.ty = .snap →
      m.dst = id →
      m.src ≠ id →
      m.term = s.term →
      s.role ≠ .leader →
      uint.Z s.commit < uint.Z m.index →
      PlogMatches s.base s.log (entryID.mk m.logterm m.index) →
      StepCF s [m]
        (psendMsgs { padoptLeader s m.src with commit := m.index }
          [Msg.mk .appResp id m.src s.term false m.index (W64 0) (W64 0) (W64 0) []])
  | snapStale (m : Msg) (s : PState) :
      m.ty = .snap →
      m.dst = id →
      m.src ≠ id →
      m.term = s.term →
      s.role ≠ .leader →
      uint.Z m.index ≤ uint.Z s.commit →
      StepCF s [m]
        (psendMsgs (padoptLeader s m.src)
          [Msg.mk .appResp id m.src s.term false s.commit (W64 0) (W64 0) (W64 0) []])
  | takeReads (s : PState) :
      StepCF s [] ({ s with rd := { s.rd with states := [] } })
  | readFwd (m : Msg) (s : PState) :
      m.ty = .readIndex → s.role ≠ .leader → s.lead ≠ W64 0 →
      StepCF s [m] (psendMsgs s [{ m with
        src := if m.src = W64 0 then id else m.src
        dst := s.lead
        term := W64 0 }])
  | readPend (m : Msg) (s : PState) (pm : MessageM) :
      m.ty = .readIndex → s.role = .leader → m.src = pm.From' →
      StepCF s [m] ({ s with rd := { s.rd with pend := s.rd.pend ++ [(pm, m.entries)] } })
  | readArrive (m : Msg) (s : PState) :
      m.ty = .readIndex → s.role = .leader →
      plogTermAt s.base s.log s.commit = some s.term →
      StepCF s [m] ({ s with rd := { s.rd with
                     ro := readonlyArrive s.rd.ro id ⟨s.commit, m.src, m.entries⟩ } })
  | readRelease (s : PState) :
      s.role = .leader → plogTermAt s.base s.log s.commit = some s.term →
      StepCF s [] ({ s with rd := { s.rd with
        pend := []
        ro := readonlyRelease s.rd.ro id s.commit s.rd.pend } })
  | readSingle (m : Msg) (s : PState) :
      m.ty = .readIndex → s.role = .leader →
      plogTermAt s.base s.log s.commit = some s.term → CfgSingle c id →
      StepCF s [m] (preadRespondAll id s [⟨s.commit, m.src, m.entries⟩])
  | readReleaseSingle (s : PState) :
      s.role = .leader → plogTermAt s.base s.log s.commit = some s.term → CfgSingle c id →
      StepCF s [] (preadRespondAll id { s with rd := { s.rd with pend := [] } }
        (s.rd.pend.map (fun p => ⟨s.commit, p.1.From', p.2⟩)))
  | readAck (m : Msg) (s : PState) (N : w64) :
      m.ty = .heartbeatResp → m.dst = id → m.term = s.term → s.role = .leader →
      m.ctx ≠ [] →
      JQuorumAcked c (fun v => ((readonlyRecvAck s.rd.ro m.src m.ctx).acks !! v).getD (W64 0))
        N →
      StepCF s [m] (preadRespondAll id
        ({ s with rd := { s.rd with
             ro := (readonlyAdvance (readonlyRecvAck s.rd.ro m.src m.ctx) N).1 } })
        (readonlyAdvance (readonlyRecvAck s.rd.ro m.src m.ctx) N).2)
  | readState (m : Msg) (s : PState) (e : EntryM) :
      m.ty = .readIndexResp → m.entries = [e] →
      StepCF s [m] ({ s with rd := { s.rd with states := s.rd.states ++ [⟨m.index, e.Data'⟩] } })
  | sendFree (s : PState) (m : Msg) :
      (m.ty = .preVote ∨ m.ty = .preVoteResp) →
      m.src = id →
      StepCF s [] (psendMsgs s [m])
  | abandon (s : PState) :
      s.role ≠ .leader →
      StepCF s [] (pbecomeFollower s s.term (W64 0))
  | zeroAck (s : PState) (dst : w64) :
      StepCF s [] (psendMsgs s [Msg.mk .appResp id dst s.term false
                                (W64 0) (W64 0) (W64 0) (W64 0) []])
  | reMatch (s : PState) (mt : GMap w64 w64) :
      s.role = .leader →
      (∀ v i, mt !! v = some i → uint.Z i = 0 ∨ s.matched !! v = some i) →
      StepCF s [] { s with matched := mt }

end frame

section frame_lemmas
variable [FfiSyntax]

/-- The `pci` an `RState` keeps across a step to `p'`: its own at a leader, `0` elsewhere. -/
def pciKeep (p' : PState) (x : w64) : w64 := if p'.role = .leader then x else W64 0

/-- A `StepCF` derivation is a `StepC` one. -/
theorem StepCF.toC {c : CfgM} {id : w64} {s : PState} {ms : List Msg} {s' : PState}
    (h : StepCF c id s ms s') : StepC c id s ms s' := by
  induction h with
  | refl s => exact .refl s
  | trans _ _ _ _ _ _ _ ih1 ih2 => exact .trans _ _ _ _ _ ih1 ih2
  | sendApps s ms h1 h2 _ => exact .sendApps s ms h1 h2
  | _ =>
    first
    | (apply StepC.higherTerm <;> assumption)
    | (apply StepC.grantVote <;> assumption)
    | (apply StepC.rejectVote <;> assumption)
    | (apply StepC.recordVote <;> assumption)
    | (apply StepC.lose <;> assumption)
    | (apply StepC.drain <;> assumption)
    | (apply StepC.appAccept <;> assumption)
    | (apply StepC.appStale <;> assumption)
    | (apply StepC.appReject <;> assumption)
    | (apply StepC.heartbeat <;> assumption)
    | (apply StepC.beat <;> assumption)
    | (apply StepC.appResp <;> assumption)
    | (apply StepC.commit <;> assumption)
    | (apply StepC.propForward <;> assumption)
    | (apply StepC.snapFastfwd <;> assumption)
    | (apply StepC.snapStale <;> assumption)
    | (apply StepC.takeReads <;> assumption)
    | (apply StepC.readFwd <;> assumption)
    | (apply StepC.readPend <;> assumption)
    | (apply StepC.readArrive <;> assumption)
    | (apply StepC.readRelease <;> assumption)
    | (apply StepC.readAck <;> assumption)
    | (apply StepC.readSingle <;> assumption)
    | (apply StepC.readReleaseSingle <;> assumption)
    | (apply StepC.readState <;> assumption)
    | (apply StepC.sendFree <;> assumption)
    | (apply StepC.abandon <;> assumption)
    | (apply StepC.zeroAck <;> assumption)
    | (apply StepC.reMatch <;> assumption)

/-- No `StepCF` rule makes a leader: one at the end was one at the start. -/
theorem StepCF.leader_back {c : CfgM} {id : w64} {s : PState} {ms : List Msg} {s' : PState}
    (h : StepCF c id s ms s') : s'.role = .leader → s.role = .leader := by
  induction h with
  | refl s => exact fun h => h
  | trans _ _ _ _ _ _ _ ih1 ih2 => exact fun h => ih1 (ih2 h)
  | readAck m s N _ _ _ h4 _ _ => exact fun _ => h4
  | readSingle m s _ h2 _ _ => exact fun _ => h2
  | readReleaseSingle s h1 _ _ => exact fun _ => h1
  | _ =>
    first
    | (intro h; simp_all [psendMsgs, padoptLeader, pbecomeFollower]; done)
    | (intro h; first | exact h | assumption)
    | (intro _; assumption)

/-- An `RState` whose protocol state moved to `p'` by a step that keeps leadership: the `pci`
it keeps at a leader, `0` elsewhere, is its own. -/
theorem RState.with_p_pci (r : RState) (p' : PState)
    (h1 : p'.role = .leader → r.p.role = .leader) (h2 : r.p.role = .leader → p'.role = .leader)
    (hz : r.p.role ≠ .leader → r.pci = W64 0) :
    ({ r with p := p', pci := pciKeep p' r.pci } : RState) =
      { r with p := p' } := by
  unfold pciKeep
  by_cases hl : p'.role = .leader
  · rw [ite_eq_left hl]
  · rw [ite_eq_right hl, ← hz (fun h => hl (h2 h))]

/-- `RState.with_p_pci` on a `StepR` derivation's target. -/
theorem StepR.pci_keep {Adm : List EntryM → CCState → Prop} {dec : CCDec} {id : w64}
    {r : RState} {ms : List Msg} {p' : PState} (h : StepR Adm dec id r ms { r with p := p' })
    (h1 : p'.role = .leader → r.p.role = .leader) (h2 : r.p.role = .leader → p'.role = .leader)
    (hz : r.p.role ≠ .leader → r.pci = W64 0) :
    StepR Adm dec id r ms { r with p := p', pci := pciKeep p' r.pci } := by
  rw [RState.with_p_pci r p' h1 h2 hz]; exact h

/-- A `StepCF` derivation is a `StepR` one, at any `RState` over its start whose non-leader
`pci` is `0`: the configuration is `c`; the extra fields are kept, but `pci`, kept at a leader
and cleared at a step-down. -/
theorem StepCF.toR {Adm : List EntryM → CCState → Prop} {dec : CCDec} {c : CfgM}
    {id : w64} {s : PState} {ms : List Msg} {s' : PState} (h : StepCF c id s ms s') :
    ∀ (r : RState), r.p = s → r.cfg.cfg = c → (r.p.role ≠ .leader → r.pci = W64 0) →
      StepR Adm dec id r ms
        { r with p := s', pci := pciKeep s' r.pci } := by
  induction h with
  | refl s =>
    intro r hp _ hz
    subst hp
    have e := RState.with_p_pci r r.p (fun h => h) (fun h => h) hz
    rw [e]
    exact .refl _
  | trans s0 m1 s1 m2 s2 h1 h2 ih1 ih2 =>
    intro r hp hc hz
    have H1 := ih1 r hp hc hz
    have H2 := ih2 { r with p := s1, pci := pciKeep s1 r.pci } rfl hc
      (fun h => by simp only [pciKeep] at h ⊢; rw [ite_eq_right h])
    refine .trans _ _ _ _ _ H1 ?_
    have e : ({ { r with p := s1, pci := pciKeep s1 r.pci } with
          p := s2,
          pci := pciKeep s2 (pciKeep s1 r.pci) } : RState) =
        { r with p := s2, pci := pciKeep s2 r.pci } := by
      unfold pciKeep
      by_cases hl : s2.role = .leader
      · rw [ite_eq_left hl, ite_eq_left hl, ite_eq_left (h2.leader_back hl)]
      · rw [ite_eq_right hl, ite_eq_right hl]
    rw [← e]; exact H2
  | higherTerm m s h1 h2 h3 =>
    intro r hp _ _
    subst hp
    have e : pciKeep (pbecomeFollower r.p m.term (if fromLeader m.ty then m.src else W64 0))
        r.pci = W64 0 := by simp [pciKeep, pbecomeFollower]
    rw [e]
    exact .higherTerm m r h1 h2 h3
  | grantVote m s h1 h2 h3 h4 h5 h6 =>
    intro r hp _ hz; subst hp
    exact StepR.pci_keep (.grantVote m r h1 h2 h3 h4 h5 h6) (fun h => h) (fun h => h) hz
  | rejectVote m s h1 h2 =>
    intro r hp _ hz; subst hp
    exact StepR.pci_keep (.rejectVote m r h1 h2) (fun h => h) (fun h => h) hz
  | recordVote m s h1 h2 h3 h4 =>
    intro r hp _ hz; subst hp
    exact StepR.pci_keep (.recordVote m r h1 h2 h3 h4) (fun h => h) (fun h => h) hz
  | lose s h1 h2 =>
    intro r hp hc hz; subst hp
    exact StepR.pci_keep (.lose r h1 (hc ▸ h2))
      (by simp [pbecomeFollower]) (by rw [h1]; simp) hz
  | drain s o' h1 =>
    intro r hp _ hz; subst hp
    exact StepR.pci_keep (.drain r o' h1) (fun h => h) (fun h => h) hz
  | appAccept m s lastnewi es' h1 h2 h3 h4 h5 h6 h7 h8 =>
    intro r hp _ hz; subst hp
    exact StepR.pci_keep (.appAccept m r lastnewi es' h1 h2 h3 h4 h5 h6 h7 h8)
      (by simp [psendMsgs, padoptLeader]) (fun h => absurd h h5) hz
  | appStale m s h1 h2 h3 h4 h5 h6 =>
    intro r hp _ hz; subst hp
    exact StepR.pci_keep (.appStale m r h1 h2 h3 h4 h5 h6)
      (by simp [psendMsgs, padoptLeader]) (fun h => absurd h h5) hz
  | appReject m s hint hintterm h1 h2 h3 h4 h5 h6 h7 =>
    intro r hp _ hz; subst hp
    exact StepR.pci_keep (.appReject m r hint hintterm h1 h2 h3 h4 h5 h6 h7)
      (by simp [psendMsgs, padoptLeader]) (fun h => absurd h h5) hz
  | heartbeat m s h1 h2 h3 h4 h5 h6 =>
    intro r hp _ hz; subst hp
    exact StepR.pci_keep (.heartbeat m r h1 h2 h3 h4 h5 h6)
      (by simp [psendMsgs, padoptLeader]) (fun h => absurd h h5) hz
  | beat s ms h1 h2 h3 =>
    intro r hp _ hz; subst hp
    exact StepR.pci_keep (.beat r ms h1 h2 h3) (fun h => h) (fun h => h) hz
  | appResp m s x h1 h2 h3 h4 h5 h6 =>
    intro r hp _ hz; subst hp
    exact StepR.pci_keep (.appResp m r x h1 h2 h3 h4 h5 h6) (fun h => h) (fun h => h) hz
  | commit s n h1 h2 h3 h4 h5 =>
    intro r hp hc hz; subst hp
    exact StepR.pci_keep (.commit r n h1 h2 h3 h4 (hc ▸ h5)) (fun h => h) (fun h => h) hz
  | sendApps s ms h1 h2 h3 =>
    intro r hp _ hz; subst hp
    exact StepR.pci_keep (.sendApps r ms h1 h2 h3) (fun h => h) (fun h => h) hz
  | propForward m s h1 h2 h3 =>
    intro r hp _ hz; subst hp
    exact StepR.pci_keep (.propForward m r h1 h2 h3) (fun h => h) (fun h => h) hz
  | snapFastfwd m s h1 h2 h3 h4 h5 h6 h7 =>
    intro r hp _ hz; subst hp
    exact StepR.pci_keep (.snapFastfwd m r h1 h2 h3 h4 h5 h6 h7)
      (by simp [psendMsgs, padoptLeader]) (fun h => absurd h h5) hz
  | snapStale m s h1 h2 h3 h4 h5 h6 =>
    intro r hp _ hz; subst hp
    exact StepR.pci_keep (.snapStale m r h1 h2 h3 h4 h5 h6)
      (by simp [psendMsgs, padoptLeader]) (fun h => absurd h h5) hz
  | takeReads s =>
    intro r hp _ hz; subst hp
    exact StepR.pci_keep (.takeReads r) (fun h => h) (fun h => h) hz
  | readFwd m s h1 h2 h3 =>
    intro r hp _ hz; subst hp
    exact StepR.pci_keep (.readFwd m r h1 h2 h3) (fun h => h) (fun h => h) hz
  | readPend m s pm h1 h2 h3 =>
    intro r hp _ hz; subst hp
    exact StepR.pci_keep (.readPend m r pm h1 h2 h3) (fun h => h) (fun h => h) hz
  | readArrive m s h1 h2 h3 =>
    intro r hp _ hz; subst hp
    exact StepR.pci_keep (.readArrive m r h1 h2 h3) (fun h => h) (fun h => h) hz
  | readRelease s h1 h2 =>
    intro r hp _ hz; subst hp
    exact StepR.pci_keep (.readRelease r h1 h2) (fun h => h) (fun h => h) hz
  | readAck m s N h1 h2 h3 h4 h5 h6 =>
    intro r hp hc hz; subst hp
    exact StepR.pci_keep (.readAck m r N h1 h2 h3 h4 h5 (hc ▸ h6))
      (by rw [preadRespondAll_role]; exact fun h => h) (by rw [preadRespondAll_role]; exact fun h => h) hz
  | readSingle m s h1 h2 h3 h4 =>
    intro r hp hc hz; subst hp
    exact StepR.pci_keep (.readSingle m r h1 h2 h3 (hc ▸ h4))
      (by rw [preadRespondAll_role]; exact fun h => h) (by rw [preadRespondAll_role]; exact fun h => h) hz
  | readReleaseSingle s h1 h2 h3 =>
    intro r hp hc hz; subst hp
    exact StepR.pci_keep (.readReleaseSingle r h1 h2 (hc ▸ h3))
      (by rw [preadRespondAll_role]; exact fun h => h) (by rw [preadRespondAll_role]; exact fun h => h) hz
  | readState m s e h1 h2 =>
    intro r hp _ hz; subst hp
    exact StepR.pci_keep (.readState m r e h1 h2) (fun h => h) (fun h => h) hz
  | sendFree s m h1 h2 =>
    intro r hp _ hz; subst hp
    exact StepR.pci_keep (.sendFree r m h1 h2) (fun h => h) (fun h => h) hz
  | abandon s h1 =>
    intro r hp _ hz; subst hp
    exact StepR.pci_keep (.abandon r h1)
      (by simp [pbecomeFollower]) (fun h => absurd h h1) hz
  | zeroAck s dst =>
    intro r hp _ hz; subst hp
    exact StepR.pci_keep (.zeroAck r dst) (fun h => h) (fun h => h) hz
  | reMatch s mt h1 h2 =>
    intro r hp _ hz; subst hp
    exact StepR.pci_keep (.reMatch r mt h1 h2) (fun h => h) (fun h => h) hz

end frame_lemmas

section code
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

/-- The ghost part of a node's `RState`: the configuration index, the configuration (with the
learner flags), the full log's prefix below the compaction boundary. -/
structure RGh where
  cidx : Nat
  cfg : CCState
  fp : List EntryM

/-- `pendingConfIndex` as the dynamic model reads it: the code's at a leader, `0` elsewhere (see
the file header). -/
def pciR (s : NState) : w64 := if s.role = .leader then s.pci else W64 0

/-- The `RState` of the physical state `s` with the ghost part `g`. -/
def rOf (s : NState) (g : RGh) : RState where
  p := toPState s
  applied := s.logst.applied
  pci := pciR s
  snap := s.logst.snap.isSome
  cidx := g.cidx
  cfg := g.cfg
  fp := g.fp

/-- A step of the code that keeps what `rOf` reads beyond `toPState`: `applied`, the pending
snapshot, and at a leader that stays one, `pendingConfIndex`. -/
def RFrame (s s' : NState) : Prop :=
  s'.logst.applied = s.logst.applied ∧ s'.logst.snap = s.logst.snap ∧
  (s'.role = .leader → s.role = .leader ∧ s'.pci = s.pci)

theorem RFrame.refl (s : NState) : RFrame s s := ⟨rfl, rfl, fun h => ⟨h, rfl⟩⟩

theorem RFrame.trans {s1 s2 s3 : NState} (h1 : RFrame s1 s2) (h2 : RFrame s2 s3) :
    RFrame s1 s3 :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, fun h => by
    obtain ⟨h21, h22⟩ := h2.2.2 h
    obtain ⟨h11, h12⟩ := h1.2.2 h21
    exact ⟨h11, h22.trans h12⟩⟩

theorem rOf_pci_zero (s : NState) (g : RGh) :
    (rOf s g).p.role ≠ .leader → (rOf s g).pci = W64 0 := by
  intro h
  have : s.role ≠ .leader := fun h' => h (by simp [rOf, toPState, h', proleRole])
  simp [rOf, pciR, this]

/-- With `RFrame`, `rOf` maps the code's step to `StepCF.toR`'s target. -/
theorem rOf_frame (s s' : NState) (g : RGh) (hf : RFrame s s') :
    rOf s' g = { rOf s g with p := toPState s', pci := pciKeep (toPState s') (rOf s g).pci } := by
  obtain ⟨ha, hs, hl⟩ := hf
  have hr : (toPState s').role = .leader ↔ s'.role = .leader := proleRole_leader _
  unfold rOf pciR pciKeep
  by_cases h : s'.role = .leader
  · obtain ⟨h1, h2⟩ := hl h
    simp [h, h1, h2, ha, hs, hr.2 h]
  · have : ¬ (toPState s').role = .leader := fun h' => h (hr.1 h')
    simp [h, this, ha, hs]

/-- The dynamic model's premises of a step of `raft.Step` (see the file header). -/
def DynHyp (m : MessageM) (s s' : NState) (g : RGh) : Prop :=
  m.Type' ≠ MsgSnap ∧ s.role ≠ .preCandidate ∧ FullOk (toPState s).base g.fp ∧
  (m.Type' = MsgStorageApplyResp →
    s.logst.snap = none ∧ NoConfIn (rOf s g).full g.cidx (uint.nat s'.logst.applied)) ∧
  -- a proposal the leader drops still moves `pendingConfIndex` (`StepR.propDrop`), whose
  -- indices the model computes without wrapping: the log is short enough for any batch
  -- `raft.Step` takes (below `2^61` entries)
  (m.Type' = MsgProp → plogLastIndexZ (toPState s).base (toPState s).log + 2 ^ 61 < 2 ^ 64)

/-- How a step moves the configuration index (2026-10-14, stage B7 part 2): not at all, but for
a `MsgStorageApplyResp`, whose `StepR.advance` takes it to the new `applied` when below. -/
def CidxMove (m : MessageM) (s' : NState) (g : RGh) (cidx' : Nat) : Prop :=
  cidx' = g.cidx ∨
    (m.Type' = MsgStorageApplyResp ∧ cidx' = max g.cidx (uint.nat s'.logst.applied))

/-- What a branch of `raft.Step` delivers (see the file header): the `StepC c` witness, and the
`StepR` one at every ghost part over `c`, under the dynamic model's premises. -/
def StepCD (c : CfgM) (id : w64) (m : MessageM) (s : NState) (recv : List Msg)
    (s' : NState) : Prop :=
  StepC c id (toPState s) recv (toPState s') ∧
  ∀ (Adm : List EntryM → CCState → Prop) (dec : CCDec) (g : RGh), g.cfg.cfg = c →
    DynHyp m s s' g → ∃ cidx', CidxMove m s' g cidx' ∧
      StepR Adm dec id (rOf s g) recv (rOf s' { g with cidx := cidx' })

/-- A frame step of the code is a `StepCD` one. -/
theorem StepCD.frame {c : CfgM} {id : w64} {m : MessageM} {s : NState}
    {recv : List Msg} {s' : NState}
    (h : StepCF c id (toPState s) recv (toPState s')) (hf : RFrame s s') :
    StepCD c id m s recv s' := by
  refine ⟨h.toC, fun Adm dec g hc _ => ⟨g.cidx, .inl rfl, ?_⟩⟩
  rw [show ({ g with cidx := g.cidx } : RGh) = g from rfl, rOf_frame s s' g hf]
  exact h.toR (rOf s g) rfl hc (rOf_pci_zero s g)

/-- A `StepCD` step that the dynamic model's premises exclude (a `MsgSnap`, a pre-candidate's):
only the `StepC` witness is needed. -/
theorem StepCD.of_excluded {c : CfgM} {id : w64} {m : MessageM} {s : NState}
    {recv : List Msg} {s' : NState} (h : StepC c id (toPState s) recv (toPState s'))
    (hx : m.Type' = MsgSnap ∨ s.role = .preCandidate) : StepCD c id m s recv s' :=
  ⟨h, fun _ _ _ _ hd => by
    rcases hx with hx | hx
    · exact absurd hx hd.1
    · exact absurd hx hd.2.1⟩

/-- A frame step, then a `StepCD` one (2026-10-14, stage B7). -/
theorem StepCD.trans_frame {c : CfgM} {id : w64} {m : MessageM} {s s1 s' : NState}
    {r1 r2 : List Msg} (h1 : StepCF c id (toPState s) r1 (toPState s1)) (hf : RFrame s s1)
    (h2 : StepCD c id m s1 r2 s') (hd : ∀ g, DynHyp m s s' g → DynHyp m s1 s' g) :
    StepCD c id m s (r1 ++ r2) s' := by
  refine ⟨.trans _ _ _ _ _ h1.toC h2.1, fun Adm dec g hc hdy => ?_⟩
  obtain ⟨cidx', Hcm, H2⟩ := h2.2 Adm dec g hc (hd g hdy)
  refine ⟨cidx', Hcm, .trans _ _ _ _ _ ?_ H2⟩
  rw [rOf_frame s s1 g hf]
  exact h1.toR (rOf s g) rfl hc (rOf_pci_zero s g)

/-- What `raft.Step`'s `MsgSnap` branch delivers (2026-10-14, reconfiguration stage B8): the
`StepC c` witness, and at every ghost part over `c`, for any prefix `fp'` the snapshot `sid` may
cover (`FullOk`) and any configuration state `cs'` over the configuration `cn` its `ConfState`
denotes that the dynamic model admits after `fp'` (`Adm`), a `StepR` witness to a ghost part over
the configuration afterwards `c'` (`cn` after a restore, `c` otherwise). Unlike `StepCD`, the
ghost part may change wholesale (`StepR.snapRestore`'s configuration index, configuration and
full prefix). -/
def StepCDS (c c' cn : CfgM) (id : w64) (sid : entryID) (s : NState) (recv : List Msg)
    (s' : NState) : Prop :=
  StepC c id (toPState s) recv (toPState s') ∧
  ∀ (Adm : List EntryM → CCState → Prop) (dec : CCDec) (g : RGh) (fp' : List EntryM)
    (cs' : CCState), g.cfg.cfg = c → FullOk sid fp' → cs'.cfg = cn → id ∈ cn.ids →
    Adm fp' cs' → ∃ g', g'.cfg.cfg = c' ∧ StepR Adm dec id (rOf s g) recv (rOf s' g')

/-- A frame step (with no configuration change), as `StepCDS`. -/
theorem StepCDS.frame {c cn : CfgM} {id : w64} {sid : entryID} {s : NState} {recv : List Msg}
    {s' : NState} (h : StepCF c id (toPState s) recv (toPState s')) (hf : RFrame s s') :
    StepCDS c c cn id sid s recv s' := by
  refine ⟨h.toC, fun Adm dec g _ _ hc _ _ _ _ => ⟨g, hc, ?_⟩⟩
  rw [rOf_frame s s' g hf]
  exact h.toR (rOf s g) rfl hc (rOf_pci_zero s g)

/-- A frame step, then a `StepCDS` one. -/
theorem StepCDS.trans_frame {c c' cn : CfgM} {id : w64} {sid : entryID} {s s1 s' : NState}
    {r1 r2 : List Msg} (h1 : StepCF c id (toPState s) r1 (toPState s1)) (hf : RFrame s s1)
    (h2 : StepCDS c c' cn id sid s1 r2 s') : StepCDS c c' cn id sid s (r1 ++ r2) s' := by
  refine ⟨.trans _ _ _ _ _ h1.toC h2.1, fun Adm dec g fp' cs' hc hfp hcs hid hA => ?_⟩
  obtain ⟨g', hc', H2⟩ := h2.2 Adm dec g fp' cs' hc hfp hcs hid hA
  refine ⟨g', hc', .trans _ _ _ _ _ ?_ H2⟩
  rw [rOf_frame s s1 g hf]
  exact h1.toR (rOf s g) rfl hc (rOf_pci_zero s g)

/-- A restore (`handleSnapshot`'s third exit) as `StepR.snapRestore`: the node takes the
snapshot's prefix `fp'` and configuration state `cs'`, at the snapshot's index, with the snapshot
pending (`applied` unchanged, `raftLog.restore`'s unstable snapshot set). -/
theorem stepR_snap_restore {Adm : List EntryM → CCState → Prop} {dec : CCDec} {id : w64}
    (s s' : NState) (g : RGh) (m : Msg) (fp' : List EntryM) (cs' : CCState)
    (h1 : m.ty = .snap) (h2 : m.dst = id) (h3 : m.src ≠ id) (h4 : m.term = (toPState s).term)
    (h5 : s.role ≠ .leader) (h6 : uint.Z (toPState s).commit < uint.Z m.index)
    (h7 : ¬ PlogMatches (toPState s).base (toPState s).log (entryID.mk m.logterm m.index))
    (h8 : FullOk (entryID.mk m.logterm m.index) fp') (h9 : id ∈ cs'.cfg.ids) (h10 : Adm fp' cs')
    (Hp : toPState s' = psendMsgs
      { padoptLeader (toPState s) m.src with
          base := entryID.mk m.logterm m.index, log := [], commit := m.index }
      [Msg.mk .appResp id m.src (toPState s).term false m.index (W64 0) (W64 0) (W64 0) []])
    (Ha : s'.logst.applied = s.logst.applied) (Hsn : s'.logst.snap.isSome = true)
    (Hl' : s'.role ≠ .leader) :
    StepR Adm dec id (rOf s g) [m] (rOf s' ⟨uint.nat m.index, cs', fp'⟩) := by
  have Hnl : (rOf s g).p.role ≠ .leader := by
    simp only [rOf, toPState_role]; exact proleRole_not_leader _ h5
  have H := StepR.snapRestore (dec := dec) m (rOf s g) fp' cs' h1 h2 h3 h4 Hnl h6 h7 h8 h9 h10
  have e : rOf s' ⟨uint.nat m.index, cs', fp'⟩ =
      { rOf s g with
        p := psendMsgs
          { padoptLeader (rOf s g).p m.src with
              base := entryID.mk m.logterm m.index, log := [], commit := m.index }
          [Msg.mk .appResp id m.src (rOf s g).p.term false m.index (W64 0) (W64 0) (W64 0) []]
        snap := true
        cidx := uint.nat m.index
        cfg := cs'
        fp := fp' } := by
    unfold rOf pciR
    simp [Hp, Ha, Hsn, h5, Hl']
  rw [e]
  exact H

/-! ### `StepLemmasC.lean`'s frame lemmas, as `StepCF` -/

omit [GoGlobalContext] [GoSemanticsFunctions] in
theorem stepCF_send_frees (c : CfgM) (id : w64) (ps : PState) (ms : List Msg)
    (Hms : ∀ m ∈ ms, (m.ty = .preVote ∨ m.ty = .preVoteResp) ∧ m.src = id) :
    StepCF c id ps [] (psendMsgs ps ms) := by
  induction ms generalizing ps with
  | nil =>
    have : psendMsgs ps [] = ps := by simp [psendMsgs]
    rw [this]; exact .refl ps
  | cons m ms IH =>
    have Hm := Hms m (List.mem_cons_self ..)
    have Heq : psendMsgs ps (m :: ms) = psendMsgs (psendMsgs ps [m]) ms := by
      simp [psendMsgs]
    rw [Heq]
    have := StepCF.trans _ [] _ [] _ (StepCF.sendFree (c := c) ps m Hm.1 Hm.2)
      (IH (psendMsgs ps [m]) (fun m' h => Hms m' (List.mem_cons_of_mem _ h)))
    simpa using this

omit [GoGlobalContext] [GoSemanticsFunctions] in
theorem stepCF_drop (c : CfgM) (id : w64) (s : PState) : StepCF c id s [] s := .refl s

omit [GoGlobalContext] [GoSemanticsFunctions] in
theorem stepCF_stepdown_then_vote (c : CfgM) (id : w64) (s : PState) (m : Msg)
    (Hty : m.ty = .vote) (Hto : m.dst = id) (Hfrom : m.src ≠ W64 0)
    (Hlt : uint.Z s.term < uint.Z m.term)
    (Hutd : plogUpToDate s.base s.log (entryID.mk m.logterm m.index) = true) :
    StepCF c id s ([m] ++ [m])
      (psendMsgs { pbecomeFollower s m.term (W64 0) with vote := m.src }
        [Msg.plain .voteResp id m.src m.term false]) := by
  have Hne : m.term ≠ s.term := by intro Heq; rw [Heq] at Hlt; omega
  have Hh := StepCF.higherTerm (c := c) m s Hlt Hto (by rw [Hty]; simp [fromLeader])
  rw [Hty] at Hh
  simp only [fromLeader] at Hh
  refine .trans _ _ _ _ _ Hh ?_
  exact StepCF.grantVote (c := c) (id := id) m (pbecomeFollower s m.term (W64 0)) Hty Hto
    Hfrom rfl (Or.inr ⟨by simp [pbecomeFollower, Hne], rfl⟩) Hutd

omit [GoGlobalContext] [GoSemanticsFunctions] in
theorem stepCF_stepdown_then_reject (c : CfgM) (id : w64) (s : PState) (m : Msg)
    (Hty : m.ty = .vote) (Hto : m.dst = id) (Hlt : uint.Z s.term < uint.Z m.term) :
    StepCF c id s ([m] ++ [m])
      (psendMsgs (pbecomeFollower s m.term (W64 0))
        [Msg.plain .voteResp id m.src m.term true]) := by
  have Hh := StepCF.higherTerm (c := c) m s Hlt Hto (by rw [Hty]; simp [fromLeader])
  rw [Hty] at Hh
  simp only [fromLeader] at Hh
  exact .trans _ _ _ _ _ Hh (StepCF.rejectVote m _ Hty Hto)

omit [GoGlobalContext] [GoSemanticsFunctions] in
theorem stepCF_record_then_lose (c : CfgM) (id : w64) (s : PState) (m : Msg)
    (Hty : m.ty = .voteResp) (Hto : m.dst = id) (Hterm : m.term = s.term)
    (Hrole : s.role = .candidate)
    (Hq : JLost c (recordVote s.votes m.src (!m.reject))) :
    StepCF c id s ([m] ++ [])
      (pbecomeFollower { s with votes := recordVote s.votes m.src (!m.reject) } s.term (W64 0)) :=
  .trans _ _ _ _ _ (StepCF.recordVote m s Hty Hto Hterm Hrole) (StepCF.lose _ Hrole Hq)

/-! ### The campaign guard on the full log -/

/-- `hasUnappliedConfChanges`'s answer as `StepR.campaign`'s guard: with the full prefix below
the log's boundary and no snapshot pending (`prev ≤ applied`), no conf entry at the log indices
`(applied, committed]` is no conf entry at the full log's positions `[applied, committed)`. -/
theorem noConfIn_of_unapplied (ls : LogState) (fp : List EntryM)
    (Hfp : (fp.length : Int) = uint.Z ls.prev.index')
    (H1 : uint.Z ls.prev.index' ≤ uint.Z ls.applied) (H2 : uint.Z ls.applied ≤ uint.Z ls.committed)
    (H3 : uint.Z ls.committed + 1 < 2 ^ 64)
    (Hno : ¬ ∃ e ∈ unappliedEnts ls, IsConfEnt e) :
    NoConfIn (fp ++ (ls.sents ++ ls.uents)) (uint.nat ls.applied) (uint.nat ls.committed) := by
  intro k e hk1 hk2 he hc
  apply Hno
  refine ⟨e, ?_, hc⟩
  have ha : uint.Z (ls.applied + W64 1) = uint.Z ls.applied + 1 := by word
  have hc1 : uint.Z (ls.committed + W64 1) = uint.Z ls.committed + 1 := by word
  have hka : uint.Z ls.applied ≤ (k : Int) := by have := uint_nat_eq ls.applied; omega
  have hkc : (k : Int) < uint.Z ls.committed := by have := uint_nat_eq ls.committed; omega
  have hkf : fp.length ≤ k := by omega
  rw [List.getElem?_append_right hkf] at he
  unfold unappliedEnts scanRange plogFrom
  rw [ha, hc1]
  apply List.mem_iff_getElem?.2
  refine ⟨k - uint.nat ls.applied, ?_⟩
  rw [List.getElem?_take, ite_eq_left (by have := uint_nat_eq ls.applied; omega), List.getElem?_drop]
  rw [← he]
  congr 1
  have := uint_nat_eq ls.applied
  omega


/-- A step to a non-leader that keeps `applied` and the pending snapshot: `rOf` with `pci`
cleared. -/
theorem rOf_nonleader (s s' : NState) (g : RGh) (ha : s'.logst.applied = s.logst.applied)
    (hs : s'.logst.snap = s.logst.snap) (hr : s'.role ≠ .leader) :
    rOf s' g = { rOf s g with p := toPState s', pci := W64 0 } := by
  unfold rOf pciR
  simp [hr, ha, hs]

/-- `hup`'s step as a `StepCD` one: nothing, a pre-election (a frame step: `abandon` and free
sends), or an election, which is `StepR.campaign` with the guard `hup` checked
(`HupGuard`). The log facts are `ownRaftLog`'s. -/
theorem stepCD_hup {c : CfgM} {id : w64} {m : MessageM} {s s' : NState}
    (Hok : HupOkC c id s s') (Hnw : uint.Z s.term + 1 < 2 ^ 64)
    (Hlog : (s.logst.snap = none → uint.Z s.logst.prev.index' ≤ uint.Z s.logst.applied) ∧
      uint.Z s.logst.applied ≤ uint.Z s.logst.committed ∧ uint.Z s.logst.committed + 1 < 2 ^ 64) :
    StepCD c id m s [] s' := by
  refine ⟨Hok.2.1, fun Adm dec g hc hd => ⟨g.cidx, .inl rfl, ?_⟩⟩
  change StepR Adm dec id (rOf s g) [] (rOf s' g)
  obtain ⟨-, -, ⟨Hl, -⟩, -, Hg⟩ := Hok
  rcases Hg with rfl | ⟨Hnl, Hin, Hsn, Hno, pre, peers, pvs, cl, Hperm, rfl⟩
  · exact .refl _
  have Hrole : (campaignState id s pre peers cl).role ≠ .leader := by
    cases pre <;> simp [campaignState, sendMsgs, becomePrecandidate, becomeCandidate]
  have Hl' : (campaignState id s pre peers cl).logst = s.logst := by
    cases pre <;> simp [campaignState, sendMsgs, becomePrecandidate, becomeCandidate, resetTo,
      resetTo0]
  rw [rOf_nonleader s ({ campaignState id s pre peers cl with prvals := pvs } : NState) g
    (by show (campaignState id s pre peers cl).logst.applied = _; rw [Hl'])
    (by show (campaignState id s pre peers cl).logst.snap = _; rw [Hl']) (by exact Hrole)]
  rw [toPState_prvals_nl (campaignState id s pre peers cl) pvs Hrole]
  have Hnl' : (rOf s g).p.role ≠ .leader := by
    simp only [rOf, toPState_role]; exact proleRole_not_leader _ Hnl
  cases pre
  · -- an election: `StepR.campaign`, with the guard
    show StepR Adm dec id (rOf s g) []
      { rOf s g with p := toPState (sendMsgs (becomeCandidate id s) _), pci := W64 0 }
    rw [toPState_sendMsgs, toPState_becomeCandidate]
    have Hgc : (rOf s g).cfg.cfg = c := hc
    refine StepR.campaign (rOf s g) peers cl Hnl' (by rw [Hgc]; exact Hin)
      (by simp [rOf, Hsn]) ?_ Hnw (by rw [Hgc]; exact Hperm)
    exact noConfIn_of_unapplied s.logst g.fp hd.2.2.1.1 (Hlog.1 Hsn) Hlog.2.1 Hlog.2.2 Hno
  · -- a pre-election: `abandon`, then the free sends
    show StepR Adm dec id (rOf s g) []
      { rOf s g with p := toPState (sendMsgs (becomePrecandidate s) _), pci := W64 0 }
    rw [toPState_sendMsgs, toPState_becomePrecandidate]
    have Hcf : StepCF c id (rOf s g).p [] (psendMsgs (pbecomeFollower (rOf s g).p s.term (W64 0))
        ([Msg.plain .preVoteResp id id (s.term + W64 1) false] ++
         peers.map fun dst => prevoteReq id dst (s.term + W64 1)
           (plogLast s.logst.prev (s.logst.sents ++ s.logst.uents)))) := by
      refine StepCF.trans _ [] _ [] _ (StepCF.abandon (c := c) (id := id) _ Hnl')
        (stepCF_send_frees c id _ _ ?_)
      intro m Hm
      rcases List.mem_append.1 Hm with h | h
      · simp only [List.mem_singleton] at h; subst h; exact ⟨Or.inr rfl, rfl⟩
      · simp only [List.mem_map] at h
        obtain ⟨_, _, rfl⟩ := h
        exact ⟨Or.inl rfl, rfl⟩
    have H := Hcf.toR (Adm := Adm) (dec := dec) (rOf s g) rfl hc (rOf_pci_zero s g)
    have e : pciKeep (psendMsgs (pbecomeFollower (rOf s g).p s.term (W64 0))
        ([Msg.plain .preVoteResp id id (s.term + W64 1) false] ++
         peers.map fun dst => prevoteReq id dst (s.term + W64 1)
           (plogLast s.logst.prev (s.logst.sents ++ s.logst.uents)))) (rOf s g).pci = W64 0 := by
      simp [pciKeep, psendMsgs, pbecomeFollower]
    rw [e] at H
    exact H
end code

end EtcdGrove
end Perennial

-- Projection lemmas, `@[simp, word_unfold]` (ProjSimps.lean).
proj_simps Perennial.EtcdGrove.rOf
