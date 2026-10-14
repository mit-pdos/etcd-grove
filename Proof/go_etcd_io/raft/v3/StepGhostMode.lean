/-
The ghost state `raft.Step` keeps, in either mode (2026-10-14, reconfiguration stage B7).

* `GMode`: the static mode (the ghost state of B4, at a configuration with the ghost state's
  voters, `CfgStatic`) or the dynamic one (B5's `ownRaftGhostR` over `rOf s g`: a decoder `dec`,
  an initial configuration `c0` with `CfgOk`, and the node's ghost part `g` over the struct's
  configuration).
* `ownStepGhost γ md c id s`: `ownRaftGhost` of `toPState s` in the mode's flag, and what else
  the mode keeps (`ghostRest`). In the dynamic mode it is `ownRaftGhostR` (`ownStepGhost_dyn`).
* `GMode.Pre md m ents s`: the dynamic mode's premises of a step the code cannot check
  (`DynHyp`, `StepLemmasR.lean`): no `MsgSnap` (B8), no pre-candidate, A1 at a
  `MsgStorageApplyResp` (no conf entry between the configuration index and the acknowledged
  index), the log short enough for a dropped proposal.
* `GMode.StepOut md c id s s' md'`: the step in the mode's model (`StepC c` statically, `StepR`
  dynamically, the configuration index possibly moved).
* `ghost_stepCD`: a branch's `StepCD` witness updates the mode's ghost state.
-/
module

public import Proof.go_etcd_io.raft.v3.StepLemmasR
public import Proof.go_etcd_io.raft.v3.Protocol.RefinementDyn

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode GMap go_etcd_io.raft.v3

section mode
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

/-- The mode of the ghost state `raft.Step` keeps (see the file header). -/
inductive GMode where
  | static
  | dyn (dec : CCDec) (c0 : CCState) (h0 : CfgOk c0) (g : RGh)

/-- The flag `ownRaftGhost` carries. -/
def GMode.isDyn : GMode → Bool
  | .static => false
  | .dyn .. => true

/-- The dynamic mode's premises of a step of `raft.Step` the code cannot check (see the file
header); none in the static mode. -/
def GMode.Pre (md : GMode) (m : raftpb.Message) (ents : List raftpb.Entry) (s : NState) : Prop :=
  match md with
  | .static => True
  | .dyn _ _ _ g =>
    m.Type' ≠ MsgSnap ∧ s.role ≠ .preCandidate ∧
    (m.Type' = MsgStorageApplyResp →
      s.logst.snap = none ∧
      ∀ e, ents.getLast? = some e → NoConfIn (rOf s g).full g.cidx (uint.nat e.Index')) ∧
    (m.Type' = MsgProp → plogLastIndexZ (toPState s).base (toPState s).log + 2 ^ 61 < 2 ^ 64)

/-- The step in the mode's model: `StepC c` statically, `StepR` at the dynamic configurations
(no snapshot prefix: a snapshot restore is outside the dynamic scope) dynamically, the
configuration index possibly moved (`StepR.advance`), only by a `MsgStorageApplyResp`
(`CidxMove`, 2026-10-14, stage B7 part 2). -/
def GMode.StepOut (md : GMode) (c : CfgM) (id : w64) (m : raftpb.Message) (s s' : NState)
    (md' : GMode) : Prop :=
  match md with
  | .static => md' = .static ∧ ∃ recv, StepC c id (toPState s) recv (toPState s')
  | .dyn dec c0 h0 g => ∃ cidx', CidxMove m s' g cidx' ∧ md' = .dyn dec c0 h0 { g with cidx := cidx' } ∧
      ∃ recv, StepR (AdmS dec c0 (fun _ => False)) dec id (rOf s g) recv
        (rOf s' { g with cidx := cidx' })

/-! ### The commit index never moves back, in either model (2026-10-14, stage B7 part 2)

As `Step.commit_mono` (`Protocol/Facts.lean`): what the `RawNode` predicate needs to carry a
queued `MsgStorageApplyResp`'s "its entries are committed" across steps. -/

private theorem plogCommitTo_ge' (c t : w64) : uint.Z c ≤ uint.Z (plogCommitTo c t) := by
  unfold plogCommitTo; split <;> omega

theorem StepC.commit_mono {c : CfgM} {id : w64} {ps : PState} {recv : List Msg} {ps' : PState}
    (H : StepC c id ps recv ps') : uint.Z ps.commit ≤ uint.Z ps'.commit := by
  induction H with
  | refl => exact Int.le_refl _
  | trans _ _ _ _ _ _ _ ih1 ih2 => omega
  | appAccept => exact plogCommitTo_ge' _ _
  | heartbeat => exact plogCommitTo_ge' _ _
  | commit _ _ _ h => exact Int.le_of_lt h
  | snapRestore _ _ _ _ _ _ _ h => simp only [psendMsgs]; omega
  | snapFastfwd _ _ _ _ _ _ _ h => simp only [psendMsgs]; omega
  | readAck m s N =>
    obtain ⟨o, r, h⟩ := preadRespondAll_eq id
      ({ s with rd := { s.rd with
           ro := (readonlyAdvance (readonlyRecvAck s.rd.ro m.src m.ctx) N).1 } })
      (readonlyAdvance (readonlyRecvAck s.rd.ro m.src m.ctx) N).2
    rw [h]; exact Int.le_refl _
  | _ => simp [psendMsgs, pbecomeFollower, pbecomeCandidate, pwinState, pappend, pbecomeLeader,
      padoptLeader]

theorem StepR.commit_mono {Adm : List raftpb.Entry → CCState → Prop} {dec : CCDec} {id : w64}
    {r : RState} {recv : List Msg} {r' : RState} (H : StepR Adm dec id r recv r') :
    uint.Z r.p.commit ≤ uint.Z r'.p.commit := by
  induction H with
  | refl => exact Int.le_refl _
  | trans _ _ _ _ _ _ _ ih1 ih2 => omega
  | appAccept => exact plogCommitTo_ge' _ _
  | heartbeat => exact plogCommitTo_ge' _ _
  | commit _ _ _ h => exact Int.le_of_lt h
  | snapRestore _ _ _ _ _ _ _ _ _ h => simp only [psendMsgs]; omega
  | snapFastfwd _ _ _ _ _ _ _ h => simp only [psendMsgs]; omega
  | readAck m r N =>
    obtain ⟨o, rd, h⟩ := preadRespondAll_eq id
      ({ r.p with rd := { r.p.rd with
           ro := (readonlyAdvance (readonlyRecvAck r.p.rd.ro m.src m.ctx) N).1 } })
      (readonlyAdvance (readonlyRecvAck r.p.rd.ro m.src m.ctx) N).2
    simp only [h]; exact Int.le_refl _
  | _ => simp [psendMsgs, pbecomeFollower, pbecomeCandidate, pwinState, pappend, pbecomeLeader,
      padoptLeader]

/-- The step in the mode's model does not move the code's commit index back. -/
theorem GMode.StepOut.commit_mono {md : GMode} {c : CfgM} {id : w64} {m : raftpb.Message}
    {s s' : NState} {md' : GMode} (H : md.StepOut c id m s s' md') :
    uint.Z s.logst.committed ≤ uint.Z s'.logst.committed := by
  cases md with
  | static =>
    obtain ⟨-, recv, H⟩ := H
    exact StepC.commit_mono H
  | dyn dec c0 h0 g =>
    obtain ⟨cidx', -, -, recv, H⟩ := H
    exact StepR.commit_mono H

/-- A step of any message but a `MsgStorageApplyResp` keeps the mode (the configuration index
does not move, `CidxMove`). -/
theorem GMode.StepOut.keep {md : GMode} {c : CfgM} {id : w64} {m : raftpb.Message}
    {s s' : NState} {md' : GMode} (H : md.StepOut c id m s s' md')
    (hm : m.Type' ≠ MsgStorageApplyResp) : md' = md := by
  cases md with
  | static => exact H.1
  | dyn dec c0 h0 g =>
    obtain ⟨cidx', Hcm, rfl, -⟩ := H
    rcases Hcm with rfl | ⟨h, -⟩
    · rfl
    · exact absurd h hm

/-- A `MsgStorageApplyResp`'s step moves the configuration index to the new `applied` when it
was below (`CidxMove`). -/
theorem GMode.StepOut.applyResp {dec : CCDec} {c0 : CCState} {h0 : CfgOk c0} {g : RGh}
    {c : CfgM} {id : w64} {m : raftpb.Message} {s s' : NState} {md' : GMode}
    (H : (GMode.dyn dec c0 h0 g).StepOut c id m s s' md') :
    ∃ cidx', (cidx' = g.cidx ∨ cidx' = max g.cidx (uint.nat s'.logst.applied)) ∧
      md' = .dyn dec c0 h0 { g with cidx := cidx' } := by
  obtain ⟨cidx', Hcm, rfl, -⟩ := H
  refine ⟨cidx', ?_, rfl⟩
  rcases Hcm with h | ⟨-, h⟩
  · exact .inl h
  · exact .inr h

/-- The dynamic mode's premises of a step, for a message that is no snapshot, no storage-apply
acknowledgement and no proposal: only that the node is no pre-candidate. -/
theorem GMode.Pre.of_other {md : GMode} {m : raftpb.Message} {ents : List raftpb.Entry}
    {s : NState} (h1 : m.Type' ≠ MsgSnap) (h2 : md.isDyn = true → s.role ≠ .preCandidate)
    (h3 : m.Type' ≠ MsgStorageApplyResp) (h4 : m.Type' ≠ MsgProp) : md.Pre m ents s := by
  cases md with
  | static => trivial
  | dyn dec c0 h0 g =>
    exact ⟨h1, h2 rfl, fun h => absurd h h3, fun h => absurd h h4⟩

/-- `GMode.Pre` gives `DynHyp` at any end state whose `applied` moved at most to the
acknowledged index, given the invariant (`applied ≤` the configuration index). -/
theorem GMode.Pre.dynHyp {md : GMode} {m : raftpb.Message} {ents : List raftpb.Entry}
    {s s' : NState} (h : md.Pre m ents s)
    (Hap : m.Type' = MsgStorageApplyResp →
      s'.logst.applied = s.logst.applied ∨
      ∃ e, ents.getLast? = some e ∧ s'.logst.applied = w64Max e.Index' s.logst.applied)
    {dec : CCDec} {c0 : CCState} {h0 : CfgOk c0} {g : RGh} (hmd : md = .dyn dec c0 h0 g)
    (HI : RInv dec c0 (rOf s g)) : DynHyp m s s' g := by
  subst hmd
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, HI.full, fun hty => ⟨(h3 hty).1, ?_⟩, h4⟩
  have Hac : uint.nat s.logst.applied ≤ g.cidx := HI.applied_cidx
  have Hempty : ∀ n, n ≤ g.cidx → NoConfIn (rOf s g).full g.cidx n :=
    fun n hn k e hk1 hk2 => absurd (Nat.lt_of_lt_of_le hk2 hn) (Nat.not_lt.2 hk1)
  rcases Hap hty with ha | ⟨e, he, ha⟩
  · rw [ha]; exact Hempty _ Hac
  · rw [ha]
    unfold w64Max
    split
    · exact (h3 hty).2 e he
    · exact Hempty _ Hac

end mode

section ghost
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]
variable {GF : BundledGFunctors} [AllG GF] [InvGS GF]

/-- What the mode keeps beyond `ownRaftGhost`: statically, the configuration's voters are the
ghost state's; dynamically, `ownRaftGhostR`'s invariant, full prefix records and campaign
record, with the ghost part over the configuration. -/
def ghostRest (γ : RaftNames) : GMode → CfgM → w64 → NState → IProp GF
  | .static, c, _, _ => iprop(⌜CfgStatic γ c⌝)
  | .dyn dec c0 h0 g, c, id, s =>
    iprop(⌜γ.dyn = some (DynCfg.ofFold dec c0 h0) ∧ g.cfg.cfg = c ∧ RInv dec c0 (rOf s g)⌝ ∗
      logRecs γ base0 g.fp ∗
      (∀ (_ : (toPState s).role = .candidate),
        isCampK γ id (toPState s).term (rOf s g).full (toPState s).commit))

/-- The ghost state `raft.Step` keeps (see the file header). -/
def ownStepGhost (γ : RaftNames) (md : GMode) (c : CfgM) (id : w64) (s : NState) : IProp GF :=
  iprop(ownRaftGhost γ id (toPState s) md.isDyn ∗ ghostRest γ md c id s)

/-- In the dynamic mode, `ownStepGhost` is `ownRaftGhostR`. -/
theorem ownStepGhost_dyn (γ : RaftNames) (dec : CCDec) (c0 : CCState) (h0 : CfgOk c0) (g : RGh)
    (c : CfgM) (id : w64) (s : NState) :
    ownStepGhost (GF := GF) γ (.dyn dec c0 h0 g) c id s ⊣⊢
      ⌜γ.dyn = some (DynCfg.ofFold dec c0 h0) ∧ g.cfg.cfg = c⌝ ∗
        ownRaftGhostR γ dec c0 id (rOf s g) := by
  simp only [ownStepGhost, ghostRest, GMode.isDyn, ownRaftGhostR, rOf.proj_p, rOf.proj_fp]
  constructor
  · iintro ⟨Hg, %Hdc, #Hfr, #Hc⟩
    obtain ⟨HD, hc, HI⟩ := Hdc
    isplitr
    · ipureintro; exact ⟨HD, hc⟩
    iframe Hg Hfr
    isplitr
    · ipureintro; exact HI
    iintro %hcand; iapply Hc; exact hcand
  · iintro ⟨%Hdc, Hg, %HI, #Hfr, #Hc⟩
    obtain ⟨HD, hc⟩ := Hdc
    iframe Hg Hfr
    isplitr
    · ipureintro; exact ⟨HD, hc, HI⟩
    iintro %hcand; iapply Hc; exact hcand

/-- A branch's step updates the mode's ghost state: statically `ownRaftGhost_stepC`,
dynamically `ownRaftGhostR_stepR` (the premises `DynHyp` from `Hdh`, given the invariant). -/
theorem ghost_stepCD (γ : RaftNames) (md : GMode) (c : CfgM) (id : w64) (m : raftpb.Message)
    (s : NState) (recv : List Msg) (s' : NState) (Hstep : StepCD c id m s recv s')
    (Hdh : ∀ (dec : CCDec) (c0 : CCState) (h0 : CfgOk c0) (g : RGh), md = .dyn dec c0 h0 g →
      RInv dec c0 (rOf s g) → DynHyp m s s' g) :
    ⊢ ([∗list] x ∈ recv, isMessage (GF := GF) γ x) -∗ rdCred γ (rdCount recv) -∗
      ownRaftGhost γ id (toPState s) md.isDyn -∗ ghostRest γ md c id s ={⊤}=∗
      ∃ md', ⌜md.StepOut c id m s s' md'⌝ ∗
        ownRaftGhost γ id (toPState s') md'.isDyn ∗ ghostRest γ md' c id s' := by
  cases md with
  | static =>
    simp only [ghostRest, GMode.isDyn]
    iintro Hrecv Hcr Hg %HC
    imod ownRaftGhost_stepC γ c HC id (toPState s) recv (toPState s') Hstep.1 $$ Hrecv Hcr Hg
      with Hg
    imodintro
    iexists GMode.static
    iframe Hg
    isplitr
    · ipureintro; exact ⟨rfl, recv, Hstep.1⟩
    ipureintro; exact HC
  | dyn dec c0 h0 g =>
    simp only [ghostRest, GMode.isDyn]
    iintro Hrecv Hcr Hg ⟨%Hdc, #Hfr, #Hc⟩
    obtain ⟨HD, hc, HI⟩ := Hdc
    obtain ⟨cidx', Hcm, HR⟩ := Hstep.2 (AdmS dec c0 (fun _ => False)) dec g hc
      (Hdh dec c0 h0 g rfl HI)
    ihave Hown : ownRaftGhostR γ dec c0 id (rOf s g) $$ [Hg]
    · simp only [ownRaftGhostR, rOf.proj_p, rOf.proj_fp]
      iframe Hg Hfr
      isplitr
      · ipureintro; exact HI
      iintro %hcand; iapply Hc; exact hcand
    imod ownRaftGhostR_stepR γ dec c0 h0 HD (fun _ => False) id (rOf s g) recv _ HR
      $$ [] Hrecv Hcr Hown with Hown
    · imodintro
      iintro %fp %h
      exact h.elim
    imodintro
    iexists GMode.dyn dec c0 h0 { g with cidx := cidx' }
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI', #Hfr', #Hc'⟩
    simp only [GMode.isDyn, rOf.proj_p, rOf.proj_fp]
    iframe Hg
    isplitr
    · ipureintro; exact ⟨cidx', Hcm, rfl, recv, HR⟩
    iframe Hfr'
    isplitr
    · ipureintro; exact ⟨HD, hc, HI'⟩
    iintro %hcand; iapply Hc'; exact hcand

/-- Two code states that the mode's ghost state reads alike (2026-10-14, stage B7 part 2): the
same protocol state, `applied`, pending snapshot and (at a leader) `pendingConfIndex`. -/
theorem rOf_congr {s s' : NState} (g : RGh) (hp : toPState s' = toPState s)
    (ha : s'.logst.applied = s.logst.applied) (hs : s'.logst.snap = s.logst.snap)
    (hpci : pciR s' = pciR s) : rOf s' g = rOf s g := by
  unfold rOf; rw [hp, ha, hs, hpci]; try rfl

theorem ownStepGhost_congr (γ : RaftNames) (md : GMode) (c : CfgM) (id : w64) {s s' : NState}
    (hp : toPState s' = toPState s) (ha : s'.logst.applied = s.logst.applied)
    (hs : s'.logst.snap = s.logst.snap) (hpci : pciR s' = pciR s) :
    ownStepGhost (GF := GF) γ md c id s ⊢ ownStepGhost γ md c id s' := by
  cases md with
  | static =>
    simp only [ownStepGhost, ghostRest]; rw [hp]
  | dyn dec c0 h0 g =>
    simp only [ownStepGhost, ghostRest]
    have hr := rOf_congr g hp ha hs hpci
    rw [hp, hr]

/-- What the mode keeps beyond `ownRaftGhost` survives a change of the code state that keeps
what it reads (2026-10-14, stage B7 part 2): the log, its boundary, the commit index, the term,
the role, `applied`, the pending snapshot and `pciR` -- e.g. a `Ready`'s drain of the outbox
and of the `ReadState`s, or `acceptReady`'s moves of `applying` and of what the storage holds. -/
theorem ghostRest_keep (γ : RaftNames) (md : GMode) (c : CfgM) (id : w64) {s s' : NState}
    (hb : (toPState s').base = (toPState s).base) (hl : (toPState s').log = (toPState s).log)
    (hc : (toPState s').commit = (toPState s).commit) (ht : (toPState s').term = (toPState s).term)
    (hr : (toPState s').role = (toPState s).role) (ha : s'.logst.applied = s.logst.applied)
    (hs : s'.logst.snap = s.logst.snap) (hpci : pciR s' = pciR s) :
    ghostRest (GF := GF) γ md c id s ⊢ ghostRest γ md c id s' := by
  cases md with
  | static => simp only [ghostRest]; exact .rfl
  | dyn dec c0 h0 g =>
    simp only [ghostRest]
    iintro ⟨%H, #Hfr, #Hc⟩
    obtain ⟨HD, hc', HI⟩ := H
    have hfull : (rOf s' g).full = (rOf s g).full := by
      simp only [RState.full, rOf.proj_fp, rOf.proj_p]; rw [hl]
    isplitr
    · ipureintro
      refine ⟨HD, hc', HI.frame (by simp [rOf]) (by simp [rOf, hb]) (by simp [rOf, hl])
        (by simp [rOf, hc]) (by simp [rOf, ha]) (by simp [rOf, hs]) (by simp [rOf])
        (by simp [rOf]) (.inr ⟨by simp [rOf, hr], by simp [rOf, hpci]⟩)⟩
    iframe Hfr
    iintro %hcand
    rw [hfull, ht, hc]
    iapply Hc
    rw [← hr]; exact hcand

end ghost

end EtcdGrove
end Perennial
