/-
The ghost state `raft.Step` keeps, in either mode (2026-10-14, reconfiguration stage B7).

* `GMode`: the static mode (the ghost state of B4, at a configuration with the ghost state's
  voters, `CfgStatic`) or the dynamic one (B5's `ownRaftGhostR` over `rOf s g`: a decoder `dec`,
  an initial configuration `c0` with `CfgOk`, and the node's ghost part `g` over the struct's
  configuration).
* `ownStepGhost γ md c id s`: `ownRaftGhost` of `toPState s` in the mode's flag, and what else
  the mode keeps (`ghostRest`). In the dynamic mode it is `ownRaftGhostR` (`ownStepGhost_dyn`).
* `GMode.Pre md m ents s`: the dynamic mode's premises of a step the code cannot check
  (`DynHyp`, `StepLemmasR.lean`): no pre-candidate, A1 at a `MsgStorageApplyResp` (no conf
  entry between the configuration index and the acknowledged index), the log short enough for
  a dropped proposal. (Until 2026-10-14, stage B8, also no `MsgSnap`.)
* `GMode.SnapOk γ md sv scfg` (2026-10-14, stage B8): what a `MsgSnap`'s snapshot must be in the
  mode, beyond `SnapScope`: statically, a non-joint `ConfState` with the ghost state's voters;
  dynamically A3 (`SnapConfOk`, `SnapConf.lean`) of the snapshot's prefix -- any prefix with
  records ending at the snapshot's entry id, which the message itself shows to exist
  (`isMessage_snap_prefix`).
* `GMode.StepOut md c id s s' md'`: the step in the mode's model (`StepC c` statically, `StepR`
  at the fold's configurations dynamically, the ghost part possibly moved: the configuration
  index by `advance`, all of it by a snapshot's restore).
* `ghost_stepCD`: a branch's `StepCD` witness updates the mode's ghost state; `ghost_stepCDS`
  (B8): a `MsgSnap` branch's `StepCDS` witness does.
-/
module

public import Proof.go_etcd_io.raft.v3.StepLemmasR
public import Proof.go_etcd_io.raft.v3.Protocol.RefinementDyn
public import Proof.go_etcd_io.raft.v3.SnapConf
public import Spec.go_etcd_io.raft.v3.raft__restore

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
    s.role ≠ .preCandidate ∧
    (m.Type' = MsgStorageApplyResp →
      s.logst.snap = none ∧
      ∀ e, ents.getLast? = some e → NoConfIn (rOf s g).full g.cidx (uint.nat e.Index')) ∧
    (m.Type' = MsgProp → plogLastIndexZ (toPState s).base (toPState s).log + 2 ^ 61 < 2 ^ 64)

/-- How a step moves the dynamic mode's ghost part (2026-10-14, stage B7 part 2): only a
snapshot (`StepR.snapRestore`) moves it freely; a `MsgStorageApplyResp` moves the configuration
index to the new `applied` when below (`CidxMove`); any other step keeps it. -/
def GMove (m : raftpb.Message) (s' : NState) (g g' : RGh) : Prop :=
  m.Type' = MsgSnap ∨ g' = g ∨
    (m.Type' = MsgStorageApplyResp ∧ g' = { g with cidx := max g.cidx (uint.nat s'.logst.applied) })

/-- The step in the mode's model: `StepC c` statically, `StepR` at the dynamic configurations
(`AdmFold`: since 2026-10-14, stage B8, a snapshot's restore included; until then no snapshot
prefix, `AdmS dec c0 (fun _ => False)`) dynamically, the ghost part possibly moved (the
configuration index by `StepR.advance`; all of it by `StepR.snapRestore`), and (2026-10-14, stage
B7 part 2) by nothing else (`GMove`). -/
def GMode.StepOut (md : GMode) (c : CfgM) (id : w64) (m : raftpb.Message) (s s' : NState)
    (md' : GMode) : Prop :=
  match md with
  | .static => md' = .static ∧ ∃ recv, StepC c id (toPState s) recv (toPState s')
  | .dyn dec c0 h0 g => ∃ g', GMove m s' g g' ∧ md' = .dyn dec c0 h0 g' ∧
      ∃ recv, StepR (AdmFold dec c0) dec id (rOf s g) recv (rOf s' g')

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
  | readSingle m s =>
    obtain ⟨o, r, h⟩ := preadRespondAll_eq id s [⟨s.commit, m.src, m.entries⟩]
    rw [h]; exact Int.le_refl _
  | readReleaseSingle s =>
    obtain ⟨o, r, h⟩ := preadRespondAll_eq id ({ s with rd := { s.rd with pend := [] } })
      (s.rd.pend.map (fun p => ⟨s.commit, p.1.From', p.2⟩))
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
  | readSingle m r =>
    obtain ⟨o, rd, h⟩ := preadRespondAll_eq id r.p [⟨r.p.commit, m.src, m.entries⟩]
    simp only [h]; exact Int.le_refl _
  | readReleaseSingle r =>
    obtain ⟨o, rd, h⟩ := preadRespondAll_eq id ({ r.p with rd := { r.p.rd with pend := [] } })
      (r.p.rd.pend.map (fun q => ⟨r.p.commit, q.1.From', q.2⟩))
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
    obtain ⟨g', -, -, recv, H⟩ := H
    exact StepR.commit_mono H

/-- A step of any message but a `MsgStorageApplyResp` keeps the mode (the configuration index
does not move, `CidxMove`). -/
theorem GMode.StepOut.keep {md : GMode} {c : CfgM} {id : w64} {m : raftpb.Message}
    {s s' : NState} {md' : GMode} (H : md.StepOut c id m s s' md')
    (hm : m.Type' ≠ MsgStorageApplyResp) (hs : m.Type' ≠ MsgSnap := by first | assumption | (intro h; simp_all) | decide) :
    md' = md := by
  cases md with
  | static => exact H.1
  | dyn dec c0 h0 g =>
    obtain ⟨g', Hcm, rfl, -⟩ := H
    rcases Hcm with h | rfl | ⟨h, -⟩
    · exact absurd h hs
    · rfl
    · exact absurd h hm

/-- A `MsgStorageApplyResp`'s step moves the configuration index to the new `applied` when it
was below (`CidxMove`). -/
theorem GMode.StepOut.applyResp {dec : CCDec} {c0 : CCState} {h0 : CfgOk c0} {g : RGh}
    {c : CfgM} {id : w64} {m : raftpb.Message} {s s' : NState} {md' : GMode}
    (H : (GMode.dyn dec c0 h0 g).StepOut c id m s s' md') (hs : m.Type' ≠ MsgSnap) :
    ∃ cidx', (cidx' = g.cidx ∨ cidx' = max g.cidx (uint.nat s'.logst.applied)) ∧
      md' = .dyn dec c0 h0 { g with cidx := cidx' } := by
  obtain ⟨g', Hcm, rfl, -⟩ := H
  rcases Hcm with h | h | ⟨-, h⟩
  · exact absurd h hs
  · refine ⟨g.cidx, .inl rfl, ?_⟩; rw [h]
  · refine ⟨_, .inr rfl, ?_⟩; rw [h]

/-- The dynamic mode's premises of a step, for a message that is no snapshot, no storage-apply
acknowledgement and no proposal: only that the node is no pre-candidate. -/
theorem GMode.Pre.of_other {md : GMode} {m : raftpb.Message} {ents : List raftpb.Entry}
    {s : NState} (_h1 : m.Type' ≠ MsgSnap) (h2 : md.isDyn = true → s.role ≠ .preCandidate)
    (h3 : m.Type' ≠ MsgStorageApplyResp) (h4 : m.Type' ≠ MsgProp) : md.Pre m ents s := by
  cases md with
  | static => trivial
  | dyn dec c0 h0 g =>
    exact ⟨h2 rfl, fun h => absurd h h3, fun h => absurd h h4⟩

/-- `GMode.Pre` gives `DynHyp` at any end state whose `applied` moved at most to the
acknowledged index, given the invariant (`applied ≤` the configuration index). -/
theorem GMode.Pre.dynHyp {md : GMode} {m : raftpb.Message} {ents : List raftpb.Entry}
    {s s' : NState} (h : md.Pre m ents s) (Hns : m.Type' ≠ MsgSnap)
    (Hap : m.Type' = MsgStorageApplyResp →
      s'.logst.applied = s.logst.applied ∨
      ∃ e, ents.getLast? = some e ∧ s'.logst.applied = w64Max e.Index' s.logst.applied)
    {dec : CCDec} {c0 : CCState} {h0 : CfgOk c0} {g : RGh} (hmd : md = .dyn dec c0 h0 g)
    (HI : RInv dec c0 (rOf s g)) : DynHyp m s s' g := by
  subst hmd
  obtain ⟨h2, h3, h4⟩ := h
  refine ⟨Hns, h2, HI.full, fun hty => ⟨(h3 hty).1, ?_⟩, h4⟩
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

/-- The commit invariant, from the ghost state in either mode (2026-10-14, stage R). -/
theorem ownStepGhost_inv (γ : RaftNames) (md : GMode) (c : CfgM) (id : w64) (s : NState) :
    ownStepGhost (GF := GF) γ md c id s ⊢ raftCommitInv γ := by
  unfold ownStepGhost
  iintro ⟨Hg, -⟩
  iapply ownRaftGhost_inv_md γ id (toPState s) $$ Hg

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
    ⊢ ([∗list] x ∈ recv, isMessage (GF := GF) γ x) -∗ rdCred γ (rdCount recv) -∗ £ 1 -∗
      ownRaftGhost γ id (toPState s) md.isDyn -∗ ghostRest γ md c id s ={⊤}=∗
      ∃ md', ⌜md.StepOut c id m s s' md'⌝ ∗
        ownRaftGhost γ id (toPState s') md'.isDyn ∗ ghostRest γ md' c id s' := by
  cases md with
  | static =>
    simp only [ghostRest, GMode.isDyn]
    iintro Hrecv Hcr Hlc Hg %HC
    imod ownRaftGhost_stepC γ c HC id (toPState s) recv (toPState s') Hstep.1 $$ Hrecv Hcr Hlc Hg
      with Hg
    imodintro
    iexists GMode.static
    iframe Hg
    isplitr
    · ipureintro; exact ⟨rfl, recv, Hstep.1⟩
    ipureintro; exact HC
  | dyn dec c0 h0 g =>
    simp only [ghostRest, GMode.isDyn]
    iintro Hrecv Hcr Hlc Hg ⟨%Hdc, #Hfr, #Hc⟩
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
      $$ [] Hrecv Hcr Hlc Hown with Hown
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
    · ipureintro
      refine ⟨_, ?_, rfl, recv, StepR.mono (fun _ _ h => h.1) HR⟩
      rcases Hcm with h | ⟨h1, h2⟩
      · exact .inr (.inl (by rw [h]))
      · exact .inr (.inr ⟨h1, by rw [h2]⟩)
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

/-- What a `MsgSnap`'s snapshot must be in the mode, beyond `SnapScope` (2026-10-14,
reconfiguration stage B8; see the file header): statically, a non-joint `ConfState` with the
ghost state's voters (the configuration a restore installs is then still `CfgStatic`);
dynamically, A3 -- the `ConfState` denotes the fold of the snapshot's prefix (`SnapConfOk`), for
any recorded prefix ending at the snapshot's entry id (records agree, so there is one; the
message shows one exists, `isMessage_snap_prefix`). -/
def GMode.SnapOk (γ : RaftNames) : GMode → raftpb.Snapshot → CSLists → IProp GF
  | .static, _, scfg => iprop(⌜GMap.listToSet scfg.voters = γ.reCfg ∧ scfg.outgoing = []⌝)
  | .dyn dec c0 _ _, sv, scfg => iprop(□ ∀ (fp : List raftpb.Entry), logRecs γ base0 fp -∗
      ⌜FullOk (snapId sv) fp⌝ -∗
      ⌜SnapConfOk dec c0 fp scfg.outgoing scfg.voters scfg.learners scfg.learnersNext
        sv.Metadata'.ConfState'.AutoLeave'⌝)

instance GMode.SnapOk_persistent (γ : RaftNames) (md : GMode) (sv : raftpb.Snapshot)
    (scfg : CSLists) : Persistent (md.SnapOk (GF := GF) γ sv scfg) := by
  cases md <;> unfold GMode.SnapOk <;> infer_instance

/-! ### The snapshot a `MsgSnap` carries, certified (2026-10-15, stage S)

`isMessage`'s `snap` case carries the application's certificate of the snapshot's `ConfState`
(`snapCert`, `Protocol/Ghost.lean`): `SnapScope`'s facts, and what the mode asks of it
(`GMode.SnapOk`). So `raft.Step`'s `"Hsnap"` no longer takes either. -/

theorem isMessage_absSnap_cert (γ : RaftNames) (m : raftpb.Message) (sv : raftpb.Snapshot)
    (scfg : CSLists) :
    isMessage (GF := GF) γ (absSnap m sv scfg) ⊢ snapCert γ (snapTrip sv scfg) := by
  unfold isMessage
  simp only [absSnap, absSnapFrom]
  iintro ⟨-, -, -, -, H⟩
  rw [show snapTrip sv scfg = Msg.trip (Msg.mkV MsgType.snap m.From' m.To' m.Term' m.Reject'
      sv.Metadata'.Index' sv.Metadata'.Term' m.Commit' m.RejectHint' [] scfg
      sv.Metadata'.ConfState'.AutoLeave' []) from rfl]
  iexact H

theorem snapCert_scope (γ : RaftNames) (sv : raftpb.Snapshot) (scfg : CSLists) :
    snapCert (GF := GF) γ (snapTrip sv scfg) ⊢ ⌜SnapScope sv scfg⌝ := by
  unfold snapCert
  iintro ⟨%H, -, -⟩
  ipureintro
  exact H

/-- The certificate gives what the mode asks of the snapshot: statically, from `γ`'s static
mode (`ownRaftGhost`'s flag), the ghost state's voters, not joint; dynamically A3, from the
mode's fold (`ghostRest`'s `γ.dyn`). -/
theorem snapOk_of_cert (γ : RaftNames) (md : GMode) (c : CfgM) (id : w64) (s : NState)
    (sv : raftpb.Snapshot) (scfg : CSLists) :
    ⊢ ownRaftGhost (GF := GF) γ id (toPState s) md.isDyn -∗ ghostRest γ md c id s -∗
      snapCert γ (snapTrip sv scfg) -∗
      md.SnapOk γ sv scfg ∗ ownRaftGhost γ id (toPState s) md.isDyn ∗ ghostRest γ md c id s := by
  cases md with
  | static =>
    iintro Hg Hr #Hc
    ihave %Hm := ownRaftGhost_mode γ id (toPState s) $$ Hg
    have Hn : γ.reDyn = none := by
      simp only [GMode.isDyn] at Hm
      cases h : γ.reDyn with
      | none => rfl
      | some _ => rw [h] at Hm; cases Hm
    iframe Hg Hr
    unfold snapCert
    icases Hc with ⟨-, %Hs, -⟩
    simp only [GMode.SnapOk]
    ipureintro; exact Hs Hn
  | dyn dec c0 h0 g =>
    iintro Hg Hr #Hc
    simp only [ghostRest]
    icases Hr with ⟨%Hdc, #Hfr, Hcamp⟩
    obtain ⟨HD, hc, HI⟩ := Hdc
    iframe Hg Hfr Hcamp
    isplitr
    · unfold snapCert
      icases Hc with ⟨%Hl, -, #Hd⟩
      simp only [GMode.SnapOk]
      imodintro
      iintro %fp #Hfp %Hfull
      ihave %Hf := Hd $$ %_ %HD %fp Hfp %Hfull
      ipureintro
      refine ⟨Hl.1, ?_⟩
      simp only [DynCfg.ofFold, Option.map_eq_some_iff] at Hf
      obtain ⟨s', Hs', Hc'⟩ := Hf
      exact ⟨s', Hs', Hc'.symm⟩
    ipureintro; exact ⟨HD, hc, HI⟩

/-- An id `restore`'s `found` search finds is an id of the configuration the `ConfState`
denotes. -/
theorem snapCfg_ids {sv : raftpb.Snapshot} {scfg : CSLists} {id : w64} (h : scfg.Has id) :
    id ∈ (snapCfg sv scfg).ids := by
  unfold snapCfg csCfgM CfgM.ids CfgM.voters
  rcases h with h | h | h
  · exact GMap.elem_of_union_l _ (GMap.elem_of_union_l _ ((GMap.elem_of_list_to_set _ _).2 h))
  · exact GMap.elem_of_union_r _ ((GMap.elem_of_list_to_set _ _).2 h)
  · exact GMap.elem_of_union_l _ (GMap.elem_of_union_r _ ((GMap.elem_of_list_to_set _ _).2 h))

/-- A `MsgSnap` branch's step updates the mode's ghost state (2026-10-14, stage B8): statically
`ownRaftGhost_stepC`, the configuration afterwards still the ghost state's (`GMode.SnapOk`);
dynamically `ownRaftGhostR_stepR` at the snapshot's prefix `fp0`, the one the message shows
(`isMessage_snap_prefix`), whose fold the `ConfState` denotes (`GMode.SnapOk`). -/
theorem ghost_stepCDS (γ : RaftNames) (md : GMode) (c c' : CfgM) (id : w64) (m : raftpb.Message)
    (Hms : m.Type' = MsgSnap) (sv : raftpb.Snapshot) (scfg : CSLists) (s : NState) (recv : List Msg) (s' : NState)
    (a : Msg) (Ha : a.ty = .snap ∧ entryID.mk a.logterm a.index = snapId sv)
    (Hstep : StepCDS c c' (snapCfg sv scfg) id (snapId sv) s recv s')
    (Hid : scfg.Has id) (Hc' : c' = c ∨ c' = snapCfg sv scfg) :
    ⊢ isMessage (GF := GF) γ a -∗ ([∗list] x ∈ recv, isMessage γ x) -∗ rdCred γ (rdCount recv) -∗ £ 1 -∗
      md.SnapOk γ sv scfg -∗ ownRaftGhost γ id (toPState s) md.isDyn -∗ ghostRest γ md c id s ={⊤}=∗
      ∃ md', ⌜md.StepOut c id m s s' md'⌝ ∗
        ownRaftGhost γ id (toPState s') md'.isDyn ∗ ghostRest γ md' c' id s' := by
  cases md with
  | static =>
    simp only [ghostRest, GMode.isDyn, GMode.SnapOk]
    iintro - Hrecv Hcr Hlc %Hso Hg %HC
    imod ownRaftGhost_stepC γ c HC id (toPState s) recv (toPState s') Hstep.1 $$ Hrecv Hcr Hlc Hg
      with Hg
    imodintro
    iexists GMode.static
    iframe Hg
    isplitr
    · ipureintro; exact ⟨rfl, recv, Hstep.1⟩
    ipureintro
    rcases Hc' with rfl | rfl
    · exact HC
    · refine ⟨?_, ?_, HC.2.2⟩
      · simp only [snapCfg, csCfgM]; exact Hso.1
      · simp only [snapCfg, csCfgM]; rw [Hso.2]; try rfl
  | dyn dec c0 h0 g =>
    simp only [ghostRest, GMode.isDyn, GMode.SnapOk]
    iintro #Hm Hrecv Hcr Hlc #Hso Hg ⟨%Hdc, #Hfr, #Hc⟩
    obtain ⟨HD, hc, HI⟩ := Hdc
    -- the snapshot's prefix, from the message, and A3 of it
    icases isMessage_snap_prefix γ a Ha.1 $$ Hm with ⟨%fp0, %Hfp0, #Hr0⟩
    rw [Ha.2] at Hfp0
    ihave %Hsc := Hso $$ %fp0 Hr0 %Hfp0
    obtain ⟨-, cs, Hfold, Hcs⟩ := Hsc
    obtain ⟨g', hg', HR⟩ := Hstep.2 (AdmS dec c0 (fun fp => fp = fp0)) dec g fp0 cs hc Hfp0
      Hcs.symm (snapCfg_ids Hid) ⟨Hfold, rfl⟩
    ihave Hown : ownRaftGhostR γ dec c0 id (rOf s g) $$ [Hg]
    · simp only [ownRaftGhostR, rOf.proj_p, rOf.proj_fp]
      iframe Hg Hfr
      isplitr
      · ipureintro; exact HI
      iintro %hcand; iapply Hc; exact hcand
    imod ownRaftGhostR_stepR γ dec c0 h0 HD (fun fp => fp = fp0) id (rOf s g) recv _ HR
      $$ [] Hrecv Hcr Hlc Hown with Hown
    · imodintro
      iintro %fp %h
      subst h
      iexact Hr0
    imodintro
    iexists GMode.dyn dec c0 h0 g'
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI', #Hfr', #Hc'⟩
    simp only [GMode.isDyn, rOf.proj_p, rOf.proj_fp]
    iframe Hg
    isplitr
    · ipureintro
      exact ⟨g', .inl Hms, rfl, recv, StepR.mono (fun _ _ h => h.1) HR⟩
    iframe Hfr'
    isplitr
    · ipureintro; exact ⟨HD, hg', HI'⟩
    iintro %hcand; iapply Hc'; exact hcand

end ghost

end EtcdGrove
end Perennial
