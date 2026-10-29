/-
The ghost state `raft.Step` keeps, in either mode (2026-10-14, reconfiguration stage B7).

* `GMode`: the static mode (the ghost state of B4, at a configuration with the ghost state's
  voters, `CfgStatic`) or the dynamic one (B5's `ownRaftGhostR` over `rOf s g`: a decoder `dec`,
  an initial configuration `c0` with `CfgOk`, and the node's ghost part `g` over the struct's
  configuration).
* `ownStepGhost γ md c id s`: `ownRaftGhost` of `toPState s` in the mode's flag, and what else
  the mode keeps (`ghostRest`). In the dynamic mode it is `ownRaftGhostR` (`ownStepGhost_dyn`).
* `GMode.Pre md m ents s`: the dynamic mode's premises of a step the code cannot check
  (`DynHyp`, `StepLemmasR.lean`): a pre-candidate with its campaign guard (`PreGuard`; until 2026-10-25 none), A1 at a `MsgStorageApplyResp` (no conf
  entry between the configuration index and the acknowledged index), the log short enough for
  a dropped proposal. (Until 2026-10-14, stage B8, also no `MsgSnap`.)
* `GMode.SnapOkIf γ id md sv scfg` (2026-10-14, stage B8; D22 S-b′4): what a `MsgSnap`'s snapshot
  must be in the mode, beyond `SnapScope`, once its `ConfState` names the node: statically, a
  non-joint `ConfState` with the ghost state's voters; dynamically (2026-10-28, stage U3c: the
  message's certificate, `raftSnapCert`; until then `GMode.SnapOk`, a premise of `raft.Step`) A3
  (`SnapConfOk`, `SnapConf.lean`) of the snapshot's prefix -- any prefix with records ending at the
  snapshot's entry id, which the message itself shows to exist (`isMessage_snap_prefix`).
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
public import Proof.go_etcd_io.raft.v3.InvStorage
public import Proof.go_etcd_io.raft.v3.Protocol.LeadWit

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode GMap go_etcd_io.raft.v3

section mode
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

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
def GMode.Pre (md : GMode) (m : MessageM) (ents : List EntryM) (s : NState) : Prop :=
  match md with
  | .static => True
  | .dyn dec _ _ g =>
    PreGuardF g.fp s ∧
    -- (2026-10-28, the decision switch) A1 over the node's decisions (until then no conf entry)
    (m.Type' = MsgStorageApplyResp →
      ∀ e, ents.getLast? = some e →
        NoUndecConfIn (effDec dec g.decs) (rOf s g).full g.cidx (uint.nat e.Index')) ∧
    (m.Type' = MsgProp → plogLastIndexZ (toPState s).base (toPState s).log + 2 ^ 61 < 2 ^ 64)

/-- How a step moves the dynamic mode's ghost part (2026-10-14, stage B7 part 2): only a
snapshot (`StepR.snapRestore`) moves it freely; a `MsgStorageApplyResp` moves the configuration
index to the new `applied` when below (`CidxMove`); (2026-10-28, stage U3) a snapshot's
acknowledgement (`StepR.applySnap`), which moves `applied`, moves the configuration index (to the new
`applied`, U3c) and the configuration, keeping the full prefix; any other step keeps it. -/
def GMove (m : MessageM) (s s' : NState) (g g' : RGh) : Prop :=
  -- (2026-10-28, stage U3c) a snapshot keeps the configuration index and the configuration (a
  -- restore's `StepR.snapRestore` does), and all of the ghost part at a pre-candidate (a restore
  -- makes a follower)
  -- (2026-10-28, the decision switch) a restore takes the snapshot certificate's decisions too
  (m.Type' = MsgSnap ∧ g'.cidx = g.cidx ∧ g'.cfg = g.cfg ∧ g.decs ⊆ g'.decs ∧
      (s'.role = .preCandidate → g'.fp = g.fp)) ∨
    g' = g ∨
    (m.Type' = MsgStorageApplyResp ∧ g' = { g with cidx := max g.cidx (uint.nat s'.logst.applied) }) ∨
    (m.Type' = MsgStorageAppendResp ∧ s'.logst.applied ≠ s.logst.applied ∧ g'.fp = g.fp ∧
      g'.decs = g.decs ∧ g'.cidx = uint.nat s'.logst.applied)

/-- The step in the mode's model: `StepC c` statically, `StepR` at the dynamic configurations
(`AdmFold`: since 2026-10-14, stage B8, a snapshot's restore included; until then no snapshot
prefix, `AdmS dec c0 (fun _ => False)`) dynamically, the ghost part possibly moved (the
configuration index by `StepR.advance`; all of it by `StepR.snapRestore`), and (2026-10-14, stage
B7 part 2) by nothing else (`GMove`). -/
def GMode.StepOut (md : GMode) (c : CfgM) (id : w64) (m : MessageM) (s s' : NState)
    (md' : GMode) : Prop :=
  match md with
  | .static => md' = .static ∧ ∃ B recv, StepC c id B (toPState s) recv (toPState s')
  | .dyn dec c0 h0 g => ∃ g', GMove m s s' g g' ∧ md' = .dyn dec c0 h0 g' ∧
      -- (2026-10-28, the decision switch) the base decoder over the decisions witnessed
      ∃ (B : Int) (recv : List Msg),
        StepR (AdmFold (effDec dec g'.decs) c0) (effDec dec g'.decs) id B (rOf s g) recv
          (rOf s' g')

/-! ### The commit index never moves back, in either model (2026-10-14, stage B7 part 2)

As `Step.commit_mono` (`Protocol/Facts.lean`): what the `RawNode` predicate needs to carry a
queued `MsgStorageApplyResp`'s "its entries are committed" across steps. -/

theorem StepC.commit_mono {c : CfgM} {id : w64} {B : Int} {ps : PState} {recv : List Msg}
    {ps' : PState} (H : StepC c id B ps recv ps') : uint.Z ps.commit ≤ uint.Z ps'.commit := by
  induction H with
  | refl => exact Int.le_refl _
  | trans _ _ _ _ _ _ _ ih1 ih2 => omega
  | appAccept => exact plogCommitTo_ge _ _
  | heartbeat => exact plogCommitTo_ge _ _
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

theorem StepR.commit_mono {Adm : List EntryM → CCState → Prop} {dec : CCDec} {id : w64}
    {B : Int} {r : RState} {recv : List Msg} {r' : RState} (H : StepR Adm dec id B r recv r') :
    uint.Z r.p.commit ≤ uint.Z r'.p.commit := by
  induction H with
  | refl => exact Int.le_refl _
  | trans _ _ _ _ _ _ _ ih1 ih2 => omega
  | appAccept => exact plogCommitTo_ge _ _
  | heartbeat => exact plogCommitTo_ge _ _
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
theorem GMode.StepOut.commit_mono {md : GMode} {c : CfgM} {id : w64} {m : MessageM}
    {s s' : NState} {md' : GMode} (H : md.StepOut c id m s s' md') :
    uint.Z s.logst.committed ≤ uint.Z s'.logst.committed := by
  cases md with
  | static =>
    obtain ⟨-, B, recv, H⟩ := H
    exact StepC.commit_mono H
  | dyn dec c0 h0 g =>
    obtain ⟨g', -, -, B, recv, H⟩ := H
    exact StepR.commit_mono H

/-- A step of any message but a `MsgStorageApplyResp`, a `MsgSnap` and (2026-10-28, stage U3) a
snapshot's acknowledgement (a `MsgStorageAppendResp` that moves `applied`) keeps the mode (the
configuration index does not move, `CidxMove`). -/
theorem GMode.StepOut.keep {md : GMode} {c : CfgM} {id : w64} {m : MessageM}
    {s s' : NState} {md' : GMode} (H : md.StepOut c id m s s' md')
    (hm : m.Type' ≠ MsgStorageApplyResp) (hs : m.Type' ≠ MsgSnap := by first | assumption | (intro h; simp_all) | decide)
    (ha : m.Type' = MsgStorageAppendResp → s'.logst.applied = s.logst.applied) :
    md' = md := by
  cases md with
  | static => exact H.1
  | dyn dec c0 h0 g =>
    obtain ⟨g', Hcm, rfl, -⟩ := H
    rcases Hcm with h | rfl | ⟨h, -⟩ | ⟨h, h2, -⟩
    · exact absurd h.1 hs
    · rfl
    · exact absurd h hm
    · exact absurd (ha h) h2

/-- (2026-10-25, T-M M2b) The dynamic mode's campaign guard of a pre-candidate (`PreGuard`, at the
ghost part's full prefix); nothing in the static mode. -/
def GMode.Guard (md : GMode) (s : NState) : Prop :=
  match md with
  | .static => True
  | .dyn _ _ _ g => PreGuardF g.fp s

/-- At a node that is no pre-candidate in the dynamic mode, the guard holds vacuously. -/
theorem GMode.Guard.of_nonpre {md : GMode} {s : NState}
    (h : md.isDyn = true → s.role ≠ .preCandidate) : md.Guard s := by
  cases md with
  | static => trivial
  | dyn dec c0 h0 g => exact fun _ hp => absurd hp (h rfl)

/-- The dynamic mode's premises of a step, for a message that is no snapshot, no storage-apply
acknowledgement and no proposal: only a pre-candidate's campaign guard (`GMode.Guard`; until
2026-10-25 that the node is no pre-candidate). -/
theorem GMode.Pre.of_other {md : GMode} {m : MessageM} {ents : List EntryM}
    {s : NState} (_h1 : m.Type' ≠ MsgSnap) (h2 : md.Guard s)
    (h3 : m.Type' ≠ MsgStorageApplyResp) (h4 : m.Type' ≠ MsgProp) : md.Pre m ents s := by
  cases md with
  | static => trivial
  | dyn dec c0 h0 g =>
    exact ⟨h2, fun h => absurd h h3, fun h => absurd h h4⟩

/-- `GMode.Pre` gives `DynHyp` at any end state whose `applied` moved at most to the
acknowledged index, given the invariant (`applied ≤` the configuration index). -/
theorem GMode.Pre.dynHyp {md : GMode} {m : MessageM} {ents : List EntryM}
    {s s' : NState} (h : md.Pre m ents s) (Hns : m.Type' ≠ MsgSnap)
    (Hap : m.Type' = MsgStorageApplyResp →
      s'.logst.applied = s.logst.applied ∨
      ∃ e, ents.getLast? = some e ∧ s'.logst.applied = w64Max e.Index' s.logst.applied)
    {dec : CCDec} {c0 : CCState} {h0 : CfgOk c0} {g : RGh} (hmd : md = .dyn dec c0 h0 g)
    {d' : CCDec} (HI : RInv d' c0 (rOf s g)) : DynHyp (effDec dec g.decs) m s s' g := by
  subst hmd
  obtain ⟨h2, h3, h4⟩ := h
  refine ⟨Hns, h2 HI.full.1, HI.full, fun hty => ?_, h4⟩
  have Hac : uint.nat s.logst.applied ≤ g.cidx := HI.applied_cidx
  have Hempty : ∀ n, n ≤ g.cidx → NoUndecConfIn (effDec dec g.decs) (rOf s g).full g.cidx n :=
    fun n hn k e hk1 hk2 => absurd (Nat.lt_of_lt_of_le hk2 hn) (Nat.not_lt.2 hk1)
  rcases Hap hty with ha | ⟨e, he, ha⟩
  · rw [ha]; exact Hempty _ Hac
  · rw [ha]
    unfold w64Max
    split
    · exact h3 hty e he
    · exact Hempty _ Hac

end mode

/-! ### The snapshots' certificates as raft carries them, and the cluster's (U8 v2, 2026-10-29)

Raft's log and struct are γ-free: they carry a snapshot's certificate as the γ-free pins of its
storage names `sn` -- a stored snapshot's validity (`svCert sn`, the contract's `snapshotValid`)
and a received snapshot's certificate (`ksnCert sn`). `storCertOk γ sn` ties them to the cluster's
certificates (`raftSnapCertD γ`): a stored snapshot's validity gives its certificate (what a
`Ready` hands out with a `MsgSnap` from the storage), a received one's pin is the certificate
(both ways: `raft.Step` pins the one a `MsgSnap` carries). The node level proves it (step 4 of
U8 v2) from the pins. Until U8 v2 the storage kept a registry of certified snapshots (`storCert`),
tied to raft's both ways (D22 S-b′2/S-r). -/

section certLink
variable [GooseExts] {GF : BundledGFunctors} [AllG GF] [ReceiptGS GF] [InvGS GF] [StorageModel GF]

/-- The namespace of the certificates' invariant (2026-10-27: the cluster's, `RaftNames.reCertNs`). -/
def raftCertN (γ : RaftNames) : Namespace := γ.reCertNs

/-- See above. -/
def storCertOk (γ : RaftNames) (sn : StorNames) : IProp GF :=
  iprop(□ (∀ (sv : SnapshotM) (E : CoPset), ⌜↑(raftCertN γ) ⊆ E⌝ -∗ svCert sn sv ={E}=∗
      raftSnapCertD γ (snapTrip sv sv.Metadata'.ConfState'.lists)) ∗
    □ (∀ (k : SnapTrip) (E : CoPset), ⌜↑(raftCertN γ) ⊆ E⌝ -∗ ksnCert sn k ={E}=∗
      raftSnapCertD γ k) ∗
    □ (∀ (k : SnapTrip) (E : CoPset), ⌜↑(raftCertN γ) ⊆ E⌝ -∗ raftSnapCertD γ k ={E}=∗
      ksnCert sn k))

instance storCertOk_persistent (γ : RaftNames) (sn : StorNames) :
    Persistent (storCertOk (GF := GF) γ sn) := by
  unfold storCertOk; infer_instance

end certLink

section ghost
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]
variable {GF : BundledGFunctors} [AllG GF] [ReceiptGS GF] [InvGS GF] [StorageModel GF]

/-- What the mode keeps beyond `ownRaftGhost`: statically, the configuration's voters are the
ghost state's, and (D19p, 2026-10-18) its voters and learners -- the ids the tracker holds -- and
the node are within the ghost state's tracked bound (`TrackedOk`); dynamically, `ownRaftGhostR`'s invariant, full prefix records and campaign
record, with the ghost part over the configuration. -/
def ghostRestM (γ : RaftNames) : GMode → CfgM → w64 → NState → IProp GF
  | .static, c, id, _ => iprop(⌜CfgStatic γ c ∧ TrackedOk γ c id⌝)
  | .dyn dec c0 h0 g, c, id, s =>
    -- (2026-10-28, the decision switch) over the decisions the node witnessed (`g.decs`)
    iprop(⌜γ.dyn = some (DynCfg.ofFold dec c0 h0) ∧ g.cfg.cfg = c ∧
        RInv (effDec dec g.decs) c0 (rOf s g)⌝ ∗ decLb γ g.decs ∗
      logRecs γ base0 g.fp ∗
      (∀ (_ : (toPState s).role = .candidate),
        isCampK γ id (toPState s).term (rOf s g).full (toPState s).commit))

/-- (2026-10-19, D21 M3) The node's no-snapshot mode (`NGhost.ns`) is the cluster's
(`RaftNames.reNoSnap`): of a cluster with a non-empty bootstrap log (`RaftNames.noSnap_boot`), what
the leader's rejection handling reads of the messages (`isMessage`'s clause of a rejecting
`appResp`), and what the messages a `Ready` hands out say (`isRaftMsg`). Set with the node
(`Bootstrap`), kept by every step. (2026-10-19, D21 M2r) And leader transfer is off
(`NGhost.xf`) exactly in the cluster's no-transfer mode (2026-10-19, D22 S-a:
`RaftNames.reNoXfer`, its own flag; until then the no-snapshot mode's). (2026-10-20, D22 S-c) And
the node is past term `0` for good (`NGhost.bt`) exactly in that mode too, its bootstrap log's.
(raft-final phase 1, 2026-10-29, U9: the no-transfer mode's two flags deleted with the mode; what is
left goes with `NGhost.ns` in phase 2's raft-level track, the no-snapshot mode being off at raft's
level, `NsCap`.) -/
def NsLink (γ : RaftNames) (s : NState) : Prop :=
  s.gh.ns = γ.reNoSnap

theorem NsLink.boot {γ : RaftNames} {s : NState} (H : NsLink γ s) (h : s.gh.ns = true) :
    γ.reBoot ≠ [] :=
  RaftNames.noSnap_boot (by rw [← H]; exact h)

/-- (D22 S-b′3, 2026-10-20; U8 v2, 2026-10-29: over the storage names, in every mode) The node's
snapshot certificates are tied to the cluster's (`storCertOk`): a `Ready` certifies the `MsgSnap`s
it hands out from them, a `MsgSnap`'s `raft.Step` pins its snapshot's. Until U8 v2 the no-snapshot
mode needed no link (`⌜γ.reNoSnap = true⌝ ∨ …`); the mode is dropped at raft's level (a node's
`NGhost.ns` is off, `ownRaftPhys`'s `Hnsoff`). -/
def certLink (γ : RaftNames) (sn : StorNames) : IProp GF := storCertOk γ sn

instance certLink_persistent (γ : RaftNames) (sn : StorNames) :
    Persistent (certLink (GF := GF) γ sn) := by
  unfold certLink; infer_instance

/-- (raft-final, 2026-10-29, U7: the design's §2.2) **The stamped transfer requests' witnesses**
(persistent): every `(To, Term)` the node recorded in `NGhost.xw` (the stamped `MsgTransferLeader`s
it queued, `XfOk`) has its destination leading at that term. What a `Ready` gives each such
message (`isRaftMsg`'s transfer clause). -/
def xfW (γ : RaftNames) (s : NState) : IProp GF :=
  iprop([∗map] p ↦ _u ∈ s.gh.xw, isLeader γ p.1 p.2)

instance xfW_persistent (γ : RaftNames) (s : NState) : Persistent (xfW (GF := GF) γ s) := by
  unfold xfW; infer_instance

/-- What the mode keeps beyond `ownRaftGhost` (`ghostRestM`), (D21 M3) `NsLink`, (D22 S-b′3) the
storage's certificate link (`certLink`), and (raft-final, 2026-10-29, U7: the design's §2.1, §2.4)
the leader witness (`leadW`) and the stamped transfer requests' witnesses (`xfW`), each a framed
conjunct of its own: the proofs that move neither `lead`, `term` nor `NGhost.xw` keep them. -/
def ghostRest (γ : RaftNames) (md : GMode) (c : CfgM) (id : w64) (s : NState) : IProp GF :=
  iprop(⌜NsLink γ s⌝ ∗ ghostRestM γ md c id s ∗ certLink γ s.gh.sn ∗ leadW γ id (toPState s) ∗
    xfW γ s)

theorem ghostRest_nsLink (γ : RaftNames) (md : GMode) (c : CfgM) (id : w64) (s : NState) :
    ghostRest (GF := GF) γ md c id s ⊢ ⌜NsLink γ s⌝ ∗ ghostRest γ md c id s := by
  unfold ghostRest
  iintro ⟨%Hn, H⟩
  iframe H
  isplitr <;> ipureintro <;> exact Hn

/-- (2026-10-25, T-M M2c) The node's configuration has a voter, in either mode: statically the
ghost state's voters (`RaftNames.reCfg_ne`), dynamically a fold of the changes from a good
configuration (`cfgFold_ok`). What a leader that need not be a voter itself (removed without
`StepDownOnRemoval`) needs for its quorums. -/
theorem ghostRest_voters_ne (γ : RaftNames) (md : GMode) (c : CfgM) (id : w64) (s : NState) :
    ghostRest (GF := GF) γ md c id s ⊢ ⌜s.role = .leader → c.voters ≠ ∅⌝ ∗ ghostRest γ md c id s := by
  have Hne : ∀ c : CfgM, c.incoming ≠ ∅ → c.voters ≠ ∅ := by
    intro c hi hv
    apply hi
    apply GMap.set_eq
    intro x
    refine ⟨fun hx => ?_, fun hx => absurd hx (GMap.not_elem_of_empty _)⟩
    have := GMap.elem_of_union_l c.outgoing hx
    rw [show c.incoming ∪ c.outgoing = c.voters from rfl, hv] at this
    exact absurd this (GMap.not_elem_of_empty _)
  cases md with
  | static =>
    unfold ghostRest
    simp only [ghostRestM]
    iintro ⟨%Hn, %HC, #Hl⟩
    isplitr
    · ipureintro; intro _; rw [CfgStatic.voters HC.1]; exact γ.reCfg_ne
    iframe Hl
    ipureintro; exact ⟨Hn, HC⟩
  | dyn dec c0 h0 g =>
    unfold ghostRest
    simp only [ghostRestM]
    iintro ⟨%Hn, ⟨%Hd, H0, H1, H2⟩, #Hl⟩
    isplitr
    · ipureintro
      intro _
      have Hok := cfgFold_ok Hd.2.2.cfg h0
      rw [← Hd.2.1]; exact Hne _ Hok.2.1
    iframe Hl
    isplitr; · ipureintro; exact Hn
    iframe H0 H1 H2
    ipureintro; exact Hd


/-- (D22 S-b′3) The certificate link, read out. -/
theorem ghostRest_certLink (γ : RaftNames) (md : GMode) (c : CfgM) (id : w64) (s : NState) :
    ghostRest (GF := GF) γ md c id s ⊢ certLink γ s.gh.sn ∗ ghostRest γ md c id s := by
  unfold ghostRest
  iintro ⟨%Hn, H, #Hl, #Hw, #Hx⟩
  iframe Hl H Hw Hx
  ipureintro; exact Hn

/-- The ghost state `raft.Step` keeps (see the file header). -/
def ownStepGhost (γ : RaftNames) (md : GMode) (c : CfgM) (id : w64) (s : NState) : IProp GF :=
  iprop(ownRaftGhost γ id (toPState s) md.isDyn ∗ ghostRest γ md c id s)

/-- (2026-10-19, D21 M2r) The node's modes are the cluster's (`NsLink`), read out. -/
theorem ownStepGhost_nsLink (γ : RaftNames) (md : GMode) (c : CfgM) (id : w64) (s : NState) :
    ownStepGhost (GF := GF) γ md c id s ⊢ ⌜NsLink γ s⌝ ∗ ownStepGhost γ md c id s := by
  iintro H
  iunfold ownStepGhost at H
  icases H with ⟨Hg, Hr⟩
  icases ghostRest_nsLink γ md c id s $$ Hr with ⟨%Hnl, Hr⟩
  isplitr
  · ipureintro; exact Hnl
  iunfold ownStepGhost
  iframe Hg Hr

/-- `LeadOk` and the leader's own witness, read out of `ownRaftGhost`. -/
private theorem ownRaftGhost_leadInfo (γ : RaftNames) (id : w64) (ps : PState) (md : Bool) :
    ownRaftGhost (GF := GF) γ id ps md ⊢
      ⌜LeadOk id ps⌝ ∗ leaderWit γ id ps ∗ ownRaftGhost γ id ps md := by
  iintro Hown
  iunfold ownRaftGhost at Hown
  icases Hown with ⟨%γv, %voted, %kl, H⟩
  iNamed H
  isplitr
  · ipureintro; exact Hlead_ok
  isplitr
  · iexact Hlead
  iapply ownRaftGhost_intro γ id ps γv voted kl Hname Hidnz Hmode $$ Hvoted [] Hfrags Hout Htally Hlead Hlg [] [] Hvrecs [] Hlcm Hrd
  · ipureintro; exact Hhist
  · ipureintro; exact Hlead_ok
  · ipureintro; exact Hfollower_votes
  · ipureintro; exact Hrole_ok

private theorem leaderWit_isLeader' (γ : RaftNames) (id : w64) (ps : PState)
    (h : ps.role = .leader) : leaderWit (GF := GF) γ id ps ⊢ isLeader γ id ps.term := by
  unfold leaderWit; simp only [h]; exact .rfl

/-- (raft-final, 2026-10-29, U7: the design's §2.1) **The node's leader leads its term**: from
`leadW` for another node, from `LeadOk` and `leaderWit` for itself (a node records itself only as
leader). Not at a pre-candidate (raft-final phase 2): `toPState` hides its leader (`lead := 0`),
so nothing witnesses a physical `lead` left there. -/
theorem ownStepGhost_lead (γ : RaftNames) (md : GMode) (c : CfgM) (id : w64) (s : NState)
    (Hr : s.role ≠ .preCandidate) :
    ownStepGhost (GF := GF) γ md c id s ⊢
      (□ (⌜s.lead ≠ W64 0⌝ -∗ isLeader γ s.lead s.term)) ∗ ownStepGhost γ md c id s := by
  iintro H
  iunfold ownStepGhost at H
  icases H with ⟨Hg, Hrest⟩
  icases ownRaftGhost_leadInfo γ id (toPState s) md.isDyn $$ Hg with ⟨%Hlo, #Hlw, Hg⟩
  iunfold ghostRest at Hrest
  icases Hrest with ⟨%Hn, Hm, #Hcl, #Hw, #Hx⟩
  have hl : (toPState s).lead = s.lead := toPState_lead_nonpre s Hr
  isplitr
  · iintro !> %Hnz
    by_cases hid : s.lead = id
    · have hrole : (toPState s).role = .leader :=
        Classical.byContradiction fun h => Hlo h (by rw [hl]; exact hid)
      rw [hid, show s.term = (toPState s).term from rfl]
      iapply leaderWit_isLeader' γ id (toPState s) hrole $$ Hlw
    · rw [← hl, show s.term = (toPState s).term from rfl]
      iunfold leadW at Hw
      iapply Hw
      ipureintro; exact ⟨by rw [hl]; exact Hnz, by rw [hl]; exact hid⟩
  iunfold ownStepGhost
  iframe Hg
  iunfold ghostRest
  iframe Hm Hcl Hw Hx
  ipureintro; exact Hn

/-- (raft-final, 2026-10-29, U7: the design's §2.1) **A stamped transfer request to the node at its
term finds it with no leader, if it is a follower**: the request's witness (`isLeader γ id T`, from
`isRaftMsg`) and the node's leader's (`ownStepGhost_lead`) agree (`isLeader_unique`), and a node
records itself only as leader (`LeadOk`). What `raft.Step`'s transfer arm needs (until then a premise
of `RestMsgOk`). -/
theorem ownStepGhost_xferRefute (γ : RaftNames) (md : GMode) (c : CfgM) (id : w64) (s : NState)
    (T : w64) :
    ownStepGhost (GF := GF) γ md c id s ∗ isLeader γ id T ⊢
      ⌜T = s.term → s.role = .follower → s.lead = W64 0⌝ ∗ ownStepGhost γ md c id s := by
  iintro ⟨H, #Hi⟩
  by_cases hc : s.role = .follower ∧ T = s.term
  · obtain ⟨hf, hT⟩ := hc
    subst hT
    icases ownStepGhost_lead γ md c id s (by rw [hf]; decide) $$ H with ⟨#Hl, H⟩
    iunfold ownStepGhost at H
    icases H with ⟨Hg, Hrest⟩
    icases ownRaftGhost_leadInfo γ id (toPState s) md.isDyn $$ Hg with ⟨%Hlo, -, Hg⟩
    by_cases hz : s.lead = W64 0
    · isplitr
      · ipureintro; intro _ _; exact hz
      iunfold ownStepGhost; iframe Hg Hrest
    · ihave #Hl2 : isLeader (GF := GF) γ s.lead s.term $$ []
      · iapply Hl; ipureintro; exact hz
      icases isLeader_unique γ s.lead id s.term $$ Hl2 Hi with %Heq
      exact (Hlo (by rw [toPState_role, hf]; decide)
        (by rw [toPState_lead_nonpre s (by rw [hf]; decide)]; exact Heq)).elim
  · isplitr
    · ipureintro; intro h1 h2; exact absurd ⟨h2, h1⟩ hc
    iexact H

/-- Recording a witnessed pair in `NGhost.xw`. -/
private theorem xfW_insert (γ : RaftNames) (s : NState) (p : w64 × w64) :
    isLeader (GF := GF) γ p.1 p.2 ∗ xfW γ s ⊢
      xfW γ { s with gh := { s.gh with xw := insert p s.gh.xw } } := by
  unfold xfW
  have e : ({ s with gh := { s.gh with xw := insert p s.gh.xw } } : NState).gh.xw =
      (insert p s.gh.xw : GSet (w64 × w64)) := rfl
  rw [e]
  by_cases hin : p ∈ s.gh.xw
  · obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 hin
    have hid : (insert p s.gh.xw : GSet (w64 × w64)) = s.gh.xw :=
      GMap.insert_id _ _ () (by cases u; exact hu)
    rw [hid]
    exact sep_elim_right
  · exact (BigSepM.bigSepM_insert (PROP := IProp GF)
      (Φ := fun (q : w64 × w64) (_ : Unit) => isLeader (GF := GF) γ q.1 q.2) (m := s.gh.xw)
      (i := p) (x := ()) (Option.not_isSome_iff_eq_none.1 hin)).2

/-- (raft-final, 2026-10-29, U7: the design's §2.2) **Recording a stamped transfer request**: the
node's leader and term, with the leader's witness (`ownStepGhost_lead`), into `NGhost.xw`. What
`raft.Step`'s transfer arm does before `stepFollower` forwards the request (`send`'s clause (c)). Not at a pre-candidate, as
`ownStepGhost_lead`. -/
theorem ownStepGhost_xw_record (γ : RaftNames) (md : GMode) (c : CfgM) (id : w64) (s : NState)
    (Hl : s.lead ≠ W64 0) (Hr : s.role ≠ .preCandidate) :
    ownStepGhost (GF := GF) γ md c id s ⊢
      ownStepGhost γ md c id { s with gh := { s.gh with xw := insert (s.lead, s.term) s.gh.xw } } := by
  iintro H
  icases ownStepGhost_lead γ md c id s Hr $$ H with ⟨#Hld, H⟩
  ihave #Hl2 : isLeader (GF := GF) γ s.lead s.term $$ []
  · iapply Hld; ipureintro; exact Hl
  iunfold ownStepGhost at H
  icases H with ⟨Hg, Hrest⟩
  iunfold ghostRest at Hrest
  icases Hrest with ⟨%Hn, Hm, #Hcl, #Hw, #Hx⟩
  have hp : toPState { s with gh := { s.gh with xw := insert (s.lead, s.term) s.gh.xw } } =
      toPState s := rfl
  have hm : ghostRestM (GF := GF) γ md c id
      { s with gh := { s.gh with xw := insert (s.lead, s.term) s.gh.xw } } =
      ghostRestM γ md c id s := by cases md <;> rfl
  iunfold ownStepGhost
  rw [hp]
  iframe Hg
  iunfold ghostRest
  rw [hm, hp]
  isplitr
  · ipureintro; exact Hn
  iframe Hm Hcl Hw
  iapply xfW_insert γ s (s.lead, s.term)
  iframe Hl2 Hx

/-- (D22 S-b′4) The mode is `γ`'s (`ownRaftGhost_mode`), read out. -/
theorem ownStepGhost_mode (γ : RaftNames) (md : GMode) (c : CfgM) (id : w64) (s : NState) :
    ownStepGhost (GF := GF) γ md c id s ⊢ ⌜γ.reDyn.isSome = md.isDyn⌝ ∗ ownStepGhost γ md c id s := by
  iintro H
  iunfold ownStepGhost at H
  icases H with ⟨Hg, Hr⟩
  ihave %Hm := ownRaftGhost_mode γ id (toPState s) (md := md.isDyn) $$ Hg
  isplitr
  · ipureintro; exact Hm
  iunfold ownStepGhost
  iframe Hg Hr

/-- The commit invariant, from the ghost state in either mode (2026-10-14, stage R). -/
theorem ownStepGhost_inv (γ : RaftNames) (md : GMode) (c : CfgM) (id : w64) (s : NState) :
    ownStepGhost (GF := GF) γ md c id s ⊢ raftCommitInv γ := by
  unfold ownStepGhost
  iintro ⟨Hg, -⟩
  iapply ownRaftGhost_inv_md γ id (toPState s) $$ Hg

/-- `ackIn` at equal arguments (2026-10-16, stage R8a): for an `ackIn` stated at a term and an index
that are only definitionally the ones a lemma wants (`(toPState s).term`, `(absMsg …).index`). -/
theorem ackIn_cast (γ : RaftNames) {t t' i i' : w64} (ht : t = t') (hi : i = i') :
    ackIn (GF := GF) γ t i ⊢ ackIn γ t' i' := by
  subst ht hi; exact .rfl

/-- (2026-10-19, D21 M3) In the no-snapshot mode a leader's last index is at least `2`
(`ownRaftGhost_leader_last`, the mode only with a bootstrap log, `NsLink`): what
`applyConfChange` needs for a peer it starts tracking (`PrLo`). -/
theorem ownRaftGhost_ns_last (γ : RaftNames) (id : w64) (s : NState) {md : Bool}
    (Hnl : NsLink γ s) :
    ⊢ ownRaftGhost (GF := GF) γ id (toPState s) md -∗
      ⌜s.gh.ns = true → s.role = .leader →
        2 ≤ plogLastIndexZ s.logst.prev (s.logst.sents ++ s.logst.uents)⌝ ∗
      ownRaftGhost γ id (toPState s) md := by
  iintro Hg
  icases ownRaftGhost_leader_last γ id (toPState s) $$ Hg with ⟨%H, Hg⟩
  iframe Hg
  ipureintro
  intro hns hl
  exact H (by rw [toPState_role]; exact (proleRole_leader _).2 hl) (Hnl.boot hns)

theorem ownStepGhost_ns_last (γ : RaftNames) (md : GMode) (c : CfgM) (id : w64) (s : NState) :
    ⊢ ownStepGhost (GF := GF) γ md c id s -∗
      ⌜s.gh.ns = true → s.role = .leader →
        2 ≤ plogLastIndexZ s.logst.prev (s.logst.sents ++ s.logst.uents)⌝ ∗
      ownStepGhost γ md c id s := by
  unfold ownStepGhost
  iintro ⟨Hg, Hr⟩
  icases ghostRest_nsLink γ md c id s $$ Hr with ⟨%Hnl, Hr⟩
  icases ownRaftGhost_ns_last γ id s Hnl $$ Hg with ⟨%H, Hg⟩
  iframe Hg Hr
  ipureintro; exact H

/-- In the dynamic mode, `ownStepGhost` is `ownRaftGhostR`, over the decisions the node witnessed
(2026-10-28, the decision switch). -/
theorem ownStepGhost_dyn (γ : RaftNames) (dec : CCDec) (c0 : CCState) (h0 : CfgOk c0) (g : RGh)
    (c : CfgM) (id : w64) (s : NState) :
    ownStepGhost (GF := GF) γ (.dyn dec c0 h0 g) c id s ⊣⊢
      ⌜γ.dyn = some (DynCfg.ofFold dec c0 h0) ∧ g.cfg.cfg = c ∧ NsLink γ s⌝ ∗
        decLb γ g.decs ∗ ownRaftGhostR γ (effDec dec g.decs) c0 id (rOf s g) ∗
        -- (raft-final, 2026-10-29, U7) with the leader witness and the transfer records' witnesses
        (certLink γ s.gh.sn ∗ leadW γ id (toPState s) ∗ xfW γ s) := by
  simp only [ownStepGhost, ghostRest, ghostRestM, GMode.isDyn, ownRaftGhostR, rOf.proj_p,
    rOf.proj_fp]
  constructor
  · iintro ⟨Hg, %Hnl, ⟨%Hdc, #HM, #Hfr, #Hc⟩, #Hcl⟩
    obtain ⟨HD, hc, HI⟩ := Hdc
    isplitr
    · ipureintro; exact ⟨HD, hc, Hnl⟩
    iframe Hg Hfr Hcl HM
    isplitr
    · ipureintro; exact HI
    iintro %hcand; iapply Hc; exact hcand
  · iintro ⟨%Hdc, #HM, ⟨Hg, %HI, #Hfr, #Hc⟩, #Hcl⟩
    obtain ⟨HD, hc, Hnl⟩ := Hdc
    iframe Hg Hfr Hcl
    isplitr
    · ipureintro; exact Hnl
    iframe HM
    isplitr
    · ipureintro; exact ⟨HD, hc, HI⟩
    iintro %hcand; iapply Hc; exact hcand

/-- (2026-10-28, the decision switch) **The node witnesses more of the client's decisions**: a lower
bound of the decision map joins the ghost part's (the two agree, `decLb_compat`; the invariant reads
the decoder through defined folds only, `RInv.mono_dec`). -/
theorem ownStepGhost_absorb (γ : RaftNames) (dec : CCDec) (c0 : CCState) (h0 : CfgOk c0)
    (g : RGh) (c : CfgM) (id : w64) (s : NState) (M : DecMap) :
    decLb (GF := GF) γ M ∗ ownStepGhost γ (.dyn dec c0 h0 g) c id s ⊢
      ownStepGhost γ (.dyn dec c0 h0 { g with decs := g.decs ∪ M }) c id s := by
  simp only [ownStepGhost, ghostRest, ghostRestM, GMode.isDyn]
  iintro ⟨#HM, Hg, %Hnl, ⟨%Hdc, #Hg0, #Hfr, #Hc⟩, #Hcl⟩
  obtain ⟨HD, hc, HI⟩ := Hdc
  ihave #Hu := decLb_union γ g.decs M $$ [Hg0 HM]
  · iframe Hg0 HM
  iframe Hg Hcl Hu
  rw [show rOf s { g with decs := g.decs ∪ M } = rOf s g from rfl]
  iframe Hfr Hc
  ipureintro
  exact ⟨Hnl, HD, hc, HI.mono_dec (effDec_mono dec (DecCompat.sub_left g.decs M))⟩
/-- A branch's step updates the mode's ghost state: statically `ownRaftGhost_stepC`,
dynamically `ownRaftGhostR_stepR` (the premises `DynHyp` from `Hdh`, given the invariant). -/
theorem ghost_stepCDM (γ : RaftNames) (md : GMode) (c : CfgM) (id : w64) (m : MessageM)
    (B : Int) (HB : B < 2 ^ 64)
    (s : NState) (recv : List Msg) (s' : NState) (Hstep : StepCD c id B m s recv s')
    (Hdh : ∀ (dec : CCDec) (c0 : CCState) (h0 : CfgOk c0) (g : RGh), md = .dyn dec c0 h0 g →
      ∀ d' : CCDec, RInv d' c0 (rOf s g) → DynHyp (effDec dec g.decs) m s s' g) :
    ⊢ ⧖ (B.toNat - γ.reBoot.length) -∗ ([∗list] x ∈ recv, isMessage (GF := GF) γ x) -∗ rdCred γ (rdCount recv) -∗ msgsTks γ recv -∗ £ 1 -∗
      ownRaftGhost γ id (toPState s) md.isDyn -∗ ghostRestM γ md c id s ={⊤}=∗
      ∃ md', ⌜md.StepOut c id m s s' md'⌝ ∗
        ownRaftGhost γ id (toPState s') md'.isDyn ∗ ghostRestM γ md' c id s' := by
  cases md with
  | static =>
    simp only [ghostRestM, GMode.isDyn]
    iintro #Hrc Hrecv Hcr Htk Hlc Hg %HC
    imod ownRaftGhost_stepC γ c HC.1 id HC.2 B HB (toPState s) recv (toPState s') Hstep.1 $$ Hrc
      Hrecv Hcr Htk Hlc Hg
      with Hg
    imodintro
    iexists GMode.static
    iframe Hg
    isplitr
    · ipureintro; exact ⟨rfl, B, recv, Hstep.1⟩
    ipureintro; exact HC
  | dyn dec c0 h0 g =>
    simp only [ghostRestM, GMode.isDyn]
    iintro #Hrc Hrecv Hcr Htk Hlc Hg ⟨%Hdc, #HM, #Hfr, #Hc⟩
    obtain ⟨HD, hc, HI⟩ := Hdc
    obtain ⟨cidx', Hcm, HR⟩ := Hstep.2 (AdmS (effDec dec (g.decs)) c0 (fun _ => False)) (effDec dec (g.decs))
      g hc (Hdh dec c0 h0 g rfl _ HI)
    ihave Hown : ownRaftGhostR γ (effDec dec (g.decs)) c0 id (rOf s g) $$ [Hg]
    · simp only [ownRaftGhostR, rOf.proj_p, rOf.proj_fp]
      iframe Hg Hfr
      isplitr
      · ipureintro; exact HI
      iintro %hcand; iapply Hc; exact hcand
    imod ownRaftGhostR_stepR γ dec (g.decs) c0 h0 HD (fun _ => False) id B HB (rOf s g) recv _ HR
      $$ Hrc HM [] Hrecv Hcr Htk Hlc Hown with Hown
    · imodintro
      iintro %fp %h
      exact h.elim
    imodintro
    iexists GMode.dyn dec c0 h0 { g with cidx := cidx' }
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI', #Hfr', #Hc'⟩
    simp only [rOf.proj_p, rOf.proj_fp]
    iframe Hg
    isplitr
    · ipureintro
      refine ⟨_, ?_, rfl, B, recv, by
        exact StepR.mono (fun _ _ h => h.1) HR⟩
      rcases Hcm with h | ⟨h1, h2⟩
      · exact .inr (.inl (by rw [h]))
      · exact .inr (.inr (.inl ⟨h1, by rw [h2]⟩))
    iframe Hfr' HM
    isplitr
    · ipureintro; exact ⟨HD, hc, HI'⟩
    iintro %hcand; iapply Hc'; exact hcand


/-- `ghost_stepCDM` with (D21 M3) `NsLink` kept: the step keeps the mode (`NGhost.ns`). -/
theorem ghost_stepCD (γ : RaftNames) (md : GMode) (c : CfgM) (id : w64) (m : MessageM)
    (B : Int) (HB : B < 2 ^ 64)
    (s : NState) (recv : List Msg) (s' : NState) (Hstep : StepCD c id B m s recv s')
    (Hdh : ∀ (dec : CCDec) (c0 : CCState) (h0 : CfgOk c0) (g : RGh), md = .dyn dec c0 h0 g →
      ∀ d' : CCDec, RInv d' c0 (rOf s g) → DynHyp (effDec dec g.decs) m s s' g)
    (Hng : s'.gh = s.gh ∧ s'.logst.storage = s.logst.storage) :

    ⊢ ⧖ (B.toNat - γ.reBoot.length) -∗ ([∗list] x ∈ recv, isMessage (GF := GF) γ x) -∗ rdCred γ (rdCount recv) -∗ msgsTks γ recv -∗ £ 1 -∗
      ownRaftGhost γ id (toPState s) md.isDyn -∗ ghostRest γ md c id s ={⊤}=∗
      ∃ md', ⌜md.StepOut c id m s s' md'⌝ ∗
        ownRaftGhost γ id (toPState s') md'.isDyn ∗ ghostRest γ md' c id s' := by
  iintro #Hrc #Hrecv Hcr Htk Hlc Hg Hrest
  iunfold ghostRest at Hrest
  icases Hrest with ⟨%Hnl, Hrest, #Hcl, #Hw, #Hx⟩
  ihave #Hw' := leadW_stepC γ c id B (toPState s) recv (toPState s') Hstep.1 $$ Hrecv Hw
  imod ghost_stepCDM γ md c id m B HB s recv s' Hstep Hdh $$ Hrc Hrecv Hcr Htk Hlc Hg Hrest
    with ⟨%md', %Hout, Hg, Hrest⟩
  imodintro
  iexists md'
  iframe Hg
  isplitr
  · ipureintro; exact Hout
  iunfold ghostRest
  iframe Hrest Hw'
  isplitr
  · ipureintro
    unfold NsLink at Hnl ⊢; rw [Hng.1]; exact Hnl
  rw [show certLink (GF := GF) γ s'.gh.sn = certLink γ s.gh.sn by rw [Hng.1],
    show xfW (GF := GF) γ s' = xfW γ s by unfold xfW; rw [Hng.1]]
  iframe Hcl Hx

/-- Two code states that the mode's ghost state reads alike (2026-10-14, stage B7 part 2): the
same protocol state, `applied`, pending snapshot and (at a leader) `pendingConfIndex`. -/
theorem rOf_congr {s s' : NState} (g : RGh) (hp : toPState s' = toPState s)
    (ha : s'.logst.applied = s.logst.applied) (hs : s'.logst.snap = s.logst.snap)
    (hpci : pciR s' = pciR s) : rOf s' g = rOf s g := by
  unfold rOf; rw [hp, ha, hs, hpci]; try rfl

theorem ownStepGhost_congr (γ : RaftNames) (md : GMode) (c : CfgM) (id : w64) {s s' : NState}
    (hp : toPState s' = toPState s) (ha : s'.logst.applied = s.logst.applied)
    (hs : s'.logst.snap = s.logst.snap) (hpci : pciR s' = pciR s)
    (hg : s'.gh.ns = s.gh.ns := by rfl) (hxw : s'.gh.xw = s.gh.xw := by rfl)
    (hld : s'.lead = s.lead := by rfl)
    (hst : s'.gh.sn = s.gh.sn := by rfl) :
    ownStepGhost (GF := GF) γ md c id s ⊢ ownStepGhost γ md c id s' := by
  have hn : NsLink γ s' = NsLink γ s := by unfold NsLink; rw [hg]
  have hx : xfW (GF := GF) γ s' = xfW γ s := by unfold xfW; rw [hxw]
  cases md with
  | static =>
    simp only [ownStepGhost, ghostRest, ghostRestM]; rw [hp, hn, hst, hx]
  | dyn dec c0 h0 g =>
    simp only [ownStepGhost, ghostRest, ghostRestM]
    have hr := rOf_congr g hp ha hs hpci
    rw [hp, hr, hn, hst, hx]

/-- What the mode keeps beyond `ownRaftGhost` survives a change of the code state that keeps
what it reads (2026-10-14, stage B7 part 2): the log, its boundary, the commit index, the term,
the role, `applied`, the pending snapshot and `pciR` -- e.g. a `Ready`'s drain of the outbox
and of the `ReadState`s, or `acceptReady`'s moves of `applying` and of what the storage holds. -/
theorem ghostRest_keep (γ : RaftNames) (md : GMode) (c : CfgM) (id : w64) {s s' : NState}
    (hb : (toPState s').base = (toPState s).base) (hl : (toPState s').log = (toPState s).log)
    (hc : (toPState s').commit = (toPState s).commit) (ht : (toPState s').term = (toPState s).term)
    (hr : (toPState s').role = (toPState s).role) (ha : s'.logst.applied = s.logst.applied)
    (hs : s'.logst.snap = s.logst.snap) (hpci : pciR s' = pciR s)
    (hg : s'.gh.ns = s.gh.ns := by rfl) (hxw : s'.gh.xw = s.gh.xw := by rfl)
    (hld : s'.lead = s.lead := by rfl)
    (hst : s'.gh.sn = s.gh.sn := by rfl) :
    ghostRest (GF := GF) γ md c id s ⊢ ghostRest γ md c id s' := by
  sorry -- PHASE1
  /- PHASE1-OLD
 by
  have hn : NsLink γ s' = NsLink γ s := by unfold NsLink; rw [hg]
  cases md with
  | static => simp only [ghostRest, ghostRestM]; rw [hn, hst]
  | dyn dec c0 h0 g =>
    simp only [ghostRest, ghostRestM]
    rw [hn, hst]
    iintro ⟨%Hnl, ⟨%H, #HM, #Hfr, #Hc⟩, #Hcl⟩
    isplitr
    · ipureintro; exact Hnl
    isplit
    rotate_left
    · iexact Hcl
    obtain ⟨HD, hc', HI⟩ := H
    iframe HM
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
  -/

/-- (D22 S-b′4, 2026-10-20) What the step needs of the mode: statically, once the `ConfState` names
the node (the restore exit: `restore` refuses it otherwise), a non-joint `ConfState` with the ghost
state's voters (the configuration a restore installs is then still `CfgStatic`), its ids within the
tracked bound (D19p), which the message's certificate gives (`snapOkIf_of_cert`); (2026-10-28, stage
U3c) dynamically the message's certificate (`raftSnapCert`), whose dynamic clause, once the
`ConfState` names the node, is A3: the `ConfState` denotes the fold of the snapshot's prefix
(`SnapConfOk`), for any recorded prefix ending at the snapshot's entry id (records agree, so there
is one; the message shows one exists, `isMessage_snap_prefix`). (Until U3c dynamically A3
unconditionally, `GMode.SnapOk`, a premise of `raft.Step`, `GMode.SnapDyn`, which no `RawNode` could
supply: the model's step asked a refused snapshot's admissibility too, `StepCDS`.) -/
def GMode.SnapOkIf (γ : RaftNames) (id : w64) : GMode → SnapshotM → CSLists → IProp GF
  | .static, sv, scfg => iprop(⌜scfg.Has id → GMap.listToSet scfg.voters = γ.reCfg ∧
      scfg.outgoing = [] ∧
      ∀ T, γ.reTracked = some T → (snapCfg sv scfg).voters ∪ (snapCfg sv scfg).learners ⊆ T⌝)
  | .dyn _ _ _ _, sv, scfg => raftSnapCert γ (snapTrip sv scfg)

instance GMode.SnapOkIf_persistent (γ : RaftNames) (id : w64) (md : GMode) (sv : SnapshotM)
    (scfg : CSLists) : Persistent (md.SnapOkIf (GF := GF) γ id sv scfg) := by
  cases md <;> unfold GMode.SnapOkIf <;> infer_instance

/-- (D22 S-b′4) The step's need of the mode from the message's certificate (statically: the
static mode is `γ`'s, `ownRaftGhost`'s flag; dynamically the certificate itself). -/
theorem snapOkIf_of_cert (γ : RaftNames) (md : GMode) (id : w64) (ps : PState)
    (sv : SnapshotM) (scfg : CSLists) (Hcl : scfg = sv.Metadata'.ConfState'.lists) :
    ⊢ ownRaftGhost (GF := GF) γ id ps md.isDyn -∗ raftSnapCert γ (snapTrip sv scfg) -∗
      md.SnapOkIf γ id sv scfg ∗ ownRaftGhost γ id ps md.isDyn := by
  cases md with
  | static =>
    iintro Hg #Hc
    ihave %Hm := ownRaftGhost_mode γ id ps (md := GMode.isDyn .static) $$ Hg
    have Hn : γ.reDyn = none := by
      simp only [GMode.isDyn] at Hm
      cases h : γ.reDyn with
      | none => rfl
      | some _ => simp [h] at Hm
    iframe Hg
    unfold raftSnapCert
    icases Hc with ⟨-, %Hs, -⟩
    simp only [GMode.SnapOkIf]
    ipureintro
    intro hhas
    obtain ⟨h1, h2, h3⟩ := Hs Hn id hhas
    refine ⟨h1, h2, fun T hT => ?_⟩
    have := h3 T hT
    simp only [SnapTrip.cfgM, snapTrip] at this
    subst Hcl
    exact this
  | dyn dec c0 h0 g =>
    iintro Hg #Hc
    iframe Hg
    simp only [GMode.SnapOkIf]
    iexact Hc

/-- A node's committed prefix, with records, is a prefix of the global committed log (persistent;
read off the ghost state's log ghost). -/
theorem ownRaftGhost_cmt (γ : RaftNames) (id : w64) (ps : PState) {md : Bool} :
    ownRaftGhost (GF := GF) γ id ps md ⊢
      ∃ fp, ⌜FullOk ps.base fp⌝ ∗ logRecs γ base0 fp ∗ isCommitted γ (cprefix fp ps) := by
  iintro Hg
  iunfold ownRaftGhost at Hg
  icases Hg with ⟨%γv, %voted, %kl, Hg⟩
  iNamed Hg
  iapply ownLogGhost_cmt γ id ps kl $$ Hlg

/-- A `MsgSnap` branch's step updates the mode's ghost state (2026-10-14, stage B8): statically
`ownRaftGhost_stepC`, the configuration afterwards still the ghost state's (`GMode.SnapOkIf`);
dynamically `ownRaftGhostR_stepR` at the snapshot's prefix `fp0`, the one the message shows
(`isMessage_snap_prefix`), whose fold the `ConfState` denotes once it names the node (the
certificate, `GMode.SnapOkIf`; 2026-10-28, stage U3c: a refused one is a frame step, `StepCDS`). -/
theorem ghost_stepCDSM (γ : RaftNames) (md : GMode) (c c' : CfgM) (id : w64) (m : MessageM)
    (Hms : m.Type' = MsgSnap) (sv : SnapshotM) (scfg : CSLists) (s : NState) (recv : List Msg) (s' : NState)
    (a : Msg) (Ha : a.ty = .snap ∧ entryID.mk a.logterm a.index = snapId sv)
    (B : Int) (HB : B < 2 ^ 64)
    (Hstep : StepCDS c c' (snapCfg sv scfg) (scfg.Has id) id B (snapId sv) s recv s')
    (Hc' : c' = c ∨ (c' = snapCfg sv scfg ∧ scfg.Has id)) :
    ⊢ ⧖ (B.toNat - γ.reBoot.length) -∗ isMessage (GF := GF) γ a -∗ ([∗list] x ∈ recv, isMessage γ x) -∗ rdCred γ (rdCount recv) -∗ msgsTks γ recv -∗ £ 1 -∗
      md.SnapOkIf γ id sv scfg -∗ ownRaftGhost γ id (toPState s) md.isDyn -∗ ghostRestM γ md c id s ={⊤}=∗
      ∃ md', ⌜md.StepOut c id m s s' md'⌝ ∗
        ownRaftGhost γ id (toPState s') md'.isDyn ∗ ghostRestM γ md' c' id s' := by
  cases md with
  | static =>
    simp only [ghostRestM, GMode.isDyn, GMode.SnapOkIf]
    iintro #Hrc - Hrecv Hcr Htk Hlc %Hso Hg %HC
    imod ownRaftGhost_stepC γ c HC.1 id HC.2 B HB (toPState s) recv (toPState s') Hstep.1 $$ Hrc
      Hrecv Hcr Htk Hlc Hg
      with Hg
    imodintro
    iexists GMode.static
    iframe Hg
    isplitr
    · ipureintro; exact ⟨rfl, B, recv, Hstep.1⟩
    ipureintro
    rcases Hc' with rfl | ⟨rfl, Hhas⟩
    · exact HC
    · have Hso := Hso Hhas
      refine ⟨⟨?_, ?_, HC.1.2.2⟩, fun T hT => ⟨Hso.2.2 T hT, (HC.2 T hT).2⟩⟩
      · simp only [snapCfg, csCfgM]; exact Hso.1
      · simp only [snapCfg, csCfgM]; rw [Hso.2.1]; try rfl
  | dyn dec c0 h0 g =>
    simp only [ghostRestM, GMode.isDyn, GMode.SnapOkIf]
    iintro #Hrc #Hm Hrecv Hcr Htk Hlc #Hso Hg ⟨%Hdc, #HM0, #Hfr, #Hc⟩
    obtain ⟨HD, hc, HI0⟩ := Hdc
    -- the snapshot's prefix, from the message, and A3 of it once the `ConfState` names the node
    -- (the certificate's dynamic clause); (2026-10-28, stage U3c) none needed otherwise
    icases isMessage_snap_prefix γ a Ha.1 $$ Hm with ⟨%fp0, %Hfp0, #Hr0, #Hc0⟩
    rw [Ha.2] at Hfp0
    unfold raftSnapCert
    icases Hso with ⟨-, -, #Hsd, -⟩
    -- (2026-10-28, the decision switch) the certificate's decisions join the node's
    ihave #HMs : iprop(∃ Ms : DecMap, decLb γ Ms ∗ ⌜∃ cs, scfg.Has id →
        cfgFold (effDec dec Ms) c0 fp0 = some cs ∧ cs.cfg = snapCfg sv scfg⌝) $$ []
    · by_cases hid : scfg.Has id
      · -- the certificate's fold, over the decisions it recorded (`raftSnapCert`)
        icases Hsd $$ %id %hid %_ %HD %fp0 Hr0 %Hfp0 with ⟨%Mc, #HMc, %Hf⟩
        simp only [DynCfg.ofFold] at Hf
        obtain ⟨cs, h1, h2⟩ := Option.map_eq_some_iff.1 Hf
        iexists Mc
        iframe HMc
        ipureintro; exact ⟨cs, fun _ => ⟨h1, h2⟩⟩
      · iexists ∅
        isplitr; · iapply decLb_empty
        ipureintro; exact ⟨g.cfg, fun h => absurd h hid⟩
    icases HMs with ⟨%Ms, #HMs, %Hsc⟩
    icases decLb_compat γ (g.decs) Ms $$ [HM0 HMs] with %Hcm
    · iframe HM0 HMs
    ihave #HM : decLb γ ((g.decs) ∪ Ms) $$ [HM0 HMs]
    · iapply decLb_union γ (g.decs) Ms; iframe HM0 HMs
    have HI : RInv (effDec dec ((g.decs) ∪ Ms)) c0 (rOf s g) :=
      HI0.mono_dec (effDec_mono dec (DecCompat.sub_left (g.decs) Ms))
    obtain ⟨cs, Hcs0'⟩ := Hsc
    have Hcs0 : scfg.Has id → cfgFold (effDec dec ((g.decs) ∪ Ms)) c0 fp0 = some cs ∧
        cs.cfg = snapCfg sv scfg := fun h =>
      ⟨cfgFold_mono (effDec_mono dec (DecCompat.sub_right Hcm)) (Hcs0' h).1, (Hcs0' h).2⟩
    -- (2026-10-28, stage U3) the prefix and the node's committed prefix: both committed
    icases (entails_wand (persistent_entails_left (ownRaftGhost_cmt γ id (toPState s)))) $$ Hg
      with ⟨Hg, %fp1, %Hf1, #Hfr1, #Hc1⟩
    icases FullOk_unique γ (toPState s).base fp1 g.fp Hf1 HI.full $$ Hfr1 Hfr with %He
    icases isCommitted_agree γ _ _ $$ Hc1 Hc0 with %Hag0
    have Hag : SnapAgree s g fp0 := by
      unfold cprefix at Hag0; rw [He] at Hag0
      unfold SnapAgree
      rw [show (rOf s g).full = g.fp ++ (toPState s).log from rfl, ← toNat_uZ]; exact Hag0
    obtain ⟨g', hg', hgc', hgf', hgp', HR⟩ := Hstep.2 (AdmS (effDec dec ((g.decs) ∪ Ms)) c0
      (fun fp => fp = fp0)) (effDec dec ((g.decs) ∪ Ms)) g fp0 cs
      hc Hfp0 Hag (fun hid => ⟨(Hcs0 hid).2, ⟨(Hcs0 hid).1, rfl⟩⟩)
    ihave Hown : ownRaftGhostR γ (effDec dec ((g.decs) ∪ Ms)) c0 id (rOf s g) $$ [Hg]
    · simp only [ownRaftGhostR, rOf.proj_p, rOf.proj_fp]
      iframe Hg Hfr
      isplitr
      · ipureintro; exact HI
      iintro %hcand; iapply Hc; exact hcand
    imod ownRaftGhostR_stepR γ dec ((g.decs) ∪ Ms) c0 h0 HD (fun fp => fp = fp0) id B HB (rOf s g)
      recv _ HR $$ Hrc HM [] Hrecv Hcr Htk Hlc Hown with Hown
    · imodintro
      iintro %fp %h
      subst h
      iexact Hr0
    imodintro
    iexists GMode.dyn dec c0 h0 { g' with decs := (g.decs) ∪ Ms }
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI', #Hfr', #Hc'⟩
    simp only [rOf.proj_p, rOf.proj_fp]
    iframe Hg
    isplitr
    · ipureintro
      refine ⟨{ g' with decs := (g.decs) ∪ Ms }, .inl ⟨Hms, hgc', hgf', ?_, ?_⟩, rfl, B, recv,
        StepR.mono (fun _ _ h => h.1) HR⟩
      · exact DecCompat.sub_left (g.decs) Ms
      · intro hp; show g'.fp = g.fp; rw [hgp' hp]
    iframe Hfr' HM
    rw [show rOf s' { g' with decs := (g.decs) ∪ Ms } = rOf s' g' from rfl]
    isplitr
    · ipureintro; exact ⟨HD, hg', HI'⟩
    iintro %hcand; iapply Hc'; exact hcand

/-- `ghost_stepCDSM` with (D21 M3) `NsLink` kept. -/
theorem ghost_stepCDS (γ : RaftNames) (md : GMode) (c c' : CfgM) (id : w64) (m : MessageM)
    (Hms : m.Type' = MsgSnap) (sv : SnapshotM) (scfg : CSLists) (s : NState) (recv : List Msg) (s' : NState)
    (a : Msg) (Ha : a.ty = .snap ∧ entryID.mk a.logterm a.index = snapId sv)
    (B : Int) (HB : B < 2 ^ 64)
    (Hstep : StepCDS c c' (snapCfg sv scfg) (scfg.Has id) id B (snapId sv) s recv s')
    (Hc' : c' = c ∨ (c' = snapCfg sv scfg ∧ scfg.Has id))
    (Hng : s'.gh = s.gh ∧ s'.logst.storage = s.logst.storage) :
    ⊢ ⧖ (B.toNat - γ.reBoot.length) -∗ isMessage (GF := GF) γ a -∗ ([∗list] x ∈ recv, isMessage γ x) -∗ rdCred γ (rdCount recv) -∗ msgsTks γ recv -∗ £ 1 -∗
      md.SnapOkIf γ id sv scfg -∗ ownRaftGhost γ id (toPState s) md.isDyn -∗ ghostRest γ md c id s ={⊤}=∗
      ∃ md', ⌜md.StepOut c id m s s' md'⌝ ∗
        ownRaftGhost γ id (toPState s') md'.isDyn ∗ ghostRest γ md' c' id s' := by
  iintro #Hrc #Hm #Hrecv Hcr Htk Hlc #Hso Hg Hrest
  iunfold ghostRest at Hrest
  icases Hrest with ⟨%Hnl, Hrest, #Hcl, #Hw, #Hx⟩
  ihave #Hw' := leadW_stepC γ c id B (toPState s) recv (toPState s') Hstep.1 $$ Hrecv Hw
  imod ghost_stepCDSM γ md c c' id m Hms sv scfg s recv s' a Ha B HB Hstep Hc' $$ Hrc Hm Hrecv
    Hcr Htk Hlc Hso Hg Hrest with ⟨%md', %Hout, Hg, Hrest⟩
  imodintro
  iexists md'
  iframe Hg
  isplitr
  · ipureintro; exact Hout
  iunfold ghostRest
  iframe Hrest Hw'
  isplitr
  · ipureintro
    unfold NsLink at Hnl ⊢; rw [Hng.1]; exact Hnl
  rw [show certLink (GF := GF) γ s'.gh.sn = certLink γ s.gh.sn by rw [Hng.1],
    show xfW (GF := GF) γ s' = xfW γ s by unfold xfW; rw [Hng.1]]
  iframe Hcl Hx

end ghost

end EtcdGrove
end Perennial
