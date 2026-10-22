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
public import Proof.go_etcd_io.raft.v3.InvStorage

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
def GMode.Pre (md : GMode) (m : MessageM) (ents : List EntryM) (s : NState) : Prop :=
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
def GMove (m : MessageM) (s' : NState) (g g' : RGh) : Prop :=
  m.Type' = MsgSnap ∨ g' = g ∨
    (m.Type' = MsgStorageApplyResp ∧ g' = { g with cidx := max g.cidx (uint.nat s'.logst.applied) })

/-- The step in the mode's model: `StepC c` statically, `StepR` at the dynamic configurations
(`AdmFold`: since 2026-10-14, stage B8, a snapshot's restore included; until then no snapshot
prefix, `AdmS dec c0 (fun _ => False)`) dynamically, the ghost part possibly moved (the
configuration index by `StepR.advance`; all of it by `StepR.snapRestore`), and (2026-10-14, stage
B7 part 2) by nothing else (`GMove`). -/
def GMode.StepOut (md : GMode) (c : CfgM) (id : w64) (m : MessageM) (s s' : NState)
    (md' : GMode) : Prop :=
  match md with
  | .static => md' = .static ∧ ∃ B recv, StepC c id B (toPState s) recv (toPState s')
  | .dyn dec c0 h0 g => ∃ g', GMove m s' g g' ∧ md' = .dyn dec c0 h0 g' ∧
      ∃ B recv, StepR (AdmFold dec c0) dec id B (rOf s g) recv (rOf s' g')

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

/-- A step of any message but a `MsgStorageApplyResp` keeps the mode (the configuration index
does not move, `CidxMove`). -/
theorem GMode.StepOut.keep {md : GMode} {c : CfgM} {id : w64} {m : MessageM}
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

/-- The dynamic mode's premises of a step, for a message that is no snapshot, no storage-apply
acknowledgement and no proposal: only that the node is no pre-candidate. -/
theorem GMode.Pre.of_other {md : GMode} {m : MessageM} {ents : List EntryM}
    {s : NState} (_h1 : m.Type' ≠ MsgSnap) (h2 : md.isDyn = true → s.role ≠ .preCandidate)
    (h3 : m.Type' ≠ MsgStorageApplyResp) (h4 : m.Type' ≠ MsgProp) : md.Pre m ents s := by
  cases md with
  | static => trivial
  | dyn dec c0 h0 g =>
    exact ⟨h2 rfl, fun h => absurd h h3, fun h => absurd h h4⟩

/-- `GMode.Pre` gives `DynHyp` at any end state whose `applied` moved at most to the
acknowledged index, given the invariant (`applied ≤` the configuration index). -/
theorem GMode.Pre.dynHyp {md : GMode} {m : MessageM} {ents : List EntryM}
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

/-! ### The storage's certificates and raft's (D22 S-b′2, 2026-10-20)

A storage's registry of certified snapshots (`storCert`, `InvStorage.lean`) is γ-free, as the rest
of the storage model; `storCertOk γ st` ties it to raft's certificates (`raftSnapCert γ`, both
ways; D22 S-r, 2026-10-21: with the data certificate, `raftSnapCertD`), from an invariant the
application allocates knowing raft's names (for a `MemoryStorage`,
`memCertInv`, `MemstorageInstance.lean`). Raft reads a certificate out of the registry for a
snapshot it sends (the storage's, `HSnapshot`), and registers the one a received message carries
(S-d's lent storage). -/

section certLink
variable [FfiSyntax] {GF : BundledGFunctors} [AllG GF] [ReceiptGS GF] [InvGS GF] [StorageModel GF]

/-- The namespace of the registry's invariant. -/
def raftCertN : Namespace := nroot .@ "raft_snapcert"

/-- See above. -/
def storCertOk (γ : RaftNames) (st : Storage) : IProp GF :=
  iprop(□ (∀ (k : SnapTrip) (E : CoPset), ⌜↑raftCertN ⊆ E⌝ -∗ storCert st k ={E}=∗
      raftSnapCertD γ k) ∗
    □ (∀ (k : SnapTrip) (E : CoPset), ⌜↑raftCertN ⊆ E⌝ -∗ raftSnapCertD γ k ={E}=∗
      storCert st k))

instance storCertOk_persistent (γ : RaftNames) (st : Storage) :
    Persistent (storCertOk (GF := GF) γ st) := by
  unfold storCertOk; infer_instance

end certLink

section ghost
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]
variable {GF : BundledGFunctors} [AllG GF] [ReceiptGS GF] [InvGS GF] [StorageModel GF]

/-- What the mode keeps beyond `ownRaftGhost`: statically, the configuration's voters are the
ghost state's, and (D19p, 2026-10-18) its voters and learners -- the ids the tracker holds -- and
the node are within the ghost state's tracked bound (`TrackedOk`); dynamically, `ownRaftGhostR`'s invariant, full prefix records and campaign
record, with the ghost part over the configuration. -/
def ghostRestM (γ : RaftNames) : GMode → CfgM → w64 → NState → IProp GF
  | .static, c, id, _ => iprop(⌜CfgStatic γ c ∧ TrackedOk γ c id⌝)
  | .dyn dec c0 h0 g, c, id, s =>
    iprop(⌜γ.dyn = some (DynCfg.ofFold dec c0 h0) ∧ g.cfg.cfg = c ∧ RInv dec c0 (rOf s g)⌝ ∗
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
the node is past term `0` for good (`NGhost.bt`) exactly in that mode too, its bootstrap log's. -/
def NsLink (γ : RaftNames) (s : NState) : Prop :=
  s.gh.ns = γ.reNoSnap ∧ s.gh.xf = γ.reNoXfer ∧ s.gh.bt = γ.reNoXfer

theorem NsLink.boot {γ : RaftNames} {s : NState} (H : NsLink γ s) (h : s.gh.ns = true) :
    γ.reBoot ≠ [] :=
  RaftNames.noSnap_boot (by rw [← H.1]; exact h)

/-- (D22 S-b′3, 2026-10-20) Outside the no-snapshot mode, the node's storage's certificate
registry is tied to raft's certificates (`storCertOk`): a `Ready` certifies the `MsgSnap`s it hands
out from it, a `MsgSnap`'s `raft.Step` registers its snapshot in it. In the mode no snapshot is
sent or received, and no link is needed (the servers' storage, from the boot contract, has none). -/
def certLink (γ : RaftNames) (st : Storage) : IProp GF :=
  iprop(⌜γ.reNoSnap = true⌝ ∨ storCertOk γ st)

instance certLink_persistent (γ : RaftNames) (st : Storage) :
    Persistent (certLink (GF := GF) γ st) := by
  unfold certLink; infer_instance

theorem certLink_noSnap (γ : RaftNames) (st : Storage) (h : γ.reNoSnap = true) :
    ⊢ certLink (GF := GF) γ st := by
  unfold certLink; ileft; ipureintro; exact h

/-- What the mode keeps beyond `ownRaftGhost` (`ghostRestM`), (D21 M3) `NsLink`, and (D22 S-b′3)
the storage's certificate link (`certLink`). -/
def ghostRest (γ : RaftNames) (md : GMode) (c : CfgM) (id : w64) (s : NState) : IProp GF :=
  iprop(⌜NsLink γ s⌝ ∗ ghostRestM γ md c id s ∗ certLink γ s.logst.storage)

theorem ghostRest_nsLink (γ : RaftNames) (md : GMode) (c : CfgM) (id : w64) (s : NState) :
    ghostRest (GF := GF) γ md c id s ⊢ ⌜NsLink γ s⌝ ∗ ghostRest γ md c id s := by
  unfold ghostRest
  iintro ⟨%Hn, H⟩
  iframe H
  isplitr <;> ipureintro <;> exact Hn

/-- (D22 S-b′3) The certificate link, read out. -/
theorem ghostRest_certLink (γ : RaftNames) (md : GMode) (c : CfgM) (id : w64) (s : NState) :
    ghostRest (GF := GF) γ md c id s ⊢ certLink γ s.logst.storage ∗ ghostRest γ md c id s := by
  unfold ghostRest
  iintro ⟨%Hn, H, #Hl⟩
  iframe Hl H
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

/-- In the dynamic mode, `ownStepGhost` is `ownRaftGhostR`. -/
theorem ownStepGhost_dyn (γ : RaftNames) (dec : CCDec) (c0 : CCState) (h0 : CfgOk c0) (g : RGh)
    (c : CfgM) (id : w64) (s : NState) :
    ownStepGhost (GF := GF) γ (.dyn dec c0 h0 g) c id s ⊣⊢
      ⌜γ.dyn = some (DynCfg.ofFold dec c0 h0) ∧ g.cfg.cfg = c ∧ NsLink γ s⌝ ∗
        ownRaftGhostR γ dec c0 id (rOf s g) ∗ certLink γ s.logst.storage := by
  simp only [ownStepGhost, ghostRest, ghostRestM, GMode.isDyn, ownRaftGhostR, rOf.proj_p,
    rOf.proj_fp]
  constructor
  · iintro ⟨Hg, %Hnl, ⟨%Hdc, #Hfr, #Hc⟩, #Hcl⟩
    obtain ⟨HD, hc, HI⟩ := Hdc
    isplitr
    · ipureintro; exact ⟨HD, hc, Hnl⟩
    iframe Hg Hfr Hcl
    isplitr
    · ipureintro; exact HI
    iintro %hcand; iapply Hc; exact hcand
  · iintro ⟨%Hdc, ⟨Hg, %HI, #Hfr, #Hc⟩, #Hcl⟩
    obtain ⟨HD, hc, Hnl⟩ := Hdc
    iframe Hg Hfr Hcl
    isplitr
    · ipureintro; exact Hnl
    isplitr
    · ipureintro; exact ⟨HD, hc, HI⟩
    iintro %hcand; iapply Hc; exact hcand

/-- A branch's step updates the mode's ghost state: statically `ownRaftGhost_stepC`,
dynamically `ownRaftGhostR_stepR` (the premises `DynHyp` from `Hdh`, given the invariant). -/
theorem ghost_stepCDM (γ : RaftNames) (md : GMode) (c : CfgM) (id : w64) (m : MessageM)
    (B : Int) (HB : B < 2 ^ 64)
    (s : NState) (recv : List Msg) (s' : NState) (Hstep : StepCD c id B m s recv s')
    (Hdh : ∀ (dec : CCDec) (c0 : CCState) (h0 : CfgOk c0) (g : RGh), md = .dyn dec c0 h0 g →
      RInv dec c0 (rOf s g) → DynHyp m s s' g) :
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
    iintro #Hrc Hrecv Hcr Htk Hlc Hg ⟨%Hdc, #Hfr, #Hc⟩
    obtain ⟨HD, hc, HI⟩ := Hdc
    obtain ⟨cidx', Hcm, HR⟩ := Hstep.2 (AdmS dec c0 (fun _ => False)) dec g hc
      (Hdh dec c0 h0 g rfl HI)
    ihave Hown : ownRaftGhostR γ dec c0 id (rOf s g) $$ [Hg]
    · simp only [ownRaftGhostR, rOf.proj_p, rOf.proj_fp]
      iframe Hg Hfr
      isplitr
      · ipureintro; exact HI
      iintro %hcand; iapply Hc; exact hcand
    imod ownRaftGhostR_stepR γ dec c0 h0 HD (fun _ => False) id B HB (rOf s g) recv _ HR
      $$ Hrc [] Hrecv Hcr Htk Hlc Hown with Hown
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
      refine ⟨_, ?_, rfl, B, recv, StepR.mono (fun _ _ h => h.1) HR⟩
      rcases Hcm with h | ⟨h1, h2⟩
      · exact .inr (.inl (by rw [h]))
      · exact .inr (.inr ⟨h1, by rw [h2]⟩)
    iframe Hfr'
    isplitr
    · ipureintro; exact ⟨HD, hc, HI'⟩
    iintro %hcand; iapply Hc'; exact hcand


/-- `ghost_stepCDM` with (D21 M3) `NsLink` kept: the step keeps the mode (`NGhost.ns`). -/
theorem ghost_stepCD (γ : RaftNames) (md : GMode) (c : CfgM) (id : w64) (m : MessageM)
    (B : Int) (HB : B < 2 ^ 64)
    (s : NState) (recv : List Msg) (s' : NState) (Hstep : StepCD c id B m s recv s')
    (Hdh : ∀ (dec : CCDec) (c0 : CCState) (h0 : CfgOk c0) (g : RGh), md = .dyn dec c0 h0 g →
      RInv dec c0 (rOf s g) → DynHyp m s s' g)
    (Hng : s'.gh = s.gh ∧ s'.logst.storage = s.logst.storage) :
    ⊢ ⧖ (B.toNat - γ.reBoot.length) -∗ ([∗list] x ∈ recv, isMessage (GF := GF) γ x) -∗ rdCred γ (rdCount recv) -∗ msgsTks γ recv -∗ £ 1 -∗
      ownRaftGhost γ id (toPState s) md.isDyn -∗ ghostRest γ md c id s ={⊤}=∗
      ∃ md', ⌜md.StepOut c id m s s' md'⌝ ∗
        ownRaftGhost γ id (toPState s') md'.isDyn ∗ ghostRest γ md' c id s' := by
  iintro #Hrc Hrecv Hcr Htk Hlc Hg Hrest
  iunfold ghostRest at Hrest
  icases Hrest with ⟨%Hnl, Hrest, #Hcl⟩
  imod ghost_stepCDM γ md c id m B HB s recv s' Hstep Hdh $$ Hrc Hrecv Hcr Htk Hlc Hg Hrest
    with ⟨%md', %Hout, Hg, Hrest⟩
  imodintro
  iexists md'
  iframe Hg
  isplitr
  · ipureintro; exact Hout
  iunfold ghostRest
  iframe Hrest
  isplitr
  · ipureintro
    unfold NsLink at Hnl ⊢; rw [Hng.1]; exact Hnl
  rw [Hng.2]; iexact Hcl

/-- Two code states that the mode's ghost state reads alike (2026-10-14, stage B7 part 2): the
same protocol state, `applied`, pending snapshot and (at a leader) `pendingConfIndex`. -/
theorem rOf_congr {s s' : NState} (g : RGh) (hp : toPState s' = toPState s)
    (ha : s'.logst.applied = s.logst.applied) (hs : s'.logst.snap = s.logst.snap)
    (hpci : pciR s' = pciR s) : rOf s' g = rOf s g := by
  unfold rOf; rw [hp, ha, hs, hpci]; try rfl

theorem ownStepGhost_congr (γ : RaftNames) (md : GMode) (c : CfgM) (id : w64) {s s' : NState}
    (hp : toPState s' = toPState s) (ha : s'.logst.applied = s.logst.applied)
    (hs : s'.logst.snap = s.logst.snap) (hpci : pciR s' = pciR s)
    (hg : s'.gh.ns = s.gh.ns := by rfl) (hx : s'.gh.xf = s.gh.xf := by rfl)
    (hbt : s'.gh.bt = s.gh.bt := by rfl)
    (hst : s'.logst.storage = s.logst.storage := by rfl) :
    ownStepGhost (GF := GF) γ md c id s ⊢ ownStepGhost γ md c id s' := by
  have hn : NsLink γ s' = NsLink γ s := by unfold NsLink; rw [hg, hx, hbt]
  cases md with
  | static =>
    simp only [ownStepGhost, ghostRest, ghostRestM]; rw [hp, hn, hst]
  | dyn dec c0 h0 g =>
    simp only [ownStepGhost, ghostRest, ghostRestM]
    have hr := rOf_congr g hp ha hs hpci
    rw [hp, hr, hn, hst]

/-- What the mode keeps beyond `ownRaftGhost` survives a change of the code state that keeps
what it reads (2026-10-14, stage B7 part 2): the log, its boundary, the commit index, the term,
the role, `applied`, the pending snapshot and `pciR` -- e.g. a `Ready`'s drain of the outbox
and of the `ReadState`s, or `acceptReady`'s moves of `applying` and of what the storage holds. -/
theorem ghostRest_keep (γ : RaftNames) (md : GMode) (c : CfgM) (id : w64) {s s' : NState}
    (hb : (toPState s').base = (toPState s).base) (hl : (toPState s').log = (toPState s).log)
    (hc : (toPState s').commit = (toPState s).commit) (ht : (toPState s').term = (toPState s).term)
    (hr : (toPState s').role = (toPState s).role) (ha : s'.logst.applied = s.logst.applied)
    (hs : s'.logst.snap = s.logst.snap) (hpci : pciR s' = pciR s)
    (hg : s'.gh.ns = s.gh.ns := by rfl) (hx : s'.gh.xf = s.gh.xf := by rfl)
    (hbt : s'.gh.bt = s.gh.bt := by rfl)
    (hst : s'.logst.storage = s.logst.storage := by rfl) :
    ghostRest (GF := GF) γ md c id s ⊢ ghostRest γ md c id s' := by
  have hn : NsLink γ s' = NsLink γ s := by unfold NsLink; rw [hg, hx, hbt]
  cases md with
  | static => simp only [ghostRest, ghostRestM]; rw [hn, hst]
  | dyn dec c0 h0 g =>
    simp only [ghostRest, ghostRestM]
    rw [hn, hst]
    iintro ⟨%Hnl, ⟨%H, #Hfr, #Hc⟩, #Hcl⟩
    isplitr
    · ipureintro; exact Hnl
    isplit
    rotate_left
    · iexact Hcl
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
def GMode.SnapOk (γ : RaftNames) : GMode → SnapshotM → CSLists → IProp GF
  | .static, sv, scfg => iprop(⌜GMap.listToSet scfg.voters = γ.reCfg ∧ scfg.outgoing = [] ∧
      -- (D19p, 2026-10-18) its ids within the tracked bound
      ∀ T, γ.reTracked = some T → (snapCfg sv scfg).voters ∪ (snapCfg sv scfg).learners ⊆ T⌝)
  | .dyn dec c0 _ _, sv, scfg => iprop(□ ∀ (fp : List EntryM), logRecs γ base0 fp -∗
      ⌜FullOk (snapId sv) fp⌝ -∗
      ⌜SnapConfOk dec c0 fp scfg.outgoing scfg.voters scfg.learners scfg.learnersNext
        sv.Metadata'.ConfState'.AutoLeave'⌝)

instance GMode.SnapOk_persistent (γ : RaftNames) (md : GMode) (sv : SnapshotM)
    (scfg : CSLists) : Persistent (md.SnapOk (GF := GF) γ sv scfg) := by
  cases md <;> unfold GMode.SnapOk <;> infer_instance

/-- (D22 S-b′4, 2026-10-20) What the step needs of the mode: statically `GMode.SnapOk` once the
`ConfState` names the node (the restore exit: `restore` refuses it otherwise), which the message's
certificate gives (`snapOkIf_of_cert`); dynamically all of it (the model's step at a dynamic
configuration asks the snapshot's admissibility, `StepCDS`, also of a refused one). -/
def GMode.SnapOkIf (γ : RaftNames) (id : w64) : GMode → SnapshotM → CSLists → IProp GF
  | .static, sv, scfg => iprop(⌜scfg.Has id → GMap.listToSet scfg.voters = γ.reCfg ∧
      scfg.outgoing = [] ∧
      ∀ T, γ.reTracked = some T → (snapCfg sv scfg).voters ∪ (snapCfg sv scfg).learners ⊆ T⌝)
  | .dyn dec c0 h0 g, sv, scfg => GMode.SnapOk γ (.dyn dec c0 h0 g) sv scfg

instance GMode.SnapOkIf_persistent (γ : RaftNames) (id : w64) (md : GMode) (sv : SnapshotM)
    (scfg : CSLists) : Persistent (md.SnapOkIf (GF := GF) γ id sv scfg) := by
  cases md <;> unfold GMode.SnapOkIf <;> (try unfold GMode.SnapOk) <;> infer_instance

/-- (D22 S-b′4) What `raft.Step`'s `"#Hsnap"` still takes of the mode: nothing statically (the
message's certificate gives it), `GMode.SnapOk` dynamically. -/
def GMode.SnapDyn (γ : RaftNames) : GMode → SnapshotM → CSLists → IProp GF
  | .static, _, _ => iprop(True)
  | .dyn dec c0 h0 g, sv, scfg => GMode.SnapOk γ (.dyn dec c0 h0 g) sv scfg

instance GMode.SnapDyn_persistent (γ : RaftNames) (md : GMode) (sv : SnapshotM)
    (scfg : CSLists) : Persistent (md.SnapDyn (GF := GF) γ sv scfg) := by
  cases md <;> unfold GMode.SnapDyn <;> (try unfold GMode.SnapOk) <;> infer_instance

/-- (D22 S-b′4) The step's need of the mode from the message's certificate (statically: the
static mode is `γ`'s, `ownRaftGhost`'s flag) and `SnapDyn` (dynamically). -/
theorem snapOkIf_of_cert (γ : RaftNames) (md : GMode) (id : w64) (ps : PState)
    (sv : SnapshotM) (scfg : CSLists) (Hcl : scfg = sv.Metadata'.ConfState'.lists) :
    ⊢ ownRaftGhost (GF := GF) γ id ps md.isDyn -∗ raftSnapCert γ (snapTrip sv scfg) -∗
      md.SnapDyn γ sv scfg -∗ md.SnapOkIf γ id sv scfg ∗ ownRaftGhost γ id ps md.isDyn := by
  cases md with
  | static =>
    iintro Hg #Hc -
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
    iintro Hg - #Hd
    iframe Hg
    simp only [GMode.SnapOkIf, GMode.SnapDyn]
    iexact Hd

/-- A `MsgSnap` branch's step updates the mode's ghost state (2026-10-14, stage B8): statically
`ownRaftGhost_stepC`, the configuration afterwards still the ghost state's (`GMode.SnapOk`);
dynamically `ownRaftGhostR_stepR` at the snapshot's prefix `fp0`, the one the message shows
(`isMessage_snap_prefix`), whose fold the `ConfState` denotes (`GMode.SnapOk`). -/
theorem ghost_stepCDSM (γ : RaftNames) (md : GMode) (c c' : CfgM) (id : w64) (m : MessageM)
    (Hms : m.Type' = MsgSnap) (sv : SnapshotM) (scfg : CSLists) (s : NState) (recv : List Msg) (s' : NState)
    (a : Msg) (Ha : a.ty = .snap ∧ entryID.mk a.logterm a.index = snapId sv)
    (B : Int) (HB : B < 2 ^ 64)
    (Hstep : StepCDS c c' (snapCfg sv scfg) id B (snapId sv) s recv s')
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
    simp only [ghostRestM, GMode.isDyn, GMode.SnapOkIf, GMode.SnapOk]
    iintro #Hrc #Hm Hrecv Hcr Htk Hlc #Hso Hg ⟨%Hdc, #Hfr, #Hc⟩
    obtain ⟨HD, hc, HI⟩ := Hdc
    -- the snapshot's prefix, from the message, and A3 of it
    icases isMessage_snap_prefix γ a Ha.1 $$ Hm with ⟨%fp0, %Hfp0, #Hr0⟩
    rw [Ha.2] at Hfp0
    ihave %Hsc := Hso $$ %fp0 Hr0 %Hfp0
    obtain ⟨-, cs, Hfold, Hcs⟩ := Hsc
    obtain ⟨g', hg', HR⟩ := Hstep.2 (AdmS dec c0 (fun fp => fp = fp0)) dec g fp0 cs hc Hfp0
      Hcs.symm ⟨Hfold, rfl⟩
    ihave Hown : ownRaftGhostR γ dec c0 id (rOf s g) $$ [Hg]
    · simp only [ownRaftGhostR, rOf.proj_p, rOf.proj_fp]
      iframe Hg Hfr
      isplitr
      · ipureintro; exact HI
      iintro %hcand; iapply Hc; exact hcand
    imod ownRaftGhostR_stepR γ dec c0 h0 HD (fun fp => fp = fp0) id B HB (rOf s g) recv _ HR
      $$ Hrc [] Hrecv Hcr Htk Hlc Hown with Hown
    · imodintro
      iintro %fp %h
      subst h
      iexact Hr0
    imodintro
    iexists GMode.dyn dec c0 h0 g'
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI', #Hfr', #Hc'⟩
    simp only [rOf.proj_p, rOf.proj_fp]
    iframe Hg
    isplitr
    · ipureintro
      exact ⟨g', .inl Hms, rfl, B, recv, StepR.mono (fun _ _ h => h.1) HR⟩
    iframe Hfr'
    isplitr
    · ipureintro; exact ⟨HD, hg', HI'⟩
    iintro %hcand; iapply Hc'; exact hcand

/-- `ghost_stepCDSM` with (D21 M3) `NsLink` kept. -/
theorem ghost_stepCDS (γ : RaftNames) (md : GMode) (c c' : CfgM) (id : w64) (m : MessageM)
    (Hms : m.Type' = MsgSnap) (sv : SnapshotM) (scfg : CSLists) (s : NState) (recv : List Msg) (s' : NState)
    (a : Msg) (Ha : a.ty = .snap ∧ entryID.mk a.logterm a.index = snapId sv)
    (B : Int) (HB : B < 2 ^ 64)
    (Hstep : StepCDS c c' (snapCfg sv scfg) id B (snapId sv) s recv s')
    (Hc' : c' = c ∨ (c' = snapCfg sv scfg ∧ scfg.Has id))
    (Hng : s'.gh = s.gh ∧ s'.logst.storage = s.logst.storage) :
    ⊢ ⧖ (B.toNat - γ.reBoot.length) -∗ isMessage (GF := GF) γ a -∗ ([∗list] x ∈ recv, isMessage γ x) -∗ rdCred γ (rdCount recv) -∗ msgsTks γ recv -∗ £ 1 -∗
      md.SnapOkIf γ id sv scfg -∗ ownRaftGhost γ id (toPState s) md.isDyn -∗ ghostRest γ md c id s ={⊤}=∗
      ∃ md', ⌜md.StepOut c id m s s' md'⌝ ∗
        ownRaftGhost γ id (toPState s') md'.isDyn ∗ ghostRest γ md' c' id s' := by
  iintro #Hrc #Hm Hrecv Hcr Htk Hlc #Hso Hg Hrest
  iunfold ghostRest at Hrest
  icases Hrest with ⟨%Hnl, Hrest, #Hcl⟩
  imod ghost_stepCDSM γ md c c' id m Hms sv scfg s recv s' a Ha B HB Hstep Hc' $$ Hrc Hm Hrecv
    Hcr Htk Hlc Hso Hg Hrest with ⟨%md', %Hout, Hg, Hrest⟩
  imodintro
  iexists md'
  iframe Hg
  isplitr
  · ipureintro; exact Hout
  iunfold ghostRest
  iframe Hrest
  isplitr
  · ipureintro
    unfold NsLink at Hnl ⊢; rw [Hng.1]; exact Hnl
  rw [Hng.2]; iexact Hcl

end ghost

end EtcdGrove
end Perennial
