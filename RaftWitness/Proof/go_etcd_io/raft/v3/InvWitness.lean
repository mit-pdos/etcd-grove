/-
The witness's heap representation (2026-10-20, witness support, `notes/raft-witness.md`): a
request (`WitnessMessage`, a value), and the witness's durable state (`*raftpb.WitnessHardState`)
field by field at a fraction: read-only (`whsRO`) as the storage hands it out and the witness
caches it, owned (`whsOwn`) while a handler builds the next one (`cloneState`'s copy, written
through its pointer fields and its hard state's), frozen before it is written back. The pure
model is `InvWitnessM.lean`.
-/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.InvWitnessM
public import RaftWitness.Proof.go_etcd_io.raft.v3.InvPb

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode GMap go_etcd_io.raft.v3

section own
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- A request to the witness (a `WitnessMessage` value) holding `μ`: its scalars, its two
replication sets and its context read-only, its vote tally a read-only map (or nil, empty). -/
def ownWMsg (mv : WitnessMessage) (μ : WMsg) : IProp GF :=
  iprop(∃ (s0 s1 : GoSlice),
    ⌜mv.Type' = μ.ty ∧ mv.From' = μ.frm ∧ mv.To' = μ.to ∧ mv.Term' = μ.term ∧
      mv.LastLogTerm' = μ.lt ∧ mv.LastLogSubterm' = μ.ls ∧ mv.LastLogIndex' = μ.li ∧
      mv.ReplicationSet'.arr = [s0, s1]⌝ ∗
    s0 ↦*□ μ.rs0 ∗ s1 ↦*□ μ.rs1 ∗
    (⌜mv.Votes' = map.nil ∧ μ.votes = ∅⌝ ∨ mv.Votes' ↦$□ μ.votes) ∗
    mv.Context' ↦*□ μ.ctx)

set_option synthInstance.maxSize 1024 in
instance ownWMsg_persistent (mv : WitnessMessage) (μ : WMsg) :
    Persistent (ownWMsg (GF := GF) mv μ) := by
  unfold ownWMsg; infer_instance

/-- The hard state of a witness state, as a `HardStateM`. -/
def WHS.hs (σ : WHS) : HardStateM := ⟨σ.term, σ.vote, σ.commit⟩

/-- A witness state's `*raftpb.HardState` at `ps ≠ nil`: its pointer fields at `dq`, its cells
read-only, its hidden fields' invariant. -/
def hsF (ps : Loc) (dq : DFrac) (σ : WHS) : IProp GF :=
  iprop(∃ (pt pv pc : Loc) (uf : List w8),
    "%Hsn" ∷ ⌜ps ≠ null⌝ ∗
    "HT" ∷ ps.[raftpb.HardState, go!"Term"] ↦{dq} pt ∗ "#cT" ∷ cellRO pt σ.term ∗
    "HV" ∷ ps.[raftpb.HardState, go!"Vote"] ↦{dq} pv ∗ "#cV" ∷ cellRO pv σ.vote ∗
    "HC" ∷ ps.[raftpb.HardState, go!"Commit"] ↦{dq} pc ∗ "#cC" ∷ cellRO pc σ.commit ∗
    "#Hpbs" ∷ pbMsg raftpb.HardState ps uf)

/-- A witness state's `State` field's target: nil (read as a zero hard state) or a hard state. -/
def hsOptW (ps : Loc) (dq : DFrac) (σ : WHS) : IProp GF :=
  iprop(⌜ps = null ∧ σ.term = W64 0 ∧ σ.vote = W64 0 ∧ σ.commit = W64 0⌝ ∨ hsF ps dq σ)

/-- A witness state at `p ≠ nil` holding `σ`, but for its `State`: its other pointer fields at
`dq`, their cells and its replication sets read-only, its hidden fields' invariant. -/
def whsRest (p : Loc) (dq : DFrac) (σ : WHS) : IProp GF :=
  iprop(∃ (pli plt pls pld : Loc) (srs sro : GoSlice) (uf : List w8),
    "%Hnn" ∷ ⌜p ≠ null⌝ ∗
    "HLi" ∷ p.[raftpb.WitnessHardState, go!"LastLogIndex"] ↦{dq} pli ∗ "#cLi" ∷ cellRO pli σ.li ∗
    "HLt" ∷ p.[raftpb.WitnessHardState, go!"LastLogTerm"] ↦{dq} plt ∗ "#cLt" ∷ cellRO plt σ.lt ∗
    "HLs" ∷ p.[raftpb.WitnessHardState, go!"LastLogSubterm"] ↦{dq} pls ∗ "#cLs" ∷ cellRO pls σ.ls ∗
    "HLd" ∷ p.[raftpb.WitnessHardState, go!"Lead"] ↦{dq} pld ∗ "#cLd" ∷ cellRO pld σ.lead ∗
    "HRs" ∷ p.[raftpb.WitnessHardState, go!"ReplicationSet"] ↦{dq} srs ∗ "#Hrs" ∷ srs ↦*□ σ.rs ∗
    "HRo" ∷ p.[raftpb.WitnessHardState, go!"ReplicationSetOutgoing"] ↦{dq} sro ∗
      "#Hro" ∷ sro ↦*□ σ.rsOut ∗
    "#Hpb" ∷ pbMsg raftpb.WitnessHardState p uf)

/-- A witness state at `p ≠ nil` holding `σ`, its fields at `dq`: its hard state at `dq` too (or
nil, read as zero). -/
def whsF (p : Loc) (dq : DFrac) (σ : WHS) : IProp GF :=
  iprop(∃ ps : Loc,
    "HS" ∷ p.[raftpb.WitnessHardState, go!"State"] ↦{dq} ps ∗ "Hhs" ∷ hsOptW ps dq σ ∗
    "Hr" ∷ whsRest p dq σ)

/-- A witness state read-only: as the storage hands it out, and the witness's cache. -/
abbrev whsRO (p : Loc) (σ : WHS) : IProp GF := whsF p DFrac.discard σ

set_option synthInstance.maxSize 1024 in
instance hsF_ro_persistent (ps : Loc) (σ : WHS) :
    Persistent (hsF (GF := GF) ps DFrac.discard σ) := by
  unfold hsF; infer_instance

set_option synthInstance.maxSize 1024 in
instance hsOptW_ro_persistent (ps : Loc) (σ : WHS) :
    Persistent (hsOptW (GF := GF) ps DFrac.discard σ) := by
  unfold hsOptW; infer_instance

set_option synthInstance.maxSize 1024 in
instance whsRest_ro_persistent (p : Loc) (σ : WHS) :
    Persistent (whsRest (GF := GF) p DFrac.discard σ) := by
  unfold whsRest; infer_instance

set_option synthInstance.maxSize 1024 in
instance whsRO_persistent (p : Loc) (σ : WHS) : Persistent (whsRO (GF := GF) p σ) := by
  unfold whsRO whsF; infer_instance

/-- The witness's cache (`w.state`): nil before its first read (every getter reads zero), or a
read-only state. -/
def whsOpt (p : Loc) (σ : WHS) : IProp GF :=
  iprop(⌜p = null ∧ σ = WHS.zero⌝ ∨ whsRO p σ)

set_option synthInstance.maxSize 1024 in
instance whsOpt_persistent (p : Loc) (σ : WHS) : Persistent (whsOpt (GF := GF) p σ) := by
  unfold whsOpt; infer_instance

/-- A witness state a handler is building (`cloneState`'s): its pointer fields owned, its hard
state there (not nil) and owned. -/
def whsOwn (p : Loc) (σ : WHS) : IProp GF :=
  iprop(∃ ps : Loc,
    "HS" ∷ p.[raftpb.WitnessHardState, go!"State"] ↦ ps ∗ "Hhs" ∷ hsF ps (DFrac.own 1) σ ∗
    "Hr" ∷ whsRest p (DFrac.own 1) σ)

theorem hsF_freeze (ps : Loc) (σ : WHS) :
    hsF (GF := GF) ps (DFrac.own 1) σ ⊢ |==> hsF ps DFrac.discard σ := by
  iintro H
  iNamed H
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HT with #HT
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HV with #HV
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HC with #HC
  imodintro
  unfold hsF
  iexists pt, pv, pc, uf
  isplitr
  · ipureintro; exact Hsn
  iframe HT cT HV cV HC cC Hpbs

theorem whsRest_freeze (p : Loc) (σ : WHS) :
    whsRest (GF := GF) p (DFrac.own 1) σ ⊢ |==> whsRest p DFrac.discard σ := by
  iintro H
  iNamed H
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HLi with #HLi
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HLt with #HLt
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HLs with #HLs
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HLd with #HLd
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HRs with #HRs
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HRo with #HRo
  imodintro
  unfold whsRest
  iexists pli, plt, pls, pld, srs, sro, uf
  isplitr
  · ipureintro; exact Hnn
  iframe HLi cLi HLt cLt HLs cLs HLd cLd HRs Hrs HRo Hro Hpb

/-- A state built, frozen (before `Update` writes it back). -/
theorem whsOwn_freeze (p : Loc) (σ : WHS) : whsOwn (GF := GF) p σ ⊢ |==> whsRO p σ := by
  iintro H
  iunfold whsOwn at H
  iNamed H
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HS with #HS
  imod hsF_freeze _ _ $$ Hhs with #Hhs
  imod whsRest_freeze _ _ $$ Hr with #Hr
  imodintro
  unfold whsRO whsF
  iexists ps
  iframe HS Hr
  unfold hsOptW
  iright; iexact Hhs

theorem whsRest_nn (p : Loc) (dq : DFrac) (σ : WHS) :
    whsRest (GF := GF) p dq σ ⊢ ⌜p ≠ null⌝ ∗ whsRest p dq σ := by
  iintro H
  iNamed H
  isplitr
  · ipureintro; exact Hnn
  unfold whsRest
  iexists pli, plt, pls, pld, srs, sro, uf
  isplitr
  · ipureintro; exact Hnn
  iframe HLi cLi HLt cLt HLs cLs HLd cLd HRs Hrs HRo Hro Hpb

/-- A freshly allocated `*pb.WitnessHardState` and `*pb.HardState` (hidden fields zero) whose
cells hold `σ`'s: an owned witness state (`cloneState`'s). -/
theorem whsOwn_of_struct (p : Loc) (v : raftpb.WitnessHardState) (hv : raftpb.HardState)
    (σ : WHS) (E : CoPset) :
    (⌜v.unknownFields' = slice.nil ∧ hv.unknownFields' = slice.nil⌝ ∗ p ↦ v ∗ v.State' ↦ hv ∗ cellRO hv.Term' σ.term ∗ cellRO hv.Vote' σ.vote ∗
      cellRO hv.Commit' σ.commit ∗ cellRO v.LastLogIndex' σ.li ∗ cellRO v.LastLogTerm' σ.lt ∗
      cellRO v.LastLogSubterm' σ.ls ∗ cellRO v.Lead' σ.lead ∗
      v.ReplicationSet' ↦*□ σ.rs ∗ v.ReplicationSetOutgoing' ↦*□ σ.rsOut : IProp GF) ⊢
      |={E}=> whsOwn p σ := by
  iintro ⟨%Huu, Hp, Hh, #cT, #cV, #cC, #cLi, #cLt, #cLs, #cLd, #Hrs, #Hro⟩
  ihave %Hnn := typedPointsto_not_null $$ Hp
  ihave %Hhn := typedPointsto_not_null $$ Hh
  icases typedPointsto_split _ _ _ $$ Hp with Hp
  simp only [TypedPointsto.typedPointstoDef]
  icases Hp with ⟨state, State, LastLogIndex, LastLogTerm, LastLogSubterm, Lead, ReplicationSet,
    ReplicationSetOutgoing, unknownFields, sizeCache, -⟩
  icases typedPointsto_split _ _ _ $$ Hh with Hh
  simp only [TypedPointsto.typedPointstoDef]
  icases Hh with ⟨hstate, Term, Vote, Commit, hunknownFields, hsizeCache, -⟩
  rw [Huu.1, Huu.2]
  ihave Hnil : (slice.nil ↦* ([] : List w8) : IProp GF) $$ []
  · iapply ownSlice_nil
  ihave Hnil' : (slice.nil ↦* ([] : List w8) : IProp GF) $$ []
  · iapply ownSlice_nil
  imod pbMsg_alloc raftpb.WitnessHardState p v.state' v.sizeCache' slice.nil [] E
    $$ [state sizeCache unknownFields Hnil] with #Hpb
  · iframe
  imod pbMsg_alloc raftpb.HardState v.State' hv.state' hv.sizeCache' slice.nil [] E
    $$ [hstate hsizeCache hunknownFields Hnil'] with #Hpbs
  · iframe
  imodintro
  unfold whsOwn
  iexists v.State'
  iframe State
  isplitl [Term Vote Commit]
  · unfold hsF
    iexists hv.Term', hv.Vote', hv.Commit', []
    isplitr
    · ipureintro; exact Hhn
    iframe Term cT Vote cV Commit cC Hpbs
  unfold whsRest
  iexists v.LastLogIndex', v.LastLogTerm', v.LastLogSubterm', v.Lead', v.ReplicationSet',
    v.ReplicationSetOutgoing', []
  isplitr
  · ipureintro; exact Hnn
  iframe LastLogIndex cLi LastLogTerm cLt LastLogSubterm cLs Lead cLd ReplicationSet Hrs
    ReplicationSetOutgoing Hro Hpb

/-- A handler's answer at `ml`: nil for none, else a fresh message holding it. -/
def respOpt (ml : Loc) : Option WResp → IProp GF
  | none => iprop(⌜ml = null⌝)
  | some r => msgOwn ml (DFrac.own 1) ⟨r.1, [], none, r.2, []⟩

end own

end EtcdGrove
end Perennial
