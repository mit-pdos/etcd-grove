/-
Lean-first (no Rocq counterpart).

# A snapshot with every pointer field set (D22 S-d4, 2026-10-21)

`pb.EnsureSnapshot` (`raftpb/util.go`) writes each `nil` pointer field of a snapshot: its
`Metadata`, the metadata's `ConfState`, `Index` and `Term`, and the conf state's `AutoLeave`
(`EnsureSnapshotMetadata`, `EnsureConfState`). Of a snapshot whose every pointer field is set it
writes nothing, so it may be called on one owned at any fraction (`ownSnapS`): what
`MemoryStorage.ApplySnapshot` needs to apply a snapshot it shares, read-only, with the node -- a
`Ready`'s snapshot, whose other half the node's queued acknowledgement holds (D22 S-d3a).
`ownSnapS_M` forgets that the fields are set.
-/
module

public import Proof.go_etcd_io.raft.v3.LemmasSendRD

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- A conf state with its `AutoLeave` set, at `dq` or read-only for good (raft freezes a restored
snapshot's conf state, `raft.restore`, D22 S-d4 item 4). -/
def csSet (p : Loc) (dq : DFrac) (c : ConfStateM) : IProp GF :=
  iprop(csPts p dq c true ∨ csPts p DFrac.discard c true)

/-- A `*pb.SnapshotMetadata` at `p` holding `md`, at `dq`, with every pointer field set: its conf
state (with its `AutoLeave`; `csSet`), its index and its term (see the file header). -/
def smPtsS (p : Loc) (dq : DFrac) (md : SnapshotMetadataM) : IProp GF :=
  iprop(∃ (pc pi pt : Loc) (uf : List w8),
    "%Hnn" ∷ ⌜p ≠ null ∧ pc ≠ null ∧ pi ≠ null ∧ pt ≠ null⌝ ∗
    "HC" ∷ p.[raftpb.SnapshotMetadata, go!"ConfState"] ↦{dq} pc ∗
      "Hc" ∷ csSet pc dq md.ConfState' ∗
    "HI" ∷ p.[raftpb.SnapshotMetadata, go!"Index"] ↦{dq} pi ∗ "#cI" ∷ cellRO pi md.Index' ∗
    "HT" ∷ p.[raftpb.SnapshotMetadata, go!"Term"] ↦{dq} pt ∗ "#cT" ∷ cellRO pt md.Term' ∗
    "#Hpb" ∷ pbMsg raftpb.SnapshotMetadata p uf)

/-- A `*pb.Snapshot` at `p` holding `s`, at `dq`, with every pointer field set (its `Metadata`,
`smPtsS`; see the file header). -/
def ownSnapS (p : Loc) (dq : DFrac) (s : SnapshotM) : IProp GF :=
  iprop(∃ (ds : GoSlice) (pm : Loc) (uf : List w8),
    "%Hnn" ∷ ⌜p ≠ null⌝ ∗
    "HD" ∷ p.[raftpb.Snapshot, go!"Data"] ↦{dq} ds ∗ "Hd" ∷ ds ↦*{dq} s.Data' ∗
    "HM" ∷ p.[raftpb.Snapshot, go!"Metadata"] ↦{dq} pm ∗ "Hm" ∷ smPtsS pm dq s.Metadata' ∗
    "#Hpb" ∷ pbMsg raftpb.Snapshot p uf)

theorem smPtsS_not_null (p : Loc) (dq : DFrac) (md : SnapshotMetadataM) :
    smPtsS (GF := GF) p dq md ⊢ smPtsS p dq md ∗ ⌜p ≠ null⌝ := by
  iintro H
  iNamed H
  isplitl
  · iunfold smPtsS
    iexists pc, pi, pt, uf
    isplitr
    · ipureintro; exact Hnn
    iframe HC Hc HI HT cI cT Hpb
  ipureintro; exact Hnn.1

/-- A set conf state is one (`csOptA`). -/
theorem csSet_A (p : Loc) (dq : DFrac) (c : ConfStateM) :
    csSet (GF := GF) p dq c ⊢ csOptA p dq c := by
  iintro H
  iunfold csSet at H
  iunfold csOptA
  icases H with (H | #H)
  · ihave H := csPts_weaken _ _ _ _ $$ H
    iright; ileft; iexact H
  · iright; iright; iexact H

/-- A metadata with every pointer field set is one (`smPts`). -/
theorem smPtsS_smPts (p : Loc) (dq : DFrac) (md : SnapshotMetadataM) :
    smPtsS (GF := GF) p dq md ⊢ smPts p dq md := by
  iintro H
  iNamed H
  ihave Hc := csSet_A _ _ _ $$ Hc
  iunfold smPts
  iexists pc, pi, pt, uf
  isplitr
  · ipureintro; exact Hnn.1
  iframe HC HI HT cI cT Hpb Hc

/-- ... and one with its conf state set (`smPtsW`). -/
theorem smPtsS_W (p : Loc) (dq : DFrac) (md : SnapshotMetadataM) :
    smPtsS (GF := GF) p dq md ⊢ smPtsW p dq md := by
  iintro H
  iNamed H
  ihave Hc := csSet_A _ _ _ $$ Hc
  iunfold smPtsW
  iexists pc, pi, pt, uf
  isplitr
  · ipureintro; exact ⟨Hnn.1, Hnn.2.1⟩
  iframe HC HI HT cI cT Hpb Hc

/-- A snapshot with every pointer field set is whole (`ownSnapW`). -/
theorem ownSnapS_W (p : Loc) (dq : DFrac) (s : SnapshotM) :
    ownSnapS (GF := GF) p dq s ⊢ ownSnapW p dq s := by
  iintro H
  iNamed H
  ihave Hm := smPtsS_W _ _ _ $$ Hm
  iunfold ownSnapW
  iexists ds, pm, uf
  isplitr
  · ipureintro; exact Hnn
  iframe HD Hd HM Hm Hpb

theorem csSet_split (p : Loc) (dq1 dq2 : DFrac) (c : ConfStateM) :
    csSet (GF := GF) p (dq1 • dq2) c ⊢ csSet p dq1 c ∗ csSet p dq2 c := by
  iintro H
  iunfold csSet at H
  icases H with (H | #H)
  · icases csPts_split _ _ _ _ _ $$ H with ⟨H1, H2⟩
    isplitl [H1]
    · iunfold csSet; ileft; iexact H1
    · iunfold csSet; ileft; iexact H2
  · isplitl []
    · iunfold csSet; iright; iexact H
    · iunfold csSet; iright; iexact H

theorem csSet_persist (p : Loc) (dq : DFrac) (c : ConfStateM) :
    csSet (GF := GF) p dq c ⊢ |==> csSet p DFrac.discard c := by
  iintro H
  iunfold csSet at H
  icases H with (H | #H)
  · imod csPts_persist _ _ _ _ $$ H with #H
    imodintro; iunfold csSet; ileft; iexact H
  · imodintro; iunfold csSet; ileft; iexact H

instance csSet_persistent (p : Loc) (c : ConfStateM) :
    Persistent (csSet (GF := GF) p DFrac.discard c) := by
  unfold csSet; infer_instance

theorem smPtsS_split (p : Loc) (dq1 dq2 : DFrac) (md : SnapshotMetadataM) :
    smPtsS (GF := GF) p (dq1 • dq2) md ⊢ smPtsS p dq1 md ∗ smPtsS p dq2 md := by
  iintro H
  iNamed H
  icases (typedPointsto_dfractional (GF := GF) _ _).dfractional dq1 dq2 |>.1 $$ HC with ⟨HC1, HC2⟩
  icases csSet_split _ _ _ _ $$ Hc with ⟨Hc1, Hc2⟩
  icases (typedPointsto_dfractional (GF := GF) _ _).dfractional dq1 dq2 |>.1 $$ HI with ⟨HI1, HI2⟩
  icases (typedPointsto_dfractional (GF := GF) _ _).dfractional dq1 dq2 |>.1 $$ HT with ⟨HT1, HT2⟩
  isplitl [HC1 Hc1 HI1 HT1]
  · iunfold smPtsS
    iexists pc, pi, pt, uf
    isplitr
    · ipureintro; exact Hnn
    iframe
    iframe cI cT Hpb
  · iunfold smPtsS
    iexists pc, pi, pt, uf
    isplitr
    · ipureintro; exact Hnn
    iframe
    iframe cI cT Hpb

/-- A set snapshot splits (as `ownSnapM_split`). -/
theorem ownSnapS_split (p : Loc) (dq1 dq2 : DFrac) (s : SnapshotM) :
    ownSnapS (GF := GF) p (dq1 • dq2) s ⊢ ownSnapS p dq1 s ∗ ownSnapS p dq2 s := by
  iintro H
  iNamed H
  icases (typedPointsto_dfractional (GF := GF) _ _).dfractional dq1 dq2 |>.1 $$ HD with ⟨HD1, HD2⟩
  icases (ownSlice_dfractional (GF := GF) _ _).dfractional dq1 dq2 |>.1 $$ Hd with ⟨Hd1, Hd2⟩
  icases (typedPointsto_dfractional (GF := GF) _ _).dfractional dq1 dq2 |>.1 $$ HM with ⟨HM1, HM2⟩
  icases smPtsS_split _ _ _ _ $$ Hm with ⟨Hm1, Hm2⟩
  isplitl [HD1 Hd1 HM1 Hm1]
  · iunfold ownSnapS
    iexists ds, pm, uf
    isplitr
    · ipureintro; exact Hnn
    iframe
    iframe Hpb
  · iunfold ownSnapS
    iexists ds, pm, uf
    isplitr
    · ipureintro; exact Hnn
    iframe
    iframe Hpb

theorem smPtsS_persist (p : Loc) (dq : DFrac) (md : SnapshotMetadataM) :
    smPtsS (GF := GF) p dq md ⊢ |==> smPtsS p DFrac.discard md := by
  iintro H
  iNamed H
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HC with #HC
  imod csSet_persist _ _ _ $$ Hc with #Hc
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HI with #HI
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HT with #HT
  imodintro
  iunfold smPtsS
  iexists pc, pi, pt, uf
  isplitr
  · ipureintro; exact Hnn
  iframe HC Hc HI HT cI cT Hpb

instance smPtsS_persistent (p : Loc) (md : SnapshotMetadataM) :
    Persistent (smPtsS (GF := GF) p DFrac.discard md) := by
  unfold smPtsS; infer_instance

/-- A set snapshot frozen read-only (as `ownSnapM_persist`): what raft's log keeps of a restored
snapshot (`pendKsn`, D22 S-d4 item 4). -/
theorem ownSnapS_persist (p : Loc) (dq : DFrac) (s : SnapshotM) :
    ownSnapS (GF := GF) p dq s ⊢ |==> ownSnapS p DFrac.discard s := by
  iintro H
  iNamed H
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HD with #HD
  imod (ownSlice_dfractional (GF := GF) _ _).dfractional_persist _ $$ Hd with #Hd
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HM with #HM
  imod smPtsS_persist _ _ _ $$ Hm with #Hm
  imodintro
  iunfold ownSnapS
  iexists ds, pm, uf
  isplitr
  · ipureintro; exact Hnn
  iframe HD Hd HM Hm Hpb

instance ownSnapS_persistent (p : Loc) (s : SnapshotM) :
    Persistent (ownSnapS (GF := GF) p DFrac.discard s) := by
  unfold ownSnapS; infer_instance

/-- A snapshot with every pointer field set is one (`ownSnapM`). -/
theorem ownSnapS_M (p : Loc) (dq : DFrac) (s : SnapshotM) :
    ownSnapS (GF := GF) p dq s ⊢ ownSnapM p dq s := by
  iintro H
  iNamed H
  ihave Hm := smPtsS_smPts _ _ _ $$ Hm
  iunfold ownSnapM
  iexists ds, pm, uf
  isplitr
  · ipureintro; exact Hnn
  iframe HD Hd HM Hpb
  iunfold smOpt
  iright; iexact Hm

/-- What `MemoryStorage.ApplySnapshot` takes of its snapshot: owned, or at any fraction with every
pointer field set (`ownSnapS`; see the file header). -/
def snapArg (p : Loc) (dq : DFrac) (s : SnapshotM) : IProp GF :=
  iprop((⌜dq = DFrac.own 1⌝ ∗ ownSnapM p dq s) ∨ ownSnapS p dq s)

theorem snapArg_not_null (p : Loc) (dq : DFrac) (s : SnapshotM) :
    snapArg (GF := GF) p dq s ⊢ snapArg p dq s ∗ ⌜p ≠ null⌝ := by
  iintro H
  iunfold snapArg at H
  icases H with (⟨%Hdq, H⟩ | H)
  · iunfold ownSnapM at H
    icases H with ⟨%ds, %pm, %uf, %Hnn, H⟩
    isplitl
    · iunfold snapArg; ileft
      isplitr
      · ipureintro; exact Hdq
      iunfold ownSnapM
      iexists ds, pm, uf
      isplitr
      · ipureintro; exact Hnn
      iexact H
    ipureintro; exact Hnn
  · iunfold ownSnapS at H
    icases H with ⟨%ds, %pm, %uf, %Hnn, H⟩
    isplitl
    · iunfold snapArg; iright
      iunfold ownSnapS
      iexists ds, pm, uf
      isplitr
      · ipureintro; exact Hnn
      iexact H
    ipureintro; exact Hnn

/-- A freshly allocated `*pb.Snapshot` (hidden fields zero) whose data and metadata (every pointer
field set) hold `s`'s: `ownSnapW_of_struct` for a set metadata. -/
theorem ownSnapS_of_struct (p : Loc) (v : raftpb.Snapshot) (s : SnapshotM) (E : CoPset)
    (Hu : v.unknownFields' = slice.nil) :
    (p ↦ v ∗ v.Data' ↦* s.Data' ∗ smPtsS v.Metadata' (DFrac.own 1) s.Metadata' : IProp GF) ⊢
      |={E}=> ownSnapS p (DFrac.own 1) s := by
  iintro ⟨Hp, Hd, Hm⟩
  ihave %Hnn := typedPointsto_not_null $$ Hp
  icases typedPointsto_split _ _ _ $$ Hp with Hp
  simp only [TypedPointsto.typedPointstoDef]
  icases Hp with ⟨state, Data, Metadata, unknownFields, sizeCache, -⟩
  rw [Hu]
  ihave Hnil : (slice.nil ↦* ([] : List w8) : IProp GF) $$ []
  · iapply ownSlice_nil
  imod pbMsg_alloc raftpb.Snapshot p v.state' v.sizeCache' slice.nil [] E $$ [state sizeCache unknownFields Hnil] with #Hpb
  · iframe
  imodintro
  iunfold ownSnapS
  iexists v.Data', v.Metadata', []
  isplitr
  · ipureintro; exact Hnn
  iframe
  iframe Hpb

/-- (D22 S-d4 item 4) A set snapshot from its parts (`raft.restore` splits the message's snapshot
there): a fraction of it set, the conf state read-only, and the rest of the other fraction
(`snapRest`). -/
theorem ownSnapS_rest_of_parts (sp pm pc pi pt : Loc) (ds : GoSlice) (uf ufm : List w8)
    (dq1 dq2 : DFrac) (sv : SnapshotM)
    (Hsp : sp ≠ null) (Hpm : pm ≠ null) (Hpc : pc ≠ null) (Hpi : pi ≠ null) (Hpt : pt ≠ null) :
    (sp.[raftpb.Snapshot, go!"Data"] ↦{dq1 • dq2} ds ∗ ds ↦*{dq1 • dq2} sv.Data' ∗
      sp.[raftpb.Snapshot, go!"Metadata"] ↦{dq1 • dq2} pm ∗
      pm.[raftpb.SnapshotMetadata, go!"ConfState"] ↦{dq1 • dq2} pc ∗
      pm.[raftpb.SnapshotMetadata, go!"Index"] ↦{dq1 • dq2} pi ∗ cellRO pi sv.Metadata'.Index' ∗
      pm.[raftpb.SnapshotMetadata, go!"Term"] ↦{dq1 • dq2} pt ∗ cellRO pt sv.Metadata'.Term' ∗
      pbMsg raftpb.Snapshot sp uf ∗ pbMsg raftpb.SnapshotMetadata pm ufm ∗
      csPts pc DFrac.discard sv.Metadata'.ConfState' true : IProp GF) ⊢
      ownSnapS sp dq1 sv ∗ snapRest sp pm pc dq2 sv := by
  iintro ⟨HD, Hd, HM, HC, HI, #cI, HT, #cT, #Hpb, #Hpbm, #Hcf⟩
  icases ((typedPointsto_dfractional (GF := GF) _ ds).dfractional dq1 dq2).1 $$ HD with ⟨HD1, HD2⟩
  icases ((ownSlice_dfractional (GF := GF) ds _).dfractional dq1 dq2).1 $$ Hd with ⟨Hd1, Hd2⟩
  icases ((typedPointsto_dfractional (GF := GF) _ pm).dfractional dq1 dq2).1 $$ HM with ⟨HM1, HM2⟩
  icases ((typedPointsto_dfractional (GF := GF) _ pc).dfractional dq1 dq2).1 $$ HC with ⟨HC1, HC2⟩
  icases ((typedPointsto_dfractional (GF := GF) _ pi).dfractional dq1 dq2).1 $$ HI with ⟨HI1, HI2⟩
  icases ((typedPointsto_dfractional (GF := GF) _ pt).dfractional dq1 dq2).1 $$ HT with ⟨HT1, HT2⟩
  isplitl [HD1 Hd1 HM1 HC1 HI1 HT1]
  · iunfold ownSnapS
    iexists ds, pm, uf
    isplitr
    · ipureintro; exact Hsp
    iframe HD1 Hd1 HM1 Hpb
    iunfold smPtsS
    iexists pc, pi, pt, ufm
    isplitr
    · ipureintro; exact ⟨Hpm, Hpc, Hpi, Hpt⟩
    iframe HC1 HI1 HT1 cI cT Hpbm
    iunfold csSet; iright; iexact Hcf
  · iunfold snapRest
    iexists ds, pi, pt, uf, ufm
    iframe
    iframe cI cT Hpb Hpbm
    ipureintro; exact ⟨Hsp, Hpm⟩

/-! ### The getters on a set snapshot (D22 S-d4 item 4) -/

theorem wp_Snapshot_GetMetadata_S (sp : Loc) (dq : DFrac) (sv : SnapshotM) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ ownSnapS sp dq sv }}
      (App (Val (sp @!! go.GoType.PointerType raftpb.Snapshot.ty @!! go!"GetMetadata")) (Val #()))
    {{ (pm : Loc), RET #pm; smPtsS pm dq sv.Metadata' ∗
        (smPtsS pm dq sv.Metadata' -∗ ownSnapS sp dq sv) }} := by
  iintro %Φ ⟨#Hinit, Hs⟩ HΦ
  iNamed Hs
  wp_apply wp_Snapshot_GetMetadata_field sp pm dq Hnn $$ [$HM] as HM
  iapply HΦ
  iframe Hm
  iintro Hm
  iunfold ownSnapS
  iexists ds, pm, uf
  isplitr
  · ipureintro; exact Hnn
  iframe HD Hd HM Hm Hpb

theorem wp_SnapshotMetadata_GetIndex_S (pm : Loc) (dq : DFrac) (md : SnapshotMetadataM) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ smPtsS pm dq md }}
      (App (Val (pm @!! go.GoType.PointerType raftpb.SnapshotMetadata.ty @!! go!"GetIndex"))
        (Val #()))
    {{ RET #md.Index'; smPtsS pm dq md }} := by
  iintro %Φ ⟨#Hinit, Hm⟩ HΦ
  iNamed Hm
  wp_apply wp_SnapshotMetadata_GetIndex_field pm pi md.Index' dq Hnn.1 $$ [$HI $cI] as HI
  iapply HΦ
  iunfold smPtsS
  iexists pc, pi, pt, uf
  isplitr
  · ipureintro; exact Hnn
  iframe HC Hc HI HT cI cT Hpb

theorem wp_SnapshotMetadata_GetTerm_S (pm : Loc) (dq : DFrac) (md : SnapshotMetadataM) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ smPtsS pm dq md }}
      (App (Val (pm @!! go.GoType.PointerType raftpb.SnapshotMetadata.ty @!! go!"GetTerm"))
        (Val #()))
    {{ RET #md.Term'; smPtsS pm dq md }} := by
  iintro %Φ ⟨#Hinit, Hm⟩ HΦ
  iNamed Hm
  wp_apply wp_SnapshotMetadata_GetTerm_field pm pt md.Term' dq Hnn.1 $$ [$HT $cT] as HT
  iapply HΦ
  iunfold smPtsS
  iexists pc, pi, pt, uf
  isplitr
  · ipureintro; exact Hnn
  iframe HC Hc HI HT cI cT Hpb

end defs

end EtcdGrove
end Perennial
