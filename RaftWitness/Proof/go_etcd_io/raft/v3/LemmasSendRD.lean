/-
Lemmas of group G2 of stage R4 phase 3 for `raft.restore` and `newRaft`: a snapshot's conf state
held apart from the rest of the snapshot, with fractions, and the snapshot getters on the fields
alone (from their bodies), so that the pointers they return are the fields' (the getters' specs
lend the nested objects and do not say which pointer they return).
-/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.InvPbLog

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-! ### Conf states, by fractions -/

theorem csPts_combine (p : Loc) (dq1 dq2 : DFrac) (c : ConfStateM) (al1 al2 : Bool) :
    csPts (GF := GF) p dq1 c al1 ∗ csPts p dq2 c al2 ⊢ csPts p (dq1 • dq2) c al1 := by
  iintro ⟨H1, H2⟩
  iNamed H1
  iunfold csPts at H2
  icases H2 with ⟨%sv2, %sl2, %so2, %sn2, %pa2, %pw2, %pwo2, -, HV2, Hv2, HL2, Hl2, HO2, Ho2, HN2, Hn2,
    HA2, -, -, HW2, -, HWO2, -, -⟩
  icombine HV HV2 gives %E1
  icombine HL HL2 gives %E2
  icombine HO HO2 gives %E3
  icombine HN HN2 gives %E4
  icombine HA HA2 gives %E5
  icombine HW HW2 gives %E6
  icombine HWO HWO2 gives %E7
  subst E1 E2 E3 E4 E5 E6 E7
  iunfold csPts
  iexists sv, sl, so, sn, pa, pw, pwo
  isplitr
  · ipureintro; exact Hnn
  isplitl [HV HV2]
  · iapply ((typedPointsto_dfractional (GF := GF) _ sv).dfractional dq1 dq2).2; iframe
  isplitl [Hv Hv2]
  · iapply ((ownSlice_dfractional (GF := GF) sv _).dfractional dq1 dq2).2; iframe
  isplitl [HL HL2]
  · iapply ((typedPointsto_dfractional (GF := GF) _ sl).dfractional dq1 dq2).2; iframe
  isplitl [Hl Hl2]
  · iapply ((ownSlice_dfractional (GF := GF) sl _).dfractional dq1 dq2).2; iframe
  isplitl [HO HO2]
  · iapply ((typedPointsto_dfractional (GF := GF) _ so).dfractional dq1 dq2).2; iframe
  isplitl [Ho Ho2]
  · iapply ((ownSlice_dfractional (GF := GF) so _).dfractional dq1 dq2).2; iframe
  isplitl [HN HN2]
  · iapply ((typedPointsto_dfractional (GF := GF) _ sn).dfractional dq1 dq2).2; iframe
  isplitl [Hn Hn2]
  · iapply ((ownSlice_dfractional (GF := GF) sn _).dfractional dq1 dq2).2; iframe
  isplitl [HA HA2]
  · iapply ((typedPointsto_dfractional (GF := GF) _ pa).dfractional dq1 dq2).2; iframe
  iframe cA
  isplitr
  · ipureintro; exact Hal
  isplitl [HW HW2]
  · iapply ((typedPointsto_dfractional (GF := GF) _ pw).dfractional dq1 dq2).2; iframe
  iframe cW
  isplitl [HWO HWO2]
  · iapply ((typedPointsto_dfractional (GF := GF) _ pwo).dfractional dq1 dq2).2; iframe
  iframe cWO Hpb

/-! ### A snapshot whose metadata is set, its conf state apart -/

/-- Everything of `ownSnapE sp dq sv` but the conf state, at the metadata `pm` and the conf state
pointer `pc`. -/
def snapRest (sp pm pc : Loc) (dq : DFrac) (sv : SnapshotM) : IProp GF :=
  iprop(∃ (ds : GoSlice) (pi pt : Loc) (uf ufm : List w8),
    "%Hnn" ∷ ⌜sp ≠ null ∧ pm ≠ null⌝ ∗
    "HD" ∷ sp.[raftpb.Snapshot, go!"Data"] ↦{dq} ds ∗ "Hd" ∷ ds ↦*{dq} sv.Data' ∗
    "HM" ∷ sp.[raftpb.Snapshot, go!"Metadata"] ↦{dq} pm ∗
    "HC" ∷ pm.[raftpb.SnapshotMetadata, go!"ConfState"] ↦{dq} pc ∗
    "HI" ∷ pm.[raftpb.SnapshotMetadata, go!"Index"] ↦{dq} pi ∗
      "#cI" ∷ cellRO pi sv.Metadata'.Index' ∗
    "HT" ∷ pm.[raftpb.SnapshotMetadata, go!"Term"] ↦{dq} pt ∗
      "#cT" ∷ cellRO pt sv.Metadata'.Term' ∗
    "#Hpb" ∷ pbMsg raftpb.Snapshot sp uf ∗ "#Hpbm" ∷ pbMsg raftpb.SnapshotMetadata pm ufm)

theorem ownSnapE_open (sp : Loc) (dq : DFrac) (sv : SnapshotM) :
    ownSnapE (GF := GF) sp dq sv ⊢
      ∃ pm pc, snapRest sp pm pc dq sv ∗ csOptA pc dq sv.Metadata'.ConfState' := by
  iintro H
  iNamed H
  iunfold smPts at Hm
  icases Hm with ⟨%pc, %pi, %pt, %ufm, %Hnnm, HC, Hc, HI, #cI, HT, #cT, #Hpbm⟩
  iexists pm, pc
  iframe Hc
  iunfold snapRest
  iexists ds, pi, pt, uf, ufm
  iframe
  iframe cI cT Hpb Hpbm
  ipureintro; exact ⟨Hnn, Hnnm⟩

theorem ownSnapE_close (sp pm pc : Loc) (dq : DFrac) (sv : SnapshotM) :
    snapRest (GF := GF) sp pm pc dq sv ∗ csOptA pc dq sv.Metadata'.ConfState' ⊢
      ownSnapE sp dq sv := by
  iintro ⟨H, Hc⟩
  iNamed H
  obtain ⟨Hnn1, Hnn2⟩ := Hnn
  iunfold ownSnapE
  iexists ds, pm, uf
  isplitr
  · ipureintro; exact Hnn1
  iframe HD Hd HM Hpb
  iunfold smPts
  iexists pc, pi, pt, ufm
  isplitr
  · ipureintro; exact Hnn2
  iframe
  iframe cI cT Hpbm

theorem snapRest_split (sp pm pc : Loc) (dq1 dq2 : DFrac) (sv : SnapshotM) :
    snapRest (GF := GF) sp pm pc (dq1 • dq2) sv ⊢
      snapRest sp pm pc dq1 sv ∗ snapRest sp pm pc dq2 sv := by
  iintro H
  iNamed H
  icases ((typedPointsto_dfractional (GF := GF) _ ds).dfractional dq1 dq2).1 $$ HD with ⟨HD1, HD2⟩
  icases ((ownSlice_dfractional (GF := GF) ds _).dfractional dq1 dq2).1 $$ Hd with ⟨Hd1, Hd2⟩
  icases ((typedPointsto_dfractional (GF := GF) _ pm).dfractional dq1 dq2).1 $$ HM with ⟨HM1, HM2⟩
  icases ((typedPointsto_dfractional (GF := GF) _ pc).dfractional dq1 dq2).1 $$ HC with ⟨HC1, HC2⟩
  icases ((typedPointsto_dfractional (GF := GF) _ pi).dfractional dq1 dq2).1 $$ HI with ⟨HI1, HI2⟩
  icases ((typedPointsto_dfractional (GF := GF) _ pt).dfractional dq1 dq2).1 $$ HT with ⟨HT1, HT2⟩
  isplitl [HD1 Hd1 HM1 HC1 HI1 HT1]
  · iunfold snapRest
    iexists ds, pi, pt, uf, ufm
    iframe
    iframe cI cT Hpb Hpbm
    ipureintro; exact Hnn
  · iunfold snapRest
    iexists ds, pi, pt, uf, ufm
    iframe
    iframe cI cT Hpb Hpbm
    ipureintro; exact Hnn

theorem snapRest_combine (sp pm pc : Loc) (dq1 dq2 : DFrac) (sv : SnapshotM) :
    snapRest (GF := GF) sp pm pc dq1 sv ∗ snapRest sp pm pc dq2 sv ⊢
      snapRest sp pm pc (dq1 • dq2) sv := by
  iintro ⟨H1, H2⟩
  iNamed H1
  iunfold snapRest at H2
  icases H2 with ⟨%ds2, %pi2, %pt2, %uf2, %ufm2, -, HD2, Hd2, HM2, HC2, HI2, -, HT2, -, -, -⟩
  icombine HD HD2 gives %E1
  icombine HI HI2 gives %E2
  icombine HT HT2 gives %E3
  subst E1 E2 E3
  iunfold snapRest
  iexists ds, pi, pt, uf, ufm
  isplitr
  · ipureintro; exact Hnn
  isplitl [HD HD2]
  · iapply ((typedPointsto_dfractional (GF := GF) _ ds).dfractional dq1 dq2).2; iframe
  isplitl [Hd Hd2]
  · iapply ((ownSlice_dfractional (GF := GF) ds _).dfractional dq1 dq2).2; iframe
  isplitl [HM HM2]
  · iapply ((typedPointsto_dfractional (GF := GF) _ pm).dfractional dq1 dq2).2; iframe
  isplitl [HC HC2]
  · iapply ((typedPointsto_dfractional (GF := GF) _ pc).dfractional dq1 dq2).2; iframe
  isplitl [HI HI2]
  · iapply ((typedPointsto_dfractional (GF := GF) _ pi).dfractional dq1 dq2).2; iframe
  isplitr
  · iexact cI
  isplitl [HT HT2]
  · iapply ((typedPointsto_dfractional (GF := GF) _ pt).dfractional dq1 dq2).2; iframe
  iframe cT Hpb Hpbm

/-- A snapshot handed back (`raftLog.restore`'s post) is the one whose other part `snapRest`
holds: the same metadata and conf state pointers (the fields agree). -/
theorem ownSnapM_tie (sp pm pc : Loc) (dq dq2 : DFrac) (sv : SnapshotM) :
    ownSnapM (GF := GF) sp dq sv ∗ snapRest sp pm pc dq2 sv ⊢
      snapRest sp pm pc dq sv ∗ csOptA pc dq sv.Metadata'.ConfState' ∗ snapRest sp pm pc dq2 sv := by
  iintro ⟨Hs, Hr⟩
  iNamed Hs
  iunfold snapRest at Hr
  icases Hr with ⟨%ds2, %pi2, %pt2, %uf2, %ufm2, %Hnn2, HD2, Hd2, HM2, HC2, HI2, #cI2, HT2, #cT2,
    #Hpb2, #Hpbm2⟩
  icombine HM HM2 gives %E1
  subst E1
  iunfold smOpt at Hm
  icases Hm with (⟨%Hpm, -⟩ | Hm)
  · exact absurd Hpm Hnn2.2
  iunfold smPts at Hm
  icases Hm with ⟨%pc', %pi, %pt, %ufm, %Hnnm, HC, Hc, HI, #cI, HT, #cT, #Hpbm⟩
  icombine HC HC2 gives %E2
  subst E2
  iframe Hc
  isplitr [HD2 Hd2 HM2 HC2 HI2 HT2]
  · iunfold snapRest
    iexists ds, pi, pt, uf, ufm
    iframe
    iframe cI cT Hpb Hpbm
    ipureintro; exact ⟨Hnn, Hnnm⟩
  · iunfold snapRest
    iexists ds2, pi2, pt2, uf2, ufm2
    iframe
    iframe cI2 cT2 Hpb2 Hpbm2
    ipureintro; exact Hnn2

theorem ownSnapM_of_rest (sp pm pc : Loc) (dq : DFrac) (sv : SnapshotM) :
    snapRest (GF := GF) sp pm pc dq sv ∗ csOptA pc dq sv.Metadata'.ConfState' ⊢
      ownSnapM sp dq sv := by
  iintro H
  iapply ownSnapE_weaken
  iapply ownSnapE_close $$ H

/-! ### The snapshot getters on the fields -/

theorem wp_Snapshot_GetMetadata_field (sp pm : Loc) (dq : DFrac) (Hnn : sp ≠ null) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗
        sp.[raftpb.Snapshot, go!"Metadata"] ↦{dq} pm }}
      (App (Val (sp @!! go.GoType.PointerType raftpb.Snapshot.ty @!! go!"GetMetadata")) (Val #()))
    {{ RET #pm; sp.[raftpb.Snapshot, go!"Metadata"] ↦{dq} pm }} := by
  wp_start as HM
  wp_auto
  wp_if_destruct
  · exact absurd rfl Hnn
  · iapply HΦ
    iframe HM

theorem wp_SnapshotMetadata_GetConfState_field (pm pc : Loc) (dq : DFrac) (Hnn : pm ≠ null) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗
        pm.[raftpb.SnapshotMetadata, go!"ConfState"] ↦{dq} pc }}
      (App (Val (pm @!! go.GoType.PointerType raftpb.SnapshotMetadata.ty @!! go!"GetConfState"))
        (Val #()))
    {{ RET #pc; pm.[raftpb.SnapshotMetadata, go!"ConfState"] ↦{dq} pc }} := by
  wp_start as HC
  wp_auto
  wp_if_destruct
  · exact absurd rfl Hnn
  · iapply HΦ
    iframe HC

theorem wp_SnapshotMetadata_GetIndex_field (pm pi : Loc) (v : w64) (dq : DFrac)
    (Hnn : pm ≠ null) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗
        pm.[raftpb.SnapshotMetadata, go!"Index"] ↦{dq} pi ∗ cellRO pi v }}
      (App (Val (pm @!! go.GoType.PointerType raftpb.SnapshotMetadata.ty @!! go!"GetIndex"))
        (Val #()))
    {{ RET #v; pm.[raftpb.SnapshotMetadata, go!"Index"] ↦{dq} pi }} := by
  wp_start as ⟨HI, #cI⟩
  wp_auto
  wp_if_destruct
  · exact absurd rfl Hnn
  ihave (⟨%Hq, %Hv⟩ | ⟨#Hq, %Hqn⟩) := cellRO_cases $$ cI
  · subst Hq
    wp_auto
    rw [show (W64 0) = v from Hv.symm]
    iapply HΦ
    iframe
  · wp_if_destruct
    · exact absurd rfl Hqn
    · iapply HΦ
      iframe

theorem wp_SnapshotMetadata_GetTerm_field (pm pt : Loc) (v : w64) (dq : DFrac)
    (Hnn : pm ≠ null) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗
        pm.[raftpb.SnapshotMetadata, go!"Term"] ↦{dq} pt ∗ cellRO pt v }}
      (App (Val (pm @!! go.GoType.PointerType raftpb.SnapshotMetadata.ty @!! go!"GetTerm"))
        (Val #()))
    {{ RET #v; pm.[raftpb.SnapshotMetadata, go!"Term"] ↦{dq} pt }} := by
  wp_start as ⟨HT, #cT⟩
  wp_auto
  wp_if_destruct
  · exact absurd rfl Hnn
  ihave (⟨%Hq, %Hv⟩ | ⟨#Hq, %Hqn⟩) := cellRO_cases $$ cT
  · subst Hq
    wp_auto
    rw [show (W64 0) = v from Hv.symm]
    iapply HΦ
    iframe
  · wp_if_destruct
    · exact absurd rfl Hqn
    · iapply HΦ
      iframe

end lemmas

end EtcdGrove
end Perennial
