-- The copy for the part `KvRaft/` of `RaftNoAx/Proof/go_etcd_io/raft/v3/raftpb/CloneCS.lean` (etc/copy-part.py; rerun it, do not edit).
/-
`CloneConfState` (`raftpb/noax.go`) at any `al` (a set `AutoLeave` stays set): the core of
`CloneConfState`'s proof, which `CloneSnapshot`'s also uses (a snapshot's set conf state, `csSet`,
must clone to a set one). The part's own (raft without hand-written axioms,
`notes/raft-noax-part.md`, "Stage 3a").
-/
module

public import KvRaft.Proof.go_etcd_io.raft.v3.raftpb.CloneLeaf
public import KvRaft.Spec.go_etcd_io.raft.v3.raftpb.CloneConfState

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `csPts_of_struct` (`InvPb.lean`) for a struct whose unknown fields are any slice holding no
bytes (a clone's), at any `al` its `AutoLeave` allows. -/
theorem csPts_of_struct_uf (p : Loc) (v : raftpb.ConfState) (c : ConfStateM) (al : Bool)
    (E : CoPset) (Hal : al = true → v.AutoLeave' ≠ null) :
    (p ↦ v ∗ v.Voters' ↦* c.Voters' ∗ v.Learners' ↦* c.Learners' ∗
      v.VotersOutgoing' ↦* c.VotersOutgoing' ∗ v.LearnersNext' ↦* c.LearnersNext' ∗
      cellRO v.AutoLeave' c.AutoLeave' ∗ v.unknownFields' ↦* ([] : List w8) : IProp GF) ⊢
      |={E}=> csPts p (DFrac.own 1) c al := by
  iintro ⟨Hp, Hv, Hl, Ho, Hn, #cA, Hu⟩
  ihave %Hnn := typedPointsto_not_null $$ Hp
  icases typedPointsto_split _ _ _ $$ Hp with Hp
  simp only [TypedPointsto.typedPointstoDef]
  icases Hp with ⟨state, Voters, Learners, VotersOutgoing, LearnersNext, AutoLeave, unknownFields, sizeCache, -⟩
  imod pbMsg_alloc raftpb.ConfState p v.state' v.sizeCache' v.unknownFields' [] E (ufWire_nil _) $$ [state sizeCache unknownFields Hu] with #Hpb
  · iframe
  imodintro
  iunfold csPts
  iexists v.Voters', v.Learners', v.VotersOutgoing', v.LearnersNext', v.AutoLeave'
  isplitr
  · ipureintro; exact Hnn
  iframe
  iframe cA Hpb
  ipureintro; exact Hal

/-- **`CloneConfState` of a conf state**, at any `al`: a fresh owned conf state holding the same
record, its `AutoLeave` set if the original's was. -/
theorem wp_CloneConfState_al (p : Loc) (dq : DFrac) (c : ConfStateM) (al : Bool) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ csPts p dq c al }}
      (App (Val #(functions raftpb.CloneConfState [])) (Val #p))
    {{ (p' : Loc), RET #p'; csPts p dq c al ∗ csPts p' (DFrac.own 1) c al }} := by
  wp_start as Hc
  iapply wp_fupd
  iNamed Hc
  icases nx_cellRO_optCell _ _ $$ cA with ⟨%oa, #Hoa, %Hoa⟩
  ihave %Hpa := optCell_null _ _ $$ Hoa
  icases pbMsg_uf _ _ _ $$ Hpb with ⟨%us, #Hus, #Hub⟩
  wp_auto
  wp_if_destruct
  · exact absurd rfl Hnn
  wp_apply wp_cloneUint64s sv dq c.Voters' $$ [$Hv] as %sv' ⟨Hv, Hv'⟩
  wp_apply wp_cloneUint64s sl dq c.Learners' $$ [$Hl] as %sl' ⟨Hl, Hl'⟩
  wp_apply wp_cloneUint64s so dq c.VotersOutgoing' $$ [$Ho] as %so' ⟨Ho, Ho'⟩
  wp_apply wp_cloneUint64s sn dq c.LearnersNext' $$ [$Hn] as %sn' ⟨Hn, Hn'⟩
  wp_apply wp_cloneBool pa oa $$ [$Hoa] as %pa' #Hoa'
  wp_apply wp_cloneUnknown us [] $$ [$Hub] as %us' Hus'
  ihave %Hpa' := optCell_null _ _ $$ Hoa'
  ihave #cA' : cellRO pa' c.AutoLeave' $$ []
  · rw [Hoa]; iapply nx_optCell_cellRO; iexact Hoa'
  have Hal' : al = true → pa' ≠ null := fun h hn => Hal h (Hpa.2 (Hpa'.1 hn))
  have hv := csPts_of_struct_uf (GF := GF) «$r0_ptr» { (zero_val raftpb.ConfState) with
    Voters' := sv', Learners' := sl', VotersOutgoing' := so', LearnersNext' := sn',
    AutoLeave' := pa', unknownFields' := us' } c al ⊤ Hal'
  imod hv $$ [«$r0» Hv' Hl' Ho' Hn' Hus'] with Hc'
  · iframe «$r0» Hv' Hl' Ho' Hn' Hus' cA'
  imodintro
  iapply HΦ
  iframe Hc'
  iunfold csPts
  iexists sv, sl, so, sn, pa
  isplitr
  · ipureintro; exact Hnn
  iframe HV Hv HL Hl HO Ho HN Hn HA cA Hpb
  ipureintro; exact Hal

/-- `CloneConfState(nil)` is `nil`. -/
theorem wp_CloneConfState_nil :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb }}
      (App (Val #(functions raftpb.CloneConfState [])) (Val #(null : Loc)))
    {{ RET #(null : Loc); True }} := by
  wp_start
  wp_auto
  iapply HΦ; ipureintro; trivial

end lemmas

end EtcdGrove
end Perennial
