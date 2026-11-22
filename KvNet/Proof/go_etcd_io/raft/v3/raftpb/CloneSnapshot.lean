-- The copy for the part `KvNet/` of `RaftNoAx/Proof/go_etcd_io/raft/v3/raftpb/CloneSnapshot.lean` (etc/copy-part.py; rerun it, do not edit).
/-
Proof of `RaftNoAx/Spec/go_etcd_io/raft/v3/raftpb/CloneSnapshot.lean`: the part's own (raft without
hand-written axioms, `notes/raft-noax-part.md`, "Stage 3a"). One core triple on a non-`nil`
snapshot's fields, the metadata's clone abstracted as a triple (`R`/`Q`); each of the four
ownership forms instantiates it with its metadata form's clone (`CloneSM.lean`), and `CloneConfState`
is proved again inside (`wp_CloneConfState_al`, which keeps a set `AutoLeave` set, as `ownSnapS`
needs), not taken as a callee spec.
-/
module

public import KvNet.Proof.go_etcd_io.raft.v3.raftpb.CloneSM

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **`CloneSnapshot` of a non-`nil` snapshot**, by its fields; the metadata's clone a triple. -/
private theorem wp_CloneSnapshot_core (p : Loc) (ds : GoSlice) (pm : Loc) (dq : DFrac)
    (s : SnapshotM) (uf : List w8) (R : IProp GF) (Q : Loc → IProp GF)
    (hsm : {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ R }}
      (App (Val #(functions raftpb.cloneSnapshotMetadata [])) (Val #pm))
      {{ (pm' : Loc), RET #pm'; R ∗ Q pm' }})
    (hp : p ≠ null) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗
        p.[raftpb.Snapshot, go!"Data"] ↦{dq} ds ∗ ds ↦*{dq} s.Data' ∗
        p.[raftpb.Snapshot, go!"Metadata"] ↦{dq} pm ∗ R ∗ pbMsg raftpb.Snapshot p uf }}
      (App (Val #(functions raftpb.CloneSnapshot [])) (Val #p))
    {{ (p' : Loc), RET #p';
        p.[raftpb.Snapshot, go!"Data"] ↦{dq} ds ∗ ds ↦*{dq} s.Data' ∗
        p.[raftpb.Snapshot, go!"Metadata"] ↦{dq} pm ∗ R ∗
        ∃ (ds' : GoSlice) (pm' : Loc), ⌜p' ≠ null⌝ ∗
          p'.[raftpb.Snapshot, go!"Data"] ↦ ds' ∗ ds' ↦* s.Data' ∗
          p'.[raftpb.Snapshot, go!"Metadata"] ↦ pm' ∗ Q pm' ∗ pbMsg raftpb.Snapshot p' uf }} := by
  wp_start as ⟨HD, Hd, HM, HR, #Hpb⟩
  iapply wp_fupd
  ihave %Huf := pbMsg_ufWire _ _ _ $$ Hpb
  icases pbMsg_uf _ _ _ $$ Hpb with ⟨%us, #Hus, #Hub⟩
  wp_auto
  wp_if_destruct
  · exact absurd rfl hp
  wp_apply wp_cloneBytes ds dq s.Data' $$ [$Hd] as %ds' ⟨Hd, Hd', -⟩
  wp_apply hsm $$ [$HR] as %pm' ⟨HR, HQ⟩
  wp_apply wp_cloneUnknown us uf $$ [$Hub] as %us' Hus'
  ihave %Hnn := typedPointsto_not_null $$ «$r0»
  icases typedPointsto_split _ _ _ $$ «$r0» with Hp
  simp only [TypedPointsto.typedPointstoDef]
  icases Hp with ⟨state, Data, Metadata, unknownFields, sizeCache, -⟩
  imod pbMsg_alloc raftpb.Snapshot _ _ _ _ uf ⊤ Huf $$ [state sizeCache unknownFields Hus'] with #Hpb'
  · iframe
  imodintro
  iapply HΦ
  iframe HD Hd HM HR
  iexists ds', pm'
  iframe
  iframe Hpb'
  ipureintro; exact Hnn

theorem raftpb.CloneSnapshot.wp_proof : raftpb.CloneSnapshot.spec (GF := GF) (hG := hG) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p dq s
    iintro %Φ ⟨#Hi, Hs⟩ HΦ
    iNamed Hs
    iapply wp_CloneSnapshot_core p ds pm dq s uf _ _ (wp_cloneSM_opt pm dq s.Metadata') Hnn
      $$ [$Hi $HD $Hd $HM $Hm $Hpb]
    iintro %p'
    inext
    iintro ⟨HD, Hd, HM, Hm, %ds', %pm', %Hn', HD', Hd', HM', Hm', #Hpb'⟩
    iapply HΦ
    isplitl [HD Hd HM Hm]
    · iunfold ownSnapM
      iexists ds, pm, uf
      isplitr
      · ipureintro; exact Hnn
      iframe HD Hd HM Hm Hpb
    · iunfold ownSnapM
      iexists ds', pm', uf
      isplitr
      · ipureintro; exact Hn'
      iframe HD' Hd' HM' Hm' Hpb'
  · wp_start
    wp_auto
    iapply HΦ; ipureintro; trivial
  · intro p dq s
    iintro %Φ ⟨#Hi, Hs⟩ HΦ
    iNamed Hs
    iapply wp_CloneSnapshot_core p ds pm dq s uf _ _ (wp_cloneSM_W pm dq s.Metadata') Hnn
      $$ [$Hi $HD $Hd $HM $Hm $Hpb]
    iintro %p'
    inext
    iintro ⟨HD, Hd, HM, Hm, %ds', %pm', %Hn', HD', Hd', HM', Hm', #Hpb'⟩
    iapply HΦ
    isplitl [HD Hd HM Hm]
    · iunfold ownSnapW
      iexists ds, pm, uf
      isplitr
      · ipureintro; exact Hnn
      iframe HD Hd HM Hm Hpb
    · iunfold ownSnapW
      iexists ds', pm', uf
      isplitr
      · ipureintro; exact Hn'
      iframe HD' Hd' HM' Hm' Hpb'
  · intro p dq s
    iintro %Φ ⟨#Hi, Hs⟩ HΦ
    iNamed Hs
    iapply wp_CloneSnapshot_core p ds pm dq s uf _ _ (wp_cloneSM_S pm dq s.Metadata') Hnn
      $$ [$Hi $HD $Hd $HM $Hm $Hpb]
    iintro %p'
    inext
    iintro ⟨HD, Hd, HM, Hm, %ds', %pm', %Hn', HD', Hd', HM', Hm', #Hpb'⟩
    iapply HΦ
    isplitl [HD Hd HM Hm]
    · iunfold ownSnapS
      iexists ds, pm, uf
      isplitr
      · ipureintro; exact Hnn
      iframe HD Hd HM Hm Hpb
    · iunfold ownSnapS
      iexists ds', pm', uf
      isplitr
      · ipureintro; exact Hn'
      iframe HD' Hd' HM' Hm' Hpb'
  · intro p dq s
    iintro %Φ ⟨#Hi, Hs⟩ HΦ
    iNamed Hs
    iapply wp_CloneSnapshot_core p ds pm dq s uf _ _ (wp_cloneSM_V pm dq s.Metadata') Hnn
      $$ [$Hi $HD $Hd $HM $Hm $Hpb]
    iintro %p'
    inext
    iintro ⟨HD, Hd, HM, Hm, %ds', %pm', %Hn', HD', Hd', HM', Hm', #Hpb'⟩
    iapply HΦ
    isplitl [HD Hd HM Hm]
    · iunfold ownSnapV
      iexists ds, pm, uf
      isplitr
      · ipureintro; exact Hnn
      iframe HD Hd HM Hm Hpb
    · iunfold ownSnapV
      iexists ds', pm', uf
      isplitr
      · ipureintro; exact Hn'
      iframe HD' Hd' HM' Hm' Hpb'

end proof

end EtcdGrove
end Perennial
