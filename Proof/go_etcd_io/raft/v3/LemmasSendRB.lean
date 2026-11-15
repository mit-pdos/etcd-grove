/-
Lemmas of group G2 (fork B: `appendEntry`, `handleAppendEntries`, `handleHeartbeat`,
`handleSnapshot`) of stage R4 phase 3.
-/
module

public import Proof.go_etcd_io.raft.v3.LemmasSendR
public import Spec.go_etcd_io.raft.v3.raftpb.Snapshot__GetMetadata

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

/-- A metadata pointer known not `nil`: owned. -/
theorem smOpt_not_null (p : Loc) (dq : DFrac) (md : SnapshotMetadataM) (Hnn : p ≠ null) :
    smOpt (GF := GF) p dq md ⊢ smPts p dq md := by
  iunfold smOpt
  iintro (%H | H)
  · exact absurd H.1 Hnn
  · iexact H

theorem smPts_not_null (p : Loc) (dq : DFrac) (md : SnapshotMetadataM) :
    smPts (GF := GF) p dq md ⊢ ⌜p ≠ null⌝ ∗ smPts p dq md := by
  iintro H
  ihave %Hnn : ⌜p ≠ null⌝ $$ [H]
  · iunfold smPts at H; iNamed H; ipureintro; exact Hnn
  iframe H; ipureintro; exact Hnn

/-- `s.GetMetadata()` on a snapshot whose metadata is set (`ownSnapE`, what `EnsureSnapshot`
returns), the metadata lent as set (R1's spec is on `ownSnapM`, whose metadata may be `nil`, and
its wand does not say the field is unchanged): `GetMetadata`'s body, `if x != nil { return
x.Metadata }`, proved again. -/
theorem wp_Snapshot_GetMetadata_E (p : Loc) (dq : DFrac) (s : SnapshotM) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ ownSnapE p dq s }}
      (App (Val (p @!! go.GoType.PointerType raftpb.Snapshot.ty @!! go!"GetMetadata"))
        (Val #()))
    {{ (pm : Loc), RET #pm;
        smPts pm dq s.Metadata' ∗ (smPts pm dq s.Metadata' -∗ ownSnapE p dq s) }} := by
  wp_start as Hs
  iNamed Hs
  wp_auto
  wp_if_destruct
  · exact absurd rfl Hnn
  · iapply HΦ
    iframe Hm
    iintro Hm
    iunfold ownSnapE
    iexists ds, pm, uf
    isplitr
    · ipureintro; exact Hnn
    iframe
    iframe Hpb

/-- `cloned[i].Term = new(r.Term)` (`appendEntry`, `raft.go:836`): a fresh cell stored into the
clone, which raft owns (out_size C3: at its content, `proto.ClonePb`'s owned `decC`). -/
theorem entPtsCC_store_Term (l : Loc) (c : EntryC) :
    entPtsCC (GF := GF) l (DFrac.own 1) c ⊢
      ∃ p : Loc, l.[raftpb.Entry, go!"Term"] ↦ p ∗
        (∀ (p' : Loc) (v : w64), l.[raftpb.Entry, go!"Term"] ↦ p' -∗ p' ↦□ v -∗
          entPtsCC l (DFrac.own 1) { c with term := some v }) := by
  iintro H
  unfold entPtsCC
  icases H with ⟨%pt, %pi, %pty, %ds, %Hnn, HT, #cT, HI, #cI, HY, #cY, HD, #Hd, #Hpb⟩
  iexists pt
  iframe HT
  iintro %p' %v HT #Hp'
  iexists p', pi, pty, ds
  isplitr
  · ipureintro; exact Hnn
  iframe HT HI HY HD cI cY Hd Hpb
  simp only [optCell]; iexact Hp'

/-- `cloned[i].Index = new(li + 1 + uint64(i))` (`appendEntry`, `raft.go:837`). -/
theorem entPtsCC_store_Index (l : Loc) (c : EntryC) :
    entPtsCC (GF := GF) l (DFrac.own 1) c ⊢
      ∃ p : Loc, l.[raftpb.Entry, go!"Index"] ↦ p ∗
        (∀ (p' : Loc) (v : w64), l.[raftpb.Entry, go!"Index"] ↦ p' -∗ p' ↦□ v -∗
          entPtsCC l (DFrac.own 1) { c with index := some v }) := by
  iintro H
  unfold entPtsCC
  icases H with ⟨%pt, %pi, %pty, %ds, %Hnn, HT, #cT, HI, #cI, HY, #cY, HD, #Hd, #Hpb⟩
  iexists pi
  iframe HI
  iintro %p' %v HI #Hp'
  iexists pt, p', pty, ds
  isplitr
  · ipureintro; exact Hnn
  iframe HT HI HY HD cT cY Hd Hpb
  simp only [optCell]; iexact Hp'

end lemmas

end EtcdGrove
end Perennial
