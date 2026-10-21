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

public import Proof.go_etcd_io.raft.v3.InvPbLog

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

/-- A `*pb.SnapshotMetadata` at `p` holding `md`, at `dq`, with every pointer field set: its conf
state (with its `AutoLeave`), its index and its term (see the file header). -/
def smPtsS (p : Loc) (dq : DFrac) (md : SnapshotMetadataM) : IProp GF :=
  iprop(∃ (pc pi pt : Loc) (uf : List w8),
    "%Hnn" ∷ ⌜p ≠ null ∧ pc ≠ null ∧ pi ≠ null ∧ pt ≠ null⌝ ∗
    "HC" ∷ p.[raftpb.SnapshotMetadata, go!"ConfState"] ↦{dq} pc ∗
      "Hc" ∷ csPts pc dq md.ConfState' true ∗
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

/-- A metadata with every pointer field set is one (`smPts`). -/
theorem smPtsS_smPts (p : Loc) (dq : DFrac) (md : SnapshotMetadataM) :
    smPtsS (GF := GF) p dq md ⊢ smPts p dq md := by
  iintro H
  iNamed H
  ihave Hc := csPts_weaken _ _ _ _ $$ Hc
  iunfold smPts
  iexists pc, pi, pt, uf
  isplitr
  · ipureintro; exact Hnn.1
  iframe HC HI HT cI cT Hpb
  iunfold csOptA
  iright; ileft
  iexact Hc

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

end defs

end EtcdGrove
end Perennial
