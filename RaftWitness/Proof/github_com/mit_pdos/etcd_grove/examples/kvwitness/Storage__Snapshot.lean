/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kv/Storage__Snapshot.lean`. Lean-first (no
Rocq counterpart). raft v3.7 (2026-10-16, stage R6b): the snapshot's emptiness is read through
`GetMetadata`/`GetIndex` on the fresh clone `MemoryStorage.Snapshot` returns; the error
`ErrSnapshotTemporarilyUnavailable` is not `nil` (`isInitialized`, raft's package fact), so a `nil`
error comes with the clone.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.Storage__Snapshot
public import Spec.go_etcd_io.raft.v3.MemoryStorage__Snapshot
public import Spec.go_etcd_io.raft.v3.raftpb.Snapshot__GetMetadata
public import Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetIndex

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kv

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]
variable [KVStor GF]

theorem Storage.Snapshot.wp_proof
    (wp_MemoryStorage_Snapshot : MemoryStorage.Snapshot.spec (GF := GF) (hG := hG))
    (wp_Snapshot_GetMetadata : raftpb.Snapshot.GetMetadata.spec (GF := GF) (hG := hG))
    (wp_SnapshotMetadata_GetIndex : raftpb.SnapshotMetadata.GetIndex.spec (GF := GF) (hG := hG)) :
    Storage.Snapshot.spec (GF := GF) (hG := hG) := by
  intro s ms γs σ esu n
  wp_start as ⟨#Hms, Hown, #Hesu, #Hn⟩
  ihave #Hraftinit : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  ihave #Hpbinit : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  -- `ErrSnapshotTemporarilyUnavailable` is not `nil`
  ihave #Hinit := isInitialized_access $$ Hraftinit
  iunfold isInitialized at Hinit
  iNamed Hinit
  icombine ErrSnapUnavail Hesu gives %Hesu_eq
  wp_auto
  wp_apply wp_MemoryStorage_Snapshot.1 ms γs σ esu n $$ [$Hraftinit $Hown $Hesu $Hn] as %snap %err ⟨Hown, Hr⟩
  cases err with
  | nil =>
    -- no error: the clone; `ErrSnapshotTemporarilyUnavailable` is not `nil`
    icases Hr with (%Herr | ⟨-, %sv, Hsv, %Hsv⟩)
    · exact absurd (Hesu_eq.trans Herr.symm) HErrSnapUnavail
    wp_auto
    wp_apply wp_Snapshot_GetMetadata.1 snap (DFrac.own 1) sv $$ [$Hpbinit $Hsv] as %pm ⟨Hsm, Hback⟩
    wp_apply wp_SnapshotMetadata_GetIndex pm (DFrac.own 1) sv.Metadata' $$ [$Hpbinit $Hsm] as Hsm
    ihave Hsv := Hback $$ Hsm
    wp_if_destruct
    · -- an empty snapshot: `ErrSnapshotTemporarilyUnavailable`
      iapply HΦ
      iframe Hown
      ileft; ipureintro; exact Hesu_eq
    · iapply HΦ
      iframe Hown
      iright
      isplitr
      · ipureintro; rfl
      iexists sv
      iframe Hsv
      ipureintro; exact ⟨Hif, Hsv.2⟩
  | ok i =>
    wp_auto
    iapply HΦ
    iframe Hown
    icases Hr with (%Herr | ⟨%Herr, -⟩)
    · ileft; ipureintro; exact Herr
    · exact absurd Herr (by simp)

end proof

end kv
end EtcdGrove
end Perennial
