/- `MemoryStorage.ApplySnapshot` (`storage.go:218`; U8 v2 step 3). The stored snapshot's index is
`0` or frozen in the map, so below the caller's owned range from `j ≤ s` (`s` the argument's index):
the out-of-date test fails. The caller's range is deleted from the map, the dummy at `s` inserted
frozen, the end moved to `s + 1`, the compaction point to `s` (registered with `J.B s`), and the
snapshot replaced by the clone (taken out of its home with the lock's key), its index's authority
raised to `s` (kvreconf-snapshot-thread, 2026-10-30: `memSnapLb γs s`, no client snapshot half). -/
module

public import Spec.go_etcd_io.raft.v3.MemoryStorage__ApplySnapshot
public import Spec.go_etcd_io.raft.v3.raftpb.EnsureSnapshot
public import Spec.go_etcd_io.raft.v3.raftpb.Snapshot__GetMetadata
public import Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetIndex
public import Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetTerm
public import Spec.google_golang_org.protobuf.proto.CloneSnapshot
public import Proof.go_etcd_io.raft.v3.LemmasMemstorage

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

/-- (D22 S-d4, 2026-10-21) `EnsureSnapshot` of `ApplySnapshot`'s argument (`snapArg`): owned, it may
write its `nil` fields; at a fraction, with every pointer field set, it writes nothing. Either way
the same pointer, holding the same snapshot at the same fraction. -/
private theorem wp_EnsureSnapshot_arg
    (wp_EnsureSnapshot : raftpb.EnsureSnapshot.spec (GF := GF) (hG := hG))
    (sp : Loc) (dq : DFrac) (sv : SnapshotM) (Hnn : sp ≠ null) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ snapArg sp dq sv }}
      (App (Val #(functions raftpb.EnsureSnapshot [])) (Val #sp))
    {{ RET #sp; ownSnapM sp dq sv }} := by
  iintro %Φ ⟨#Hinit, Hs⟩ HΦ
  iunfold snapArg at Hs
  icases Hs with (⟨%Hdq, Hs⟩ | Hs)
  · subst Hdq
    wp_apply wp_EnsureSnapshot.1 sp (some sv) $$ [Hs] as %r ⟨Hr, %Hrsp⟩
    · simp only [snapOpt]; iexact Hs
    ihave Hr := ownSnapS_W _ _ _ $$ Hr
    ihave Hr := ownSnapW_E $$ Hr
    have Hr' : r = sp := Hrsp Hnn
    subst Hr'
    simp only [Option.getD_some]
    iapply HΦ
    iapply ownSnapE_weaken $$ Hr
  · wp_apply wp_EnsureSnapshot.2 sp dq sv $$ [$Hs] as Hs
    iapply HΦ
    iapply ownSnapS_M $$ Hs

theorem MemoryStorage.ApplySnapshot.wp_proof
    (wp_EnsureSnapshot : raftpb.EnsureSnapshot.spec (GF := GF) (hG := hG))
    (wp_GetMetadata : raftpb.Snapshot.GetMetadata.spec (GF := GF) (hG := hG))
    (wp_GetIndex : raftpb.SnapshotMetadata.GetIndex.spec (GF := GF) (hG := hG))
    (wp_GetTerm : raftpb.SnapshotMetadata.GetTerm.spec (GF := GF) (hG := hG))
    (wp_CloneSnapshot : proto.CloneSnapshot.spec (GF := GF) (hG := hG)) :
    MemoryStorage.ApplySnapshot.spec (GF := GF) (hG := hG) := by
  sorry -- durability stage I (I-5): statement changed (mode o / detached memStorFresh c sv)

end proof

end EtcdGrove
end Perennial
