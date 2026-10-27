/-
`EnsureSnapshotMetadata` (`raftpb/util.go:33`, new in raft v3.7). Lean-first (raft v3.7
retarget, stage R1).
-/
module

public import Proof.go_etcd_io.raft.v3.InvPbSnapSet

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `EnsureSnapshotMetadata(m)` of a metadata pointer, `nil` or owned (fully: it may write its
fields and its conf state's `AutoLeave`) holding `md`: a non-`nil` metadata holding `md`, owned;
`m` itself when `m` was not `nil`. The record does not change: every `nil` field it fills reads
as the zero value it is given (`EnsureConfState` on the conf state). Since D17d (2026-10-18) its
`ConfState` set too (`smPtsW`); since D22 S-d4 item 4 (2026-10-21) every pointer field (`smPtsS`). -/
abbrev raftpb.EnsureSnapshotMetadata.spec : Prop :=
  (∀ (m : Loc) (md : SnapshotMetadataM),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ smOpt m (DFrac.own 1) md }}
      (App (Val #(functions raftpb.EnsureSnapshotMetadata [])) (Val #m))
    {{ (r : Loc), RET #r; smPtsS r (DFrac.own 1) md ∗ ⌜m ≠ null → r = m⌝ }}) ∧
  -- (D22 S-d4, 2026-10-21) every pointer field set (`smPtsS`), at any fraction: nothing written
  (∀ (m : Loc) (dq : DFrac) (md : SnapshotMetadataM),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ smPtsS m dq md }}
      (App (Val #(functions raftpb.EnsureSnapshotMetadata [])) (Val #m))
    {{ RET #m; smPtsS m dq md }})

end spec

end EtcdGrove
end Perennial
